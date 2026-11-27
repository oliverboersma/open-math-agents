import FormalConjectures.Wikipedia.EllipticCurveRank

/-
Adapted from github.com/b-mehta/EllipticCurveRank (commit 9cb92e9a7ddf28666d89cb221a89fb35de75b4d3),
(c) 2026 Bhavik Mehta, GPL-3.0 (rank certificate checker, descent characters, F2 matrix inverse, data of curves 11, 273 and 302);
and from github.com/MichaelStollBayreuth/EllipticCurves (commit 2164fb57f067b75cd515029cddb2be50fd059983),
(c) 2026 Michael Stoll, Apache-2.0 (Mordell-Weil theorem, weak Mordell-Weil, Selmer groups);
plus the naive height and approximate parallelogram law for elliptic curves from Mathlib
(v4.36.0, (c) Michael Stoll and Mathlib contributors, Apache-2.0), backported to the Mathlib pin.
Ported to Lean v4.33.1 and merged into one file; the bridge OMA.solution is new.
-/

abbrev IsMulFG (M : Type*) [Group M] : Prop := Group.FG M
abbrev IsAddFG (M : Type*) [AddGroup M] : Prop := AddGroup.FG M
abbrev HasUniqueDiv (M : Type*) [AddMonoid M] : Prop := IsAddTorsionFree M

noncomputable def Ideal.ramIdxU {S : Type*} [CommRing S] (P : Ideal S) (R : Type*) [CommRing R]
    [Algebra R S] : ℕ := Ideal.ramificationIdx' (P.under R) P

instance numberFieldUnitsGroupFG (K : Type*) [Field K] [NumberField K] :
    Group.FG (NumberField.RingOfIntegers K)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance

namespace WeierstrassCurve.Affine

section MLFormula
variable {R : Type*} {F : Type*} [CommRing R] [Field F] {W' : Affine R} {W : Affine F} [DecidableEq F]


lemma addX_of_X_ne {x₁ y₁ x₂ y₂ : F} (hn : x₁ ≠ x₂) :
     W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) =
       ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) - (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^2) /
         (x₁ - x₂) ^ 2 := by
  grind only [addX, slope]




lemma den_duplication_eq {x y : R} (h : W'.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = (2 * y + W'.a₁ * x + W'.a₃) ^ 2 := by
  have Heq := (W'.equation_iff x y).mp h
  simp only [b₂, b₄, b₆]
  linear_combination -4 * Heq


lemma den_duplication_eq_zero_iff [IsReduced R] {x y : R} (h : W'.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = 0 ↔ y = W'.negY x y := by
  rw [den_duplication_eq h, sq_eq_zero_iff, negY]
  grind only


lemma den_duplication_ne_zero_or_num_duplication_ne_zero {x y : F} (h : W.Nonsingular x y) :
    4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ≠ 0 ∨
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ ≠ 0 := by
  have ⟨h₁, h₂⟩ := (W.nonsingular_iff x y).mp h
  rw [equation_iff x y] at h₁
  by_cases H : 2 * y + W.a₁ * x + W.a₃ = 0
  · right
    replace h₂ : W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by grind
    contrapose h₂
    rw [b₄, b₆, b₈] at h₂
    grobner
  · left
    clear h₂
    contrapose H
    rw [b₂, b₄, b₆] at H
    grobner


lemma addX_self_of_Y_ne {x y : F} (h : W.Equation x y) (hn : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) =
      (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  have aux {a b c : F} (h : a ≠ 0) : a ^ 2 * (b * (c / a)) = a * b * c := by field
  have hn' := (den_duplication_eq_zero_iff h).not.mpr hn
  refine mul_left_cancel₀ hn' ?_
  have hn'' : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [den_duplication_eq h] at hn'
    grind
  rw [mul_div_cancel₀ _ hn', addX, sub_sub, sub_sub, mul_sub, mul_add]
  simp only [slope, ↓reduceIte, hn]
  rw [negY, show y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ by ring, div_pow]
  nth_rewrite 1 2 [den_duplication_eq h]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hn'', aux hn'', b₂, b₄, b₆, b₈]
  linear_combination -W.a₁ ^ 2 * (W.equation_iff x y).mp h


end MLFormula

namespace Point
section MLPoint
variable {F : Type*} [Field F] {W : Affine F}
variable [DecidableEq F]


lemma xRep_add_self_of_Y_ne {x y : F} (h : W.Nonsingular x y) (hn : y ≠ W.negY x y) :
    (some x y h + some x y h).xRep =
      ![(x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆), 1] := by
  simp only [add_self_of_Y_ne hn, ← addX_self_of_Y_ne h.1 hn, xRep_some]


lemma xRep_add_self_of_Y_eq {x y : F} (h : W.Nonsingular x y) (hn : y = W.negY x y) :
    (some x y h + some x y h).xRep = ![1, 0] := by
  simp only [add_self_of_Y_eq hn, xRep_zero]


lemma xRep_add_of_X_ne {xP yP xQ yQ : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hn : xP ≠ xQ) :
    (some xP yP hP + some xQ yQ hQ).xRep =
      ![((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) - (W.a₂ + xP + xQ) * (xP - xQ) ^2) /
         (xP - xQ) ^ 2, 1] := by
  simp only [add_of_X_ne (h₁ := hP) (h₂ := hQ) hn, xRep_some, addX_of_X_ne hn]


lemma xRep_sub_of_X_ne {xP yP xQ yQ : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hn : xP ≠ xQ) :
    (some xP yP hP - some xQ yQ hQ).xRep =
      ![((yP + yQ + W.a₁ * xQ + W.a₃) ^ 2 + W.a₁ * (yP + yQ + W.a₁ * xQ + W.a₃) * (xP - xQ)
           - (W.a₂ + xP + xQ) * (xP - xQ) ^2) / (xP - xQ) ^ 2, 1] := by
  simp only [sub_eq_add_neg (some ..), neg_some hQ,
    add_of_X_ne (h₁ := hP) (h₂ := (nonsingular_neg ..).mpr hQ) hn, xRep_some,
    addX_of_X_ne hn]
  grind only [negY]


end MLPoint
end Point

section MLQ
variable {F : Type*} [Field F] {W : Affine F}
lemma finite_preimage_xRep (x : F) : {P : W.Point | P.xRep = ![x, 1]}.Finite := by
  rcases Set.eq_empty_or_nonempty {P : W.Point | P.xRep = ![x, 1]} with h | h
  · exact h ▸ Set.finite_empty
  choose Q hQ using h
  simp only [Set.mem_setOf_eq] at hQ
  rw [show {P | P.xRep = ![x, 1]} = {Q, -Q} by ext : 1; simp [← hQ, Point.xRep_eq_xRep_iff]]
  simp

lemma finite_preimage_xRep0 (x : F) : {P : W.Point | P.xRep 0 = x}.Finite := by
  have : {P : W.Point | P.xRep 0 = x} ⊆ {P | P.xRep = ![x, 1]} ∪ {0} := by
    intro P hP
    match P with
    | 0 => simp
    | .some x' y h => simp_all [Point.xRep_some]
  exact (finite_preimage_xRep x).union (Set.finite_singleton 0) |>.subset this


end MLQ
end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.Point

variable {R : Type*} [CommRing R] {W' : Affine R}

lemma sym2x_eq {P Q : W'.Point} :
    sym2x P Q =
      ![P.xRep 0 * Q.xRep 0, P.xRep 0 * Q.xRep 1 + P.xRep 1 * Q.xRep 0, P.xRep 1 * Q.xRep 1] :=
  (rfl)


open Nat in
lemma sym2x_self_eq_addSubMap (P : W'.Point) :
    sym2x P P = (addSubMap W' · |>.eval <| sym2x P 0) := by
  match P with
  | 0 => ext i : 1; fin_cases i <;> simp [addSubMap]
  | some .. => ext i : 1; fin_cases i <;> simp [pow_two, two_mul, addSubMap]

section Field

variable {F : Type*} [Field F] {W : Affine F}


lemma addSubMap_sym2x_some_some {xP yP xQ yQ : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) :
    (addSubMap W · |>.eval <| sym2x (some xP yP hP) (some xQ yQ hQ)) =
      ![(xP * xQ) ^ 2 - W.b₄ * (xP * xQ) - W.b₆ * (xP + xQ) - W.b₈,
        2 * (xP + xQ) * (xP * xQ) + W.b₂ * (xP * xQ) + W.b₄ * (xP + xQ) + W.b₆, (xP - xQ) ^ 2] := by
  ext i : 1
  fin_cases i <;> simp [addSubMap]
  ring


lemma addSubMap_sym2x_some_self {x y : F} (h : W.Nonsingular x y) :
    (addSubMap W · |>.eval <| sym2x (some x y h) (some x y h)) =
      ![x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈,
        4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆, 0] := by
  rw [addSubMap_sym2x_some_some]
  ext i : 1
  fin_cases i <;> dsimp <;> ring

variable [DecidableEq F]


private lemma sym2x_add_self_zero (P : W.Point) :
    ∃ t : F, t ≠ 0 ∧ t • sym2x (P + P) 0 = (addSubMap W · |>.eval <| sym2x P P) := by
  match P with
  | 0 => exact ⟨1, one_ne_zero, by ext i : 1; fin_cases i <;> simp [addSubMap]⟩
  | some x y h =>
    have Heq := (W.equation_iff x y).mp h.1
    rw [addSubMap_sym2x_some_self]
    by_cases H : y = W.negY x y
    · have H' := (den_duplication_eq_zero_iff h.1).mpr H
      rw [H', add_self_of_Y_eq H, sym2x_zero_zero]
      refine ⟨_, den_duplication_ne_zero_or_num_duplication_ne_zero h |>.neg_resolve_left H', ?_⟩
      simp
    · have H' := (den_duplication_eq_zero_iff h.1).not.mpr H
      exact ⟨_, H', by simp [sym2x, xRep_add_self_of_Y_ne h H, mul_div_cancel₀ _ H']⟩


lemma sym2x_add_sub_eq_addSubMap_sym2x (P Q : W.Point) :
    ∃ t : F, t ≠ 0 ∧ t • sym2x (P + Q) (P - Q) = (addSubMap W · |>.eval <| sym2x P Q) := by
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using P.sym2x_add_self_zero
  rcases eq_or_ne Q (-P) with rfl | hPQ'
  · simpa [sym2x_comm, sym2x_neg_right] using P.sym2x_add_self_zero
  match P, Q with
  | P, 0 =>  exact ⟨1, one_ne_zero, by simpa using P.sym2x_self_eq_addSubMap⟩
  | 0, Q =>
    refine ⟨1, one_ne_zero, ?_⟩
    simpa [sym2x_comm, sym2x_neg_right, sym2x_neg_left] using Q.sym2x_self_eq_addSubMap
  | some xP yP hP, some xQ yQ hQ =>
    have hxPQ : xP ≠ xQ := fun Heq ↦ by grind only [X_eq_iff.mp Heq]
    refine ⟨(xP - xQ) ^ 2, pow_ne_zero 2 (sub_ne_zero_of_ne hxPQ), ?_⟩
    rw [addSubMap_sym2x_some_some, sym2x, xRep_add_of_X_ne hP hQ hxPQ,
      xRep_sub_of_X_ne hP hQ hxPQ, b₂, b₄, b₆, b₈]
    ext i : 1
    
    have HeqP := (W.equation_iff xP yP).mp hP.1
    have HeqQ := (W.equation_iff xQ yQ).mp hQ.1
    fin_cases i <;> simp [field] <;> grobner

end Field


end WeierstrassCurve.Affine.Point

namespace WeierstrassCurve.Affine

open Height

variable {F : Type*} [Field F] [AdmissibleAbsValues F] {W : Affine F}

section NaiveHeight


noncomputable def Point.mwHeight (P : W.Point) : ℝ :=
  logHeight P.xRep

lemma Point.mwHeight_eq_logHeight (P : W.Point) : P.mwHeight = logHeight P.xRep :=
  (rfl)

lemma Point.mwHeight_eq_logHeight₁ {P : W.Point} :
    P.mwHeight = logHeight₁ (P.xRep 0) := by
  match P with
  | 0 => simp [mwHeight, xRep]
  | some .. => simpa [mwHeight] using (logHeight₁_eq_logHeight _).symm

variable (W)

lemma abs_logHeight_sym2x_sub_le :
    ∃ C, ∀ P Q : W.Point, |logHeight (P.sym2x Q) - (P.mwHeight + Q.mwHeight)| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight_sym2_sub_le F
  refine ⟨C, fun P Q ↦ ?_⟩
  rw [P.mwHeight_eq_logHeight, Q.mwHeight_eq_logHeight, Point.sym2x_eq]
  have H₁ := logHeight_fun_mul_eq P.xRep_ne_zero Q.xRep_ne_zero
  have H (v : Fin 2 → F) : ![v 0, v 1] = v := by ext i : 1; fin_cases i <;> simp
  have h₀ (P : W.Point) : ![P.xRep 0, P.xRep 1] ≠ 0 := H P.xRep ▸ P.xRep_ne_zero
  specialize hC (h₀ P) (h₀ Q)
  rw [H P.xRep, H Q.xRep] at *
  grind only [= abs.eq_1, = max_def]

variable [W.IsElliptic]


theorem approx_parallelogram_law [DecidableEq F] :
    ∃ C, ∀ (P Q : W.Point),
      |(P + Q).mwHeight + (P - Q).mwHeight - 2 * (P.mwHeight + Q.mwHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := abs_logHeight_sym2x_sub_le W
  obtain ⟨C₂, hC₂⟩ := abs_logHeight_addSubMap_sub_two_mul_logHeight_le W
  refine ⟨3 * C₁ + C₂, fun P Q ↦ ?_⟩
  obtain ⟨t, ht₀, ht⟩ := Point.sym2x_add_sub_eq_addSubMap_sym2x P Q
  replace ht := congrArg logHeight ht
  rw [Height.logHeight_smul_eq_logHeight _ ht₀] at ht
  have hPQ := hC₁ P Q
  have haddsub := hC₁ (P + Q) (P - Q)
  have hC := ht ▸ hC₂ (P.sym2x Q)
  grind only [= abs.eq_1, = max_def]

end NaiveHeight

section Northcott

instance [Northcott (logHeight₁ (K := F))] : Northcott (Point.mwHeight (F := F) (W := W)) := by
  eta_expand
  simp only [Point.mwHeight_eq_logHeight₁]
  rw [← Function.comp_def]
  have : Filter.TendstoCofinite fun P : W.Point ↦ P.xRep 0 :=
    (Filter.tendstoCofinite_iff_finite_preimage_singleton _).mpr finite_preimage_xRep0
  exact Northcott.comp_of_finite_fibers ..

variable [Northcott (logHeight₁ (K := F))]

variable (W) in

lemma finite_mwHeight_le (B : ℝ) : {P : W.Point | P.mwHeight ≤ B}.Finite :=
  Northcott.finite_le B

end Northcott

end WeierstrassCurve.Affine


section M0



section



section Group

variable {G H : Type*} [Group G] [Group H]


def MonoidHom.ofMapMulMulEqOne {f : G → H} (hf₁ : f 1 = 1)
    (hf : ∀ a b c, a * b * c = 1 → f a * f b * f c = 1) :
    G →* H :=
  .ofMapMulInv f fun x y ↦ by
    have (x : G) : f x⁻¹ = (f x)⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv', ← mul_one (_ * _)]
      nth_rewrite 1 [← hf₁]
      exact hf _ _ _ <| by group
    rw [eq_mul_inv_iff_mul_eq, eq_comm, ← inv_mul_eq_one, ← mul_assoc, ← this]
    exact hf _ _ _ <| by group

@[simp]
lemma MonoidHom.coe_ofMapMulMulEqOne {f : G → H} (hf₁ : f 1 = 1)
    (hf : ∀ a b c, a * b * c = 1 → f a * f b * f c = 1) :
    ⇑(ofMapMulMulEqOne hf₁ hf) = f :=
  rfl


lemma Subgroup.finite_comap_of_injective {f : G →* H} (hf : Function.Injective f)
    (S : Subgroup H) [Finite S] : Finite (S.comap f) :=
  .of_injective (fun x ↦ (⟨f x, x.2⟩ : S)) fun _ _ h ↦
    Subtype.ext <| hf <| congrArg Subtype.val h


instance Subgroup.instFinitePi {ι : Type*} [Finite ι] {G : ι → Type*} [(i : ι) → Group (G i)]
    {S : (i : ι) → Subgroup (G i)} [(i : ι) → Finite (S i)] :
    Finite (Subgroup.pi Set.univ S) :=
  .of_injective (fun x i ↦ (⟨x.1 i, x.2 i (Set.mem_univ i)⟩ : S i)) fun _ _ h ↦
    Subtype.ext <| funext fun i ↦ congrArg Subtype.val (congrFun h i)

end Group

section Units

variable {α : Type*} [Monoid α]

lemma IsUnit.exists_pow_eq_unit_iff {a : α} (h : IsUnit a) (n : ℕ) :
    (∃ x, x ^ n = h.unit) ↔ ∃ x, x ^ n = a := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩, fun ⟨x, hx⟩ ↦ ?_⟩
  · simpa using congrArg Units.val hx
  · cases n with
    | zero => exact ⟨1, Units.ext (by simpa using hx)⟩
    | succ _ => exact ⟨(isUnit_pow_succ_iff.mp (hx ▸ h)).unit, Units.ext hx⟩


theorem Squarefree.map {β : Type*} [Monoid β] (e : α ≃* β) {r : α} (h : Squarefree r) :
    Squarefree (e r) := by
  intro x ⟨c, hc⟩
  have hd : e.symm x * e.symm x ∣ r :=
    ⟨e.symm c, by simpa [mul_assoc] using congrArg e.symm hc⟩
  simpa using (h _ hd).map e

end Units

section modPow


lemma IsAlgClosed.of_ringEquiv' {k K : Type*} [Field k] [Field K] [IsAlgClosed k]
    (e : k ≃+* K) : IsAlgClosed K := by
  refine IsAlgClosed.of_exists_root _ fun p _ hpi ↦ ?_
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map (e.symm : K →+* k))
    (by rw [Polynomial.degree_map]; exact (Polynomial.degree_pos_of_irreducible hpi).ne')
  refine ⟨e z, (map_eq_zero_iff (e.symm : K →+* k) e.symm.injective).mp ?_⟩
  rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map,
    show (e.symm : K →+* k) (e z) = z from e.symm_apply_apply z]
  exact hz


abbrev Units.modPow (α : Type*) [CommMonoid α] (n : ℕ) : Type _ :=
  αˣ ⧸ (powMonoidHom n : αˣ →* αˣ).range


def QuotientGroup.congrRangePowMonoidHom {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    G ⧸ (powMonoidHom n : G →* G).range ≃* H ⧸ (powMonoidHom n : H →* H).range :=
  QuotientGroup.congr _ _ e <| by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨e u, by simp⟩
    · rintro ⟨u, rfl⟩
      exact ⟨e.symm u ^ n, ⟨_, rfl⟩, by simp⟩

namespace Units.modPow

variable {α β : Type*} [CommMonoid α] [CommMonoid β] {a b c : α}

open QuotientGroup

lemma unit_eq_one_iff (ha : IsUnit a) (n : ℕ) :
    (ha.unit : Units.modPow α n) = 1 ↔ ∃ z, z ^ n = a := by
  simp [IsUnit.exists_pow_eq_unit_iff]

lemma unit_mul_unit_mul_unit_eq_one_iff (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) (n : ℕ) :
    (ha.unit : Units.modPow α n) * hb.unit * hc.unit = 1 ↔ ∃ z, z ^ n = a * b * c := by
  simp only [← mk_mul, ← IsUnit.unit_mul]
  exact unit_eq_one_iff ((ha.mul hb).mul hc) n

lemma mk_eq_one_iff {u : αˣ} (n : ℕ) :
    (QuotientGroup.mk u : Units.modPow α n) = 1 ↔ ∃ w : αˣ, w ^ n = u := by
  simp

lemma mk_eq_mk_iff {u v : αˣ} (n : ℕ) :
    (QuotientGroup.mk u : Units.modPow α n) = QuotientGroup.mk v ↔ ∃ w : αˣ, v = u * w ^ n := by
  simp only [QuotientGroup.eq, MonoidHom.mem_range, powMonoidHom_apply]
  exact ⟨fun ⟨w, hw⟩ ↦ ⟨w, by rw [hw]; group⟩, fun ⟨w, hw⟩ ↦ ⟨w, by rw [hw]; group⟩⟩


lemma mk_eq_one_iff_isSquare {u : αˣ} :
    (QuotientGroup.mk u : Units.modPow α 2) = 1 ↔ IsSquare (u : α) := by
  rw [mk_eq_one_iff]
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨w, by rw [← hw]; push_cast [sq]; rfl⟩, fun ⟨s, hs⟩ ↦ ?_⟩
  have hsu : IsUnit s := isUnit_of_mul_isUnit_left (hs ▸ u.isUnit)
  exact ⟨hsu.unit, Units.ext (by rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, sq, ← hs])⟩

@[simp]
lemma pow_eq_one {n : ℕ} (m : Units.modPow α n) : m ^ n = 1 := by
  obtain ⟨u, rfl⟩ := mk'_surjective _ m
  rw [mk'_apply, ← mk_pow]
  exact (mk_eq_one_iff n).mpr ⟨u, rfl⟩


lemma subsingleton_of_forall_exists_pow {n : ℕ} (h : ∀ u : αˣ, ∃ w : αˣ, w ^ n = u) :
    Subsingleton (Units.modPow α n) := by
  refine ⟨fun a b ↦ ?_⟩
  induction a using QuotientGroup.induction_on with
  | H u =>
    induction b using QuotientGroup.induction_on with
    | H w => rw [(mk_eq_one_iff n).mpr (h u), (mk_eq_one_iff n).mpr (h w)]


lemma subsingleton_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] {n : ℕ} (hn : n ≠ 0) :
    Subsingleton (Units.modPow K n) := by
  refine subsingleton_of_forall_exists_pow fun u ↦ ?_
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : K) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := fun h0 ↦ u.ne_zero (by rw [← hz, h0, zero_pow hn])
  exact ⟨Units.mk0 z hz0, Units.ext (by simp [hz])⟩


def map (φ : α →* β) (n : ℕ) : Units.modPow α n →* Units.modPow β n :=
  QuotientGroup.map _ _ (Units.map φ) <| by
    rintro _ ⟨u, rfl⟩
    exact ⟨Units.map φ u, by simp [powMonoidHom]⟩

@[simp]
lemma map_mk (φ : α →* β) (n : ℕ) (u : αˣ) :
    map φ n (QuotientGroup.mk u) = QuotientGroup.mk (Units.map φ u) :=
  rfl

@[simp]
lemma map_id (n : ℕ) : map (MonoidHom.id α) n = MonoidHom.id (Units.modPow α n) := by
  ext
  simp

lemma map_comp {γ : Type*} [CommMonoid γ] (ψ : β →* γ) (φ : α →* β) (n : ℕ) :
    (map ψ n).comp (map φ n) = map (ψ.comp φ) n := by
  ext
  simp

@[simp]
lemma map_unit (φ : α →* β) (n : ℕ) (ha : IsUnit a) :
    map φ n (ha.unit : Units.modPow α n) = ((ha.map φ).unit : Units.modPow β n) := by
  rw [map, ← mk'_apply, map_mk']
  exact congrArg _ (Units.ext rfl)


def congr (e : α ≃* β) (n : ℕ) : Units.modPow α n ≃* Units.modPow β n :=
  congrRangePowMonoidHom (Units.mapEquiv e) n


lemma subsingleton_of_isAlgClosed_of_isIntegral (k K : Type*) [Field k] [IsAlgClosed k]
    [CommRing K] [IsDomain K] [Algebra k K] [Algebra.IsIntegral k K] {n : ℕ} (hn : n ≠ 0) :
    Subsingleton (Units.modPow K n) :=
  have : Subsingleton (Units.modPow k n) := subsingleton_of_isAlgClosed k hn
  (congr (RingEquiv.ofBijective (algebraMap k K)
    IsAlgClosed.algebraMap_bijective_of_isIntegral).toMulEquiv n).symm.toEquiv.subsingleton


lemma bijective_map {φ : α →* β} (hφ : Function.Bijective φ) (n : ℕ) :
    Function.Bijective (map φ n) := by
  have h : ⇑(map φ n) = ⇑(congr (MulEquiv.ofBijective φ hφ) n) := by
    ext m
    induction m using QuotientGroup.induction_on with
    | H u => rfl
  rw [h]
  exact (congr (MulEquiv.ofBijective φ hφ) n).bijective


noncomputable def piEquiv {ι : Type*} (α : ι → Type*) [(i : ι) → CommMonoid (α i)] (n : ℕ) :
    Units.modPow ((i : ι) → α i) n ≃* ((i : ι) → Units.modPow (α i) n) :=
  (congrRangePowMonoidHom MulEquiv.piUnits n).trans <|
    mulEquivPiModRangePowMonoidHom (fun i ↦ (α i)ˣ) n

@[simp]
lemma piEquiv_mk {ι : Type*} (α : ι → Type*) [(i : ι) → CommMonoid (α i)] (n : ℕ)
    (u : ((i : ι) → α i)ˣ) (i : ι) :
    piEquiv α n (QuotientGroup.mk u) i = QuotientGroup.mk (MulEquiv.piUnits u i) := by
  simp [piEquiv, congrRangePowMonoidHom, mulEquivPiModRangePowMonoidHom_apply]

end Units.modPow

end modPow

section Ideal


lemma Ideal.comap_ne_bot_of_comap_comap_ne_bot {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] {ρ : R →+* S} {φ : S →+* T} (hρ : Function.Injective ρ) {I : Ideal T}
    (h : (I.comap φ).comap ρ ≠ ⊥) : I.comap φ ≠ ⊥ := fun h0 ↦
  h (by rw [h0, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot ρ).mp hρ])

end Ideal

section LinearAlgebra


lemma linearIndependent_of_diagonal {ι A : Type*} [CommRing A] [NoZeroDivisors A]
    {u : ι → ι → A} (hd : ∀ i, u i i ≠ 0) (ho : ∀ i j, j ≠ i → u i j = 0) :
    LinearIndependent A u := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrFun hg i
  rw [Finset.sum_apply, Pi.zero_apply,
    Finset.sum_eq_single i
      (fun j _ hji ↦ by rw [Pi.smul_apply, ho j i (fun hc ↦ hji (hc ▸ rfl)), smul_zero])
      (fun hni ↦ absurd hi hni),
    Pi.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_right (hd i)


theorem Matrix.det_blockDiagonal' {ι : Type*} [Fintype ι] [DecidableEq ι] {η : ι → Type*}
    [(i : ι) → Fintype (η i)] [(i : ι) → DecidableEq (η i)] {R : Type*} [CommRing R]
    (M : (i : ι) → Matrix (η i) (η i) R) :
    (Matrix.blockDiagonal' M).det = ∏ i, (M i).det := by
  let : LinearOrder ι := LinearOrder.lift' _ (Fintype.equivFin ι).injective
  have hbt : (blockDiagonal' M).BlockTriangular Sigma.fst := by
    intro x y h
    obtain ⟨k, i⟩ := x
    obtain ⟨k', j⟩ := y
    exact blockDiagonal'_apply_ne _ _ _ h.ne'
  rw [hbt.det_fintype]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  let e : {x : Σ i, η i // x.fst = k} ≃ η k :=
    { toFun := fun x ↦ x.2 ▸ x.1.2
      invFun := fun j ↦ ⟨⟨k, j⟩, rfl⟩
      left_inv := fun ⟨⟨k', j⟩, h⟩ ↦ by subst h; rfl
      right_inv := fun j ↦ rfl }
  rw [← Matrix.det_reindex_self e]
  congr 1
  ext j j'
  simp [e, Matrix.toSquareBlock_def]


theorem LinearMap.det_pi' {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {S : ι → Type*}
    [(i : ι) → AddCommGroup (S i)] [(i : ι) → Module R (S i)]
    [(i : ι) → Module.Free R (S i)] [(i : ι) → Module.Finite R (S i)]
    (f : (i : ι) → S i →ₗ[R] S i) :
    (LinearMap.pi fun i ↦ (f i).comp (LinearMap.proj i)).det = ∏ i, (f i).det := by
  classical
  let b (i : ι) := Module.Free.chooseBasis R (S i)
  rw [← LinearMap.det_toMatrix (Pi.basis b)]
  have h : LinearMap.toMatrix (Pi.basis b) (Pi.basis b)
        (LinearMap.pi fun i ↦ (f i).comp (LinearMap.proj i))
      = Matrix.blockDiagonal' fun i ↦ LinearMap.toMatrix (b i) (b i) (f i) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    rcases eq_or_ne i₁ j₁ with rfl | hne
    · simp [LinearMap.toMatrix_apply']
    · simp [LinearMap.toMatrix_apply', Matrix.blockDiagonal'_apply_ne _ _ _ hne,
        Pi.single_eq_of_ne hne]
  rw [h, Matrix.det_blockDiagonal']
  simp [LinearMap.det_toMatrix]

end LinearAlgebra

section Valuation

open Polynomial

variable {L Γ : Type*} [CommRing L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)
  {t a b : L}

lemma Valuation.map_natCast_le_one {R : Type*} [Ring R] (v : Valuation R Γ) (n : ℕ) :
    v (n : R) ≤ 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ]
    exact (v.map_add _ _).trans (max_le ih v.map_one.le)


lemma Valuation.eq_one_of_mul_eq_one (ha : v a ≤ 1) (hb : v b ≤ 1) (hab : v (a * b) = 1) :
    v a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : Γ) = v a * v b := by rw [← map_mul, hab]
    _ ≤ v a * 1 := by gcongr
    _ = v a := mul_one _


lemma Valuation.map_eval_eq_of_one_lt {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, v (p.coeff i) ≤ 1) (ht : 1 < v t) :
    v (p.eval t) = v t ^ p.natDegree := by
  set n := p.natDegree with hn
  have h0 : v t ≠ 0 := (zero_lt_one.trans ht).ne'
  have heval : p.eval t = (∑ i ∈ Finset.range n, p.coeff i * t ^ i) + t ^ n := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul]
  have hlt : v (∑ i ∈ Finset.range n, p.coeff i * t ^ i) < v (t ^ n) := by
    rw [map_pow]
    refine v.map_sum_lt (pow_ne_zero n h0) fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    calc v (p.coeff i * t ^ i) ≤ 1 * v t ^ i := by
          rw [map_mul, map_pow]; gcongr; exact hcoeff i hi
      _ = v t ^ i := one_mul _
      _ < v t ^ n := pow_lt_pow_right₀ ht hi
  rw [heval, v.map_add_eq_of_lt_right hlt, map_pow]


lemma Valuation.le_one_of_root_monic {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, v (p.coeff i) ≤ 1) (hdeg : p.natDegree ≠ 0)
    (heq : p.eval t = 0) :
    v t ≤ 1 := by
  by_contra! hlt
  have h := v.map_eval_eq_of_one_lt hp hcoeff hlt
  rw [heq, map_zero] at h
  exact (zero_lt_one.trans hlt).ne' (pow_eq_zero_iff hdeg |>.mp h.symm)

end Valuation

section DedekindDomain

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]


lemma IsDedekindDomain.HeightOneSpectrum.finite_setOf_valuation_ne_one {x : K} (hx : x ≠ 0) :
    {v : HeightOneSpectrum R | v.valuation K x ≠ 1}.Finite := by
  refine ((Support.finite R x).union (Support.finite R x⁻¹)).subset fun v hv ↦ ?_
  rcases lt_or_gt_of_ne hv with h | h
  · refine .inr ?_
    rw [Support, Set.mem_ofPred_eq, map_inv₀,
      one_lt_inv₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx))]
    exact h
  · exact .inl h

lemma Set.integer_mono {S T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) :
    S.integer K ≤ T.integer K :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (hST hvS)

lemma Set.unit_mono {S T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) : S.unit K ≤ T.unit K :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (hST hvS)


lemma IsDedekindDomain.HeightOneSpectrum.le_count_iff_le {A : Type*} [CommRing A]
    [IsDedekindDomain A] (v : HeightOneSpectrum A) {J : Ideal A} (hJ : J ≠ ⊥) (k : ℕ) :
    k ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors ↔ J ≤ v.asIdeal ^ k := by
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]


lemma IsDedekindDomain.HeightOneSpectrum.le_count_iff {A : Type*} [CommRing A]
    [IsDedekindDomain A] (v : HeightOneSpectrum A) {x : A} (hx : x ≠ 0) (k : ℕ) :
    k ≤ Associates.count (Associates.mk v.asIdeal) (Associates.mk (Ideal.span {x})).factors ↔
      x ∈ v.asIdeal ^ k := by
  rw [v.le_count_iff_le (fun h ↦ hx (Ideal.span_singleton_eq_bot.mp h)) k,
    Ideal.span_singleton_le_iff_mem]


lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_iff (v : HeightOneSpectrum R)
    (u : Kˣ) (m : Multiplicative ℤ) :
    v.valuationOfNeZero u = m ↔ v.valuation K (u : K) = (m : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq]


lemma IsDedekindDomain.HeightOneSpectrum.dvd_toAdd_valuationOfNeZero (v : HeightOneSpectrum R)
    {n : ℕ} {u z : Kˣ} (h : v.valuation K (u : K) = v.valuation K (z : K) ^ n) :
    (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  have hu : v.valuationOfNeZero u = v.valuationOfNeZero z ^ n := by
    rw [valuationOfNeZero_eq_iff]
    push_cast
    rw [valuationOfNeZero_eq, h]
  exact ⟨Multiplicative.toAdd (v.valuationOfNeZero z), by rw [hu]; simp [toAdd_pow]⟩


lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod_mk (v : HeightOneSpectrum R)
    (n : ℕ) (u : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk u) =
      Multiplicative.ofAdd ((Multiplicative.toAdd (v.valuationOfNeZero u) : ℤ) : ZMod n) :=
  rfl


lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff
    (v : HeightOneSpectrum R) (n : ℕ) (u : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk u) = 1 ↔
      (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  rw [valuationOfNeZeroMod_mk, ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd]


lemma IsDedekindDomain.HeightOneSpectrum.valuation_algebraMap_eq_one_of_pow_eq_span
    {v w : HeightOneSpectrum R} (hne : w ≠ v) {n : ℕ} {π : R}
    (h : v.asIdeal ^ n = Ideal.span {π}) :
    w.valuation K (algebraMap R K π) = 1 := by
  refine w.valuation_eq_one_iff_notMem.mpr fun hmem ↦ hne (HeightOneSpectrum.ext ?_).symm
  refine v.isMaximal.eq_of_le w.isPrime.ne_top (Ideal.IsPrime.le_of_pow_le (n := n) ?_)
  rwa [h, Ideal.span_le, Set.singleton_subset_iff]

open WithZero in

lemma IsDedekindDomain.HeightOneSpectrum.exp_neg_one_le_valuation_algebraMap
    {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) {r : R} (hr : r ∉ v.asIdeal ^ 2) :
    exp (-1 : ℤ) ≤ v.valuation K (algebraMap R K r) := by
  rw [valuation_of_algebraMap]
  have h2 : ¬ v.intValuation r ≤ exp (-((2 : ℕ) : ℤ)) := fun hc ↦
    hr ((intValuation_le_pow_iff_mem v r 2).mp hc)
  rw [intValuation_le_exp_iff_le_emultiplicity, not_le] at h2
  rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num,
    exp_le_intValuation_iff_emultiplicity_le]
  exact Order.le_of_lt_succ (by exact_mod_cast h2)


lemma IsDedekindDomain.HeightOneSpectrum.notMem_pow_two_of_squarefree
    {R : Type*} [CommRing R] [IsPrincipalIdealRing R] (v : HeightOneSpectrum R) {r : R}
    (hr : Squarefree r) : r ∉ v.asIdeal ^ 2 := by
  obtain ⟨p, hp⟩ := IsPrincipalIdealRing.principal v.asIdeal
  intro hmem
  rw [hp, Ideal.submodule_span_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  have hunit : IsUnit p := hr p (by rwa [← sq])
  exact v.isPrime.ne_top <| by
    rw [hp, Ideal.submodule_span_eq, Ideal.span_singleton_eq_top]
    exact hunit

variable (R) (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra R B]


def IsDedekindDomain.HeightOneSpectrum.primesAbove (S : Set (HeightOneSpectrum R)) :
    Set (HeightOneSpectrum B) :=
  {w | ∃ v ∈ S, v.asIdeal = w.asIdeal.under R}




lemma IsDedekindDomain.HeightOneSpectrum.primesAbove_mono {S T : Set (HeightOneSpectrum R)}
    (hST : S ⊆ T) : primesAbove R B S ⊆ primesAbove R B T :=
  fun _ ⟨v, hv, hva⟩ ↦ ⟨v, hST hv, hva⟩


@[simp]
lemma IsDedekindDomain.HeightOneSpectrum.primesAbove_empty :
    primesAbove R B (∅ : Set (HeightOneSpectrum R)) = ∅ := by
  ext w
  simp [primesAbove]

instance IsDedekindDomain.HeightOneSpectrum.instLiesOverUnder [Algebra.IsIntegral R B]
    (w : HeightOneSpectrum B) :
    w.asIdeal.LiesOver (w.under R).asIdeal :=
  Ideal.over_under ..

lemma IsDedekindDomain.HeightOneSpectrum.mem_primesAbove_iff [Algebra.IsIntegral R B]
    (S : Set (HeightOneSpectrum R)) (w : HeightOneSpectrum B) :
    w ∈ primesAbove R B S ↔ w.under R ∈ S := by
  refine ⟨fun ⟨v, hv, hva⟩ ↦ ?_, fun hw ↦ ⟨w.under R, hw, rfl⟩⟩
  rwa [show w.under R = v from HeightOneSpectrum.ext hva.symm]


lemma IsDedekindDomain.HeightOneSpectrum.primesAbove_finite [Algebra.IsIntegral R B]
    [Module.IsTorsionFree R B] {S : Set (HeightOneSpectrum R)} (hS : S.Finite) :
    (primesAbove R B S).Finite := by
  have hsub : primesAbove R B S ⊆
      ⋃ v ∈ S, {w : HeightOneSpectrum B | w.asIdeal ∈ v.asIdeal.primesOver B} :=
    fun w ⟨v, hv, hva⟩ ↦ Set.mem_biUnion hv ⟨w.isPrime, ⟨hva⟩⟩
  refine (hS.biUnion fun v _ ↦ ?_).subset hsub
  have := v.isMaximal
  exact (IsDedekindDomain.primesOver_finite v.asIdeal B).preimage
    (fun a _ b _ hab ↦ HeightOneSpectrum.ext hab)


def IsDedekindDomain.selmerGroupAbove (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    (S : Set (HeightOneSpectrum R)) (n : ℕ) : Subgroup (Units.modPow L n) :=
  selmerGroup (R := B) (K := L) (S := HeightOneSpectrum.primesAbove R B S) (n := n)

lemma IsDedekindDomain.mem_selmerGroupAbove_iff (L : Type*) [Field L] [Algebra B L]
    [IsFractionRing B L] (S : Set (HeightOneSpectrum R)) (n : ℕ) (x : Units.modPow L n) :
    x ∈ selmerGroupAbove R B L S n ↔
      ∀ w ∉ HeightOneSpectrum.primesAbove R B S, w.valuationOfNeZeroMod n x = 1 :=
  Iff.rfl


lemma IsDedekindDomain.selmerGroupAbove_empty (L : Type*) [Field L] [Algebra B L]
    [IsFractionRing B L] (n : ℕ) :
    selmerGroupAbove R B L (∅ : Set (HeightOneSpectrum R)) n =
      selmerGroup (R := B) (K := L) (S := (∅ : Set (HeightOneSpectrum B))) (n := n) := by
  rw [selmerGroupAbove, HeightOneSpectrum.primesAbove_empty]

namespace IsDiscreteValuationRing

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

@[simp]
lemma asIdeal_maximalIdeal : (maximalIdeal A).asIdeal = IsLocalRing.maximalIdeal A := rfl

variable {A}


lemma _root_.IsDedekindDomain.HeightOneSpectrum.eq_maximalIdeal (P : HeightOneSpectrum A) :
    P = maximalIdeal A :=
  HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal P.isMaximal)

end IsDiscreteValuationRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]


def comapOfNeBot (ψ : B →+* C) (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) :
    HeightOneSpectrum B where
  asIdeal := w.asIdeal.comap ψ
  isPrime := w.isPrime.comap ψ
  ne_bot := hne


@[simp]
lemma comapOfNeBot_asIdeal (ψ : B →+* C) (w : HeightOneSpectrum C)
    (hne : w.asIdeal.comap ψ ≠ ⊥) :
    (comapOfNeBot ψ w hne).asIdeal = w.asIdeal.comap ψ :=
  rfl

variable {L N : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
  [Field N] [Algebra C N] [IsFractionRing C N]


theorem exists_valuationOfNeZero_map_eq (φ : L →+* N) (ψ : B →+* C)
    (hcomp : (algebraMap C N).comp ψ = φ.comp (algebraMap B L))
    (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) :
    ∃ e : ℕ, ∀ u : Lˣ, w.valuationOfNeZero (Units.map (φ : L →* N) u) =
      (comapOfNeBot ψ w hne).valuationOfNeZero u ^ e := by
  let _ : Algebra B C := ψ.toAlgebra
  let _ : Algebra L N := φ.toAlgebra
  let _ : Algebra B N := (φ.comp (algebraMap B L)).toAlgebra
  have hψ : Function.Injective ψ := by
    have h : Function.Injective ((algebraMap C N).comp ψ) := by
      rw [hcomp]
      exact φ.injective.comp (IsFractionRing.injective B L)
    exact fun x y hxy ↦ h (by simp only [RingHom.comp_apply, hxy])
  have ht1 : IsScalarTower B L N := .of_algebraMap_eq' rfl
  have ht2 : IsScalarTower B C N := .of_algebraMap_eq fun x ↦ (RingHom.congr_fun hcomp x).symm
  have htf : Module.IsTorsionFree B C := Module.isTorsionFree_iff_algebraMap_injective.mpr hψ
  have hlie : w.asIdeal.LiesOver (comapOfNeBot ψ w hne).asIdeal := ⟨rfl⟩
  refine ⟨w.asIdeal.ramIdxU B, fun u ↦ ?_⟩
  rw [valuationOfNeZero_eq_iff, WithZero.coe_pow, valuationOfNeZero_eq, Units.coe_map,
    ]
  exact (valuation_liesOver N (comapOfNeBot ψ w hne) w (u : L)).symm


theorem dvd_toAdd_valuationOfNeZero_map (φ : L →+* N) (ψ : B →+* C)
    (hcomp : (algebraMap C N).comp ψ = φ.comp (algebraMap B L))
    (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) {n : ℕ} (u : Lˣ)
    (h : (n : ℤ) ∣ Multiplicative.toAdd ((comapOfNeBot ψ w hne).valuationOfNeZero u)) :
    (n : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero (Units.map (φ : L →* N) u)) := by
  obtain ⟨e, he⟩ := exists_valuationOfNeZero_map_eq φ ψ hcomp w hne
  rw [he u, toAdd_pow, nsmul_eq_mul]
  exact h.mul_left _


theorem comap_maximalIdeal_adicCompletionIntegers (v : HeightOneSpectrum R) :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).comap
      (algebraMap R (v.adicCompletionIntegers K)) = v.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← valuation_lt_one_iff_mem (K := K)]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
    (WithZero (Multiplicative ℤ))))).trans ?_
  rw [show ((algebraMap R (v.adicCompletionIntegers K) x : v.adicCompletionIntegers K) :
    v.adicCompletion K) = ((algebraMap R K x : K) : v.adicCompletion K) from rfl,
    valuedAdicCompletion_eq_valuation']

end IsDedekindDomain.HeightOneSpectrum

end DedekindDomain

namespace Polynomial

variable {R : Type*} [CommRing R] {g : R[X]}


lemma resultant_C_sub_X (f : R[X]) (x : R) (m : ℕ) (hm : f.natDegree ≤ m) :
    f.resultant (C x - X) m 1 = f.eval x := by
  have h : f.resultant (X - C x) m 1 = (-1) ^ m * f.eval x := by
    have := resultant_X_sub_C_pow_right f x m 1 hm
    rwa [pow_one, mul_one, pow_one] at this
  rw [show C x - X = C (-1 : R) * (X - C x) by simp, resultant_C_mul_right, h,
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

lemma Monic.resultant_one_right (hg : g.Monic) (n : ℕ) :
    g.resultant 1 g.natDegree n = 1 := by
  rw [Polynomial.resultant_one_right, hg.coeff_natDegree, one_pow]


lemma Monic.resultant_congr_right (hg : g.Monic) {p : R[X]} {n₁ n₂ : ℕ}
    (h₁ : p.natDegree ≤ n₁) (h₂ : n₁ ≤ n₂) :
    g.resultant p g.natDegree n₂ = g.resultant p g.natDegree n₁ := by
  rw [← Nat.add_sub_cancel' h₂, resultant_add_right_deg _ _ _ _ _ h₁, hg.coeff_natDegree,
    one_pow, one_mul]


lemma Monic.resultant_deriv {f : R[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    f.resultant (derivative f) f.natDegree (f.natDegree - 1) =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
  rw [Polynomial.resultant_deriv (natDegree_pos_iff_degree_pos.mp hdeg), hf.leadingCoeff, mul_one]

private lemma resultant_X_sub_C_add_mul_derivative (hdeg : 0 < g.natDegree) (x : R) :
    (X - C x).resultant (g + (X - C x) * derivative g) 1 g.natDegree = g.eval x := by
  have hd' : (derivative g).natDegree + 1 ≤ g.natDegree := by
    have := natDegree_derivative_le g; lia
  rw [resultant_add_mul_right _ _ _ _ _ hd' (natDegree_X_sub_C_le x),
    resultant_X_sub_C_left _ _ _ le_rfl]

private lemma resultant_add_mul_derivative [Nontrivial R] (hg : g.Monic)
    (hdeg : 0 < g.natDegree) (x : R) :
    g.resultant (g + (X - C x) * derivative g) g.natDegree g.natDegree =
      (-1) ^ g.natDegree * g.eval x *
        g.resultant (derivative g) g.natDegree (g.natDegree - 1) := by
  have hd' : (derivative g).natDegree + 1 ≤ g.natDegree := by
    have := natDegree_derivative_le g; lia
  rw [show g + (X - C x) * derivative g = (X - C x) * derivative g + g * 1 by ring,
    resultant_add_mul_right _ _ _ _ _ (by simp) le_rfl,
    hg.resultant_congr_right natDegree_mul_le (by rw [natDegree_X_sub_C]; lia),
    resultant_mul_right g (X - C x) (derivative g) g.natDegree le_rfl, natDegree_X_sub_C,
    resultant_X_sub_C_right _ _ _ le_rfl,
    ← hg.resultant_congr_right (n₂ := g.natDegree - 1) le_rfl (natDegree_derivative_le g)]


private lemma resultant_derivative_X_sub_C_mul [Nontrivial R] (hg : g.Monic)
    (hdeg : 0 < g.natDegree) (x : R) :
    ((X - C x) * g).resultant (derivative ((X - C x) * g)) (g.natDegree + 1) g.natDegree =
      (-1) ^ g.natDegree * g.eval x ^ 2 *
        g.resultant (derivative g) g.natDegree (g.natDegree - 1) := by
  have hder : derivative ((X - C x) * g) = g + (X - C x) * derivative g := by
    simp [derivative_mul]
  have hDle : (g + (X - C x) * derivative g).natDegree ≤ g.natDegree := by
    have h := natDegree_derivative_le ((X - C x) * g)
    rw [hder, (monic_X_sub_C x).natDegree_mul hg, natDegree_X_sub_C] at h
    lia
  have h := resultant_mul_left (X - C x) g (g + (X - C x) * derivative g) g.natDegree hDle
  rw [natDegree_X_sub_C, add_comm 1 g.natDegree, resultant_X_sub_C_add_mul_derivative hdeg x,
    resultant_add_mul_derivative hg hdeg x] at h
  rw [hder, h]; ring


theorem discr_X_sub_C_mul (hg : g.Monic) (hdeg : 0 < g.natDegree) (x : R) :
    ((X - C x) * g).discr = g.discr * g.eval x ^ 2 := by
  nontriviality R
  have hN : ((X - C x) * g).natDegree = g.natDegree + 1 := by
    rw [(monic_X_sub_C x).natDegree_mul hg, natDegree_X_sub_C, add_comm]
  have h := ((monic_X_sub_C x).mul hg).resultant_deriv (by rw [hN]; lia)
  rw [hN, Nat.triangle_succ, pow_add, Nat.add_sub_cancel,
    resultant_derivative_X_sub_C_mul hg hdeg x, hg.resultant_deriv hdeg] at h
  refine (isUnit_neg_one.pow (g.natDegree * (g.natDegree - 1) / 2 + g.natDegree)).mul_left_cancel ?_
  linear_combination -h

lemma mem_degreeLT_natDegree_iff {q : R[X]} (hg : g ≠ 0) :
    q ∈ degreeLT R g.natDegree ↔ q.degree < g.degree := by
  rw [mem_degreeLT, degree_eq_natDegree hg]


theorem eval_pos_of_monic_of_irreducible_of_natDegree_eq_two {q : ℝ[X]}
    (hm : q.Monic) (hirr : Irreducible q) (hd : q.natDegree = 2) (x : ℝ) : 0 < q.eval x :=
  zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    (fun y hy ↦ absurd hy (hirr.not_isRoot_of_natDegree_ne_one (by lia)))
    (hm.leadingCoeff ▸ zero_le_one)

section

variable [Nontrivial R] {q : R[X]} {n : ℕ}

lemma exists_eq_C_mul_X_sub_C_of_natDegree_le_one {p : R[X]} (hdeg : p.natDegree ≤ 1)
    {x : R} (hx : p.IsRoot x) :
    ∃ γ, p = C γ * (X - C x) := by
  obtain ⟨q, rfl⟩ := dvd_iff_isRoot.mpr hx
  rcases eq_or_ne q 0 with rfl | hq
  · exact ⟨0, by simp⟩
  have h1 : (X - C x).leadingCoeff * q.leadingCoeff ≠ 0 := by
    rwa [(monic_X_sub_C x).leadingCoeff, one_mul, leadingCoeff_ne_zero]
  rw [natDegree_mul' h1, natDegree_X_sub_C] at hdeg
  refine ⟨q.coeff 0, ?_⟩
  nth_rw 1 [eq_C_of_natDegree_eq_zero (by lia : q.natDegree = 0), mul_comm]

lemma modByMonic_mem_degreeLT (hg : g.Monic) (q : R[X]) :
    q %ₘ g ∈ degreeLT R g.natDegree :=
  (mem_degreeLT_natDegree_iff hg.ne_zero).mpr <| degree_modByMonic_lt q hg

lemma divByMonic_mem_degreeLT (hg : g.Monic)
    (hq : q ∈ degreeLT R (g.natDegree + n)) : q /ₘ g ∈ degreeLT R n := by
  rw [mem_degreeLT] at hq ⊢
  rcases eq_or_ne (q /ₘ g) 0 with h | h
  · simp [h]
  have hq0 : q ≠ 0 := fun h0 ↦ h (by simp [h0])
  rw [← natDegree_lt_iff_degree_lt h, natDegree_divByMonic q hg]
  refine Nat.sub_lt_left_of_lt_add ?_ <| (natDegree_lt_iff_degree_lt hq0).mpr hq
  by_contra! hcon
  exact h <| (divByMonic_eq_zero_iff hg).mpr <| degree_lt_degree hcon

lemma eq_zero_of_monic_dvd_of_degree_lt (hg : g.Monic) (hdvd : g ∣ q)
    (hq : q.degree < g.degree) : q = 0 :=
  ((modByMonic_eq_self_iff hg).mpr hq).symm.trans <| (modByMonic_eq_zero_iff_dvd hg).mpr hdvd

private lemma Monic.divMod_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g ∧ (g * v + u) %ₘ g = u %ₘ g := by
  refine div_modByMonic_unique _ _ hg ⟨?_, degree_modByMonic_lt u hg⟩
  conv_rhs => rw [← modByMonic_add_div u g]
  ring

lemma Monic.divByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g :=
  (hg.divMod_mul_add v u).1

lemma Monic.modByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) %ₘ g = u %ₘ g :=
  (hg.divMod_mul_add v u).2

end

section Sylvester

open Module LinearMap LinearEquiv

variable [Nontrivial R] {p : R[X]} {n : ℕ}




noncomputable def mulModByMonic (hg : g.Monic) (p : R[X]) :
    degreeLT R g.natDegree →ₗ[R] degreeLT R g.natDegree where
  toFun q := ⟨p * (q : R[X]) %ₘ g, modByMonic_mem_degreeLT hg _⟩
  map_add' q₁ q₂ := by ext1; simp [mul_add, add_modByMonic]
  map_smul' c q := by ext1; simp [smul_modByMonic]

@[simp]
lemma mulModByMonic_apply_coe (hg : g.Monic) (p : R[X])
    (q : degreeLT R g.natDegree) : (mulModByMonic hg p q : R[X]) = p * (q : R[X]) %ₘ g :=
  rfl


noncomputable def sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (degreeLT R g.natDegree × degreeLT R n) ≃ₗ[R] degreeLT R (g.natDegree + n) :=
  ofBijective (sylvesterMap g 1 le_rfl (by simp)) <| by
    constructor
    · intro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ h
      replace h : g * v + u = g * v' + u' := by simpa using congrArg Subtype.val h
      rw [mem_degreeLT_natDegree_iff hg.ne_zero] at hu hu'
      have hmod {w : R[X]} (hw : w.degree < g.degree) : w %ₘ g = w :=
        (modByMonic_eq_self_iff hg).mpr hw
      have hdiv {w : R[X]} (hw : w.degree < g.degree) : w /ₘ g = 0 :=
        (divByMonic_eq_zero_iff hg).mpr hw
      have h₁ : u = u' := by
        rw [← hmod hu, ← hmod hu', ← hg.modByMonic_mul_add v u, ← hg.modByMonic_mul_add v' u', h]
      have h₂ : v = v' := by
        have := congrArg (· /ₘ g) h
        simpa [hg.divByMonic_mul_add, hdiv hu, hdiv hu'] using this
      simp only [Prod.mk.injEq, Subtype.mk.injEq]
      exact ⟨h₁, h₂⟩
    · intro ⟨q, hq⟩
      refine ⟨(⟨q %ₘ g, modByMonic_mem_degreeLT hg q⟩,
        ⟨q /ₘ g, divByMonic_mem_degreeLT hg hq⟩), ?_⟩
      ext1
      simpa [add_comm] using modByMonic_add_div q g

@[simp]
lemma coe_sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (sylvesterEquivOne hg n).toLinearMap = sylvesterMap g 1 le_rfl (by simp) :=
  rfl


lemma coe_sylvesterEquivOne_symm (hg : g.Monic) (n : ℕ)
    (q : degreeLT R (g.natDegree + n)) :
    ((((sylvesterEquivOne hg n).symm q).1 : R[X]) = (q : R[X]) %ₘ g) ∧
      ((((sylvesterEquivOne hg n).symm q).2 : R[X]) = (q : R[X]) /ₘ g) := by
  obtain ⟨w, rfl⟩ : ∃ w, q = sylvesterEquivOne hg n w :=
    ⟨_, ((sylvesterEquivOne hg n).apply_symm_apply q).symm⟩
  have hq : ((sylvesterEquivOne hg n w : degreeLT R (g.natDegree + n)) : R[X]) =
      g * (w.2 : R[X]) + (w.1 : R[X]) := by
    show g * (w.2 : R[X]) + 1 * (w.1 : R[X]) = _
    rw [one_mul]
  have h : (w.1 : R[X]).degree < g.degree := (mem_degreeLT_natDegree_iff hg.ne_zero).mp w.1.2
  rw [symm_apply_apply, hq]
  refine ⟨?_, ?_⟩
  · rw [hg.modByMonic_mul_add, (modByMonic_eq_self_iff hg).mpr h]
  · rw [hg.divByMonic_mul_add, (divByMonic_eq_zero_iff hg).mpr h, add_zero]


noncomputable def sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    degreeLT R g.natDegree × degreeLT R n →ₗ[R] degreeLT R g.natDegree × degreeLT R n :=
  (sylvesterEquivOne hg n).symm.toLinearMap ∘ₗ sylvesterMap g p le_rfl hp


lemma coe_sylvesterBlock_apply_fst (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).1 : R[X]) = p * (u : R[X]) %ₘ g := by
  rw [sylvesterBlock, comp_apply, LinearEquiv.coe_coe,
    (coe_sylvesterEquivOne_symm hg n _).1, sylvesterMap_apply_coe, hg.modByMonic_mul_add]


lemma coe_sylvesterBlock_apply_snd (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).2 : R[X]) = (v : R[X]) + p * (u : R[X]) /ₘ g := by
  rw [sylvesterBlock, comp_apply, LinearEquiv.coe_coe,
    (coe_sylvesterEquivOne_symm hg n _).2, sylvesterMap_apply_coe, hg.divByMonic_mul_add]

open Matrix in

lemma det_sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    LinearMap.det (sylvesterBlock hg p hp) = LinearMap.det (mulModByMonic hg p) := by
  set bm := degreeLT.basis R g.natDegree
  set bn := degreeLT.basis R n
  have hinl j : (bm.prod bn) (Sum.inl j) = (bm j, 0) :=
    Prod.ext (Basis.prod_apply_inl_fst ..) (Basis.prod_apply_inl_snd ..)
  have hinr j : (bm.prod bn) (Sum.inr j) = (0, bn j) :=
    Prod.ext (Basis.prod_apply_inr_fst ..) (Basis.prod_apply_inr_snd ..)
  
  have hfst u : (sylvesterBlock hg p hp (u, 0)).1 = mulModByMonic hg p u :=
    Subtype.ext <| by rw [coe_sylvesterBlock_apply_fst, mulModByMonic_apply_coe]
  have hz (v : degreeLT R n) :
      sylvesterBlock hg p hp ((0 : degreeLT R g.natDegree), v) = (0, v) :=
    Prod.ext (Subtype.ext <| by simp [coe_sylvesterBlock_apply_fst])
      (Subtype.ext <| by simp [coe_sylvesterBlock_apply_snd])
  rw [← det_toMatrix (bm.prod bn), ← det_toMatrix bm]
  have hmat : toMatrix (bm.prod bn) (bm.prod bn) (sylvesterBlock hg p hp) =
      fromBlocks (toMatrix bm bm (mulModByMonic hg p)) 0
        (.of fun i j ↦ bn.repr (sylvesterBlock hg p hp (bm j, 0)).2 i) 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [toMatrix_apply, hinl, Basis.prod_repr_inl, fromBlocks_apply₁₁, toMatrix_apply, hfst]
    · rw [toMatrix_apply, hinr, hz, Basis.prod_repr_inl, fromBlocks_apply₁₂]
      simp
    · rw [toMatrix_apply, hinl, Basis.prod_repr_inr, fromBlocks_apply₂₁, of_apply]
    · rw [toMatrix_apply, hinr, hz, Basis.prod_repr_inr, fromBlocks_apply₂₂,
        Basis.repr_self, Matrix.one_apply, Finsupp.single_apply]
      exact if_congr eq_comm rfl rfl
  rw [hmat, det_fromBlocks_zero₁₂, det_one, mul_one]

end Sylvester


theorem Monic.irreducible_map_fraction_map_of_irreducible_map [IsIntegrallyClosed R]
    [IsDomain R] {S K : Type*} [CommRing S] [IsDomain S] [Field K] [Algebra R K]
    [IsFractionRing R K] (hg : g.Monic) (φ : R →+* S) (h : Irreducible (g.map φ)) :
    Irreducible (g.map (algebraMap R K)) :=
  (hg.irreducible_iff_irreducible_map_fraction_map (K := K)).mp
    (hg.irreducible_of_irreducible_map φ _ h)

end Polynomial

open Polynomial LinearMap LinearEquiv

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {g : R[X]} {n : ℕ}

@[simp]
lemma mk_modByMonic (hg : g.Monic) (q : R[X]) : mk g (q %ₘ g) = mk g q := by
  simpa using mk_leftInverse hg (mk g q)

lemma exists_degree_lt_mk_eq [Nontrivial R] (hg : g.Monic) (a : AdjoinRoot g) :
    ∃ p, p.degree < g.degree ∧ a = mk g p := by
  obtain ⟨q, rfl⟩ := mk_surjective a
  exact ⟨q %ₘ g, degree_modByMonic_lt q hg, (mk_modByMonic hg q).symm⟩

lemma mk_eq_mk_iff_of_degree_lt [Nontrivial R] (hg : g.Monic) {p q : R[X]}
    (hp : p.degree < g.degree) (hq : q.degree < g.degree) :
    mk g p = mk g q ↔ p = q :=
  ⟨fun h ↦ sub_eq_zero.mp <| eq_zero_of_monic_dvd_of_degree_lt hg (mk_eq_mk.mp h) <|
    (degree_sub_le p q).trans_lt (max_lt hp hq), fun h ↦ h ▸ rfl⟩


noncomputable def degreeLTEquiv [Nontrivial R] (hg : g.Monic) :
    degreeLT R g.natDegree ≃ₗ[R] AdjoinRoot g :=
  ofBijective ((mkₐ g).toLinearMap ∘ₗ (degreeLT R g.natDegree).subtype) <| by
    constructor
    · intro ⟨q, hq⟩ ⟨q', hq'⟩ h
      replace h : mk g q = mk g q' := h
      rw [mk_eq_mk] at h
      rw [mem_degreeLT_natDegree_iff hg.ne_zero] at hq hq'
      refine Subtype.ext (sub_eq_zero.mp <| eq_zero_of_monic_dvd_of_degree_lt hg h ?_)
      exact (degree_sub_le q q').trans_lt (max_lt hq hq')
    · intro a
      obtain ⟨q, rfl⟩ := mk_surjective a
      exact ⟨⟨q %ₘ g, modByMonic_mem_degreeLT hg q⟩, mk_modByMonic hg q⟩

@[simp]
lemma degreeLTEquiv_apply [Nontrivial R] (hg : g.Monic)
    (q : degreeLT R g.natDegree) :
    degreeLTEquiv hg q = mk g (q : R[X]) :=
  rfl


theorem nonempty_algEquiv_complex {q : ℝ[X]} (hm : q.Monic) (hirr : Irreducible q)
    (hd : q.natDegree = 2) : Nonempty (AdjoinRoot q ≃ₐ[ℝ] ℂ) := by
  have : Fact (Irreducible q) := ⟨hirr⟩
  have : FiniteDimensional ℝ (AdjoinRoot q) := (powerBasis' hm).finite
  refine (Real.nonempty_algEquiv_or (AdjoinRoot q)).resolve_left fun ⟨e⟩ ↦
    absurd e.toLinearEquiv.finrank_eq (by
      rw [Module.finrank_self, (powerBasis' hm).finrank, powerBasis'_dim, hd]
      norm_num)


lemma norm_mk_eq_det_mulModByMonic [Nontrivial R] (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = LinearMap.det (mulModByMonic hg p) := by
  rw [Algebra.norm_apply, ← det_conj (mulModByMonic hg p) (degreeLTEquiv hg)]
  congr 1
  refine ext fun a ↦ ?_
  obtain ⟨q, rfl⟩ := (degreeLTEquiv hg).surjective a
  simp only [comp_apply, LinearEquiv.coe_coe, symm_apply_apply]
  simp only [degreeLTEquiv_apply, mulModByMonic_apply_coe, Algebra.coe_lmul_eq_mul,
    mul_apply']
  rw [mk_modByMonic hg, map_mul]


lemma norm_mk_eq_resultant [Nontrivial R] (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = g.resultant p g.natDegree p.natDegree := by
  set m := g.natDegree
  set k := p.natDegree
  set b₁ := ((degreeLT.basis R m).prod (degreeLT.basis R k)).reindex finSumFinEquiv
  set b₂ := degreeLT.basis R (m + k)
  have hΨ : (sylvesterMap g 1 le_rfl (by simp)) ∘ₗ sylvesterBlock hg p le_rfl =
      sylvesterMap g p le_rfl le_rfl := by
    rw [sylvesterBlock, ← LinearMap.comp_assoc, ← coe_sylvesterEquivOne hg k, comp_coe,
      symm_trans_self, refl_toLinearMap, id_comp]
  have key : (sylvesterMap g p le_rfl le_rfl).toMatrix b₁ b₂ =
      (sylvesterMap g 1 le_rfl (by simp)).toMatrix b₁ b₂ *
        (sylvesterBlock hg p le_rfl).toMatrix b₁ b₁ := by
    rw [← toMatrix_comp b₁ b₁ b₂, hΨ]
  rw [norm_mk_eq_det_mulModByMonic hg, ← det_sylvesterBlock hg p le_rfl,
    ← det_toMatrix b₁, resultant, ← toMatrix_sylvesterMap' g p le_rfl le_rfl, key,
    Matrix.det_mul, toMatrix_sylvesterMap' g 1 le_rfl (by simp), ← resultant,
    hg.resultant_one_right, one_mul]


theorem isIntegralElem_root_of_map {S : Type*} [CommRing S] (φ : R →+* S) {h : S[X]}
    (hg : g.Monic) (hmap : g.map φ = h) :
    ((algebraMap S (AdjoinRoot h)).comp φ).IsIntegralElem (root h) :=
  ⟨g, hg, by rw [← eval₂_map, hmap, ← aeval_def, aeval_eq, mk_self]⟩

section Map

variable {S : Type*} [CommRing S] (σ : R →+* S)


@[simp]
lemma map_mk {p : R[X]} {q : S[X]} (hq : q ∣ p.map σ) (g : R[X]) :
    AdjoinRoot.map σ p q hq (mk p g) = mk q (g.map σ) := by
  rw [AdjoinRoot.map, lift_mk, ← Polynomial.eval₂_map, ← algebraMap_eq, ← Polynomial.aeval_def,
    aeval_eq]

end Map

end AdjoinRoot


lemma AdjoinRoot.map_comp_algebraMap {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (v : IsDedekindDomain.HeightOneSpectrum R) {p : K[X]} {q : (v.adicCompletion K)[X]}
    (hq : q ∣ p.map (algebraMap K (v.adicCompletion K))) :
    (AdjoinRoot.map (algebraMap K (v.adicCompletion K)) p q hq).comp
        (algebraMap R (AdjoinRoot p)) =
      (algebraMap (v.adicCompletionIntegers K) (AdjoinRoot q)).comp
        (algebraMap R (v.adicCompletionIntegers K)) := by
  ext c
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply R K (AdjoinRoot p), AdjoinRoot.algebraMap_eq, map_of,
    IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K)
      (AdjoinRoot q), AdjoinRoot.algebraMap_eq]
  rfl




theorem Algebra.norm_prod {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B]
    (x : A × B) : Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  have h : Algebra.lmul R (A × B) x = ((Algebra.lmul R A x.1).prodMap (Algebra.lmul R B x.2)) := by
    ext <;> simp
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, h, LinearMap.det_prodMap]


theorem Algebra.norm_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {S : ι → Type*}
    [(i : ι) → CommRing (S i)] [(i : ι) → Algebra R (S i)]
    [(i : ι) → Module.Free R (S i)] [(i : ι) → Module.Finite R (S i)]
    (g : (i : ι) → S i) :
    Algebra.norm R g = ∏ i, Algebra.norm R (g i) := by
  have h : Algebra.lmul R ((i : ι) → S i) g
      = LinearMap.pi fun i ↦ (Algebra.lmul R (S i) (g i)).comp (LinearMap.proj i) := by
    ext x j
    simp [Algebra.lmul]
  rw [Algebra.norm_apply, h, LinearMap.det_pi']
  simp_rw [← Algebra.norm_apply]

section EtaleDecomposition



open Polynomial UniqueFactorizationMonoid

namespace Polynomial

variable {K : Type*} [Field K] {f : K[X]}


abbrev Factors (f : K[X]) : Type _ := {p : K[X] // p.Monic ∧ Irreducible p ∧ p ∣ f}

namespace Factors

lemma monic (p : f.Factors) : (p : K[X]).Monic := p.2.1

lemma irreducible (p : f.Factors) : Irreducible (p : K[X]) := p.2.2.1

lemma dvd (p : f.Factors) : (p : K[X]) ∣ f := p.2.2.2


lemma coe_eq (hf : Irreducible f) (hmon : f.Monic) (p : f.Factors) : (p : K[X]) = f :=
  Polynomial.eq_of_monic_of_associated p.monic hmon (p.irreducible.associated_of_dvd hf p.dvd)


abbrev unique (hf : Irreducible f) (hmon : f.Monic) : Unique f.Factors where
  default := ⟨f, hmon, hf, dvd_rfl⟩
  uniq p := Subtype.ext (coe_eq hf hmon p)

lemma ne_zero (p : f.Factors) : (p : K[X]) ≠ 0 := p.irreducible.ne_zero

lemma prime (p : f.Factors) : Prime (p : K[X]) := p.irreducible.prime

lemma separable (hf : f.Separable) (p : f.Factors) : (p : K[X]).Separable :=
  hf.of_dvd p.dvd


lemma mem_normalizedFactors_iff [DecidableEq K] (hf : f ≠ 0) {p : K[X]} :
    p ∈ normalizedFactors f ↔ p.Monic ∧ Irreducible p ∧ p ∣ f := by
  rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff' hf]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₂ ▸ monic_normalize h₁.ne_zero, h₁, h₃⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₂, h₁.normalize_eq_self, h₃⟩⟩

lemma finite (hf : f ≠ 0) : Finite f.Factors := by
  classical
  have h : Finite {p : K[X] // p ∈ normalizedFactors f} :=
    (normalizedFactors f).finite_toSet.to_subtype
  exact .of_injective _
    (Subtype.impEmbedding _ (· ∈ normalizedFactors f)
      fun p hp ↦ (mem_normalizedFactors_iff hf).mpr hp).injective

lemma nonempty (hu : ¬ IsUnit f) : Nonempty f.Factors :=
  let ⟨p, hp⟩ := f.exists_monic_irreducible_factor hu
  ⟨⟨p, hp⟩⟩


noncomputable def linearEquivRoots :
    {p : f.Factors // (p : K[X]).natDegree = 1} ≃ {x : K // f.eval x = 0} where
  toFun p := ⟨-((p : f.Factors) : K[X]).coeff 0,
    eval_eq_zero_of_dvd_of_eval_eq_zero (p : f.Factors).dvd <| by
      conv_lhs => rw [(p : f.Factors).monic.eq_X_add_C p.2]
      simp⟩
  invFun x := ⟨⟨X - C (x : K), monic_X_sub_C _, irreducible_X_sub_C _,
    dvd_iff_isRoot.mpr x.2⟩, natDegree_X_sub_C _⟩
  left_inv p := by
    refine Subtype.ext (Subtype.ext ?_)
    show X - C (-((p : f.Factors) : K[X]).coeff 0) = _
    conv_rhs => rw [(p : f.Factors).monic.eq_X_add_C p.2]
    rw [map_neg, sub_neg_eq_add]
  right_inv x := by
    refine Subtype.ext ?_
    show -(X - C (x : K)).coeff 0 = _
    simp

lemma isCoprime {p q : f.Factors} (hne : p ≠ q) : IsCoprime (p : K[X]) (q : K[X]) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mp <| Ideal.isCoprime_iff_sup_eq.mpr <|
    Ideal.IsMaximal.coprime_of_ne
      (PrincipalIdealRing.isMaximal_of_irreducible p.irreducible)
      (PrincipalIdealRing.isMaximal_of_irreducible q.irreducible)
      fun h ↦ hne <| Subtype.ext <| eq_of_monic_of_associated p.monic q.monic <|
        Ideal.span_singleton_eq_span_singleton.mp h

lemma isCoprime_span {p q : f.Factors} (hne : p ≠ q) :
    IsCoprime (Ideal.span {(p : K[X])}) (Ideal.span {(q : K[X])}) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mpr (isCoprime hne)

lemma associated_prod [Fintype f.Factors] (hf : f ≠ 0) (hsq : Squarefree f) :
    Associated (∏ p : f.Factors, (p : K[X])) f := by
  classical
  
  have hprod : ∏ p : f.Factors, (p : K[X]) =
      ∏ p : {p : K[X] // p ∈ (normalizedFactors f).toFinset}, (p : K[X]) :=
    Fintype.prod_equiv (Equiv.subtypeEquivRight fun p ↦ by
        rw [Multiset.mem_toFinset, mem_normalizedFactors_iff hf]) _ _
      fun x ↦ by rw [Equiv.subtypeEquivRight_apply]
  have hcoe : ∏ p : {p : K[X] // p ∈ (normalizedFactors f).toFinset}, (p : K[X]) =
      ∏ p ∈ (normalizedFactors f).toFinset, p :=
    Finset.prod_coe_sort _ fun x ↦ x
  rw [hprod, hcoe, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr ((squarefree_iff_nodup_normalizedFactors hf).mp hsq),
    Multiset.map_id']
  exact prod_normalizedFactors hf


lemma sum_natDegree_le [Fintype f.Factors] (hf : f ≠ 0) :
    ∑ p : f.Factors, (p : K[X]).natDegree ≤ f.natDegree := by
  rw [← natDegree_prod _ _ fun p _ ↦ p.ne_zero]
  exact natDegree_le_of_dvd
    (Fintype.prod_dvd_of_coprime (fun p q hpq ↦ isCoprime hpq) fun p ↦ p.dvd) hf

lemma span_eq_iInf_span (hf : f ≠ 0) (hsq : Squarefree f) :
    Ideal.span {f} = ⨅ p : f.Factors, Ideal.span {(p : K[X])} := by
  have : Fintype f.Factors := @Fintype.ofFinite _ (finite hf)
  rw [Ideal.iInf_span_singleton fun _ _ hpq ↦ isCoprime hpq]
  exact (Ideal.span_singleton_eq_span_singleton.mpr (associated_prod hf hsq)).symm


lemma exists_dvd_map {L : Type*} [Field L] (σ : K →+* L) (hf : f ≠ 0)
    {q : L[X]} (hq : Prime q) (hdvd : q ∣ f.map σ) :
    ∃ p : f.Factors, q ∣ (p : K[X]).map σ := by
  classical
  have h1 : Associated ((normalizedFactors f).map (Polynomial.map σ)).prod (f.map σ) := by
    have h2 := (prod_normalizedFactors hf).map (mapRingHom σ)
    rwa [map_multiset_prod, coe_mapRingHom] at h2
  obtain ⟨g, hgmem, hgdvd⟩ := hq.exists_mem_multiset_dvd (hdvd.trans h1.symm.dvd)
  obtain ⟨p₀, hp₀, rfl⟩ := Multiset.mem_map.mp hgmem
  exact ⟨⟨p₀, (mem_normalizedFactors_iff hf).mp hp₀⟩, hgdvd⟩

end Factors

end Polynomial

namespace AdjoinRoot

variable {K : Type*} [Field K] {f : K[X]}

instance instFactIrreducible (p : f.Factors) : Fact (Irreducible (p : K[X])) := ⟨p.irreducible⟩

instance instFiniteDimensional (p : f.Factors) : FiniteDimensional K (AdjoinRoot (p : K[X])) :=
  (powerBasis p.irreducible.ne_zero).finite

instance instNumberField [NumberField K] (p : f.Factors) :
    NumberField (AdjoinRoot (p : K[X])) :=
  .of_module_finite K _


theorem finrank_eq_natDegree (hf : f ≠ 0) : Module.finrank K (AdjoinRoot f) = f.natDegree := by
  rw [(powerBasis hf).finrank, powerBasis_dim]

lemma minpoly_root_factor (p : f.Factors) : minpoly K (root (p : K[X])) = (p : K[X]) := by
  rw [minpoly_root p.irreducible.ne_zero, p.monic.leadingCoeff, inv_one, map_one, mul_one]


theorem discr_powerBasis_eq_discr [Fact (Irreducible f)] [Algebra.IsSeparable K (AdjoinRoot f)]
    (hf : f.Monic) (hd : f.derivative.natDegree = f.natDegree - 1) :
    Algebra.discr K (powerBasis hf.ne_zero).basis = f.discr := by
  have : Module.Finite K (AdjoinRoot f) := (powerBasis hf.ne_zero).finite
  rw [Algebra.discr_powerBasis_eq_norm, (powerBasis hf.ne_zero).finrank, powerBasis_dim,
    powerBasis_gen, minpoly_root hf.ne_zero, hf.leadingCoeff, inv_one, map_one, mul_one,
    aeval_eq, norm_mk_eq_resultant hf, hd, resultant_deriv (Fact.out : Irreducible f).degree_pos,
    hf.leadingCoeff, mul_one, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]

open IntermediateField in

lemma isSeparable_of_separable (hf : f.Separable) (p : f.Factors) :
    Algebra.IsSeparable K (AdjoinRoot (p : K[X])) := by
  have hsep : IsSeparable K (root (p : K[X])) := by
    rw [IsSeparable, minpoly_root_factor p]
    exact p.separable hf
  have htop : K⟮root (p : K[X])⟯ = ⊤ :=
    adjoin_eq_top_of_algebra (F := K) (S := {root (p : K[X])}) adjoinRoot_eq_top
  have h := (isSeparable_adjoin_simple_iff_isSeparable K (AdjoinRoot (p : K[X]))).2 hsep
  rw [htop] at h
  exact (isSeparable_top (F := K) (E := AdjoinRoot (p : K[X]))).mp h


noncomputable def equivPiFactors (hf : f ≠ 0) (hsq : Squarefree f) :
    AdjoinRoot f ≃ₐ[K] ((p : f.Factors) → AdjoinRoot (p : K[X])) :=
  have : Finite f.Factors := Factors.finite hf
  AlgEquiv.ofRingEquiv (f :=
    (Ideal.quotEquivOfEq (Factors.span_eq_iInf_span hf hsq)).trans <|
      Ideal.quotientInfRingEquivPiQuotient _ fun _ _ hpq ↦ Factors.isCoprime_span hpq)
    fun _ ↦ rfl

@[simp]
lemma equivPiFactors_mk (hf : f ≠ 0) (hsq : Squarefree f) (q : K[X]) (p : f.Factors) :
    equivPiFactors hf hsq (mk f q) p = mk (p : K[X]) q :=
  rfl


noncomputable def projFactor (hf : f ≠ 0) (hsq : Squarefree f) (p : f.Factors) :
    AdjoinRoot f →+* AdjoinRoot (p : K[X]) :=
  (Pi.evalRingHom _ p).comp (equivPiFactors hf hsq).toRingEquiv.toRingHom

@[simp]
lemma projFactor_mk (hf : f ≠ 0) (hsq : Squarefree f) (q : K[X]) (p : f.Factors) :
    projFactor hf hsq p (mk f q) = mk (p : K[X]) q :=
  rfl


noncomputable def modPowEquivPiFactors (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ) :
    Units.modPow (AdjoinRoot f) n ≃*
      ((p : f.Factors) → Units.modPow (AdjoinRoot (p : K[X])) n) :=
  (Units.modPow.congr (equivPiFactors hf hsq).toMulEquiv n).trans <|
    Units.modPow.piEquiv (fun p : f.Factors ↦ AdjoinRoot (p : K[X])) n


@[simp]
lemma modPowEquivPiFactors_unit (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ) {a : AdjoinRoot f}
    (ha : IsUnit a) (p : f.Factors) :
    modPowEquivPiFactors hf hsq n (ha.unit : Units.modPow (AdjoinRoot f) n) p =
      ((ha.map (projFactor hf hsq p)).unit :
        Units.modPow (AdjoinRoot (p : K[X])) n) := by
  simp only [modPowEquivPiFactors, MulEquiv.trans_apply, Units.modPow.congr,
    QuotientGroup.congrRangePowMonoidHom, QuotientGroup.congr_mk, Units.modPow.piEquiv,
    QuotientGroup.mulEquivPiModRangePowMonoidHom_apply]
  exact congrArg _ (Units.ext rfl)


@[simp]
lemma modPowEquivPiFactors_mk (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ)
    (u : (AdjoinRoot f)ˣ) (p : f.Factors) :
    modPowEquivPiFactors hf hsq n (QuotientGroup.mk u) p =
      QuotientGroup.mk (Units.map (projFactor hf hsq p).toMonoidHom u) := by
  have h := modPowEquivPiFactors_unit hf hsq n u.isUnit p
  rw [show u.isUnit.unit = u from Units.ext rfl] at h
  exact h.trans (congrArg QuotientGroup.mk (Units.ext rfl))


lemma modPow_mk_eq_one_iff_forall_factors (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ)
    (u : (AdjoinRoot f)ˣ) :
    (QuotientGroup.mk u : Units.modPow (AdjoinRoot f) n) = 1 ↔
      ∀ p : f.Factors,
        (QuotientGroup.mk (Units.map (projFactor hf hsq p).toMonoidHom u) :
          Units.modPow (AdjoinRoot (p : K[X])) n) = 1 := by
  rw [← map_eq_one_iff (modPowEquivPiFactors hf hsq n) (modPowEquivPiFactors hf hsq n).injective,
    funext_iff]
  exact forall_congr' fun p ↦ by rw [modPowEquivPiFactors_mk, Pi.one_apply]


theorem norm_eq_prod_norm_projFactor [Fintype f.Factors] (hf : f ≠ 0) (hsq : Squarefree f)
    (a : AdjoinRoot f) :
    Algebra.norm K a = ∏ p : f.Factors, Algebra.norm K (projFactor hf hsq p a) := by
  rw [← Algebra.norm_eq_of_algEquiv (equivPiFactors hf hsq) a, Algebra.norm_pi]
  rfl


lemma norm_projFactor_mk_C_sub_X (hf : f ≠ 0) (hsq : Squarefree f) (p : f.Factors) (x : K) :
    Algebra.norm K (projFactor hf hsq p (mk f (C x - X))) = (p : K[X]).eval x := by
  have hd : (C x - X).natDegree = 1 := by compute_degree!
  rw [projFactor_mk, norm_mk_eq_resultant p.monic, hd, resultant_C_sub_X _ _ _ le_rfl]

end AdjoinRoot

end EtaleDecomposition



section NumberField

open NumberField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

instance Rat.instIsPrincipalIdealRingRingOfIntegers : IsPrincipalIdealRing (𝓞 ℚ) :=
  .of_surjective (Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ) Rat.ringOfIntegersEquiv.symm.surjective


theorem isIntegralClosure_int_integralClosure :
    IsIntegralClosure (integralClosure (𝓞 K) L) ℤ L := by
  refine ⟨Subtype.val_injective, fun {x} ↦ ⟨fun hx ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩⟩
  · exact ⟨⟨x, IsIntegral.tower_top (A := 𝓞 K) hx⟩, rfl⟩
  · have hyint : IsIntegral (𝓞 K) (y : L) := y.2
    have := isIntegral_trans (R := ℤ) (y : L) hyint
    rwa [show (y : L) = x from hy] at this

variable [NumberField K] [FiniteDimensional K L]


theorem NumberField.finite_classGroup_integralClosure :
    Finite (ClassGroup (integralClosure (𝓞 K) L)) := by
  have : NumberField L := .of_module_finite K L
  have := isIntegralClosure_int_integralClosure K L
  have := ClassGroup.fintypeOfAdmissibleOfFinite ℚ L
    (S := integralClosure (𝓞 K) L) AbsoluteValue.absIsAdmissible
  exact Finite.of_fintype _


theorem NumberField.fg_units_integralClosure :
    IsMulFG (integralClosure (𝓞 K) L)ˣ := by
  have : NumberField L := .of_module_finite K L
  have e : integralClosure (𝓞 K) L ≃ₐ[𝓞 K] (𝓞 L) :=
    IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L)
  exact Group.fg_of_surjective (f := (Units.mapEquiv e.symm.toRingEquiv.toMulEquiv).toMonoidHom) (Units.mapEquiv e.symm.toRingEquiv.toMulEquiv).surjective


theorem NumberField.subsingleton_classGroup_integralClosure (h : IsPrincipalIdealRing (𝓞 L)) :
    Subsingleton (ClassGroup (integralClosure (𝓞 K) L)) := by
  have : NumberField L := .of_module_finite K L
  have e : integralClosure (𝓞 K) L ≃ₐ[𝓞 K] 𝓞 L :=
    IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L)
  have : IsPrincipalIdealRing (integralClosure (𝓞 K) L) :=
    IsPrincipalIdealRing.of_surjective e.symm.toRingEquiv.toRingHom e.symm.surjective
  exact Fintype.card_le_one_iff_subsingleton.mp card_classGroup_eq_one.le


theorem NumberField.finrank_additive_units_integralClosure :
    Module.finrank ℤ (Additive (integralClosure (𝓞 K) L)ˣ) =
      Module.finrank ℤ (Additive (𝓞 L)ˣ) := by
  have : NumberField L := .of_module_finite K L
  have e : integralClosure (𝓞 K) L ≃ₐ[𝓞 K] 𝓞 L :=
    IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L)
  exact (MulEquiv.toAdditive
    (Units.mapEquiv e.toRingEquiv.toMulEquiv)).toIntLinearEquiv.finrank_eq

end NumberField



section Discriminant

open NumberField Module

variable {K : Type*} [Field K] [NumberField K]


theorem NumberField.exists_eq_discr_mul_sq (pb : PowerBasis ℚ K)
    (hpb : IsIntegral ℤ pb.gen) {d : ℤ} (hd : Algebra.discr ℚ pb.basis = (d : ℚ)) :
    ∃ q : ℤ, d = discr K * q ^ 2 := by
  let b := (integralBasis K).reindex ((integralBasis K).indexEquiv pb.basis)
  have hP (i j : Fin pb.dim) : IsIntegral ℤ (b.toMatrix pb.basis i j) := by
    have hint : IsIntegral ℤ (pb.basis j) := by rw [pb.coe_basis]; exact hpb.pow _
    rw [Basis.toMatrix_apply, Basis.repr_reindex_apply,
      ← IsIntegralClosure.algebraMap_mk' (𝓞 K) (pb.basis j) hint, integralBasis_repr_apply]
    exact isIntegral_algebraMap
  obtain ⟨q, hq⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.det hP)
  rw [eq_intCast (algebraMap ℤ ℚ)] at hq
  have key : Algebra.discr ℚ pb.basis = (b.toMatrix pb.basis).det ^ 2 * Algebra.discr ℚ b := by
    nth_rw 1 [← b.toMatrix_map_vecMul pb.basis]
    rw [Algebra.discr_of_matrix_vecMul]
  have hb : Algebra.discr ℚ ⇑b = (discr K : ℚ) := by
    rw [Basis.coe_reindex, Algebra.discr_reindex, ← coe_discr]
  refine ⟨q, ?_⟩
  have h : (d : ℚ) = ((discr K * q ^ 2 : ℤ) : ℚ) := by
    push_cast
    rw [← hd, key, hb, ← hq]
    ring
  exact_mod_cast h


theorem NumberField.RingOfIntegers.finrank_additive_units_of_discr_neg (h3 : finrank ℚ K = 3)
    (hd : discr K < 0) : finrank ℤ (Additive (𝓞 K)ˣ) = 1 := by
  have hsign := sign_discr K
  rw [Int.sign_eq_neg_one_of_neg hd] at hsign
  have hodd : Odd (InfinitePlace.nrComplexPlaces K) := by
    by_contra hc
    rw [(Nat.not_odd_iff_even.mp hc).neg_one_pow] at hsign
    norm_num at hsign
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [h3] at h2
  rw [Units.finrank_eq]
  simp only [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  obtain ⟨k, hk⟩ := hodd
  lia


theorem NumberField.RingOfIntegers.finrank_additive_units_of_discr_pos (h3 : finrank ℚ K = 3)
    (hd : 0 < discr K) : finrank ℤ (Additive (𝓞 K)ˣ) = 2 := by
  have hsign := sign_discr K
  rw [Int.sign_eq_one_of_pos hd] at hsign
  have heven : Even (InfinitePlace.nrComplexPlaces K) := by
    by_contra hc
    rw [(Nat.not_even_iff_odd.mp hc).neg_one_pow] at hsign
    norm_num at hsign
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [h3] at h2
  rw [Units.finrank_eq]
  simp only [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  obtain ⟨k, hk⟩ := heven
  lia


theorem NumberField.RingOfIntegers.isPrincipalIdealRing_of_finrank_eq_three_of_abs_discr_le
    (h3 : finrank ℚ K = 3) (hd : |discr K| ≤ 49) : IsPrincipalIdealRing (𝓞 K) := by
  refine RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt ?_
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [h3] at h2
  have hd' : (|discr K| : ℝ) ≤ 49 := by exact_mod_cast hd
  have hpi := Real.pi_gt_d4
  set s := InfinitePlace.nrComplexPlaces K
  have hs : s ≤ 1 := by lia
  rw [h3]
  interval_cases s <;> norm_num <;> nlinarith

end Discriminant

end
end M0
section M1



section



open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors Classical

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace FractionalIdeal



section PrincipalIdeal

variable [IsDomain R]

lemma spanSingleton_eq_one_iff {x : K} (hx : x ≠ 0) :
    spanSingleton R⁰ x = 1 ↔ ∃ a : Rˣ, algebraMap R K a = x := by
  constructor
  · intro h
    have hinv : spanSingleton R⁰ x⁻¹ = 1 := by rw [← spanSingleton_inv, h, inv_one]
    obtain ⟨a, ha⟩ := (mem_one_iff R⁰).mp (h ▸ mem_spanSingleton_self R⁰ x)
    obtain ⟨b, hb⟩ := (mem_one_iff R⁰).mp (hinv ▸ mem_spanSingleton_self R⁰ x⁻¹)
    have hab : a * b = 1 := IsFractionRing.injective R K (by
      rw [map_mul, ha, hb, mul_inv_cancel₀ hx, map_one])
    exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩
  · rintro ⟨a, rfl⟩
    rw [← coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr a.isUnit, coeIdeal_top]


lemma toPrincipalIdeal_eq_one_iff (u : Kˣ) :
    toPrincipalIdeal R K u = 1 ↔ ∃ a : Rˣ, Units.map (algebraMap R K : R →* K) a = u := by
  rw [← Units.val_inj, coe_toPrincipalIdeal, Units.val_one, spanSingleton_eq_one_iff u.ne_zero]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, Units.ext ha⟩, fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha]; rfl⟩⟩


lemma _root_.ClassGroup.mk_eq_one_iff_exists {I : (FractionalIdeal R⁰ K)ˣ} :
    ClassGroup.mk K I = 1 ↔ ∃ x : Kˣ, toPrincipalIdeal R K x = I := by
  rw [ClassGroup.mk_eq_one_iff]
  constructor
  · intro hI
    obtain ⟨x, hx⟩ := hI.principal
    have hx' : (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ x := by
      apply Subtype.coe_injective
      simp only [val_eq_coe, hx, coe_spanSingleton]
    have hx0 : x ≠ 0 := fun h ↦ Units.ne_zero I (by rw [hx', h, spanSingleton_zero])
    exact ⟨Units.mk0 x hx0, by rw [← Units.val_inj, coe_toPrincipalIdeal, hx']; rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨(x : K), by rw [coe_toPrincipalIdeal, coe_spanSingleton]⟩⟩

@[simp]
lemma _root_.ClassGroup.mk_toPrincipalIdeal (x : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal R K x) = 1 :=
  ClassGroup.mk_eq_one_iff_exists.mpr ⟨x, rfl⟩

end PrincipalIdeal

variable [IsDedekindDomain R]


noncomputable def unitOfPrime (v : HeightOneSpectrum R) : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr v.ne_bot)

@[simp] lemma coe_unitOfPrime (v : HeightOneSpectrum R) :
    ((unitOfPrime v : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = v.asIdeal := rfl


noncomputable def toFinsupp (I : (FractionalIdeal R⁰ K)ˣ) : HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v ↦ count K v (I : FractionalIdeal R⁰ K)) (by
    have := finite_factors (I : FractionalIdeal R⁰ K)
    simpa [Function.support, Filter.eventually_cofinite] using this)

@[simp] lemma toFinsupp_apply (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    toFinsupp I v = count K v (I : FractionalIdeal R⁰ K) := rfl


noncomputable def ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) : (FractionalIdeal R⁰ K)ˣ :=
  g.prod (fun v e ↦ unitOfPrime v ^ e)

lemma coe_ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) :
    ((ofFinsupp g : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K)
      = g.prod (fun v e ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ e) := by
  rw [ofFinsupp, ← Units.coeHom_apply, map_finsuppProd]
  simp [Units.coeHom]

lemma count_ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) (v : HeightOneSpectrum R) :
    count K v ((ofFinsupp g : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = g v := by
  rw [coe_ofFinsupp, count_finsuppProd]


lemma count_injective {I J : (FractionalIdeal R⁰ K)ˣ}
    (h : ∀ v, count K v (I : FractionalIdeal R⁰ K) = count K v (J : FractionalIdeal R⁰ K)) :
    I = J := by
  apply Units.ext
  rw [← finprod_heightOneSpectrum_factorization' K (Units.ne_zero I),
    ← finprod_heightOneSpectrum_factorization' K (Units.ne_zero J)]
  exact finprod_congr fun v ↦ by rw [h v]


noncomputable def factorization :
    (FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) where
  toFun I := Multiplicative.ofAdd (toFinsupp I)
  invFun g := ofFinsupp (Multiplicative.toAdd g)
  left_inv I := count_injective fun v ↦ by rw [count_ofFinsupp]; rfl
  right_inv g := by
    apply Multiplicative.toAdd.injective
    ext
    simp only [toAdd_ofAdd, toFinsupp_apply, count_ofFinsupp]
  map_mul' I J := by
    apply Multiplicative.toAdd.injective
    ext v
    simp only [toAdd_ofAdd, Finsupp.coe_add, Pi.add_apply, toFinsupp_apply, Units.val_mul,
      toAdd_mul]
    exact count_mul K v (Units.ne_zero I) (Units.ne_zero J)

@[simp] lemma factorization_apply (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    Multiplicative.toAdd (factorization I) v = count K v (I : FractionalIdeal R⁰ K) := rfl

lemma ofFinsupp_single (v : HeightOneSpectrum R) (m : ℤ) :
    (ofFinsupp (Finsupp.single v m) : (FractionalIdeal R⁰ K)ˣ) = unitOfPrime v ^ m := by
  rw [ofFinsupp, Finsupp.prod_single_index (zpow_zero _)]


@[simp]
lemma factorization_unitOfPrime (v : HeightOneSpectrum R) :
    factorization (unitOfPrime v : (FractionalIdeal R⁰ K)ˣ) =
      Multiplicative.ofAdd (Finsupp.single v 1) := by
  apply Multiplicative.toAdd.injective
  ext w
  rw [toAdd_ofAdd, factorization_apply, coe_unitOfPrime, Finsupp.single_apply,
    count_maximal K w v]


lemma pow_left_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective fun I : (FractionalIdeal R⁰ K)ˣ ↦ I ^ n := by
  intro I J h
  have h2 := congrArg (Multiplicative.toAdd <| factorization ·) h
  simp only [map_pow, toAdd_pow] at h2
  refine factorization.injective (Multiplicative.toAdd.injective (Finsupp.ext fun v ↦ ?_))
  have := congrArg (· v) h2
  simp only [Finsupp.smul_apply, nsmul_eq_mul] at this
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hn) this


noncomputable def _root_.IsDedekindDomain.HeightOneSpectrum.classGroupMk
    (v : HeightOneSpectrum R) : ClassGroup R :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

lemma _root_.IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_one_iff
    (v : HeightOneSpectrum R) : v.classGroupMk = 1 ↔ v.asIdeal.IsPrincipal :=
  ClassGroup.mk0_eq_one_iff _

lemma _root_.IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk_unitOfPrime (K : Type*)
    [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    v.classGroupMk = ClassGroup.mk K (unitOfPrime v) := by
  rw [HeightOneSpectrum.classGroupMk, ← ClassGroup.mk_mk0 K]
  exact congrArg _ (Units.ext rfl)


lemma _root_.IsDedekindDomain.HeightOneSpectrum.exists_pow_eq_span [Finite (ClassGroup R)]
    (v : HeightOneSpectrum R) :
    ∃ (n : ℕ) (π : R), 0 < n ∧ π ≠ 0 ∧ v.asIdeal ^ n = Ideal.span {π} := by
  set m := orderOf v.classGroupMk with hm
  refine ⟨m, ?_⟩
  have h1 : v.classGroupMk ^ m = 1 := pow_orderOf_eq_one _
  have hpow : (⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ : (Ideal R)⁰) ^ m =
      ⟨v.asIdeal ^ m, pow_mem (mem_nonZeroDivisors_of_ne_zero v.ne_bot) m⟩ :=
    Subtype.ext (SubmonoidClass.coe_pow _ m)
  rw [HeightOneSpectrum.classGroupMk, ← map_pow, hpow] at h1
  obtain ⟨π, hπ⟩ := (ClassGroup.mk0_eq_one_iff _).mp h1
  rw [Ideal.submodule_span_eq] at hπ
  refine ⟨π, by rw [hm]; exact orderOf_pos _, ?_, hπ⟩
  rintro rfl
  exact pow_ne_zero _ v.ne_bot (hπ.trans (by simp))


lemma mk_mem_closure_of_count_eq_zero {T : Set (HeightOneSpectrum R)}
    {I : (FractionalIdeal R⁰ K)ˣ}
    (h : ∀ v ∉ T, count K v (I : FractionalIdeal R⁰ K) = 0) :
    ClassGroup.mk K I ∈ Subgroup.closure (HeightOneSpectrum.classGroupMk '' T) := by
  have hI : I = ofFinsupp (toFinsupp I) := (factorization.left_inv I).symm
  rw [hI, ofFinsupp, map_finsuppProd]
  refine Subgroup.prod_mem _ fun v hv ↦ ?_
  have hvT : v ∈ T := by
    by_contra hvn
    exact Finsupp.mem_support_iff.mp hv (by rw [toFinsupp_apply, h v hvn])
  show ClassGroup.mk K (unitOfPrime v ^ toFinsupp I v) ∈
    Subgroup.closure (HeightOneSpectrum.classGroupMk '' T)
  rw [map_zpow, ← v.classGroupMk_eq_mk_unitOfPrime K]
  exact Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_image_of_mem _ hvT)) _


lemma mk0_mem_closure_of_count_eq {T : Set (HeightOneSpectrum R)} {J : (Ideal R)⁰} {x : Kˣ}
    (h : ∀ v ∉ T, count K v ((J : Ideal R) : FractionalIdeal R⁰ K) =
      count K v (spanSingleton R⁰ (x : K))) :
    ClassGroup.mk0 J ∈ Subgroup.closure (HeightOneSpectrum.classGroupMk '' T) := by
  have hmk : ClassGroup.mk0 J =
      ClassGroup.mk K (FractionalIdeal.mk0 K J * (toPrincipalIdeal R K x)⁻¹) := by
    rw [map_mul, map_inv, ClassGroup.mk_toPrincipalIdeal, inv_one, mul_one, ClassGroup.mk_mk0]
  rw [hmk]
  refine mk_mem_closure_of_count_eq_zero fun v hv ↦ ?_
  rw [Units.val_mul, count_mul K v (Units.ne_zero _) (Units.ne_zero _),
    Units.val_inv_eq_inv_val, count_inv, FractionalIdeal.coe_mk0, coe_toPrincipalIdeal, h v hv]
  exact add_neg_cancel _


theorem valuation_eq_exp_neg_count (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (- count K v (spanSingleton R⁰ x)) := by
  have key (r : R) (hr : r ≠ 0) : v.valuation K (algebraMap R K r) =
      WithZero.exp (- count K v (spanSingleton R⁰ (algebraMap R K r))) := by
    rw [valuation_of_algebraMap, intValuation_apply, v.intValuationDef_if_neg hr,
      ← coeIdeal_span_singleton, count_coe K v (by simpa using hr)]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hsa : spanSingleton R⁰ (algebraMap R K a) ≠ 0 := by
    rwa [spanSingleton_ne_zero_iff, ne_eq, _root_.map_eq_zero_iff _ (IsFractionRing.injective R K)]
  have hsb : spanSingleton R⁰ (algebraMap R K (b:R)) ≠ 0 := by
    rwa [spanSingleton_ne_zero_iff, ne_eq, _root_.map_eq_zero_iff _ (IsFractionRing.injective R K)]
  have hcount : count K v (spanSingleton R⁰ (algebraMap R K a / algebraMap R K (b:R))) =
      count K v (spanSingleton R⁰ (algebraMap R K a)) -
        count K v (spanSingleton R⁰ (algebraMap R K (b:R))) := by
    rw [← spanSingleton_div_spanSingleton, div_eq_mul_inv, count_mul K v hsa (inv_ne_zero hsb),
      count_inv, sub_eq_add_neg]
  rw [map_div₀, key a ha0, key (b:R) hb0, hcount, div_eq_mul_inv, ← WithZero.exp_neg,
    ← WithZero.exp_add]
  congr 1
  ring


theorem toAdd_valuationOfNeZero (v : HeightOneSpectrum R) (x : Kˣ) :
    Multiplicative.toAdd (v.valuationOfNeZero x) =
      - count K v (spanSingleton R⁰ (x : K)) := by
  have h : (v.valuationOfNeZero x : WithZero (Multiplicative ℤ)) =
      WithZero.exp (- count K v (spanSingleton R⁰ (x : K))) := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq, valuation_eq_exp_neg_count v x.ne_zero]
  rw [WithZero.exp_eq_coe_ofAdd, WithZero.coe_inj] at h
  rw [h, toAdd_ofAdd]



section NthRoot

variable (R K)


def nDivisible (n : ℕ) : Subgroup (FractionalIdeal R⁰ K)ˣ where
  carrier := {I | ∀ v, (n : ℤ) ∣ count K v (I : FractionalIdeal R⁰ K)}
  one_mem' v := by rw [Units.val_one, count_one]; exact dvd_zero _
  mul_mem' {I J} hI hJ v := by
    rw [Units.val_mul, count_mul K v (Units.ne_zero I) (Units.ne_zero J)]
    exact dvd_add (hI v) (hJ v)
  inv_mem' {I} hI v := by
    rw [Units.val_inv_eq_inv_val, count_inv]; exact (hI v).neg_right

variable {R K} in
lemma mem_nDivisible {n : ℕ} {I : (FractionalIdeal R⁰ K)ˣ} :
    I ∈ nDivisible R K n ↔ ∀ v, (n : ℤ) ∣ count K v (I : FractionalIdeal R⁰ K) :=
  Iff.rfl


noncomputable def nthRootFun (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ) : (FractionalIdeal R⁰ K)ˣ :=
  ofFinsupp (Finsupp.mapRange (· / (n:ℤ)) (by simp) (toFinsupp I))

lemma count_nthRootFun (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    count K v (nthRootFun R K n I : FractionalIdeal R⁰ K) =
      count K v (I : FractionalIdeal R⁰ K) / n := by
  rw [nthRootFun, count_ofFinsupp, Finsupp.mapRange_apply, toFinsupp_apply]


noncomputable def nthRootHom (n : ℕ) : nDivisible R K n →* (FractionalIdeal R⁰ K)ˣ where
  toFun I := nthRootFun R K n (I : (FractionalIdeal R⁰ K)ˣ)
  map_one' := count_injective fun v ↦ by
    simp only [count_nthRootFun, Subgroup.coe_one, Units.val_one, count_one, Int.zero_ediv]
  map_mul' I J := count_injective fun v ↦ by
    rw [count_nthRootFun, Units.val_mul, count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      count_nthRootFun, count_nthRootFun, Subgroup.coe_mul, Units.val_mul,
      count_mul K v (Units.ne_zero _) (Units.ne_zero _), Int.add_ediv_of_dvd_left (I.2 v)]

variable {R K} in
@[simp] lemma nthRootHom_apply (n : ℕ) (I : nDivisible R K n) :
    nthRootHom R K n I = nthRootFun R K n (I : (FractionalIdeal R⁰ K)ˣ) := rfl


lemma nthRootHom_pow (n : ℕ) (I : nDivisible R K n) :
    (nthRootHom R K n I) ^ n = (I : (FractionalIdeal R⁰ K)ˣ) := by
  apply count_injective
  intro v
  rw [Units.val_pow_eq_pow_val, count_pow, nthRootHom_apply,
    count_nthRootFun, Int.mul_ediv_cancel' (I.2 v)]


lemma exists_pow_eq (n : ℕ) {I : (FractionalIdeal R⁰ K)ˣ}
    (h : ∀ v, (n : ℤ) ∣ count K v (I : FractionalIdeal R⁰ K)) :
    ∃ J : (FractionalIdeal R⁰ K)ˣ, J ^ n = I :=
  ⟨nthRootHom R K n ⟨I, h⟩, nthRootHom_pow R K n ⟨I, h⟩⟩

end NthRoot



section NthRootClass


variable (R K)


def unitsNDivisible (n : ℕ) : Subgroup Kˣ :=
  Subgroup.comap (toPrincipalIdeal R K) (nDivisible R K n)

variable {R K} in
lemma mem_unitsNDivisible {n : ℕ} {u : Kˣ} :
    u ∈ unitsNDivisible R K n ↔ ∀ v, (n : ℤ) ∣ count K v (spanSingleton R⁰ (u : K)) := by
  rw [unitsNDivisible, Subgroup.mem_comap, mem_nDivisible]
  simp only [coe_toPrincipalIdeal]


def unitsNDivisibleToNDivisible (n : ℕ) :
    unitsNDivisible R K n →* nDivisible R K n :=
  (toPrincipalIdeal R K).restrict fun _ hx ↦ hx

@[simp] lemma coe_unitsNDivisibleToNDivisible (n : ℕ) (u : unitsNDivisible R K n) :
    (unitsNDivisibleToNDivisible R K n u : (FractionalIdeal R⁰ K)ˣ) =
      toPrincipalIdeal R K (u : Kˣ) := rfl


noncomputable def nthRootClass (n : ℕ) : unitsNDivisible R K n →* ClassGroup R :=
  (ClassGroup.mk K).comp ((nthRootHom R K n).comp (unitsNDivisibleToNDivisible R K n))

@[simp]
lemma nthRootClass_apply (n : ℕ) (u : unitsNDivisible R K n) :
    nthRootClass R K n u =
      ClassGroup.mk K (nthRootHom R K n (unitsNDivisibleToNDivisible R K n u)) :=
  rfl


lemma nthRootClass_eq_one_iff {n : ℕ} (hn : n ≠ 0) (u : unitsNDivisible R K n) :
    nthRootClass R K n u = 1 ↔
      ∃ (a : Rˣ) (w : Kˣ), Units.map (algebraMap R K : R →* K) a * w ^ n = (u : Kˣ) := by
  rw [nthRootClass_apply, ClassGroup.mk_eq_one_iff_exists]
  constructor
  · intro ⟨w, hw⟩
    
    have hpow : toPrincipalIdeal R K (w ^ n) = toPrincipalIdeal R K (u : Kˣ) := by
      rw [map_pow, hw, nthRootHom_pow, coe_unitsNDivisibleToNDivisible]
    have h1 : toPrincipalIdeal R K ((u : Kˣ) * (w ^ n)⁻¹) = 1 := by
      rw [map_mul, map_inv, hpow, mul_inv_cancel]
    obtain ⟨a, ha⟩ := (toPrincipalIdeal_eq_one_iff _).mp h1
    exact ⟨a, w, by rw [ha]; group⟩
  · intro ⟨a, w, hw⟩
    
    refine ⟨w, count_injective fun v ↦ ?_⟩
    have hcu : count K v ((toPrincipalIdeal R K (u : Kˣ) : (FractionalIdeal R⁰ K)ˣ) :
        FractionalIdeal R⁰ K) = n * count K v
          ((toPrincipalIdeal R K w : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) := by
      rw [← hw, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val,
        count_mul K v (Units.ne_zero _) (pow_ne_zero _ (Units.ne_zero _)), count_pow,
        (toPrincipalIdeal_eq_one_iff _).mpr ⟨a, rfl⟩, Units.val_one, count_one, zero_add]
    rw [nthRootHom_apply, count_nthRootFun, coe_unitsNDivisibleToNDivisible, hcu,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr hn)]

end NthRootClass

end FractionalIdeal

end
end M1
section M2



section



open IsDedekindDomain FractionalIdeal

open scoped nonZeroDivisors Classical

section DenomIdeal

variable {R : Type*} [CommRing R] (K : Type*) [CommRing K] [Algebra R K]


abbrev IsDedekindDomain.SInteger.denomIdeal (x : K) : Ideal R := (1 : Submodule R K).colon {x}

lemma IsDedekindDomain.SInteger.mem_denomIdeal_iff {x : K} {r : R} :
    r ∈ denomIdeal K x ↔ ∃ s : R, algebraMap R K r * x = algebraMap R K s := by
  rw [Submodule.mem_colon_singleton, Algebra.smul_def, Submodule.mem_one]
  exact exists_congr fun s ↦ eq_comm

end DenomIdeal

section IdealExtension

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  [IsDedekindDomain R]


theorem Ideal.map_eq_top_of_inv_subset {A : Subalgebra R K} {I : Ideal R} (hI : I ≠ ⊥)
    (h : (((I : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Set K) ⊆ A) :
    Ideal.map (algebraMap R A) I = ⊤ := by
  set M := Ideal.map (algebraMap R A) I
  have key : (1 : Submodule R K) ≤ (M.restrictScalars R).map A.val.toLinearMap := by
    rw [← FractionalIdeal.coe_one, ← mul_inv_cancel₀ (show ((I : FractionalIdeal R⁰ K)) ≠ 0 by simpa using hI),
      FractionalIdeal.coe_mul]
    refine Submodule.mul_le.mpr fun x hx y hy ↦ ?_
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hx
    exact ⟨algebraMap R A a * ⟨y, h hy⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha), rfl⟩
  exact (Ideal.eq_top_iff_one M).mpr (by simpa using Submodule.one_le.mp key)

end IdealExtension

namespace IsDedekindDomain.SInteger

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (S : Set (HeightOneSpectrum R))

lemma mem_integer_iff {x : K} : x ∈ S.integer K ↔ ∀ v ∉ S, v.valuation K x ≤ 1 := Iff.rfl

lemma toSubring_le_valuationSubring {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (S.integer K).toSubring ≤ (v.valuation K).valuationSubring.toSubring :=
  fun _ hx ↦ hx v hv


example : IsFractionRing (S.integer K) K := inferInstance


instance isIntegrallyClosed : IsIntegrallyClosed (S.integer K) := by
  rw [isIntegrallyClosed_iff K]
  intro x hx
  refine ⟨⟨x, fun v hv ↦ ?_⟩, rfl⟩
  
  set V := (v.valuation K).valuationSubring with hV
  let _ : Algebra (S.integer K) V :=
    (Subring.inclusion (toSubring_le_valuationSubring K S hv)).toAlgebra
  have _ : IsScalarTower (S.integer K) V K := .of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).mp inferInstance (hx.tower_top (A := V))
  rw [← hy]
  exact y.property




lemma exists_mem_notMem {v w : HeightOneSpectrum R} (h : w ≠ v) :
    ∃ a ∈ v.asIdeal, a ∉ w.asIdeal := by
  by_contra! hc
  exact h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)


lemma mem_integer_of_mem_inv {v : HeightOneSpectrum R} (hv : v ∈ S) {y : K}
    (hy : y ∈ (v.asIdeal : FractionalIdeal R⁰ K)⁻¹) : y ∈ S.integer K := by
  intro w hw
  obtain ⟨a, ha, haw⟩ := exists_mem_notMem (show w ≠ v by rintro rfl; exact hw hv)
  have h1 : y * algebraMap R K a ∈ (1 : FractionalIdeal R⁰ K) :=
    (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)).mp hy _
      (FractionalIdeal.mem_coeIdeal_of_mem R⁰ ha)
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h1
  have h2 : w.valuation K (y * algebraMap R K a) ≤ 1 := hr ▸ w.valuation_le_one r
  rwa [map_mul, w.valuation_eq_one_iff_notMem.mpr haw, mul_one] at h2


lemma map_asIdeal_eq_top {v : HeightOneSpectrum R} (hv : v ∈ S) :
    Ideal.map (algebraMap R (S.integer K)) v.asIdeal = ⊤ :=
  Ideal.map_eq_top_of_inv_subset v.ne_bot fun _ hy ↦ mem_integer_of_mem_inv K S hv hy




lemma denomIdeal_not_le {x : K} (hx : x ∈ S.integer K) {w : HeightOneSpectrum R} (hw : w ∉ S) :
    ¬ denomIdeal K x ≤ w.asIdeal := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer w x (hx w hw)
  refine fun hle ↦ d.property (hle ?_)
  rw [mem_denomIdeal_iff]
  exact ⟨n, by rw [mul_comm]; exact hnd⟩


lemma denomIdeal_ne_bot (x : K) : denomIdeal K x ≠ (⊥ : Ideal R) := by
  obtain ⟨⟨a, b, hb⟩, hab⟩ := IsLocalization.surj R⁰ x
  refine fun h0 ↦ nonZeroDivisors.ne_zero hb ?_
  have : b ∈ denomIdeal K x := by rw [mem_denomIdeal_iff]; exact ⟨a, by rw [mul_comm]; exact hab⟩
  simpa [h0] using this


lemma map_denomIdeal_eq_top {x : K} (hx : x ∈ S.integer K) :
    Ideal.map (algebraMap R (S.integer K)) (denomIdeal K x) = ⊤ := by
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  have h𝔭le : denomIdeal K x ≤ M.comap (algebraMap R (S.integer K)) :=
    (Ideal.le_comap_map).trans (Ideal.comap_mono hle)
  have h𝔭ne : M.comap (algebraMap R (S.integer K)) ≠ ⊥ :=
    fun h0 ↦ denomIdeal_ne_bot K x (le_bot_iff.mp (h0 ▸ h𝔭le))
  have hprime : (M.comap (algebraMap R (S.integer K))).IsPrime := hM.isPrime.comap _
  have hwS : (⟨_, hprime, h𝔭ne⟩ : HeightOneSpectrum R) ∈ S :=
    by_contra fun hwn ↦ denomIdeal_not_le K S hx hwn h𝔭le
  have htop := map_asIdeal_eq_top K S hwS
  exact hM.ne_top (top_le_iff.mp (htop.ge.trans Ideal.map_comap_le))


theorem map_comap_eq (I : Ideal (S.integer K)) :
    Ideal.map (algebraMap R (S.integer K)) (I.comap (algebraMap R (S.integer K))) = I := by
  refine le_antisymm Ideal.map_comap_le fun x hx ↦ ?_
  set f := algebraMap R (S.integer K)
  set J := Ideal.map f (I.comap f)
  
  have key (d : R) (hd : d ∈ denomIdeal K (x : K)) : f d * x ∈ J := by
    obtain ⟨s, hs⟩ := (mem_denomIdeal_iff K).mp hd
    have hfx : f d * x = f s := Subtype.ext (by simpa [f] using hs)
    exact hfx ▸ Ideal.mem_map_of_mem f (show f s ∈ I from hfx ▸ I.mul_mem_left _ hx)
  
  have hsub : Ideal.map f (denomIdeal K (x : K)) ≤ J.colon {x} :=
    Ideal.map_le_iff_le_comap.mpr fun d hd ↦ Submodule.mem_colon_singleton.mpr (key d hd)
  simpa using hsub ((Ideal.eq_top_iff_one _).mp (map_denomIdeal_eq_top K S x.property))




instance isNoetherianRing : IsNoetherianRing (S.integer K) := by
  refine (isNoetherianRing_iff_ideal_fg _).mpr fun I ↦ ?_
  rw [← map_comap_eq K S I]
  exact Ideal.FG.map (IsNoetherian.noetherian (R := R) (I.comap (algebraMap R (S.integer K))))
    (algebraMap R (S.integer K))


lemma comap_ne_bot {P : Ideal (S.integer K)} (hP : P ≠ ⊥) :
    P.comap (algebraMap R (S.integer K)) ≠ ⊥ := by
  intro h0
  exact hP (by rw [← map_comap_eq K S P, h0, Ideal.map_bot])


instance dimensionLEOne : Ring.DimensionLEOne (S.integer K) := by
  refine ⟨fun {P} hP hPp ↦ ?_⟩
  set f := algebraMap R (S.integer K) with hf
  
  obtain ⟨M, hM, hPM⟩ := P.exists_le_maximal hPp.ne_top
  have hcP : P.comap f ≠ ⊥ := comap_ne_bot K S hP
  have hMne : M ≠ ⊥ := fun h ↦ hP (le_bot_iff.mp (h ▸ hPM))
  have hcM : M.comap f ≠ ⊥ := comap_ne_bot K S hMne
  
  have hcPmax : (P.comap f).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hcP (hPp.comap f)
  have hcMprime : (M.comap f).IsPrime := hM.isPrime.comap f
  have heq : P.comap f = M.comap f :=
    hcPmax.eq_of_le hcMprime.ne_top (Ideal.comap_mono hPM)
  
  rwa [← map_comap_eq K S P, heq, map_comap_eq K S M]


instance isDedekindDomain : IsDedekindDomain (S.integer K) where




lemma map_asIdeal_ne_top {v : HeightOneSpectrum R} (hv : v ∉ S) :
    Ideal.map (algebraMap R (S.integer K)) v.asIdeal ≠ ⊤ := by
  set i : S.integer K →+* (v.valuation K).valuationSubring :=
    Subring.inclusion (toSubring_le_valuationSubring K S hv)
  refine ne_top_of_le_ne_top (Ideal.comap_ne_top i (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
    (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_)
  exact (v.valuation K).mem_maximalIdeal_iff.mpr ((v.valuation_lt_one_iff_mem a).mpr ha)

lemma comap_map_asIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (Ideal.map (algebraMap R (S.integer K)) v.asIdeal).comap (algebraMap R (S.integer K)) =
      v.asIdeal := by
  set f := algebraMap R (S.integer K) with hf
  refine (v.isMaximal.eq_of_le ?_ Ideal.le_comap_map).symm
  rw [Ne, Ideal.comap_eq_top_iff]
  exact map_asIdeal_ne_top K S hv

lemma isMaximal_map_asIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (Ideal.map (algebraMap R (S.integer K)) v.asIdeal).IsMaximal := by
  set f := algebraMap R (S.integer K) with hf
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (map_asIdeal_ne_top K S hv)
  have hcle : v.asIdeal ≤ M.comap f := (comap_map_asIdeal K S hv).ge.trans (Ideal.comap_mono hle)
  have hceq : M.comap f = v.asIdeal :=
    (v.isMaximal.eq_of_le (hM.isPrime.comap f).ne_top hcle).symm
  rwa [← map_comap_eq K S M, hceq] at hM


lemma map_asIdeal_ne_bot {v : HeightOneSpectrum R} (hv : v ∉ S) :
    Ideal.map (algebraMap R (S.integer K)) v.asIdeal ≠ ⊥ := by
  intro h
  refine v.ne_bot ?_
  rw [← comap_map_asIdeal K S hv, h,
    Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R (S.integer K))]


noncomputable def primeOfNotMem {v : HeightOneSpectrum R} (hv : v ∉ S) :
    HeightOneSpectrum (S.integer K) where
  asIdeal := Ideal.map (algebraMap R (S.integer K)) v.asIdeal
  isPrime := (isMaximal_map_asIdeal K S hv).isPrime
  ne_bot := map_asIdeal_ne_bot K S hv

@[simp] lemma primeOfNotMem_asIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (primeOfNotMem K S hv).asIdeal = Ideal.map (algebraMap R (S.integer K)) v.asIdeal :=
  rfl


noncomputable def primeBelow (P : HeightOneSpectrum (S.integer K)) : HeightOneSpectrum R where
  asIdeal := P.asIdeal.comap (algebraMap R (S.integer K))
  isPrime := P.isPrime.comap _
  ne_bot := comap_ne_bot K S P.ne_bot

@[simp] lemma primeBelow_asIdeal (P : HeightOneSpectrum (S.integer K)) :
    (primeBelow K S P).asIdeal = P.asIdeal.comap (algebraMap R (S.integer K)) :=
  rfl

lemma primeBelow_notMem (P : HeightOneSpectrum (S.integer K)) : primeBelow K S P ∉ S := by
  intro hv
  have h1 := map_asIdeal_eq_top K S hv
  rw [primeBelow_asIdeal, map_comap_eq] at h1
  exact P.isPrime.ne_top h1


noncomputable def heightOneSpectrumEquiv :
    {v : HeightOneSpectrum R // v ∉ S} ≃ HeightOneSpectrum (S.integer K) where
  toFun v := primeOfNotMem K S v.property
  invFun P := ⟨primeBelow K S P, primeBelow_notMem K S P⟩
  left_inv v := Subtype.ext <| HeightOneSpectrum.ext <| comap_map_asIdeal K S v.property
  right_inv P := HeightOneSpectrum.ext <| map_comap_eq K S P.asIdeal

@[simp] lemma heightOneSpectrumEquiv_apply (v : {v : HeightOneSpectrum R // v ∉ S}) :
    heightOneSpectrumEquiv K S v = primeOfNotMem K S v.property :=
  rfl

@[simp] lemma heightOneSpectrumEquiv_symm_apply (P : HeightOneSpectrum (S.integer K)) :
    ((heightOneSpectrumEquiv K S).symm P : HeightOneSpectrum R) = primeBelow K S P :=
  rfl


lemma comap_map_pow {v : HeightOneSpectrum R} (hv : v ∉ S) (n : ℕ) :
    (Ideal.map (algebraMap R (S.integer K)) (v.asIdeal ^ n)).comap
        (algebraMap R (S.integer K)) = v.asIdeal ^ n := by
  set f := algebraMap R (S.integer K) with hf
  have hP0 : Ideal.map f v.asIdeal ≠ 0 := map_asIdeal_ne_bot K S hv
  have hPnu : ¬ IsUnit (Ideal.map f v.asIdeal) :=
    fun h ↦ map_asIdeal_ne_top K S hv (Ideal.isUnit_iff.mp h)
  refine le_antisymm ?_ Ideal.le_comap_map
  have hdvd : (Ideal.map f (v.asIdeal ^ n)).comap f ∣ v.asIdeal ^ n :=
    Ideal.dvd_iff_le.mpr Ideal.le_comap_map
  obtain ⟨j, -, hassoc⟩ := (dvd_prime_pow v.prime n).mp hdvd
  rw [associated_iff_eq] at hassoc
  have hmapQ : Ideal.map f ((Ideal.map f (v.asIdeal ^ n)).comap f) =
      Ideal.map f (v.asIdeal ^ n) := map_comap_eq K S _
  rw [hassoc, Ideal.map_pow, Ideal.map_pow] at hmapQ
  rw [hassoc, (pow_inj_of_not_isUnit hPnu hP0).mp hmapQ]


lemma intValuationDef_map {v : HeightOneSpectrum R} (hv : v ∉ S) (a : R) :
    (primeOfNotMem K S hv).intValuationDef (algebraMap R (S.integer K) a) =
      v.intValuationDef a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hfa : algebraMap R (S.integer K) a ≠ 0 := fun h ↦ ha
    (FaithfulSMul.algebraMap_injective R (S.integer K)
      (h.trans (map_zero (algebraMap R (S.integer K))).symm))
  have hmem (k : ℕ) : a ∈ v.asIdeal ^ k ↔
      algebraMap R (S.integer K) a ∈ (primeOfNotMem K S hv).asIdeal ^ k := by
    rw [primeOfNotMem_asIdeal, ← Ideal.map_pow, ← Ideal.mem_comap, comap_map_pow K S hv]
  suffices h : Associates.count (Associates.mk (primeOfNotMem K S hv).asIdeal)
        (Associates.mk (Ideal.span {algebraMap R (S.integer K) a})).factors =
      Associates.count (Associates.mk v.asIdeal) (Associates.mk (Ideal.span {a})).factors by
    rw [v.intValuationDef_if_neg ha, (primeOfNotMem K S hv).intValuationDef_if_neg hfa, h]
  refine Nat.le_antisymm ?_ ?_
  · exact (v.le_count_iff ha _).mpr
      ((hmem _).mpr (((primeOfNotMem K S hv).le_count_iff hfa _).mp le_rfl))
  · exact ((primeOfNotMem K S hv).le_count_iff hfa _).mpr
      ((hmem _).mp ((v.le_count_iff ha _).mp le_rfl))


lemma valuation_heightOneSpectrumEquiv (v : {v : HeightOneSpectrum R // v ∉ S}) (x : K) :
    (heightOneSpectrumEquiv K S v).valuation K x = (v : HeightOneSpectrum R).valuation K x := by
  have hR (a : R) : (heightOneSpectrumEquiv K S v).valuation K (algebraMap R K a) =
      (v : HeightOneSpectrum R).valuation K (algebraMap R K a) := by
    have e1 : (heightOneSpectrumEquiv K S v).valuation K (algebraMap R K a) =
        (primeOfNotMem K S v.property).intValuationDef (algebraMap R (S.integer K) a) := by
      rw [IsScalarTower.algebraMap_apply R (S.integer K) K a,
        HeightOneSpectrum.valuation_of_algebraMap]; rfl
    rw [e1, intValuationDef_map K S v.property a, HeightOneSpectrum.valuation_of_algebraMap]; rfl
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [map_div₀, map_div₀, hR a, hR b]




instance : Module.IsTorsionFree R (S.integer K) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  exact FaithfulSMul.algebraMap_injective R (S.integer K)


lemma extendedHom_surjective :
    Function.Surjective (ClassGroup.extendedHom R (S.integer K)) := by
  intro c
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hI : (I : Ideal (S.integer K)) ≠ ⊥ := by
    have := I.2; rwa [mem_nonZeroDivisors_iff_ne_zero] at this
  refine ⟨ClassGroup.mk0 ⟨(I : Ideal (S.integer K)).comap (algebraMap R (S.integer K)),
    mem_nonZeroDivisors_iff_ne_zero.mpr (comap_ne_bot K S hI)⟩, ?_⟩
  rw [ClassGroup.extendedHom_mk0]
  exact congrArg _ (Subtype.ext (map_comap_eq K S _))


instance finite_classGroup [Finite (ClassGroup R)] : Finite (ClassGroup (S.integer K)) :=
  .of_surjective _ (extendedHom_surjective K S)


instance subsingleton_classGroup [Subsingleton (ClassGroup R)] :
    Subsingleton (ClassGroup (S.integer K)) :=
  (extendedHom_surjective K S).subsingleton


lemma map_le_map_pow_iff {v : HeightOneSpectrum R} (hv : v ∉ S) (J : Ideal R) (k : ℕ) :
    Ideal.map (algebraMap R (S.integer K)) J ≤ (primeOfNotMem K S hv).asIdeal ^ k ↔
      J ≤ v.asIdeal ^ k := by
  rw [primeOfNotMem_asIdeal, ← Ideal.map_pow]
  exact ⟨fun h ↦ Ideal.le_comap_map.trans ((Ideal.comap_mono h).trans (comap_map_pow K S hv k).le),
    Ideal.map_mono⟩


lemma count_map_coeIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) {J : Ideal R} (hJ : J ≠ ⊥) :
    count K (primeOfNotMem K S hv)
        ((Ideal.map (algebraMap R (S.integer K)) J : Ideal (S.integer K)) :
          FractionalIdeal (S.integer K)⁰ K) =
      count K v (J : FractionalIdeal R⁰ K) := by
  have hmJ := Ideal.map_ne_bot_of_ne_bot (S := S.integer K) hJ
  rw [count_coe K _ hmJ, count_coe K v hJ, Nat.cast_inj]
  refine Nat.le_antisymm
    ((v.le_count_iff_le hJ _).mpr ((map_le_map_pow_iff K S hv J _).mp
      (((primeOfNotMem K S hv).le_count_iff_le hmJ _).mp le_rfl)))
    (((primeOfNotMem K S hv).le_count_iff_le hmJ _).mpr ((map_le_map_pow_iff K S hv J _).mpr
      ((v.le_count_iff_le hJ _).mp le_rfl)))


lemma count_spanSingleton_primeOfNotMem {v : HeightOneSpectrum R} (hv : v ∉ S) (x : Kˣ) :
    count K (primeOfNotMem K S hv) (spanSingleton (S.integer K)⁰ (x : K)) =
      count K v (spanSingleton R⁰ (x : K)) := by
  refine neg_injective (WithZero.exp_injective ?_)
  rw [← valuation_eq_exp_neg_count _ x.ne_zero, ← valuation_eq_exp_neg_count v x.ne_zero]
  exact valuation_heightOneSpectrumEquiv K S ⟨v, hv⟩ (x : K)


lemma closure_le_ker_extendedHom :
    Subgroup.closure (HeightOneSpectrum.classGroupMk '' S) ≤
      (ClassGroup.extendedHom R (S.integer K)).ker := by
  rw [Subgroup.closure_le]
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, HeightOneSpectrum.classGroupMk,
    ClassGroup.extendedHom_mk0]
  refine (ClassGroup.mk0_eq_one_iff _).mpr ?_
  show (Ideal.map (algebraMap R (S.integer K)) v.asIdeal).IsPrincipal
  rw [map_asIdeal_eq_top K S hv]
  exact ⟨1, by simp⟩


lemma ker_extendedHom_le :
    (ClassGroup.extendedHom R (S.integer K)).ker ≤
      Subgroup.closure (HeightOneSpectrum.classGroupMk '' S) := by
  intro c hc
  obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective c
  rw [MonoidHom.mem_ker, ClassGroup.extendedHom_mk0, ← ClassGroup.mk_mk0 K,
    ClassGroup.mk_eq_one_iff_exists] at hc
  obtain ⟨x, hx⟩ := hc
  
  have hxval : spanSingleton (S.integer K)⁰ (x : K) =
      ((Ideal.map (algebraMap R (S.integer K)) (J : Ideal R) : Ideal (S.integer K)) :
        FractionalIdeal (S.integer K)⁰ K) := by
    have h := congrArg Units.val hx
    rwa [coe_toPrincipalIdeal, FractionalIdeal.coe_mk0] at h
  refine FractionalIdeal.mk0_mem_closure_of_count_eq (x := x) fun v hv ↦ ?_
  rw [← count_map_coeIdeal K S hv (mem_nonZeroDivisors_iff_ne_zero.mp J.2), ← hxval,
    count_spanSingleton_primeOfNotMem K S hv x]


lemma ker_extendedHom :
    (ClassGroup.extendedHom R (S.integer K)).ker =
      Subgroup.closure (HeightOneSpectrum.classGroupMk '' S) :=
  le_antisymm (ker_extendedHom_le K S) (closure_le_ker_extendedHom K S)


noncomputable def classGroupEquiv :
    ClassGroup (S.integer K) ≃*
      ClassGroup R ⧸ Subgroup.closure (HeightOneSpectrum.classGroupMk '' S) :=
  (QuotientGroup.quotientKerEquivOfSurjective _ (extendedHom_surjective K S)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (ker_extendedHom K S))

end IsDedekindDomain.SInteger

end
end M2
section M3



section



open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal

open scoped nonZeroDivisors




theorem Group.fg_of_module_finite_int {G : Type*} [CommGroup G]
    (h : Module.Finite ℤ (Additive G)) : IsMulFG G :=
  (GroupFG.iff_add_fg).mpr (Module.Finite.iff_addGroup_fg.mp h)


theorem Subgroup.fg_of_commGroup_fg {G : Type*} [CommGroup G] [IsMulFG G] (H : Subgroup G) :
    IsMulFG H :=
  Group.fg_of_module_finite_int <| Module.Finite.iff_fg.mpr <|
    IsNoetherian.noetherian (R := ℤ) (AddSubgroup.toIntSubmodule H.toAddSubgroup)


theorem Group.fg_of_fg_ker_of_fg_range {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hker : IsMulFG φ.ker) (hrange : IsMulFG φ.range) : IsMulFG G := by
  obtain ⟨S, hS, hSfin⟩ := (Subgroup.fg_iff _).mp ((Group.fg_iff_subgroup_fg _).mp hker)
  obtain ⟨T, hT, hTfin⟩ := (Subgroup.fg_iff _).mp ((Group.fg_iff_subgroup_fg _).mp hrange)
  
  obtain ⟨V, -, hVfin, hTV⟩ := (Set.exists_subset_image_finite_and (s := Set.univ)).mp
    ⟨T, fun t ht ↦ by simpa using hT.le (Subgroup.subset_closure ht), hTfin, subset_rfl⟩
  refine Group.fg_iff.mpr ⟨V ∪ S, ?_, hVfin.union hSfin⟩
  refine Subgroup.map_injective_of_ker_le φ
    (hS.ge.trans (Subgroup.closure_mono Set.subset_union_right)) le_top
    (le_antisymm (Subgroup.map_mono le_top) ?_)
  rw [← MonoidHom.range_eq_map, ← hT, MonoidHom.map_closure, Set.image_union]
  exact Subgroup.closure_mono (hTV.trans Set.subset_union_left)


theorem Subgroup.two_mul_card_inf_ker_le {G H : Type*} [Group G] [Group H] {X : Subgroup G}
    [Finite X] (φ : G →* H) {x : G} (hx : x ∈ X) (hφx : φ x ≠ 1) :
    2 * Nat.card (X ⊓ φ.ker : Subgroup G) ≤ Nat.card X := by
  set ψ := φ.comp X.subtype with hψ
  have : Finite ψ.range := Finite.of_surjective _ ψ.rangeRestrict_surjective
  have hker : Nat.card ψ.ker = Nat.card (X ⊓ φ.ker : Subgroup G) :=
    Nat.card_congr ⟨fun a ↦ ⟨a.1, a.1.2, a.2⟩, fun a ↦ ⟨⟨a.1, a.2.1⟩, a.2.2⟩,
      fun a ↦ rfl, fun a ↦ rfl⟩
  have hrange : 2 ≤ Nat.card ψ.range := by
    have : Nontrivial ψ.range :=
      ⟨1, ⟨ψ ⟨x, hx⟩, MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩⟩,
        fun hc ↦ hφx (Subtype.ext_iff.mp hc).symm⟩
    exact Finite.one_lt_card
  calc 2 * Nat.card (X ⊓ φ.ker : Subgroup G) = 2 * Nat.card ψ.ker := by rw [hker]
    _ ≤ Nat.card ψ.range * Nat.card ψ.ker := Nat.mul_le_mul_right _ hrange
    _ = Nat.card X := by rw [mul_comm]; rw [← Subgroup.index_ker, Subgroup.card_mul_index]

lemma AddMonoidHom.ker_nsmulAddMonoidHom {G : Type*} [AddCommGroup G] [HasUniqueDiv G] {n : ℕ}
    (hn : n ≠ 0) : (nsmulAddMonoidHom (α := G) n).ker = ⊥ :=
  AddMonoidHom.ker_eq_bot _ fun _ _ hab ↦
    nsmul_right_injective hn (by simpa only [nsmulAddMonoidHom_apply] using hab)


lemma AddMonoidHom.range_nsmulAddMonoidHom (R : Type*) [CommRing R] (n : ℕ) :
    (nsmulAddMonoidHom (α := R) n).range = (Ideal.span {(n : R)}).toAddSubgroup := by
  ext x
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, Submodule.mem_toAddSubgroup,
    Ideal.mem_span_singleton']
  constructor <;> exact fun ⟨c, hc⟩ ↦ ⟨c, by rw [← hc, nsmul_eq_mul, mul_comm]⟩

open AddSubgroup in

private lemma relIndex_range_comp_subtype {G : Type*} [AddCommGroup G]
    (U : AddSubgroup G) (n : ℕ) :
    (((nsmulAddMonoidHom (α := G) n).comp U.subtype).range).relIndex
        (nsmulAddMonoidHom (α := G) n).range =
      ((nsmulAddMonoidHom (α := G) n).ker ⊔ U).index := by
  set φG := nsmulAddMonoidHom (α := G) n
  set B : AddSubgroup G := (φG.comp U.subtype).range
  set C : AddSubgroup G := φG.ker ⊔ U
  set ρ := (QuotientAddGroup.mk' (B.addSubgroupOf φG.range)).comp φG.rangeRestrict with hρdef
  have hρ : Function.Surjective ρ :=
    (QuotientAddGroup.mk'_surjective _).comp φG.rangeRestrict_surjective
  have hker : ρ.ker = C := by
    ext g
    rw [AddMonoidHom.mem_ker, hρdef, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff]
    constructor
    · intro ⟨u, hu⟩
      refine AddSubgroup.mem_sup.mpr ⟨g - u, ?_, u, u.2, by abel⟩
      rw [AddMonoidHom.mem_ker, map_sub]
      have : φG (u : G) = φG g := hu
      rw [this, sub_self]
    · intro hg
      obtain ⟨k, hk, u, hu, rfl⟩ := AddSubgroup.mem_sup.mp hg
      refine ⟨⟨u, hu⟩, ?_⟩
      have hk0 : φG k = 0 := hk
      show φG (u : G) = φG (k + u)
      rw [map_add, hk0, zero_add]
  calc B.relIndex φG.range
      = Nat.card (φG.range ⧸ B.addSubgroupOf φG.range) := rfl
    _ = Nat.card (G ⧸ C) := Nat.card_congr <| ((QuotientAddGroup.quotientKerEquivOfSurjective
          ρ hρ).symm.trans (QuotientAddGroup.quotientAddEquivOfEq hker)).toEquiv
    _ = C.index := rfl

open AddSubgroup in

private lemma relIndex_sup_ker_mul_card_ker {G : Type*} [AddCommGroup G]
    (U : AddSubgroup G) (n : ℕ) :
    U.relIndex ((nsmulAddMonoidHom (α := G) n).ker ⊔ U) *
        Nat.card (nsmulAddMonoidHom (α := U) n).ker =
      Nat.card (nsmulAddMonoidHom (α := G) n).ker := by
  set φG := nsmulAddMonoidHom (α := G) n
  set φU := nsmulAddMonoidHom (α := U) n
  have h2 : Nat.card (φG.ker ⧸ U.addSubgroupOf φG.ker) = U.relIndex (φG.ker ⊔ U) :=
    Nat.card_congr (QuotientAddGroup.quotientInfEquivSumNormalQuotient φG.ker U).toEquiv
  have h3 : Nat.card (U.addSubgroupOf φG.ker) = Nat.card φU.ker :=
    Nat.card_congr
      ⟨fun x ↦ ⟨⟨(x : G), x.2⟩, Subtype.ext (x : φG.ker).2⟩,
        fun y ↦ ⟨⟨(y : U), congrArg Subtype.val y.2⟩, (y : U).2⟩,
        fun x ↦ rfl, fun y ↦ rfl⟩
  rw [← h2, ← h3]
  exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm

open AddSubgroup in

theorem AddSubgroup.index_range_nsmul_mul_card_ker {G : Type*} [AddCommGroup G]
    (U : AddSubgroup G) [U.FiniteIndex] (n : ℕ) :
    (nsmulAddMonoidHom (α := G) n).range.index *
        Nat.card ((nsmulAddMonoidHom (α := U) n)).ker =
      Nat.card ((nsmulAddMonoidHom (α := G) n)).ker *
        (nsmulAddMonoidHom (α := U) n).range.index := by
  set φG := nsmulAddMonoidHom (α := G) n
  set φU := nsmulAddMonoidHom (α := U) n
  set B : AddSubgroup G := (φG.comp U.subtype).range
  set C : AddSubgroup G := φG.ker ⊔ U
  
  have hBA : B ≤ φG.range := by
    rintro _ ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  have hBU : B ≤ U := by
    rintro _ ⟨u, rfl⟩
    exact U.nsmul_mem u.2 n
  have hUC : U ≤ C := le_sup_right
  
  have hrBU : B.relIndex U = φU.range.index := by
    have h : B.addSubgroupOf U = φU.range := by
      ext u
      exact ⟨fun ⟨w, hw⟩ ↦ ⟨w, Subtype.ext hw⟩, fun ⟨w, hw⟩ ↦ ⟨w, congrArg Subtype.val hw⟩⟩
    rw [relIndex, h]
  have hrBA : B.relIndex φG.range = C.index := relIndex_range_comp_subtype U n
  have hUK : U.relIndex C * Nat.card φU.ker = Nat.card φG.ker :=
    relIndex_sup_ker_mul_card_ker U n
  
  have h24 : C.index * φG.range.index = φU.range.index * U.index := by
    rw [← hrBA, ← hrBU, relIndex_mul_index hBA, relIndex_mul_index hBU]
  have hCne : C.index ≠ 0 := by
    intro h
    exact FiniteIndex.index_ne_zero (H := U)
      (Nat.eq_zero_of_zero_dvd (h ▸ AddSubgroup.index_dvd_of_le hUC))
  have hA : φG.range.index = φU.range.index * U.relIndex C := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hCne) ?_
    rw [h24, ← relIndex_mul_index hUC]
    ring
  calc φG.range.index * Nat.card φU.ker
      = φU.range.index * (U.relIndex C * Nat.card φU.ker) := by rw [hA]; ring
    _ = φU.range.index * Nat.card φG.ker := by rw [hUK]
    _ = Nat.card φG.ker * φU.range.index := mul_comm _ _


lemma AddEquiv.map_ker_nsmulAddMonoidHom {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃+ N) (n : ℕ) :
    ((nsmulAddMonoidHom (α := M) n).ker).map e.toAddMonoidHom =
      (nsmulAddMonoidHom (α := N) n).ker := by
  ext x
  rw [AddSubgroup.mem_map_equiv]
  simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
  rw [← map_nsmul, EmbeddingLike.map_eq_zero_iff]


lemma AddEquiv.index_range_nsmulAddMonoidHom {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃+ N) (n : ℕ) :
    (nsmulAddMonoidHom (α := M) n).range.index = (nsmulAddMonoidHom (α := N) n).range.index := by
  simpa [AddEquiv.map_range_nsmulAddMonoidHom]
    using (AddSubgroup.index_map_equiv (nsmulAddMonoidHom (α := M) n).range e).symm

lemma nsmulAddMonoidHom_range_prod (A B : Type*) [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    (nsmulAddMonoidHom (α := A × B) n).range =
      ((nsmulAddMonoidHom (α := A) n).range).prod (nsmulAddMonoidHom (α := B) n).range := by
  ext x
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, AddSubgroup.mem_prod]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨⟨y.1, congrArg Prod.fst hy⟩, ⟨y.2, congrArg Prod.snd hy⟩⟩,
    fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ ⟨(a, b), Prod.ext ha hb⟩⟩

lemma nsmulAddMonoidHom_ker_prod (A B : Type*) [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    (nsmulAddMonoidHom (α := A × B) n).ker =
      ((nsmulAddMonoidHom (α := A) n).ker).prod (nsmulAddMonoidHom (α := B) n).ker := by
  ext x
  simp [AddMonoidHom.mem_ker, AddSubgroup.mem_prod, Prod.ext_iff]


lemma Module.rank_eq_zero_of_finite (R M : Type*) [Ring R] [CharZero R] [AddCommGroup M]
    [Module R M] [Finite M] :
    Module.rank R M = 0 :=
  rank_eq_zero_iff.mpr fun x ↦ ⟨addOrderOf x, Nat.cast_ne_zero.mpr (addOrderOf_pos x).ne',
    by rw [Nat.cast_smul_eq_nsmul]; exact addOrderOf_nsmul_eq_zero x⟩

open scoped DirectSum in
open Module in

theorem AddSubgroup.index_range_nsmul_of_fg (G : Type*) [AddCommGroup G] [IsAddFG G]
    {n : ℕ} (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := G) n).range.index =
      n ^ finrank ℤ G * Nat.card (nsmulAddMonoidHom (α := G) n).ker := by
  obtain ⟨r, ι, fι, p, hp, e, ⟨eqv⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  have hne (i : ι) : NeZero (p i ^ e i) := ⟨pow_ne_zero _ (hp i).pos.ne'⟩
  have hTfin : Finite (⨁ i, ZMod (p i ^ e i)) := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have hidx : (nsmulAddMonoidHom (α := G) n).range.index
      = (nsmulAddMonoidHom (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).range.index := by
    simpa [AddEquiv.map_range_nsmulAddMonoidHom]
      using (AddSubgroup.index_map_equiv (nsmulAddMonoidHom (α := G) n).range eqv).symm
  have hker : Nat.card (nsmulAddMonoidHom (α := G) n).ker
      = Nat.card (nsmulAddMonoidHom (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).ker := by
    rw [← eqv.map_ker_nsmulAddMonoidHom n]
    exact Nat.card_congr
      (AddSubgroup.equivMapOfInjective _ eqv.toAddMonoidHom eqv.injective).toEquiv
  have hrk : finrank ℤ G = r := by
    have h1 : Module.rank ℤ ((Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) = r := by
      set π := LinearMap.fst ℤ (Fin r →₀ ℤ) (⨁ i, ZMod (p i ^ e i)) with hπ
      have h0 : Module.rank ℤ (LinearMap.ker π) = 0 := by
        have e2 : LinearMap.ker π ≃ₗ[ℤ] ⨁ i, ZMod (p i ^ e i) :=
          { toFun x := x.1.2
            map_add' _ _ := rfl
            map_smul' _ _ := rfl
            invFun t := ⟨(0, t), rfl⟩
            left_inv x := Subtype.ext (Prod.ext (x.2 : x.1.1 = 0).symm rfl)
            right_inv t := rfl }
        rw [e2.rank_eq]
        exact Module.rank_eq_zero_of_finite ℤ _
      rw [← π.rank_range_add_rank_ker, LinearMap.range_eq_top.mpr Prod.fst_surjective, rank_top,
        rank_finsupp_self', Cardinal.mk_fin, h0, add_zero]
    have h2 : finrank ℤ ((Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) = r := by
      simp [Module.finrank, h1]
    rw [eqv.toIntLinearEquiv.finrank_eq]
    convert h2 using 2
  have hkerF : (nsmulAddMonoidHom (α := Fin r →₀ ℤ) n).ker = ⊥ :=
    (AddMonoidHom.ker_eq_bot_iff _).mpr
      (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hn)
  rw [hidx, hker, hrk, nsmulAddMonoidHom_range_prod, AddSubgroup.index_prod,
    AddSubgroup.index_range_nsmul, AddSubgroup.index_range,
    nsmulAddMonoidHom_ker_prod, Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv,
    Nat.card_prod, hkerF]
  simp

open Module in

theorem CommGroup.card_modPow (G : Type*) [CommGroup G] [IsMulFG G] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      n ^ finrank ℤ (Additive G) * Nat.card (powMonoidHom n : G →* G).ker := by
  have hrange : (powMonoidHom n : G →* G).range =
      AddSubgroup.toSubgroup' (nsmulAddMonoidHom (α := Additive G) n).range := by
    ext x
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨Additive.ofMul y, hy⟩, fun ⟨y, hy⟩ ↦ ⟨y.toMul, hy⟩⟩
  have hker : (powMonoidHom n : G →* G).ker =
      AddSubgroup.toSubgroup' (nsmulAddMonoidHom (α := Additive G) n).ker := by
    ext x
    exact Iff.rfl
  rw [hrange, hker, ← Subgroup.index_eq_card]
  exact AddSubgroup.index_range_nsmul_of_fg (Additive G) hn


theorem Units.card_ker_powMonoidHom_two (R : Type*) [CommRing R] [IsDomain R]
    (h2 : ringChar R ≠ 2) :
    Nat.card ((powMonoidHom 2 : Rˣ →* Rˣ).ker) = 2 := by
  have hker : (powMonoidHom 2 : Rˣ →* Rˣ).ker = Subgroup.zpowers (-1 : Rˣ) := by
    ext x
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    constructor
    · intro hx
      have : (x : R) * x = 1 := by
        rw [← Units.val_mul, ← sq, hx, Units.val_one]
      rcases mul_self_eq_one_iff.mp this with h | h
      · exact ⟨0, by ext; simp [h]⟩
      · exact ⟨1, by ext; simp [h]⟩
    · rintro ⟨k, rfl⟩
      calc ((-1 : Rˣ) ^ k) ^ 2 = ((-1 : Rˣ) ^ 2) ^ k := by group
        _ = 1 := by simp
  rw [hker, Nat.card_zpowers]
  have hne : (-1 : Rˣ) ≠ 1 := fun h => Ring.neg_one_ne_one_of_char_ne_two h2 (by simpa using congrArg Units.val h)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by ext; simp) hne

open Module in

theorem Units.card_modPow_two (R : Type*) [CommRing R] [IsDomain R] [IsMulFG Rˣ]
    (h2 : ringChar R ≠ 2) :
    Nat.card (Units.modPow R 2) = 2 ^ (finrank ℤ (Additive Rˣ) + 1) := by
  rw [Units.modPow, CommGroup.card_modPow Rˣ two_ne_zero, Units.card_ker_powMonoidHom_two R h2,
    pow_succ]

open Module in

theorem AddCommGroup.nonempty_addEquiv_int_of_finrank_le_one {G : Type*} [AddCommGroup G]
    [IsAddFG G] [HasUniqueDiv G] [Nontrivial G] (h : Module.finrank ℤ G ≤ 1) :
    Nonempty (G ≃+ ℤ) := by
  have hfin : Module.Finite ℤ G := Module.Finite.iff_addGroup_fg.mpr ‹_›
  have h1 : Module.finrank ℤ G = 1 := le_antisymm h Module.finrank_pos
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ G) = 1 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, h1]
  obtain ⟨u⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hcard
  exact ⟨((Module.Free.chooseBasis ℤ G).equiv (Basis.singleton Unit ℤ)
    (Equiv.equivPUnit _)).toAddEquiv⟩

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]



variable (S : Set (HeightOneSpectrum R))


noncomputable def sUnitValuation : S.unit K →* (S → Multiplicative ℤ) where
  toFun x v := (v : HeightOneSpectrum R).valuationOfNeZero (x : Kˣ)
  map_one' := funext fun _ ↦ map_one _
  map_mul' x y := by simp only [Subgroup.coe_mul, map_mul]; rfl

@[simp]
lemma sUnitValuation_apply (x : S.unit K) (v : S) :
    sUnitValuation K S x v = (v : HeightOneSpectrum R).valuationOfNeZero (x : Kˣ) :=
  rfl


theorem ker_sUnitValuation :
    (sUnitValuation K S).ker =
      ((∅ : Set (HeightOneSpectrum R)).unit K).subgroupOf (S.unit K) := by
  ext x
  simp only [MonoidHom.mem_ker, funext_iff, Pi.one_apply, sUnitValuation_apply,
    Subgroup.mem_subgroupOf]
  refine ⟨fun hx v _ ↦ ?_, fun hx v ↦ ?_⟩
  · by_cases hv : v ∈ S
    · simpa using (v.valuationOfNeZero_eq_iff (x : Kˣ) 1).mp (hx ⟨v, hv⟩)
    · exact x.property v hv
  · exact (v.1.valuationOfNeZero_eq_iff (x : Kˣ) 1).mpr (by
      simpa using hx v.1 (Set.notMem_empty _))

variable (R) in

noncomputable def unitsEquivEmptyUnit : Rˣ ≃* (∅ : Set (HeightOneSpectrum R)).unit K :=
  let e₁ : R ≃ₐ[R] (⊥ : Subalgebra R K) :=
    (Algebra.botEquivOfInjective (IsFractionRing.injective R K)).symm
  let e₂ : (⊥ : Subalgebra R K) ≃ₐ[R] (∅ : Set (HeightOneSpectrum R)).integer K :=
    Subalgebra.equivOfEq _ _ (IsDedekindDomain.integer_empty R K).symm
  (Units.mapEquiv (e₁.trans e₂).toRingEquiv.toMulEquiv).trans (Set.unitEquivUnitsInteger _ K).symm

@[simp]
lemma coe_unitsEquivEmptyUnit (a : Rˣ) :
    ((unitsEquivEmptyUnit R K a : ↥((∅ : Set (HeightOneSpectrum R)).unit K)) : Kˣ) =
      Units.map (algebraMap R K : R →* K) a :=
  Units.ext rfl


theorem fg_sUnit [IsMulFG Rˣ] (hS : S.Finite) : IsMulFG (S.unit K) := by
  have : Finite S := hS.to_subtype
  refine Group.fg_of_fg_ker_of_fg_range (sUnitValuation K S) ?_ (Subgroup.fg_of_commGroup_fg _)
  rw [ker_sUnitValuation]
  have : IsMulFG ((∅ : Set (HeightOneSpectrum R)).unit K) :=
    Group.fg_of_surjective (f := (unitsEquivEmptyUnit R K).toMonoidHom)
      (unitsEquivEmptyUnit R K).surjective
  have hle : (∅ : Set (HeightOneSpectrum R)).unit K ≤ S.unit K := Set.unit_mono S.empty_subset
  exact Group.fg_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hle).symm.surjective



section Rank

open Module


noncomputable def sUnitLog : Additive (S.unit K) →ₗ[ℤ] (S → ℤ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x w ↦ Multiplicative.toAdd (sUnitValuation K S (Additive.toMul x) w)
      map_zero' := by ext w; simp
      map_add' := fun x y ↦ by ext w; simp }

@[simp]
lemma sUnitLog_apply (x : Additive (S.unit K)) (w : S) :
    sUnitLog K S x w = Multiplicative.toAdd (sUnitValuation K S (Additive.toMul x) w) :=
  rfl


lemma mem_ker_sUnitLog_iff (x : Additive (S.unit K)) :
    x ∈ LinearMap.ker (sUnitLog K S) ↔
      Additive.toMul x ∈ MonoidHom.ker (sUnitValuation K S) := by
  simp only [LinearMap.mem_ker, MonoidHom.mem_ker]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · ext w
    have h2 : Multiplicative.toAdd (sUnitValuation K S (Additive.toMul x) w) = 0 :=
      congrFun hx w
    simpa using toAdd_eq_zero.mp h2
  · ext w
    show Multiplicative.toAdd (sUnitValuation K S (Additive.toMul x) w) = 0
    rw [hx]
    rfl


noncomputable def sUnitLogKerEquiv : ↥(LinearMap.ker (sUnitLog K S)) ≃ₗ[ℤ] Additive Rˣ :=
  have ekermul : ↥(MonoidHom.ker (sUnitValuation K S)) ≃* Rˣ :=
    ((unitsEquivEmptyUnit R K).trans <|
      ((Subgroup.subgroupOfEquivOfLe (Set.unit_mono S.empty_subset)).symm.trans
        (MulEquiv.subgroupCongr (ker_sUnitValuation K S)).symm)).symm
  AddEquiv.toIntLinearEquiv <|
    AddEquiv.trans
      { toFun := fun x ↦ Additive.ofMul (⟨Additive.toMul x.1, (mem_ker_sUnitLog_iff K S _).mp x.2⟩ :
          ↥(MonoidHom.ker (sUnitValuation K S)))
        invFun := fun y ↦ ⟨Additive.ofMul ((Additive.toMul y : _) : S.unit K),
          (mem_ker_sUnitLog_iff K S _).mpr (Additive.toMul y).2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl }
      (MulEquiv.toAdditive ekermul)

variable [Finite (ClassGroup R)]


lemma exists_sUnit_valuation_single (v : S) :
    ∃ (x : S.unit K) (n : ℤ), n ≠ 0 ∧ sUnitValuation K S x v = Multiplicative.ofAdd n ∧
      ∀ w : S, w ≠ v → sUnitValuation K S x w = 1 := by
  classical
  obtain ⟨h, π, hpos, hπ0, hπ⟩ := (v : HeightOneSpectrum R).exists_pow_eq_span
  have hπK : algebraMap R K π ≠ 0 :=
    fun h0 ↦ hπ0 (IsFractionRing.injective R K (h0.trans (map_zero _).symm))
  
  have hmem : Units.mk0 (algebraMap R K π) hπK ∈ S.unit K := fun w hw ↦
    HeightOneSpectrum.valuation_algebraMap_eq_one_of_pow_eq_span
      (fun hc ↦ hw (by rw [hc]; exact v.2)) hπ
  
  have hval (w : S) : Multiplicative.toAdd
      (sUnitValuation K S ⟨Units.mk0 (algebraMap R K π) hπK, hmem⟩ w) =
        -(if (w : HeightOneSpectrum R) = v then (h : ℤ) else 0) := by
    show Multiplicative.toAdd
      ((w : HeightOneSpectrum R).valuationOfNeZero (Units.mk0 (algebraMap R K π) hπK)) = _
    rw [toAdd_valuationOfNeZero, Units.val_mk0, ← coeIdeal_span_singleton, ← hπ, coeIdeal_pow,
      count_pow, count_maximal]
    simp only [mul_ite, mul_one, mul_zero]
    exact congrArg Neg.neg (if_congr eq_comm rfl rfl)
  refine ⟨⟨Units.mk0 (algebraMap R K π) hπK, hmem⟩, -(h : ℤ),
    neg_ne_zero.mpr (Int.natCast_ne_zero.mpr hpos.ne'), ?_, fun w hne ↦ ?_⟩
  · exact Multiplicative.toAdd.injective (by rw [toAdd_ofAdd, hval v, if_pos rfl])
  · exact Multiplicative.toAdd.injective (by
      rw [toAdd_one, hval w, if_neg (fun hc ↦ hne (Subtype.ext hc)), neg_zero])

open Module in

lemma finrank_range_sUnitLog (hS : S.Finite) :
    finrank ℤ ↥(LinearMap.range (sUnitLog K S)) = S.ncard := by
  classical
  have hSfin : Finite S := hS.to_subtype
  have hSfin' : Fintype S := Fintype.ofFinite S
  choose x n hn hxv hxw using fun v : S ↦ exists_sUnit_valuation_single K S v
  have hψx (v w : S) : sUnitLog K S (Additive.ofMul (x v)) w = if w = v then n v else 0 := by
    rw [sUnitLog_apply]
    rcases eq_or_ne w v with rfl | hne
    · rw [if_pos rfl, toMul_ofMul, hxv w, toAdd_ofAdd]
    · rw [if_neg hne, toMul_ofMul, hxw v w hne, toAdd_one]
  have hfam : LinearIndependent ℤ fun v : S ↦ sUnitLog K S (Additive.ofMul (x v)) := by
    refine linearIndependent_of_diagonal (fun v ↦ ?_) (fun v w hne ↦ ?_)
    · rw [hψx v v, if_pos rfl]
      exact hn v
    · rw [hψx v w, if_neg hne]
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  refine le_antisymm ?_ ?_
  · have h := Submodule.finrank_le (LinearMap.range (sUnitLog K S))
    rwa [finrank_fintype_fun_eq_card] at h
  · have hfam' : LinearIndependent ℤ fun v : S ↦
        (⟨sUnitLog K S (Additive.ofMul (x v)), LinearMap.mem_range_self _ _⟩ :
          ↥(LinearMap.range (sUnitLog K S))) :=
      hfam.of_comp (LinearMap.range (sUnitLog K S)).subtype
    exact hfam'.fintype_card_le_finrank

open Module in

theorem finrank_sUnit [IsMulFG Rˣ] (hS : S.Finite) :
    finrank ℤ (Additive (S.unit K)) = finrank ℤ (Additive Rˣ) + S.ncard := by
  have hFG : IsMulFG (S.unit K) := fg_sUnit K S hS
  
  have hadd := Submodule.rank_quotient_add_rank (LinearMap.ker (sUnitLog K S))
  have hM := rank_lt_aleph0 ℤ (Additive (S.unit K))
  rw [← hadd] at hM
  have htn := congrArg Cardinal.toNat hadd
  rw [Cardinal.toNat_add (le_self_add.trans_lt hM) (le_add_self.trans_lt hM)] at htn
  
  have h₁ := congrArg Cardinal.toNat (LinearMap.quotKerEquivRange (sUnitLog K S)).lift_rank_eq
  have h₂ := congrArg Cardinal.toNat (sUnitLogKerEquiv K S).lift_rank_eq
  simp only [Cardinal.toNat_lift] at h₁ h₂
  rw [h₁, h₂] at htn
  rw [show Cardinal.toNat (Module.rank ℤ ↥(LinearMap.range (sUnitLog K S))) =
      finrank ℤ ↥(LinearMap.range (sUnitLog K S)) from rfl, finrank_range_sUnitLog K S hS] at htn
  have htn' : S.ncard + finrank ℤ (Additive Rˣ) = finrank ℤ (Additive (S.unit K)) := htn
  rw [← htn', Nat.add_comm]

end Rank



variable (S : Set (HeightOneSpectrum R)) (n : ℕ)


noncomputable def sUnitToSelmer : S.unit K →* selmerGroup (K := K) (S := S) (n := n) where
  toFun x := ⟨QuotientGroup.mk (x : Kˣ), fun v hv ↦ by
    rw [HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
    have : v.valuationOfNeZero (x : Kˣ) = 1 :=
      (v.valuationOfNeZero_eq_iff (x : Kˣ) 1).mpr (by rw [x.property v hv, WithZero.coe_one])
    simp [this]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
lemma coe_sUnitToSelmer (x : S.unit K) :
    (sUnitToSelmer K S n x : Units.modPow K n) = QuotientGroup.mk (x : Kˣ) :=
  rfl


noncomputable def sUnitModPowToSelmer :
    (S.unit K ⧸ (powMonoidHom n : S.unit K →* S.unit K).range) →*
      selmerGroup (K := K) (S := S) (n := n) :=
  QuotientGroup.lift _ (sUnitToSelmer K S n) <| by
    rintro _ ⟨x, rfl⟩
    refine Subtype.ext ?_
    exact (QuotientGroup.eq_one_iff _).mpr ⟨(x : Kˣ), rfl⟩

@[simp]
lemma range_sUnitModPowToSelmer :
    (sUnitModPowToSelmer K S n).range = (sUnitToSelmer K S n).range := by
  ext
  exact ⟨by rintro ⟨y, rfl⟩; induction y using QuotientGroup.induction_on with
    | H y => exact ⟨y, rfl⟩, fun ⟨y, hy⟩ ↦ ⟨QuotientGroup.mk y, hy⟩⟩


lemma SInteger.valuationOfNeZero_heightOneSpectrumEquiv (v : {v : HeightOneSpectrum R // v ∉ S})
    (u : Kˣ) : (SInteger.heightOneSpectrumEquiv K S v).valuationOfNeZero u
      = (v : HeightOneSpectrum R).valuationOfNeZero u := by
  rw [← WithZero.coe_inj,
    show ((_ : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = _ from
      HeightOneSpectrum.valuationOfNeZero_eq _ u, HeightOneSpectrum.valuationOfNeZero_eq,
    SInteger.valuation_heightOneSpectrumEquiv K S v (u : K)]


lemma mem_selmerGroup_iff_unitsNDivisible (u : Kˣ) :
    (QuotientGroup.mk u : Units.modPow K n) ∈ selmerGroup (R := R) (K := K) (S := S) (n := n) ↔
      u ∈ unitsNDivisible (S.integer K) K n := by
  rw [mem_unitsNDivisible, ← (SInteger.heightOneSpectrumEquiv K S).forall_congr_right,
    Subtype.forall]
  exact forall₂_congr fun v hv ↦ by
    rw [HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff,
      ← SInteger.valuationOfNeZero_heightOneSpectrumEquiv K S ⟨v, hv⟩,
      toAdd_valuationOfNeZero, Int.dvd_neg]


noncomputable def selmerGroupFromUnits :
    unitsNDivisible (S.integer K) K n →* selmerGroup (R := R) (K := K) (S := S) (n := n) :=
  (QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range).restrict
    fun u hu ↦ (mem_selmerGroup_iff_unitsNDivisible K S n u).mpr hu

@[simp] lemma coe_selmerGroupFromUnits (u : unitsNDivisible (S.integer K) K n) :
    (selmerGroupFromUnits K S n u : Units.modPow K n) = QuotientGroup.mk (u : Kˣ) := rfl

lemma selmerGroupFromUnits_surjective :
    Function.Surjective (selmerGroupFromUnits K S n) := by
  intro ⟨c, hc⟩
  induction c using QuotientGroup.induction_on with
  | H u =>
    exact ⟨⟨u, (mem_selmerGroup_iff_unitsNDivisible K S n u).mp hc⟩, rfl⟩


lemma ker_selmerGroupFromUnits_le [NeZero n] :
    (selmerGroupFromUnits K S n).ker ≤ (nthRootClass (S.integer K) K n).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have : (QuotientGroup.mk (u : Kˣ) : Units.modPow K n) = 1 := congrArg Subtype.val hu
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).mp this
  exact (nthRootClass_eq_one_iff _ _ (NeZero.ne n) u).mpr ⟨1, w, by
    rw [map_one, one_mul]; exact hw⟩


noncomputable def toSClassGroup [NeZero n] :
    selmerGroup (R := R) (K := K) (S := S) (n := n) →* ClassGroup (S.integer K) :=
  (QuotientGroup.lift _ (nthRootClass (S.integer K) K n)
      (ker_selmerGroupFromUnits_le K S n)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (selmerGroupFromUnits_surjective K S n)).symm.toMonoidHom

lemma toSClassGroup_selmerGroupFromUnits [NeZero n] (u : unitsNDivisible (S.integer K) K n) :
    toSClassGroup K S n (selmerGroupFromUnits K S n u) =
      nthRootClass (S.integer K) K n u := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective _
      (selmerGroupFromUnits_surjective K S n)).symm (selmerGroupFromUnits K S n u) =
        QuotientGroup.mk u := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [toSClassGroup, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk']

lemma coe_unitEquivUnitsInteger_symm (a : (S.integer K)ˣ) :
    ((S.unitEquivUnitsInteger K).symm a : Kˣ) =
      Units.map (algebraMap (S.integer K) K : S.integer K →* K) a := by
  apply Units.ext
  rw [Set.unitEquivUnitsInteger_symm_apply_coe]
  rfl


theorem ker_toSClassGroup [NeZero n] :
    (toSClassGroup K S n).ker = (sUnitToSelmer K S n).range := by
  ext x
  obtain ⟨u, rfl⟩ := selmerGroupFromUnits_surjective K S n x
  rw [MonoidHom.mem_ker, toSClassGroup_selmerGroupFromUnits,
    nthRootClass_eq_one_iff _ _ (NeZero.ne n)]
  simp only [MonoidHom.mem_range, Subtype.ext_iff, coe_sUnitToSelmer, coe_selmerGroupFromUnits,
    Units.modPow.mk_eq_mk_iff]
  refine (S.unitEquivUnitsInteger K).symm.toEquiv.exists_congr fun a ↦ exists_congr fun w ↦ ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, coe_unitEquivUnitsInteger_symm,
    eq_comm]


theorem range_toSClassGroup [NeZero n] :
    (toSClassGroup K S n).range =
      (powMonoidHom n : ClassGroup (S.integer K) →* ClassGroup (S.integer K)).ker := by
  ext c
  rw [MonoidHom.mem_ker, powMonoidHom_apply]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := selmerGroupFromUnits_surjective K S n x
    rw [toSClassGroup_selmerGroupFromUnits, nthRootClass_apply, ← map_pow, nthRootHom_pow]
    exact ClassGroup.mk_eq_one_iff_exists.mpr ⟨(u : Kˣ), rfl⟩
  · intro hc
    obtain ⟨I, rfl⟩ : ∃ I, ClassGroup.mk K I = c :=
      ClassGroup.induction (K := K) (fun I ↦ ⟨I, rfl⟩) c
    rw [← map_pow, ClassGroup.mk_eq_one_iff_exists] at hc
    obtain ⟨x, hx⟩ := hc
    have hcount (v : HeightOneSpectrum (S.integer K)) :
        count K v ((toPrincipalIdeal (S.integer K) K x : (FractionalIdeal (S.integer K)⁰ K)ˣ) :
            FractionalIdeal (S.integer K)⁰ K) =
          n * count K v ((I : (FractionalIdeal (S.integer K)⁰ K)ˣ) :
            FractionalIdeal (S.integer K)⁰ K) := by
      rw [hx, Units.val_pow_eq_pow_val, count_pow]
    have hmem : x ∈ unitsNDivisible (S.integer K) K n := fun v ↦ by
      rw [hcount v]; exact Dvd.intro _ rfl
    refine ⟨selmerGroupFromUnits K S n ⟨x, hmem⟩, ?_⟩
    rw [toSClassGroup_selmerGroupFromUnits, nthRootClass_apply]
    congr 1
    refine count_injective fun v ↦ ?_
    rw [nthRootHom_apply, count_nthRootFun, coe_unitsNDivisibleToNDivisible, hcount v,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr (NeZero.ne n))]



variable (R) in

theorem finite_selmerGroup [Finite (ClassGroup R)] [IsMulFG Rˣ] (hS : S.Finite) [NeZero n] :
    Finite (selmerGroup (K := K) (S := S) (n := n)) := by
  have := fg_sUnit K S hS
  have hker : Finite (toSClassGroup K S n).ker := by
    rw [ker_toSClassGroup, ← range_sUnitModPowToSelmer]
    have := Subgroup.finiteIndex_range_powMonoidHom_of_fg (S.unit K) (NeZero.ne n)
    exact Finite.Set.finite_range _
  have hquot : Finite (selmerGroup (K := K) (S := S) (n := n) ⧸ (toSClassGroup K S n).ker) :=
    .of_injective _ (QuotientGroup.kerLift_injective (toSClassGroup K S n))
  exact Finite.of_subgroup_quotient (toSClassGroup K S n).ker




theorem sUnitToSelmer_surjective [NeZero n] [Subsingleton (ClassGroup (S.integer K))] :
    Function.Surjective (sUnitToSelmer K S n) := fun x ↦ by
  have hx : x ∈ (sUnitToSelmer K S n).range := by
    rw [← ker_toSClassGroup, MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  exact hx


theorem card_selmerGroup_le [NeZero n] [IsMulFG Rˣ] (hS : S.Finite)
    [Subsingleton (ClassGroup (S.integer K))] :
    Nat.card (selmerGroup (K := K) (S := S) (n := n)) ≤
      Nat.card (S.unit K ⧸ (powMonoidHom n : S.unit K →* S.unit K).range) := by
  have := fg_sUnit K S hS
  have := Subgroup.finiteIndex_range_powMonoidHom_of_fg (S.unit K) (NeZero.ne n)
  refine Nat.card_le_card_of_surjective (sUnitModPowToSelmer K S n) fun x ↦ ?_
  obtain ⟨u, hu⟩ := sUnitToSelmer_surjective K S n x
  exact ⟨QuotientGroup.mk u, hu⟩


theorem card_selmerGroup_empty_le [NeZero n] [IsMulFG Rˣ] [Subsingleton (ClassGroup R)] :
    Nat.card (selmerGroup (K := K) (S := (∅ : Set (HeightOneSpectrum R))) (n := n)) ≤
      Nat.card (Units.modPow R n) := by
  refine (card_selmerGroup_le K ∅ n Set.finite_empty).trans_eq ?_
  exact Nat.card_congr
    (QuotientGroup.congrRangePowMonoidHom (unitsEquivEmptyUnit K (R := R)).symm n).toEquiv



section Etale

variable {ι : Type*} (L : ι → Type*) [(i : ι) → Field (L i)]
  (B : (i : ι) → Type*) [(i : ι) → CommRing (B i)] [(i : ι) → IsDedekindDomain (B i)]
  [(i : ι) → Algebra (B i) (L i)] [(i : ι) → IsFractionRing (B i) (L i)]
  (S : (i : ι) → Set (HeightOneSpectrum (B i))) (n : ℕ)


noncomputable def selmerGroupPi : Subgroup ((i : ι) → Units.modPow (L i) n) :=
  Subgroup.pi Set.univ fun i ↦ selmerGroup (R := B i) (K := L i) (S := S i) (n := n)

lemma mem_selmerGroupPi_iff (x : (i : ι) → Units.modPow (L i) n) :
    x ∈ selmerGroupPi L B S n ↔
      ∀ i, x i ∈ selmerGroup (R := B i) (K := L i) (S := S i) (n := n) := by
  simp [selmerGroupPi, Subgroup.mem_pi]


theorem finite_selmerGroupPi [Finite ι] [(i : ι) → Finite (ClassGroup (B i))]
    [(i : ι) → IsMulFG (B i)ˣ] (hS : ∀ i, (S i).Finite) [NeZero n] :
    Finite (selmerGroupPi L B S n) := by
  have (i : ι) : Finite (selmerGroup (R := B i) (K := L i) (S := S i) (n := n)) :=
    finite_selmerGroup (B i) (L i) (S i) n (hS i)
  exact .of_injective (fun x i ↦ (⟨x.1 i, (mem_selmerGroupPi_iff L B S n x.1).mp x.2 i⟩ :
    selmerGroup (R := B i) (K := L i) (S := S i) (n := n)))
    fun x y hxy ↦ Subtype.ext <| funext fun i ↦ congrArg Subtype.val (congrFun hxy i)

variable {A : Type*} [CommRing A]


noncomputable def selmerGroupOfEquiv
    (e : Units.modPow A n ≃* ((i : ι) → Units.modPow (L i) n)) :
    Subgroup (Units.modPow A n) :=
  (selmerGroupPi L B S n).comap e.toMonoidHom

lemma mem_selmerGroupOfEquiv_iff (e : Units.modPow A n ≃* ((i : ι) → Units.modPow (L i) n))
    (x : Units.modPow A n) :
    x ∈ selmerGroupOfEquiv L B S n e ↔
      ∀ i, e x i ∈ selmerGroup (R := B i) (K := L i) (S := S i) (n := n) := by
  simp [selmerGroupOfEquiv, selmerGroupPi, Subgroup.mem_pi]


theorem finite_selmerGroupOfEquiv [Finite ι] [(i : ι) → Finite (ClassGroup (B i))]
    [(i : ι) → IsMulFG (B i)ˣ] (hS : ∀ i, (S i).Finite) [NeZero n]
    (e : Units.modPow A n ≃* ((i : ι) → Units.modPow (L i) n)) :
    Finite (selmerGroupOfEquiv L B S n e) := by
  have := finite_selmerGroupPi L B S n hS
  exact .of_injective (fun x ↦ (⟨e x.1, x.2⟩ : selmerGroupPi L B S n))
    fun x y hxy ↦ Subtype.ext <| e.injective <| congrArg Subtype.val hxy

end Etale



section NumberField

open NumberField

variable (F : Type*) [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F))) (n : ℕ)


theorem finite_selmerGroup_of_numberField [NeZero n] (hS : S.Finite) :
    Finite (selmerGroup (K := F) (S := S) (n := n)) :=
  finite_selmerGroup (𝓞 F) F S n hS

open Module in

theorem finrank_sUnit_of_numberField (hS : S.Finite) :
    finrank ℤ (Additive (S.unit F)) = NumberField.Units.rank F + S.ncard := by
  rw [finrank_sUnit F S hS, NumberField.Units.finrank_eq]

end NumberField

end IsDedekindDomain

end
end M3
section M4



section



namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)



lemma variableChange_negY (x y : F) :
    W.toAffine.negY ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) ^ 3 * (C • W).toAffine.negY x y + (C.u : F) ^ 2 * C.s * x + C.t := by
  simp [negY, variableChange_a₁, variableChange_a₃]
  field


lemma variableChange_negY_ne {x₁ x₂ y₁ y₂ : F}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    ¬((C.u : F) ^ 2 * x₁ + C.r = (C.u : F) ^ 2 * x₂ + C.r ∧
      (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t = W.toAffine.negY
        ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  intro ⟨hX, hY⟩
  have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
  subst hx
  rw [variableChange_negY] at hY
  exact hxy ⟨rfl, mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY)⟩

lemma variableChange_addX (x₁ x₂ ℓ : F) :
    W.toAffine.addX ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  simp [addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_negAddY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.negAddY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.negAddY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp [negAddY, addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_addY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.addY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [addY, variableChange_negAddY, variableChange_addX, variableChange_negY]

lemma variableChange_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : (C • W).toAffine.Equation x₁ y₁) (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rcases eq_or_ne x₁ x₂ with rfl | hx
  · have hy : y₁ ≠ (C • W).toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    obtain rfl := Y_eq_of_Y_ne h₁ h₂ rfl hy
    have hΦy : (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t
        ≠ W.toAffine.negY ((C.u : F) ^ 2 * x₁ + C.r)
            ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) := by
      rw [variableChange_negY]
      exact fun h ↦ hy (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination h))
    rw [W.toAffine.slope_of_Y_ne rfl hΦy, (C • W).toAffine.slope_of_Y_ne rfl hy,
      ← mul_div_assoc, div_add' _ _ _ (sub_ne_zero.mpr hy),
      div_eq_div_iff (sub_ne_zero.mpr hΦy) (sub_ne_zero.mpr hy)]
    simp [negY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]
    field
  · have hΦx : (C.u : F) ^ 2 * x₁ + C.r ≠ (C.u : F) ^ 2 * x₂ + C.r := by
      simpa [mul_right_inj' (pow_ne_zero 2 hu)] using hx
    rw [W.toAffine.slope_of_X_ne hΦx, (C • W).toAffine.slope_of_X_ne hx]
    have h1 := sub_ne_zero.mpr hΦx
    have h2 := sub_ne_zero.mpr hx
    field


lemma variableChange_equation (x y : F) :
    W.toAffine.Equation ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Equation x y := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [equation_iff', variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val, field]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> linear_combination h



namespace Point

variable [W.IsElliptic]


def mapVariableChangeFun : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .some ((C.u : F) ^ 2 * x + C.r)
      ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      (equation_iff_nonsingular.mp
        ((variableChange_equation W C x y).mpr (equation_iff_nonsingular.mpr h)))

@[simp] lemma mapVariableChangeFun_zero : mapVariableChangeFun W C 0 = 0 := rfl

lemma mapVariableChangeFun_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    mapVariableChangeFun W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          (equation_iff_nonsingular.mp
            ((variableChange_equation W C x y).mpr (equation_iff_nonsingular.mpr h))) := rfl

lemma some_eq_some (W : WeierstrassCurve F) {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂} :
    (some x₁ y₁ h₁ : W.toAffine.Point) = some x₂ y₂ h₂ := by
  subst hx hy; rfl

lemma mapVariableChangeFun_injective :
    Function.Injective (mapVariableChangeFun W C) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · simp [mapVariableChangeFun] at h
  · simp [mapVariableChangeFun] at h
  · rw [mapVariableChangeFun_some, mapVariableChangeFun_some] at h
    injection h with hX hY
    have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
    exact some_eq_some (C • W) hx
      (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY - (C.u : F) ^ 2 * C.s * hx))

variable [DecidableEq F]


def equivOfEq {V V' : WeierstrassCurve F} (h : V = V') :
    V.toAffine.Point ≃+ V'.toAffine.Point := by
  subst h; exact AddEquiv.refl _

@[simp] lemma equivOfEq_some {V V' : WeierstrassCurve F} (h : V = V') {x y : F}
    (hns : V.toAffine.Nonsingular x y) :
    equivOfEq h (some x y hns) = some x y (h ▸ hns) := by
  subst h; rfl


def mapVariableChange : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := mapVariableChangeFun W C
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    simp only [mapVariableChangeFun_some]
    have e₁ : (C • W).toAffine.Equation x₁ y₁ := equation_iff_nonsingular.mpr h₁
    have e₂ : (C • W).toAffine.Equation x₂ y₂ := equation_iff_nonsingular.mpr h₂
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2, mapVariableChangeFun_zero]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, mapVariableChangeFun_some, add_some (variableChange_negY_ne W C hxy)]
      simp only [variableChange_slope W C e₁ e₂ hxy, variableChange_addX, variableChange_addY]


def equivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  have hright : ∀ P, mapVariableChangeFun W C
      (mapVariableChangeFun (C • W) C⁻¹ (equivOfEq (inv_smul_smul C W).symm P)) = P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨X, Y, h⟩)
    · simp [← zero_def]
    · rw [equivOfEq_some, mapVariableChangeFun_some, mapVariableChangeFun_some]
      refine some_eq_some W ?_ ?_ <;>
        (simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]; field)
  { toFun := mapVariableChangeFun W C
    invFun := fun P ↦ mapVariableChangeFun (C • W) C⁻¹ (equivOfEq (inv_smul_smul C W).symm P)
    left_inv := Function.RightInverse.leftInverse_of_injective hright
      (mapVariableChangeFun_injective W C)
    right_inv := hright
    map_add' := (mapVariableChange W C).map_add' }

lemma equivVariableChange_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    equivVariableChange W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          (equation_iff_nonsingular.mp
            ((variableChange_equation W C x y).mpr (equation_iff_nonsingular.mpr h))) := rfl

end Point

end WeierstrassCurve.Affine

end
end M4
section M5



section





section CommRing

variable {R : Type*} [CommRing R]


lemma sq_add_add_eq_mul_mul_of_mul_mul_eq_zero {a b c : R} (h : a * b * c = 0) :
    (a * b + a * c + b * c) ^ 2 = (b * c - a) * (a * c - b) * (a * b - c) := by
  linear_combination (a ^ 2 - a * b * c + 2 * a + b ^ 2 + 2 * b + c ^ 2 + 2 * c + 1) * h


lemma sq_add_mul_eq_mul_mul_of_mul_eq_zero {a b c d e : R} (had : a * d = 0)
    (h : b * c = d - e ^ 2 * a) : (d + e * a) ^ 2 = (d - a) * b * c := by
  grobner

end CommRing

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K)



open Polynomial


noncomputable abbrev f : K[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

lemma natDegree_f : W.f.natDegree = 3 := by
  simp only [f]
  compute_degree!

lemma monic_f : W.f.Monic := by
  simp only [f]
  monicity!

lemma f_ne_zero : W.f ≠ 0 := W.monic_f.ne_zero

lemma degree_f : W.f.degree = 3 := by
  rw [degree_eq_natDegree W.f_ne_zero, natDegree_f]; rfl


lemma discr_f : W.f.discr = W.a₂ ^ 2 * W.a₄ ^ 2 - 4 * W.a₄ ^ 3 - 4 * W.a₂ ^ 3 * W.a₆
    - 27 * W.a₆ ^ 2 + 18 * W.a₂ * W.a₄ * W.a₆ := by
  rw [Polynomial.discr_of_degree_eq_three W.degree_f]
  simp only [f, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num


lemma Δ_eq_discr_f [W.IsCharNeTwoNF] : W.Δ = 16 * W.f.discr := by
  rw [Δ_of_isCharNeTwoNF W, W.discr_f]; ring

lemma discr_f_ne_zero [W.IsElliptic] [W.IsCharNeTwoNF] : W.f.discr ≠ 0 := fun h ↦
  W.isUnit_Δ.ne_zero (by rw [W.Δ_eq_discr_f, h, mul_zero])


protected lemma two_ne_zero [W.IsElliptic] [W.IsCharNeTwoNF] : (2 : K) ≠ 0 := fun h2 ↦
  W.isUnit_Δ.ne_zero <| by rw [Δ_eq_discr_f]; grind [W.discr_f_ne_zero]

lemma derivative_f : derivative W.f = C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄ := by
  simp [f, C_ofNat]
  ring


lemma natDegree_derivative_f (h3 : (3 : K) ≠ 0) : (derivative W.f).natDegree = 2 :=
  W.derivative_f ▸ natDegree_quadratic h3


lemma aeval_f_mul_add_aeval_derivative_f_mul_eq_discr {A : Type*} [CommRing A] [Algebra K A]
    (t : A) :
    aeval t W.f * ((18 * algebraMap K A W.a₄ - 6 * algebraMap K A W.a₂ ^ 2) * t
        + (15 * algebraMap K A W.a₂ * algebraMap K A W.a₄ - 4 * algebraMap K A W.a₂ ^ 3
          - 27 * algebraMap K A W.a₆))
      + aeval t (derivative W.f) * ((2 * algebraMap K A W.a₂ ^ 2 - 6 * algebraMap K A W.a₄) * t ^ 2
        + (2 * algebraMap K A W.a₂ ^ 3 - 7 * algebraMap K A W.a₂ * algebraMap K A W.a₄
          + 9 * algebraMap K A W.a₆) * t
        + (algebraMap K A W.a₂ ^ 2 * algebraMap K A W.a₄ - 4 * algebraMap K A W.a₄ ^ 2
          + 3 * algebraMap K A W.a₂ * algebraMap K A W.a₆)) = algebraMap K A W.f.discr := by
  rw [derivative_f, discr_f]
  simp only [f, map_add, map_mul, map_pow, map_sub, map_ofNat, aeval_C, aeval_X]
  ring

lemma separable_f [W.IsElliptic] [W.IsCharNeTwoNF] : W.f.Separable := by
  have h := W.aeval_f_mul_add_aeval_derivative_f_mul_eq_discr (X : K[X])
  simp only [aeval_X_left, AlgHom.id_apply, algebraMap_eq] at h
  obtain ⟨d, c, h⟩ : ∃ d c : K[X], W.f * d + derivative W.f * c = C W.f.discr := ⟨_, _, h⟩
  refine ⟨C W.f.discr⁻¹ * d, C W.f.discr⁻¹ * c, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, mul_comm d, mul_comm c, h, ← C_mul,
    inv_mul_cancel₀ W.discr_f_ne_zero, C_1]

lemma squarefree_f [W.IsElliptic] [W.IsCharNeTwoNF] : Squarefree W.f :=
  (separable_f W).squarefree

lemma eval_f (x : K) : W.f.eval x = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by simp [f]

lemma map_eval_f {L : Type*} [CommRing L] [Algebra K L] (x : K) :
    algebraMap K L (W.f.eval x) = algebraMap K L x ^ 3 +
      algebraMap K L W.a₂ * algebraMap K L x ^ 2 +
      algebraMap K L W.a₄ * algebraMap K L x + algebraMap K L W.a₆ := by
  simp [f]

lemma equation_iff_eval_f_eq_sq [W.IsCharNeTwoNF] (x y : K) :
    W.Equation x y ↔ W.f.eval x = y ^ 2 := by
  rw [equation_iff x y, eq_comm]
  simp [f]

@[simp]
lemma negY_of_isCharNeTwoNF [W.IsCharNeTwoNF] (x y : K) : W.negY x y = -y := by
  rw [negY, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]
  ring


lemma slope_self_of_isCharNeTwoNF [DecidableEq K] [W.IsCharNeTwoNF] {x y : K}
    (hy : y ≠ W.negY x y) :
    W.slope x x y y = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) / (2 * y) := by
  rw [slope_of_Y_ne rfl hy, negY_of_isCharNeTwoNF, a₁_of_isCharNeTwoNF, zero_mul, sub_zero,
    sub_neg_eq_add, ← two_mul]


lemma ne_zero_of_eval_f_ne_zero [W.IsCharNeTwoNF] {x y : K} (h : W.Equation x y)
    (hx : W.f.eval x ≠ 0) : y ≠ 0 :=
  fun h0 ↦ hx <| by simp [(equation_iff_eval_f_eq_sq W x y).mp h, h0]


noncomputable abbrev fCofactor (x : K) : K[X] :=
  X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)

lemma natDegree_fCofactor (x : K) : (W.fCofactor x).natDegree = 2 := by
  simp only [fCofactor]
  compute_degree!

lemma monic_fCofactor (x : K) : (W.fCofactor x).Monic := by
  simp only [fCofactor]
  monicity!

lemma eval_fCofactor_self (x : K) :
    (W.fCofactor x).eval x = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
  simp [fCofactor]
  ring

lemma fCofactor_mul_eq (x : K) : W.fCofactor x * (X - C x) = W.f - C (W.f.eval x) := by
  simp [fCofactor, f]
  algebra


lemma C_sub_X_mul_eq_C_sub_fCofactor (x : K) :
    (C x - X) * (X + C (2 * x + W.a₂)) = C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) - W.fCofactor x := by
  simp only [fCofactor, C_eq_algebraMap]
  algebra

lemma f_eq_mul_of_eval_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.f = W.fCofactor x * (X - C x) := by
  simp [fCofactor_mul_eq, hx]

lemma discr_fCofactor (x : K) :
    (W.fCofactor x).discr = (x + W.a₂) ^ 2 - 4 * (x ^ 2 + W.a₂ * x + W.a₄) := by
  have hdeg : (W.fCofactor x).degree = 2 := by
    rw [degree_eq_natDegree (W.monic_fCofactor x).ne_zero, W.natDegree_fCofactor x]; rfl
  rw [discr_of_degree_eq_two hdeg]
  simp only [fCofactor, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num


lemma discr_f_eq_discr_fCofactor_mul_sq {x : K} (hx : W.f.eval x = 0) :
    W.f.discr = (W.fCofactor x).discr * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 := by
  conv_lhs => rw [W.f_eq_mul_of_eval_eq_zero hx, mul_comm]
  rw [discr_X_sub_C_mul (W.monic_fCofactor x) (by rw [W.natDegree_fCofactor]; norm_num) x,
    W.eval_fCofactor_self x]


private lemma f_dvd_of_fCofactor_dvd {x r s : K} (hx : W.f.eval x = 0) (hr : r ≠ 0)
    (hdvd : W.fCofactor x ∣ (C r * X + C s) ^ 2 - (C x - X)) :
    W.f ∣ (X - C (-s / r)) ^ 2 * (X - C x) - -(C (1 / r) * X + C (-x / r)) ^ 2 := by
  obtain ⟨q, hq⟩ := hdvd
  have hu : C r * C r⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ hr, C_1]
  refine ⟨C (r⁻¹ ^ 2) * q, ?_⟩
  rw [W.f_eq_mul_of_eval_eq_zero hx]
  simp only [div_eq_mul_inv, map_mul, map_neg, one_mul, map_pow]
  grobner


private lemma mk_sq_ne_mk_C_sub_X {g : K[X]} (hg : g.Monic) (hg2 : 2 ≤ g.natDegree) {q : K[X]}
    (hq : 2 * q.natDegree < g.natDegree) (x : K) :
    AdjoinRoot.mk g q ^ 2 ≠ AdjoinRoot.mk g (C x - X) := by
  have hx : (C x - X).natDegree = 1 := by compute_degree!
  rw [← map_pow, Ne, AdjoinRoot.mk_eq_mk_iff_of_degree_lt hg
    (degree_lt_degree (natDegree_pow_le.trans_lt hq)) (degree_lt_degree (by lia))]
  intro h
  have := congrArg natDegree h
  rw [natDegree_pow, hx] at this
  lia

lemma fCofactor_eq_of_f_eq {xP xQ xR : K} (hf : W.f = (X - C xP) * (X - C xQ) * (X - C xR)) :
    W.fCofactor xP = (X - C xQ) * (X - C xR) ∧ W.fCofactor xQ = (X - C xP) * (X - C xR) ∧
      W.fCofactor xR = (X - C xP) * (X - C xQ) := by
  have key {u v w : K} (h : W.f = (X - C u) * ((X - C v) * (X - C w))) :
      W.fCofactor u = (X - C v) * (X - C w) := by
    have h₀ : W.f.eval u = 0 := by rw [h]; simp
    refine mul_left_cancel₀ (X_sub_C_ne_zero u) ?_
    rw [← h, W.f_eq_mul_of_eval_eq_zero h₀, mul_comm]
  exact ⟨key <| by rw [hf]; ring, key <| by rw [hf]; ring, key <| by rw [hf]; ring⟩


lemma deriv_f_ne_zero [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) :
    3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ≠ 0 := by
  have h := W.aeval_f_mul_add_aeval_derivative_f_mul_eq_discr x
  simp only [coe_aeval_eq_eval, Algebra.algebraMap_self, RingHom.id_apply, hx, zero_mul, zero_add,
    derivative_f, eval_add, eval_mul, eval_C, eval_X, eval_pow] at h
  exact left_ne_zero_of_mul (h ▸ W.discr_f_ne_zero)


abbrev A : Type _ := AdjoinRoot W.f

lemma finrank_A : Module.finrank K W.A = 3 := by
  rw [(AdjoinRoot.powerBasis W.f_ne_zero).finrank, AdjoinRoot.powerBasis_dim, natDegree_f]

lemma exists_mk_eq (a : W.A) :
    ∃ r s t, a = AdjoinRoot.mk W.f (C r * X ^ 2 + C s * X + C t) := by
  obtain ⟨p, hp, rfl⟩ := AdjoinRoot.exists_degree_lt_mk_eq W.monic_f a
  rw [degree_eq_natDegree W.monic_f.ne_zero, natDegree_f] at hp
  exact ⟨_, _, _, congrArg (AdjoinRoot.mk W.f) <|
    eq_quadratic_of_degree_le_two <| Order.lt_succ_iff.mp hp⟩

lemma exists_X_sub_C_mul_eq (r s t : K) (hr : r ≠ 0) :
    ∃ ξ l m, AdjoinRoot.mk W.f (X - C ξ) * AdjoinRoot.mk W.f (C r * X ^ 2 + C s * X + C t) =
       AdjoinRoot.mk W.f (C l * X + C m) := by
  have hu : C r * C r⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ hr, C_1]
  refine ⟨s / r - W.a₂, t - W.a₄ * r - s ^ 2 / r + W.a₂ * s,
    -W.a₆ * r - t * s / r + W.a₂ * t, ?_⟩
  rw [← map_mul, ← sub_eq_zero, ← map_sub, AdjoinRoot.mk_eq_zero]
  refine ⟨C r, ?_⟩
  simp only [f, div_eq_mul_inv, map_sub, map_add, map_mul, map_pow, map_neg]
  grobner


abbrev A' (x : K) : Type _ := AdjoinRoot (W.fCofactor x)

lemma exists_mk_eq' {x : K} (a : W.A' x) :
    ∃ r s, a = AdjoinRoot.mk (W.fCofactor x) (C r * X + C s) := by
  obtain ⟨p, hp, rfl⟩ := AdjoinRoot.exists_degree_lt_mk_eq (W.monic_fCofactor x) a
  rw [degree_eq_natDegree (W.monic_fCofactor x).ne_zero, natDegree_fCofactor] at hp
  exact ⟨_, _, congrArg (AdjoinRoot.mk (W.fCofactor x)) <|
    eq_X_add_C_of_natDegree_le_one <| natDegree_le_of_degree_le <| Order.lt_succ_iff.mp hp⟩


noncomputable def equivProdA' [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) :
    W.A ≃+* K × W.A' x :=
  let eA : W.A ≃+* K[X] ⧸ (Ideal.span {X - C x} * Ideal.span {W.fCofactor x}) :=
    Ideal.quotEquivOfEq <| by
      rw [Ideal.span_singleton_mul_span_singleton, mul_comm, ← W.f_eq_mul_of_eval_eq_zero hx]
  have H : IsCoprime (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr <|
      (W.f_eq_mul_of_eval_eq_zero hx ▸ separable_f W).isCoprime.symm
  eA.trans <|
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x})
      H).trans <|
    RingEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv x |>.toRingEquiv) (RingEquiv.refl _)

lemma equivProdA'_apply [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) (p : K[X]) :
    W.equivProdA' hx (AdjoinRoot.mk W.f p) = (p.eval x, AdjoinRoot.mk (W.fCofactor x) p) :=
  rfl

lemma mk_eq_mk_iff [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) {p q : K[X]} :
    AdjoinRoot.mk W.f p = AdjoinRoot.mk W.f q ↔
      p.eval x = q.eval x ∧ AdjoinRoot.mk (W.fCofactor x) p = AdjoinRoot.mk (W.fCofactor x) q := by
  rw [← EquivLike.apply_eq_iff_eq <| W.equivProdA' hx]
  simpa only [equivProdA'_apply] using Prod.mk_inj

lemma isUnit_mk_iff [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) {p : K[X]} :
    IsUnit (AdjoinRoot.mk W.f p) ↔
      IsUnit (p.eval x) ∧ IsUnit (AdjoinRoot.mk (W.fCofactor x) p) := by
  let e := W.equivProdA' hx
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · have : IsUnit (e _) := e.toRingHom.isUnit_map H
    rwa [W.equivProdA'_apply hx, Prod.isUnit_iff] at this
  · have : IsUnit (eval x p, AdjoinRoot.mk (W.fCofactor x) p) := by rwa [Prod.isUnit_iff]
    have : IsUnit (e.symm _) := e.symm.toRingHom.isUnit_map this
    convert this
    rw [RingEquiv.eq_symm_apply, W.equivProdA'_apply hx]

variable {W}

lemma isUnit_mk_sub_X_of_eval_f_ne_zero {x : K} (h : W.f.eval x ≠ 0) :
    IsUnit <| AdjoinRoot.mk W.f (C x - X) := by
  refine .of_mul_eq_one (AdjoinRoot.mk W.f (C (W.f.eval x)⁻¹ * W.fCofactor x)) ?_
  rw [← map_mul, mul_left_comm,
    show (1 : W.A) = AdjoinRoot.mk W.f (1 - C (eval x W.f)⁻¹ * W.f) by simp]
  congr 1
  have h1 : (C x - X) * W.fCofactor x = C (W.f.eval x) - W.f := by
    linear_combination -W.fCofactor_mul_eq x
  rw [h1, mul_sub, ← C_mul, inv_mul_cancel₀ h, map_one]

section

variable [W.IsCharNeTwoNF]

lemma y_eq_zero_of_eval_f_eq_zero {x y : K} (h : W.Equation x y) (hf : W.f.eval x = 0) :
    y = 0 := by
  rwa [equation_iff_eval_f_eq_sq, hf, eq_comm, sq_eq_zero_iff] at h

variable [W.IsElliptic]

lemma isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero {x : K} (h : W.f.eval x = 0) :
    IsUnit <| AdjoinRoot.mk W.f <| C x - X + W.fCofactor x := by
  have H : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ≠ 0 := deriv_f_ne_zero W h
  rw [isUnit_mk_iff W h, map_add, AdjoinRoot.mk_self, add_zero]
  refine ⟨?_, .of_mul_eq_one (AdjoinRoot.mk _
    (C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (X + C (2 * x + W.a₂)))) ?_⟩
  · simpa [isUnit_iff_ne_zero, W.eval_fCofactor_self] using H
  · rw [← map_mul, mul_left_comm, W.C_sub_X_mul_eq_C_sub_fCofactor, mul_sub, ← C_mul]
    simp [inv_mul_cancel₀ H]


lemma nonsingular_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.Nonsingular x 0 :=
  (equation_iff_nonsingular_of_Δ_ne_zero W.isUnit_Δ.ne_zero).mp
    (by rw [equation_iff_eval_f_eq_sq, hx]; ring)

end




abbrev M : Type _ := Units.modPow W.A 2

lemma M.sq_eq_one (m : W.M) : m ^ 2 = 1 := Units.modPow.pow_eq_one m

lemma M.mul_self (m : W.M) : m * m = 1 := by rw [← sq, sq_eq_one]

@[simp] lemma M.inv_eq_self (m : W.M) : m⁻¹ = m := inv_eq_of_mul_eq_one_right (M.mul_self m)

variable [DecidableEq K] [W.IsCharNeTwoNF]

section μ₀

variable [W.IsElliptic]


noncomputable def μX (x : K) : W.M :=
  if hx : W.f.eval x = 0
    then (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit
    else (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit

@[simp] lemma μX_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.μX x = (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit := by
  simp only [μX, dif_pos hx]

@[simp] lemma μX_of_eval_f_ne_zero {x : K} (hx : W.f.eval x ≠ 0) :
    W.μX x = (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit := by
  simp only [μX, dif_neg hx]


noncomputable def μ₀ : W.Point → W.M
  | 0 => 1
  | .some x _ _ => W.μX x

@[simp] lemma μ₀_zero : W.μ₀ 0 = 1 := rfl

@[simp] lemma μ₀_some {x y : K} (h : W.Nonsingular x y) : W.μ₀ (.some x y h) = W.μX x := rfl

end μ₀




lemma Point.exists_eq_f_sub_sq_of_add_add_eq_zero {xP yP xQ yQ xR yR : K}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) :
    ∃ pol, (X - C xP) * (X - C xQ) * (X - C xR) = W.f - pol ^ 2 ∧ pol.natDegree ≤ 1 := by
  refine ⟨linePolynomial xP yP <| W.slope xP xQ yP yQ, ?_, ?_⟩
  · have hgeneric : ¬(xP = xQ ∧ yP = W.negY xQ yQ) := by
      by_contra H
      simp [add_of_Y_eq H.1 H.2] at hPQR
    have := addPolynomial_slope hP.1 hQ.1 hgeneric |>.symm
    rw [neg_eq_iff_eq_neg] at this
    convert this using 1
    · congr
      rw [add_eq_zero_iff_eq_neg, neg_some, add_some hgeneric] at hPQR
      grind
    · simp [addPolynomial, polynomial]
  · simp only [linePolynomial, natDegree_add_C]
    compute_degree

open Point in
private lemma xQ_ne_xP_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h : W.f.eval xP = 0) :
    xQ ≠ xP := by
  contrapose! hPQR
  rw! [hPQR] at hQ ⊢
  rw! [y_eq_zero_of_eval_f_eq_zero hP.1 h, y_eq_zero_of_eval_f_eq_zero hQ.1 h]
  rw [add_self_of_Y_eq <| by simp, zero_add]
  exact some_ne_zero hR

open Point in

private lemma f_eq_prod_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.f = (X - C xP) * (X - C xQ) * (X - C xR) := by
  have hPQ : xQ ≠ xP := xQ_ne_xP_of_eval_f_eq_zero hP hQ hR hPQR h₁
  obtain ⟨pol, hpol, hpol₁⟩ := Point.exists_eq_f_sub_sq_of_add_add_eq_zero hP hQ hR hPQR
  have hpol₀ : pol = 0 := by
    refine pol.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {xP, xQ} (fun x hx ↦ ?_) ?_
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      apply_fun (·.eval x) at hpol
      rcases hx with rfl | rfl <;>
        rw [eval_sub, ‹eval x (f W) = 0›] at hpol <;>
        simpa using hpol
    · grind
  rwa [hpol₀, zero_pow two_ne_zero, sub_zero, eq_comm] at hpol


private lemma exists_pol_of_eq_two_smul {x y : K} (h : W.Nonsingular x y) {P : W.Point}
    (hP : Point.some x y h = 2 • P) :
    ∃ ξ l m, (X - C ξ) ^ 2 * (X - C x) = W.f - (C l * X + C m) ^ 2 := by
  match P with
  | 0 => simp at hP 
  | .some ξ η h' =>
    rw [← sub_eq_zero, sub_eq_add_neg, two_smul, neg_add, ← add_assoc, add_rotate,
      Point.neg_some] at hP
    have H : W.Nonsingular ξ (W.negY ξ η) := (nonsingular_neg ξ η).mpr h'
    obtain ⟨pol, hpol, hpol₁⟩ := Point.exists_eq_f_sub_sq_of_add_add_eq_zero H H h hP
    rw [← sq] at hpol
    obtain ⟨l, m, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hpol₁
    exact ⟨_, _, _, hpol⟩

variable [W.IsElliptic]

section μ₀_helper_lemmas

open Point

lemma μ₀_mul_eq_one (P : W.Point) : W.μ₀ P * W.μ₀ (-P) = 1 := by
  match P with
  | 0 => simp
  | .some x y h => rw [Point.neg_some h, μ₀_some, μ₀_some, M.mul_self]

variable {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
  (hR : W.Nonsingular xR yR) (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0)

include hPQR

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  have hf := f_eq_prod_of_eval_f_eq_zero hP hQ hR hPQR h₁ h₂
  have h₃ : W.f.eval xR = 0 := by rw [hf]; simp
  obtain ⟨hfcP, hfcQ, hfcR⟩ := W.fCofactor_eq_of_f_eq hf
  rw [μX_of_eval_f_eq_zero h₁, μX_of_eval_f_eq_zero h₂, μX_of_eval_f_eq_zero h₃,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  simp only [hfcP, hfcQ, hfcR,
    show ∀ (a b c : K), C a - X + (X - C b) * (X - C c) =
      (X - C b) * (X - C c) - (X - C a) by intro a b c; ring]
  rw [map_sub, map_sub _ _ (X - C xQ), map_sub _ _ (X - C xR)]
  simp only [map_mul]
  rw [← sq_add_add_eq_mul_mul_of_mul_mul_eq_zero <| by rw [← map_mul, ← map_mul, ← hf]; simp]
  exact ⟨_, rfl⟩


private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne (h : W.f.eval xP = 0)
    (hQ₀ : W.f.eval xQ ≠ 0) (hR₀ : W.f.eval xR ≠ 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rw [μX_of_eval_f_eq_zero h, μX_of_eval_f_ne_zero hQ₀, μX_of_eval_f_ne_zero hR₀,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ := Point.exists_eq_f_sub_sq_of_add_add_eq_zero hP hQ hR hPQR
  obtain ⟨γ, rfl⟩ : ∃ γ, pol = C γ * (X - C xP) := by
    apply_fun (·.eval xP) at hpol
    rw [eval_sub, h] at hpol
    exact exists_eq_C_mul_X_sub_C_of_natDegree_le_one hpol₁ (by simpa using hpol)
  rw [W.f_eq_mul_of_eval_eq_zero h, mul_assoc, mul_comm (W.fCofactor _),
    show (C γ * (X - C xP)) ^ 2 = (X - C xP) * (C γ ^ 2 * (X - C xP)) by ring, ← mul_sub] at hpol
  replace hpol := mul_left_cancel₀ (X_sub_C_ne_zero xP) hpol
  simp only [← map_mul]
  rw [show (C xP - X + fCofactor W xP) * (C xQ - X) * (C xR - X) =
    (fCofactor W xP - (X - C xP)) * (X - C xQ) * (X - C xR) by ring, map_mul, map_mul, map_sub]
  rw [← sq_add_mul_eq_mul_mul_of_mul_eq_zero (e := AdjoinRoot.mk W.f (C γ)) ?H₁ ?H₂]
  case H₁ =>
    rw [← map_mul, mul_comm, ← f_eq_mul_of_eval_eq_zero W h]
    simp
  case H₂ => simp only [← map_mul, ← map_pow, ← map_sub, hpol]
  exact ⟨_, rfl⟩

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero (h : W.f.eval xP = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  by_cases hQ₀ : W.f.eval xQ = 0
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hQ hR hPQR h hQ₀
  by_cases hR₀ : W.f.eval xR = 0
  · rw [mul_right_comm]
    rw [add_right_comm] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hR hQ hPQR h hR₀
  exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne hP hQ hR hPQR h hQ₀ hR₀

lemma μX_mul_mul_eq_one : W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rcases eq_or_ne (W.f.eval xP) 0 with HP | HP
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero hP hQ hR hPQR HP
  rcases eq_or_ne (W.f.eval xQ) 0 with HQ | HQ
  · rw [mul_comm (W.μX xP)]
    rw [add_comm (Point.some xP ..)] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hQ hP hR hPQR HQ
  rcases eq_or_ne (W.f.eval xR) 0 with HR | HR
  · rw [mul_comm, ← mul_assoc]
    rw [add_comm, ← add_assoc] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hR hP hQ hPQR HR
  rw [μX_of_eval_f_ne_zero HP, μX_of_eval_f_ne_zero HQ, μX_of_eval_f_ne_zero HR,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ := Point.exists_eq_f_sub_sq_of_add_add_eq_zero hP hQ hR hPQR
  simp only [← map_mul, hpol, neg_sub,
    show (C xP - X) * (C xQ - X) * (C xR - X) = -((X - C xP) * (X - C xQ) * (X - C xR))
      by algebra]
  simp

end μ₀_helper_lemmas

lemma μ₀_mul_mul_eq_one_of_add_add_eq_zero {P Q R : W.Point} (hPQR : P + Q + R = 0) :
    μ₀ P * μ₀ Q * μ₀ R = 1 := by
  match P, Q, R with
  | 0, _, _ =>
    rw [zero_add, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, one_mul, hPQR, μ₀_mul_eq_one]
  | .some .., 0, _
  | .some .., .some .., 0 =>
    rw [add_zero, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, mul_one, hPQR, μ₀_mul_eq_one]
  | .some xP yP hP, .some xQ yQ hQ, .some xR yR hR =>
    simp only [μ₀_some]
    exact μX_mul_mul_eq_one hP hQ hR hPQR


noncomputable def μ : Multiplicative W.Point →* W.M :=
  .ofMapMulMulEqOne (f := μ₀ ∘ Multiplicative.toAdd) (by simp) fun P' Q' R' ↦ by
    simp_rw [← toAdd_eq_zero, toAdd_mul, Function.comp_apply]
    exact μ₀_mul_mul_eq_one_of_add_add_eq_zero

@[simp]
lemma μ_apply (P : W.Point) : μ (.ofAdd P) = μ₀ P := rfl

@[simp]
lemma μ₀_two_nsmul (P : W.Point) : W.μ₀ (2 • P) = 1 := by
  rw [← μ_apply, ofAdd_nsmul, map_pow, M.sq_eq_one]




private lemma exists_eq_two_smul_of_identities {x y ξ l m : K} (h : W.Nonsingular x y)
    (H₂ : x + 2 * ξ = l ^ 2 - W.a₂) (H₁ : 2 * x * ξ + ξ ^ 2 = W.a₄ - 2 * l * m)
    (H₀ : x * ξ ^ 2 = -W.a₆ + m ^ 2) :
    ∃ P, Point.some x y h = 2 • P := by
  
  have hy₀ : l * ξ + m ≠ 0 := fun h0 ↦ W.deriv_f_ne_zero (x := ξ)
    (by rw [eval_f]; linear_combination ξ ^ 2 * H₂ - ξ * H₁ + H₀ + (l * ξ + m) * h0)
    (by linear_combination 2 * ξ * H₂ - H₁ + 2 * l * h0)
  have h2y : 2 * (l * ξ + m) ≠ 0 := mul_ne_zero W.two_ne_zero hy₀
  have hy : l * ξ + m ≠ W.negY ξ (l * ξ + m) :=
    sub_ne_zero.mp <| by rwa [negY_of_isCharNeTwoNF, sub_neg_eq_add, ← two_mul]
  have hsl : W.slope ξ ξ (l * ξ + m) (l * ξ + m) = l := by
    rw [W.slope_self_of_isCharNeTwoNF hy, div_eq_iff h2y]
    linear_combination 2 * ξ * H₂ - H₁
  let P : W.Point := .some ξ (l * ξ + m) <| equation_iff_nonsingular.mp <| by
    rw [equation_iff_eval_f_eq_sq, eval_f]; linear_combination ξ ^ 2 * H₂ - ξ * H₁ + H₀
  suffices .some x y h = 2 • P ∨ .some x y h = 2 • (-P) from this.casesOn (⟨_, ·⟩) (⟨_, ·⟩)
  simp only [smul_neg, P, two_smul, Point.add_self_of_Y_ne hy, ← Point.X_eq_iff, hsl, addX,
    a₁_of_isCharNeTwoNF, zero_mul, add_zero]
  linear_combination H₂


lemma exists_eq_two_smul_iff {x y : K} (h : W.Nonsingular x y) :
    (∃ P, Point.some x y h = 2 • P) ↔
      ∃ ξ l m, (X - C ξ) ^ 2 * (X - C x) = W.f - (C l * X + C m) ^ 2 := by
  refine ⟨fun ⟨P, hP⟩ ↦ exists_pol_of_eq_two_smul h hP, fun ⟨ξ, l, m, H⟩ ↦ ?_⟩
  have H' : X ^ 3 - C (x + 2 * ξ) * X ^ 2 + C (2 * x * ξ + ξ ^ 2) * X - C (x * ξ ^ 2) =
      X ^ 3 - C (l ^ 2 - W.a₂) * X ^ 2 + C (W.a₄ - 2 * l * m) * X - C (-W.a₆ + m ^ 2) := by
    simp only [f] at H
    convert H using 1 <;> { simp only [C_eq_algebraMap]; algebra }
  replace H' n := congrArg (fun p ↦ p.coeff n) H'
  simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at H'
  exact exists_eq_two_smul_of_identities h (by simpa using congrArg (-·) (H' 2))
    (by simpa using H' 1) (by simpa using congrArg (-·) (H' 0))


lemma exists_eq_two_smul_iff' {x y : K} (h : W.Nonsingular x y) :
    (∃ P, Point.some x y h = 2 • P) ↔
      ∃ ξ l m, AdjoinRoot.mk W.f ((X - C ξ) ^ 2 * (X - C x)) =
        AdjoinRoot.mk W.f (-(C l * X + C m) ^ 2) := by
  rw [exists_eq_two_smul_iff]
  refine ⟨fun ⟨ξ, l, m, H⟩ ↦ ⟨ξ, l, m, ?_⟩, fun ⟨ξ, l, m, H⟩ ↦ ⟨ξ, l, m, ?_⟩⟩
  · rw [H, map_sub, sub_eq_add_neg, map_neg, add_eq_right]
    simp
  · rw [AdjoinRoot.mk_eq_mk, sub_neg_eq_add] at H
    have hmon : ((X - C ξ) ^ 2 * (X - C x) + (C l * X + C m) ^ 2).Monic := by monicity!
    have hf := eq_of_dvd_of_natDegree_le_of_leadingCoeff H
      (by rw [natDegree_f]; compute_degree!) (by rw [W.monic_f.leadingCoeff, hmon.leadingCoeff])
    linear_combination -hf

section kernel

variable {x y : K} (h : W.Nonsingular x y)

include h

private lemma eq_two_smul_of_μ_eq_one_of_ne (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x ≠ 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_ne_zero hx, Units.modPow.unit_eq_one_iff] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨r, s, t, rfl⟩ := W.exists_mk_eq z
  have hr : r ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_mul, zero_add] at hz
    exact mk_sq_ne_mk_C_sub_X W.monic_f (by rw [natDegree_f]; norm_num)
      (by have := natDegree_linear_le (a := s) (b := t); rw [natDegree_f]; lia) x hz
  obtain ⟨ξ, l, m, H⟩ := W.exists_X_sub_C_mul_eq r s t hr
  rw [← map_mul] at H
  refine ⟨ξ, l, m, ?_⟩
  apply_fun (fun p ↦ AdjoinRoot.mk W.f (X - C ξ) ^ 2 * p) at hz
  rw [← neg_inj, eq_comm, ← map_pow, ← map_mul, ← map_neg] at hz
  conv_rhs at hz => rw [← map_pow, ← map_mul, ← mul_pow, map_pow, H, ← map_pow, ← map_neg]
  convert hz
  ring

private lemma eq_two_smul_of_μ_eq_one_of_eq (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x = 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_eq_zero hx, Units.modPow.unit_eq_one_iff] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨r, s, hrs⟩ := W.exists_mk_eq' (AdjoinRoot.mk (W.fCofactor x) p)
  rw [← map_pow, AdjoinRoot.mk_eq_mk] at hz
  have hdvd : W.fCofactor x ∣ W.f := ⟨X - C x, W.f_eq_mul_of_eval_eq_zero hx⟩
  have hz' : AdjoinRoot.mk (W.fCofactor x) (p ^ 2) =
      AdjoinRoot.mk (W.fCofactor x) (C x - X + W.fCofactor x) :=
    AdjoinRoot.mk_eq_mk.mpr <| hdvd.trans hz
  rw [map_pow, hrs, map_add _ _ (fCofactor ..), AdjoinRoot.mk_self, add_zero] at hz'
  have hr₀ : r ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_mul, zero_add] at hz'
    exact mk_sq_ne_mk_C_sub_X (W.monic_fCofactor x) (W.natDegree_fCofactor x).ge
      (by rw [natDegree_fCofactor, natDegree_C]; norm_num) x hz'
  rw [← map_pow, AdjoinRoot.mk_eq_mk] at hz'
  exact ⟨-s / r, 1 / r, -x / r, AdjoinRoot.mk_eq_mk.mpr (W.f_dvd_of_fCofactor_dvd hx hr₀ hz')⟩

lemma eq_two_smul_of_μ_eq_one (hμ : (μ <| .ofAdd <| .some x y h) = 1) :
    ∃ P : W.Point, .some x y h = 2 • P := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · exact eq_two_smul_of_μ_eq_one_of_eq h hμ hx
  · exact eq_two_smul_of_μ_eq_one_of_ne h hμ hx

end kernel


lemma ker_μ_eq : (μ (W := W)).ker = (nsmulAddMonoidHom 2).range.toSubgroup := by
  ext P'
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P'
  rw [MonoidHom.mem_ker, μ_apply, Multiplicative.mem_toSubgroup, toAdd_ofAdd,
    AddMonoidHom.mem_range]
  simp only [nsmulAddMonoidHom_apply]
  constructor
  · match P with
    | 0 => exact fun _ ↦ ⟨0, by simp⟩
    | .some x y h => exact fun hμ ↦ (eq_two_smul_of_μ_eq_one h hμ).imp fun Q hQ ↦ hQ.symm
  · rintro ⟨Q, rfl⟩
    exact μ₀_two_nsmul Q


lemma finite_index_range_nsmulAddMonoidHom_two_iff :
    (nsmulAddMonoidHom (α := W.Point) 2).range.FiniteIndex ↔ Finite (μ (W := W)).range := by
  rw [← AddSubgroup.finiteIndex_toSubgroup_iff, ← ker_μ_eq,
    Equiv.finite_iff (QuotientGroup.quotientKerEquivRange (μ (W := W))).symm.toEquiv]
  exact Subgroup.finiteIndex_iff_finite_quotient

end WeierstrassCurve.Affine



section Cubic



open Polynomial

variable {L Γ : Type*} [CommRing L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)
  {t s a b c : L}

private lemma Valuation.map_cubic_deriv_le_one (ha : v a ≤ 1) (hb : v b ≤ 1) (ht : v t ≤ 1) :
    v (3 * t ^ 2 + 2 * a * t + b) ≤ 1 :=
  let t' : v.integer := ⟨t, ht⟩
  let a' : v.integer := ⟨a, ha⟩
  let b' : v.integer := ⟨b, hb⟩
  (3 * t' ^ 2 + 2 * a' * t' + b').prop

private lemma Valuation.map_cubic_deriv_eq_one (ha : v a ≤ 1) (hb : v b ≤ 1) (hc : v c ≤ 1)
    (ht : v t ≤ 1) {δ : L} (hδ : v δ = 1)
    (hmul : (3 * t ^ 2 + 2 * a * t + b) * ((2 * a ^ 2 - 6 * b) * t ^ 2
      + (2 * a ^ 3 - 7 * a * b + 9 * c) * t + (a ^ 2 * b - 4 * b ^ 2 + 3 * a * c)) = δ) :
    v (3 * t ^ 2 + 2 * a * t + b) = 1 :=
  let t' : v.integer := ⟨t, ht⟩
  let a' : v.integer := ⟨a, ha⟩
  let b' : v.integer := ⟨b, hb⟩
  let c' : v.integer := ⟨c, hc⟩
  v.eq_one_of_mul_eq_one (v.map_cubic_deriv_le_one ha hb ht)
    ((2 * a' ^ 2 - 6 * b') * t' ^ 2 + (2 * a' ^ 3 - 7 * a' * b' + 9 * c') * t'
      + (a' ^ 2 * b' - 4 * b' ^ 2 + 3 * a' * c')).prop (hmul ▸ hδ)

private lemma Valuation.map_cofactor_eq_one (ha : v a ≤ 1) (ht : v t ≤ 1) (hs : v s ≤ 1)
    (hlt : v (s - t) < 1) (hderiv : v (3 * t ^ 2 + 2 * a * t + b) = 1) :
    v (s ^ 2 + t * s + t ^ 2 + a * (s + t) + b) = 1 := by
  have h2t : v (s + 2 * t + a) ≤ 1 :=
    let t' : v.integer := ⟨t, ht⟩
    let a' : v.integer := ⟨a, ha⟩
    let s' : v.integer := ⟨s, hs⟩
    (s' + 2 * t' + a').prop
  have hlt' : v ((s - t) * (s + 2 * t + a)) < v (3 * t ^ 2 + 2 * a * t + b) := by
    rw [hderiv, map_mul]
    exact (mul_le_of_le_one_right' h2t).trans_lt hlt
  rw [show s ^ 2 + t * s + t ^ 2 + a * (s + t) + b
      = (s - t) * (s + 2 * t + a) + (3 * t ^ 2 + 2 * a * t + b) by ring,
    v.map_add_eq_of_lt_right hlt', hderiv]

private lemma Valuation.map_sub_eq_one_or_eq_map_sq (ha : v a ≤ 1) (ht : v t ≤ 1) {x y : L}
    (hx : v x ≤ 1) (hderiv : v (3 * t ^ 2 + 2 * a * t + b) = 1)
    (hfac : (x - t) * (x ^ 2 + t * x + t ^ 2 + a * (x + t) + b) = y ^ 2) :
    v (x - t) = 1 ∨ v (x - t) = v y ^ 2 := by
  by_cases h1 : v (x - t) = 1
  · exact .inl h1
  refine .inr ?_
  have hlt : v (x - t) < 1 := lt_of_le_of_ne ((v.map_sub x t).trans (max_le hx ht)) h1
  rw [← map_pow, ← hfac, map_mul, v.map_cofactor_eq_one ha ht hx hlt hderiv, mul_one]

variable [Nontrivial L]

private lemma cubic_coeff_le_one (ha : v a ≤ 1) (hb : v b ≤ 1) (hc : v c ≤ 1) :
    ∀ i < (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree,
      v ((X ^ 3 + C a * X ^ 2 + C b * X + C c).coeff i) ≤ 1 := by
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  intro i hi
  rw [hdeg] at hi
  interval_cases i <;> simp [ha, hb, hc]

private lemma Valuation.map_cubic_of_one_lt (ha : v a ≤ 1) (hb : v b ≤ 1) (hc : v c ≤ 1)
    (ht : 1 < v t) :
    v (t ^ 3 + a * t ^ 2 + b * t + c) = v t ^ 3 := by
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  have h := v.map_eval_eq_of_one_lt hp (cubic_coeff_le_one v ha hb hc) ht
  rw [hdeg] at h
  simpa using h

private lemma Valuation.le_one_of_root_cubic (ha : v a ≤ 1) (hb : v b ≤ 1) (hc : v c ≤ 1)
    (heq : t ^ 3 + a * t ^ 2 + b * t + c = 0) :
    v t ≤ 1 := by
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  refine v.le_one_of_root_monic hp (cubic_coeff_le_one v ha hb hc) (by rw [hdeg]; norm_num) ?_
  simpa using heq

private lemma Valuation.map_sub_add_cofactor_eq_one [NoZeroDivisors L] (ha : v a ≤ 1) (hb : v b ≤ 1)
    (hc : v c ≤ 1) (hs : s ^ 3 + a * s ^ 2 + b * s + c = 0) (ht : t ^ 3 + a * t ^ 2 + b * t + c = 0)
    (hderiv : v (3 * s ^ 2 + 2 * a * s + b) = 1) :
    v (s - t + (t ^ 2 + (s + a) * t + (s ^ 2 + a * s + b))) = 1 := by
  have hs1 : v s ≤ 1 := v.le_one_of_root_cubic ha hb hc hs
  have ht1 : v t ≤ 1 := v.le_one_of_root_cubic ha hb hc ht
  have hprod : (s - t) * (t ^ 2 + (s + a) * t + (s ^ 2 + a * s + b)) = 0 := by
    linear_combination hs - ht
  rcases mul_eq_zero.mp hprod with h0 | h0
  · 
    rw [h0, zero_add,
      show t ^ 2 + (s + a) * t + (s ^ 2 + a * s + b) = 3 * s ^ 2 + 2 * a * s + b by
        linear_combination -(t + 2 * s + a) * h0, hderiv]
  · 
    rw [h0, add_zero]
    have h2t : v (2 * s + t + a) ≤ 1 :=
      let t' : v.integer := ⟨t, ht1⟩
      let a' : v.integer := ⟨a, ha⟩
      let s' : v.integer := ⟨s, hs1⟩
      (2 * s' + t' + a').prop
    refine v.eq_one_of_mul_eq_one ((v.map_sub s t).trans (max_le hs1 ht1)) h2t ?_
    rw [show (s - t) * (2 * s + t + a) = 3 * s ^ 2 + 2 * a * s + b by linear_combination -h0,
      hderiv]

end Cubic

section CubicField

variable {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)
  {t a b c : L}

private lemma Valuation.map_sub_eq_map_div_sq (ha : v a ≤ 1) (hb : v b ≤ 1) (hc : v c ≤ 1)
    (ht : v t ≤ 1) {x y : L} (hx : 1 < v x) (heq : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) :
    v (x - t) = v (y / x) ^ 2 := by
  have hx0 : v x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hval : v y ^ 2 = v x ^ 3 := by rw [← map_pow, heq, v.map_cubic_of_one_lt ha hb hc hx]
  rw [v.map_sub_eq_of_lt_left (ht.trans_lt hx), map_div₀, div_pow, hval, pow_succ,
    mul_div_cancel_left₀ _ (pow_ne_zero 2 hx0)]

end CubicField

namespace WeierstrassCurve

variable {K Γ : Type*} [CommRing K] [LinearOrderedCommGroupWithZero Γ]


structure IsIntegralAt (W : WeierstrassCurve K) (v : Valuation K Γ) : Prop where
  a₁ : v W.a₁ ≤ 1
  a₂ : v W.a₂ ≤ 1
  a₃ : v W.a₃ ≤ 1
  a₄ : v W.a₄ ≤ 1
  a₆ : v W.a₆ ≤ 1


lemma isIntegralAt_of_isCharNeTwoNF {W : WeierstrassCurve K} [W.IsCharNeTwoNF] {v : Valuation K Γ}
    (ha₂ : v W.a₂ ≤ 1) (ha₄ : v W.a₄ ≤ 1) (ha₆ : v W.a₆ ≤ 1) : W.IsIntegralAt v :=
  ⟨by simp [a₁_of_isCharNeTwoNF], ha₂, by simp [a₃_of_isCharNeTwoNF], ha₄, ha₆⟩


lemma isIntegralAt_valuation {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K) [IsIntegral R W]
    (v : IsDedekindDomain.HeightOneSpectrum R) : W.IsIntegralAt (v.valuation K) := by
  obtain ⟨W₀, rfl⟩ := IsIntegral.integral (R := R) (W := W)
  exact ⟨v.valuation_le_one _, v.valuation_le_one _, v.valuation_le_one _, v.valuation_le_one _,
    v.valuation_le_one _⟩

end WeierstrassCurve

namespace WeierstrassCurve.Affine

open IsDedekindDomain Polynomial UniqueFactorizationMonoid




variable {K : Type*} [Field K] (W : Affine K)




def badPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] :
    Set (HeightOneSpectrum R) :=
  {v | v.valuation K 2 ≠ 1} ∪ {v | v.valuation K W.Δ ≠ 1} ∪ HeightOneSpectrum.Support R W.a₂ ∪
    HeightOneSpectrum.Support R W.a₄ ∪ HeightOneSpectrum.Support R W.a₆


lemma finite_badPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
    [IsFractionRing R K] [W.IsElliptic] [W.IsCharNeTwoNF] : (W.badPrimes R).Finite :=
  ((((HeightOneSpectrum.finite_setOf_valuation_ne_one W.two_ne_zero).union
    (HeightOneSpectrum.finite_setOf_valuation_ne_one W.isUnit_Δ.ne_zero)).union
      (HeightOneSpectrum.Support.finite R W.a₂)).union
        (HeightOneSpectrum.Support.finite R W.a₄)).union
          (HeightOneSpectrum.Support.finite R W.a₆)

section BadPrimes

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R}

lemma valuation_a₂_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₂ ≤ 1 :=
  not_lt.mp fun hlt ↦ hv (.inl (.inl (.inr hlt)))

lemma valuation_a₄_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₄ ≤ 1 :=
  not_lt.mp fun hlt ↦ hv (.inl (.inr hlt))

lemma valuation_a₆_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₆ ≤ 1 :=
  not_lt.mp fun hlt ↦ hv (.inr hlt)

lemma isIntegralAt_of_notMem_badPrimes [W.IsCharNeTwoNF] (hv : v ∉ W.badPrimes R) :
    W.IsIntegralAt (v.valuation K) :=
  isIntegralAt_of_isCharNeTwoNF (W.valuation_a₂_le_one_of_notMem_badPrimes R hv)
    (W.valuation_a₄_le_one_of_notMem_badPrimes R hv)
    (W.valuation_a₆_le_one_of_notMem_badPrimes R hv)

lemma valuation_Δ_eq_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.Δ = 1 :=
  not_not.mp fun hne ↦ hv (.inl (.inl (.inl (.inr hne))))

lemma valuation_two_eq_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K 2 = 1 :=
  not_not.mp fun hne ↦ hv (.inl (.inl (.inl (.inl hne))))


lemma valuation_discr_eq_one_of_notMem_badPrimes [W.IsCharNeTwoNF] (hv : v ∉ W.badPrimes R) :
    v.valuation K W.f.discr = 1 := by
  have h16 : v.valuation K 16 = 1 := by
    rw [show (16 : K) = 2 ^ 4 by norm_num, map_pow,
      W.valuation_two_eq_one_of_notMem_badPrimes R hv, one_pow]
  have hΔ := W.valuation_Δ_eq_one_of_notMem_badPrimes R hv
  rwa [W.Δ_eq_discr_f, map_mul, h16, one_mul] at hΔ

end BadPrimes

section DerivativeUnit




lemma valuation_discr_le_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ}
    (hW : W.IsIntegralAt v) : v W.f.discr ≤ 1 := by
  have h : W.a₂ ^ 2 * W.a₄ ^ 2 - 4 * W.a₄ ^ 3 - 4 * W.a₂ ^ 3 * W.a₆ - 27 * W.a₆ ^ 2
      + 18 * W.a₂ * W.a₄ * W.a₆ ∈ v.integer :=
    add_mem (sub_mem (sub_mem (sub_mem (mul_mem (pow_mem hW.a₂ 2) (pow_mem hW.a₄ 2))
      (mul_mem (ofNat_mem _ 4) (pow_mem hW.a₄ 3))) (mul_mem (mul_mem (ofNat_mem _ 4)
        (pow_mem hW.a₂ 3)) hW.a₆)) (mul_mem (ofNat_mem _ 27) (pow_mem hW.a₆ 2)))
      (mul_mem (mul_mem (mul_mem (ofNat_mem _ 18) hW.a₂) hW.a₄) hW.a₆)
  rw [W.discr_f]
  exact h

open WithZero in
private lemma eq_one_of_le_one_of_exp_neg_one_le_sq {t : ℤᵐ⁰} (h1 : t ≤ 1)
    (h2 : exp (-1) ≤ t ^ 2) : t = 1 := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at h2
  rw [← exp_log ht0] at h1 h2 ⊢
  rw [← exp_nsmul, two_nsmul] at h2
  rw [← exp_zero] at h1
  rw [exp_eq_one]
  have e1 := exp_le_exp.mp h1
  have e2 := exp_le_exp.mp h2
  omega

open WithZero in

lemma valuation_deriv_eval_eq_one {v : Valuation K ℤᵐ⁰} {x : K} (hx : W.f.eval x = 0)
    (hW : W.IsIntegralAt v) (hd : exp (-1) ≤ v W.f.discr) :
    v (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 1 := by
  have hx1 : v x ≤ 1 := by
    rw [eval_f] at hx
    exact v.le_one_of_root_cubic hW.a₂ hW.a₄ hW.a₆ hx
  have hfx : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∈ v.integer :=
    add_mem (add_mem (mul_mem (ofNat_mem _ 3) (pow_mem hx1 2))
      (mul_mem (mul_mem (ofNat_mem _ 2) hW.a₂) hx1)) hW.a₄
  have hcd' : (x + W.a₂) ^ 2 - 4 * (x ^ 2 + W.a₂ * x + W.a₄) ∈ v.integer :=
    sub_mem (pow_mem (add_mem hx1 hW.a₂) 2) (mul_mem (ofNat_mem _ 4)
      (add_mem (add_mem (pow_mem hx1 2) (mul_mem hW.a₂ hx1)) hW.a₄))
  have hcd : v (W.fCofactor x).discr ≤ 1 := by rw [W.discr_fCofactor x]; exact hcd'
  rw [W.discr_f_eq_discr_fCofactor_mul_sq hx, map_mul, map_pow] at hd
  exact eq_one_of_le_one_of_exp_neg_one_le_sq hfx (hd.trans (mul_le_of_le_one_left' hcd))

end DerivativeUnit

section RingOfIntegers

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K]


noncomputable abbrev ringOfIntegersFactor (p : W.f.Factors) : Type _ :=
  integralClosure R (AdjoinRoot (p : K[X]))


instance isDedekindDomain_ringOfIntegersFactor [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors) :
    IsDedekindDomain (W.ringOfIntegersFactor R p) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.isDedekindDomain R K (AdjoinRoot (p : K[X])) _


instance isFractionRing_ringOfIntegersFactor [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors) :
    IsFractionRing (W.ringOfIntegersFactor R p) (AdjoinRoot (p : K[X])) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.isFractionRing_of_finite_extension R K (AdjoinRoot (p : K[X])) _


instance instIsTorsionFreeRingOfIntegersFactor (p : W.f.Factors) :
    Module.IsTorsionFree R (W.ringOfIntegersFactor R p) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  have hinj : Function.Injective (algebraMap R (AdjoinRoot (p : K[X]))) := by
    rw [IsScalarTower.algebraMap_eq R K (AdjoinRoot (p : K[X]))]
    exact (algebraMap K (AdjoinRoot (p : K[X]))).injective.comp (IsFractionRing.injective R K)
  exact fun a b hab ↦ hinj (congrArg Subtype.val hab)


lemma valuation_algebraMap_eq [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)) (z : K) :
    (w.under R).valuation K z ^ w.asIdeal.ramIdxU R =
      w.valuation (AdjoinRoot (p : K[X])) (algebraMap K (AdjoinRoot (p : K[X])) z) :=
  HeightOneSpectrum.valuation_liesOver _ _ _ z


lemma valuation_algebraMap_le_one [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)) {z : K}
    (hz : (w.under R).valuation K z ≤ 1) :
    w.valuation (AdjoinRoot (p : K[X])) (algebraMap K (AdjoinRoot (p : K[X])) z) ≤ 1 := by
  rw [← W.valuation_algebraMap_eq R p w z]
  simpa using pow_le_pow_left' hz _


lemma under_notMem_of_notMem_primesAbove [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    {S : Set (HeightOneSpectrum R)} {w : HeightOneSpectrum (W.ringOfIntegersFactor R p)}
    (hw : w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S) : w.under R ∉ S :=
  fun hv ↦ hw ((HeightOneSpectrum.mem_primesAbove_iff R _ _ w).mpr hv)


lemma root_cubic_eq_zero (p : W.f.Factors) :
    AdjoinRoot.root (p : K[X]) ^ 3 + algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X]) ^ 2 + algebraMap K (AdjoinRoot (p : K[X])) W.a₄ * AdjoinRoot.root (p : K[X]) + algebraMap K (AdjoinRoot (p : K[X])) W.a₆ = 0 := by
  have hz : AdjoinRoot.mk (p : K[X]) W.f = 0 :=
    AdjoinRoot.mk_eq_zero.mpr p.dvd
  simpa [f, AdjoinRoot.algebraMap_eq] using hz


lemma deriv_root_mul_eq_discr_f (p : W.f.Factors) :
    (3 * AdjoinRoot.root (p : K[X]) ^ 2 + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X]) + algebraMap K (AdjoinRoot (p : K[X])) W.a₄)
        * ((2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ ^ 2 - 6 * algebraMap K (AdjoinRoot (p : K[X])) W.a₄) * AdjoinRoot.root (p : K[X]) ^ 2
          + (2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ ^ 3 - 7 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * algebraMap K (AdjoinRoot (p : K[X])) W.a₄ + 9 * algebraMap K (AdjoinRoot (p : K[X])) W.a₆) * AdjoinRoot.root (p : K[X])
          + (algebraMap K (AdjoinRoot (p : K[X])) W.a₂ ^ 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₄ - 4 * algebraMap K (AdjoinRoot (p : K[X])) W.a₄ ^ 2 + 3 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * algebraMap K (AdjoinRoot (p : K[X])) W.a₆)) =
      algebraMap K (AdjoinRoot (p : K[X])) W.f.discr := by
  have h := W.aeval_f_mul_add_aeval_derivative_f_mul_eq_discr (AdjoinRoot.root (p : K[X]))
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero.mpr p.dvd, zero_mul,
    zero_add, derivative_f] at h
  simpa only [map_add, map_mul, map_pow, map_ofNat, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
    AdjoinRoot.algebraMap_eq] using h


lemma mk_fCofactor_eq (p : W.f.Factors) (x : K) :
    AdjoinRoot.mk (p : K[X]) (W.fCofactor x) =
      AdjoinRoot.root (p : K[X]) ^ 2 + (algebraMap K (AdjoinRoot (p : K[X])) x + algebraMap K (AdjoinRoot (p : K[X])) W.a₂) * AdjoinRoot.root (p : K[X]) + (algebraMap K (AdjoinRoot (p : K[X])) x ^ 2 + algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * algebraMap K (AdjoinRoot (p : K[X])) x + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) := by
  simp only [fCofactor, map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    ← AdjoinRoot.algebraMap_eq]

variable [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
  {w : HeightOneSpectrum (W.ringOfIntegersFactor R p)}
  (hW : W.IsIntegralAt ((w.under R).valuation K)) (hd : (w.under R).valuation K W.f.discr = 1)
  
  
  (hderiv : w.valuation (AdjoinRoot (p : K[X]))
    (3 * AdjoinRoot.root (p : K[X]) ^ 2
      + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X])
      + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = 1)

include hW in

lemma valuation_root_le_one : w.valuation (AdjoinRoot (p : K[X])) (AdjoinRoot.root (p : K[X])) ≤ 1 :=
  Valuation.le_one_of_root_cubic _
    (W.valuation_algebraMap_le_one R p w hW.a₂)
    (W.valuation_algebraMap_le_one R p w hW.a₄)
    (W.valuation_algebraMap_le_one R p w hW.a₆)
    (W.root_cubic_eq_zero p)


lemma valuation_algebraMap_eq_one {z : K} (hz : (w.under R).valuation K z = 1) :
    w.valuation (AdjoinRoot (p : K[X])) (algebraMap K (AdjoinRoot (p : K[X])) z) = 1 := by
  rw [← W.valuation_algebraMap_eq R p w z, hz, one_pow]

include hW in

lemma valuation_deriv_root_le_one :
    w.valuation (AdjoinRoot (p : K[X])) (3 * AdjoinRoot.root (p : K[X]) ^ 2 + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X]) + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) ≤ 1 :=
  Valuation.map_cubic_deriv_le_one _ (W.valuation_algebraMap_le_one R p w hW.a₂)
    (W.valuation_algebraMap_le_one R p w hW.a₄) (W.valuation_root_le_one R p hW)

include hW hd in

lemma valuation_deriv_root_eq_one :
    w.valuation (AdjoinRoot (p : K[X])) (3 * AdjoinRoot.root (p : K[X]) ^ 2 + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X]) + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = 1 :=
  Valuation.map_cubic_deriv_eq_one _ (W.valuation_algebraMap_le_one R p w hW.a₂)
    (W.valuation_algebraMap_le_one R p w hW.a₄) (W.valuation_algebraMap_le_one R p w hW.a₆)
    (W.valuation_root_le_one R p hW) (W.valuation_algebraMap_eq_one R p hd)
    (W.deriv_root_mul_eq_discr_f p)

include hW hderiv in

lemma valuation_cofactor_eq_one {x : K}
    (hx : w.valuation (AdjoinRoot (p : K[X])) (algebraMap K (AdjoinRoot (p : K[X])) x) ≤ 1)
    (hlt : w.valuation (AdjoinRoot (p : K[X])) (algebraMap K (AdjoinRoot (p : K[X])) x - AdjoinRoot.root (p : K[X])) < 1) :
    w.valuation (AdjoinRoot (p : K[X])) (algebraMap K (AdjoinRoot (p : K[X])) x ^ 2 + AdjoinRoot.root (p : K[X]) * algebraMap K (AdjoinRoot (p : K[X])) x + AdjoinRoot.root (p : K[X]) ^ 2
      + algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * (algebraMap K (AdjoinRoot (p : K[X])) x + AdjoinRoot.root (p : K[X])) + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = 1 :=
  Valuation.map_cofactor_eq_one _ (W.valuation_algebraMap_le_one R p w hW.a₂)
    (W.valuation_root_le_one R p hW) hx hlt hderiv

include hW in

lemma valuation_projFactor_torsion_eq_one {x : K} (hx : W.f.eval x = 0)
    (hdx : (w.under R).valuation K (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 1) :
    w.valuation (AdjoinRoot (p : K[X])) (algebraMap K (AdjoinRoot (p : K[X])) x - AdjoinRoot.root (p : K[X]) + AdjoinRoot.mk (p : K[X]) (W.fCofactor x)) = 1 := by
  rw [W.mk_fCofactor_eq p x]
  refine Valuation.map_sub_add_cofactor_eq_one _ (W.valuation_algebraMap_le_one R p w hW.a₂)
    (W.valuation_algebraMap_le_one R p w hW.a₄) (W.valuation_algebraMap_le_one R p w hW.a₆)
    (by rw [← W.map_eval_f, hx, map_zero]) (W.root_cubic_eq_zero p) ?_
  simpa only [map_add, map_mul, map_pow, map_ofNat] using
    W.valuation_algebraMap_eq_one R p (w := w) hdx

end RingOfIntegers

section Core

variable [W.IsElliptic] [W.IsCharNeTwoNF]
  (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (p : W.f.Factors)
  {x y : K} (h : W.Equation x y) (hx : W.f.eval x ≠ 0)
  (u : (AdjoinRoot (p : K[X]))ˣ)
  (hu : (u : AdjoinRoot (p : K[X])) =
    algebraMap K (AdjoinRoot (p : K[X])) x - AdjoinRoot.root (p : K[X]))
  (w : HeightOneSpectrum (W.ringOfIntegersFactor R p))
  (hW : W.IsIntegralAt ((w.under R).valuation K))
  
  
  (hderiv : w.valuation (AdjoinRoot (p : K[X]))
    (3 * AdjoinRoot.root (p : K[X]) ^ 2
      + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X])
      + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = 1)

include h hx hu hW


lemma even_valuationOfNeZero_sub_root_of_one_lt
    (hx' : 1 < w.valuation (AdjoinRoot (p : K[X])) (algebraMap K (AdjoinRoot (p : K[X])) x)) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  have hx0 : algebraMap K (AdjoinRoot (p : K[X])) x ≠ 0 := (w.valuation (AdjoinRoot (p : K[X]))).ne_zero_iff.mp (zero_lt_one.trans hx').ne'
  have hy0 : algebraMap K (AdjoinRoot (p : K[X])) y ≠ 0 := (_root_.map_ne_zero _).mpr (W.ne_zero_of_eval_f_ne_zero h hx)
  have heq : algebraMap K (AdjoinRoot (p : K[X])) y ^ 2 = algebraMap K (AdjoinRoot (p : K[X])) x ^ 3 + algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * algebraMap K (AdjoinRoot (p : K[X])) x ^ 2 + algebraMap K (AdjoinRoot (p : K[X])) W.a₄ * algebraMap K (AdjoinRoot (p : K[X])) x + algebraMap K (AdjoinRoot (p : K[X])) W.a₆ := by
    rw [← W.map_eval_f, (equation_iff_eval_f_eq_sq W x y).mp h, map_pow]
  have hkey : w.valuation (AdjoinRoot (p : K[X])) u = w.valuation (AdjoinRoot (p : K[X])) (Units.mk0 _ (div_ne_zero hy0 hx0)) ^ 2 := by
    rw [hu, Units.val_mk0]
    exact Valuation.map_sub_eq_map_div_sq _ (W.valuation_algebraMap_le_one R p w hW.a₂)
      (W.valuation_algebraMap_le_one R p w hW.a₄) (W.valuation_algebraMap_le_one R p w hW.a₆)
      (W.valuation_root_le_one R p hW) hx' heq
  simpa using w.dvd_toAdd_valuationOfNeZero hkey

include hderiv in

lemma even_valuationOfNeZero_sub_root_of_le_one
    (hx' : w.valuation (AdjoinRoot (p : K[X])) (algebraMap K (AdjoinRoot (p : K[X])) x) ≤ 1) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  have hy0 : algebraMap K (AdjoinRoot (p : K[X])) y ≠ 0 := (_root_.map_ne_zero _).mpr (W.ne_zero_of_eval_f_ne_zero h hx)
  have heq : algebraMap K (AdjoinRoot (p : K[X])) y ^ 2 = algebraMap K (AdjoinRoot (p : K[X])) x ^ 3 + algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * algebraMap K (AdjoinRoot (p : K[X])) x ^ 2 + algebraMap K (AdjoinRoot (p : K[X])) W.a₄ * algebraMap K (AdjoinRoot (p : K[X])) x + algebraMap K (AdjoinRoot (p : K[X])) W.a₆ := by
    rw [← W.map_eval_f, (equation_iff_eval_f_eq_sq W x y).mp h, map_pow]
  have hfac : (algebraMap K (AdjoinRoot (p : K[X])) x - AdjoinRoot.root (p : K[X])) * (algebraMap K (AdjoinRoot (p : K[X])) x ^ 2 + AdjoinRoot.root (p : K[X]) * algebraMap K (AdjoinRoot (p : K[X])) x + AdjoinRoot.root (p : K[X]) ^ 2 + algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * (algebraMap K (AdjoinRoot (p : K[X])) x + AdjoinRoot.root (p : K[X]))
      + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = algebraMap K (AdjoinRoot (p : K[X])) y ^ 2 := by
    linear_combination -W.root_cubic_eq_zero p - heq
  rcases Valuation.map_sub_eq_one_or_eq_map_sq _ (W.valuation_algebraMap_le_one R p w hW.a₂)
    (W.valuation_root_le_one R p hW) hx' hderiv hfac with h1 | h1
  · simpa using w.dvd_toAdd_valuationOfNeZero (n := 2) (z := 1)
      (by rw [Units.val_one, map_one, one_pow, hu, h1])
  · simpa using w.dvd_toAdd_valuationOfNeZero (n := 2) (z := Units.mk0 _ hy0)
      (by simpa [hu] using h1)

include hderiv in

lemma even_valuationOfNeZero_sub_root :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  by_cases hx' : 1 < w.valuation (AdjoinRoot (p : K[X])) (algebraMap K (AdjoinRoot (p : K[X])) x)
  · exact W.even_valuationOfNeZero_sub_root_of_one_lt R p h hx u hu w hW hx'
  · exact W.even_valuationOfNeZero_sub_root_of_le_one R p h hx u hu w hW hderiv
      (not_lt.mp hx')

end Core

section Selmer


lemma dvd_fCofactor_of_ne {x : K} (hx : W.f.eval x = 0) (p : W.f.Factors)
    (hp : (p : K[X]) ≠ X - C x) : (p : K[X]) ∣ W.fCofactor x := by
  have hdvd : (p : K[X]) ∣ W.fCofactor x * (X - C x) := by
    rw [← W.f_eq_mul_of_eval_eq_zero hx]
    exact p.dvd
  refine (p.prime.2.2 _ _ hdvd).resolve_right fun h ↦ hp ?_
  exact eq_of_monic_of_associated p.monic (monic_X_sub_C x)
    (p.irreducible.associated_of_dvd (irreducible_X_sub_C x) h)


lemma mk_fCofactor_eq_zero {x : K} (hx : W.f.eval x = 0) (p : W.f.Factors)
    (hp : (p : K[X]) ≠ X - C x) : AdjoinRoot.mk (p : K[X]) (W.fCofactor x) = 0 :=
  AdjoinRoot.mk_eq_zero.mpr (W.dvd_fCofactor_of_ne hx p hp)

variable [W.IsElliptic] [W.IsCharNeTwoNF]


lemma projFactor_mk_C_sub_X (x : K) (p : W.f.Factors) :
    AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p (AdjoinRoot.mk W.f (C x - X)) =
      algebraMap K (AdjoinRoot (p : K[X])) x - AdjoinRoot.root (p : K[X]) := by
  rw [AdjoinRoot.projFactor_mk, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.algebraMap_eq]


lemma projFactor_mk_C_sub_X_add_fCofactor (x : K) (p : W.f.Factors) :
    AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p
        (AdjoinRoot.mk W.f (C x - X + W.fCofactor x)) =
      algebraMap K (AdjoinRoot (p : K[X])) x - AdjoinRoot.root (p : K[X]) + AdjoinRoot.mk (p : K[X]) (W.fCofactor x) := by
  rw [AdjoinRoot.projFactor_mk, map_add, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.algebraMap_eq]

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R))


noncomputable def selmerGroupFactor (p : W.f.Factors) :
    Subgroup (Units.modPow (AdjoinRoot (p : K[X])) 2) :=
  IsDedekindDomain.selmerGroupAbove R (W.ringOfIntegersFactor R p) (AdjoinRoot (p : K[X])) S 2


noncomputable def selmerGroupPi :
    Subgroup ((p : W.f.Factors) → Units.modPow (AdjoinRoot (p : K[X])) 2) :=
  Subgroup.pi Set.univ (W.selmerGroupFactor R S)


noncomputable def selmerGroupA : Subgroup W.M :=
  (W.selmerGroupPi R S).comap
    (AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2).toMonoidHom

lemma mem_selmerGroupA_iff (m : W.M) :
    m ∈ W.selmerGroupA R S ↔ ∀ p : W.f.Factors,
      AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2 m p ∈
        W.selmerGroupFactor R S p := by
  simp [selmerGroupA, selmerGroupPi, Subgroup.mem_pi]




lemma mem_selmerGroupFactor_unit_iff (p : W.f.Factors) (u : (AdjoinRoot (p : K[X]))ˣ) :
    (QuotientGroup.mk u : Units.modPow (AdjoinRoot (p : K[X])) 2) ∈ W.selmerGroupFactor R S p ↔
      ∀ w : HeightOneSpectrum (W.ringOfIntegersFactor R p),
        w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S →
          (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) :=
  forall₂_congr fun w _ ↦ HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff w 2 u


lemma mem_selmerGroupA_unit_iff (a : W.Aˣ) :
    (QuotientGroup.mk a : W.M) ∈ W.selmerGroupA R S ↔
      ∀ (p : W.f.Factors) (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)),
        w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S →
          (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero
            (Units.map (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p).toMonoidHom a)) := by
  rw [mem_selmerGroupA_iff]
  refine forall_congr' fun p ↦ ?_
  rw [AdjoinRoot.modPowEquivPiFactors_mk, mem_selmerGroupFactor_unit_iff]

variable (hS : ∀ v ∉ S, W.IsIntegralAt (v.valuation K)) (hSd : ∀ v ∉ S, v.valuation K W.f.discr = 1)

include hS hSd in

lemma mem_selmerGroupFactor_of_eval_f_ne_zero {x y : K} (h : W.Equation x y)
    (hx : W.f.eval x ≠ 0) (p : W.f.Factors) :
    (((isUnit_mk_sub_X_of_eval_f_ne_zero hx).map
      (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit :
        Units.modPow (AdjoinRoot (p : K[X])) 2) ∈ W.selmerGroupFactor R S p := by
  rw [W.mem_selmerGroupFactor_unit_iff R S p]
  intro w hw
  have hv := W.under_notMem_of_notMem_primesAbove R p hw
  refine W.even_valuationOfNeZero_sub_root R p h hx _ ?_ w (hS _ hv)
    (W.valuation_deriv_root_eq_one R p (hS _ hv) (hSd _ hv))
  exact W.projFactor_mk_C_sub_X x p

include hS hSd in

lemma mem_selmerGroupFactor_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0)
    (p : W.f.Factors) :
    (((isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).map
      (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit :
        Units.modPow (AdjoinRoot (p : K[X])) 2) ∈ W.selmerGroupFactor R S p := by
  rw [W.mem_selmerGroupFactor_unit_iff R S p]
  intro w hw
  have hv := W.under_notMem_of_notMem_primesAbove R p hw
  set u := ((isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).map
    (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit with hudef
  have hd1 : WithZero.exp (-1 : ℤ) ≤ (w.under R).valuation K W.f.discr := by
    rw [hSd _ hv]
    exact (WithZero.exp_le_exp.mpr (by lia)).trans_eq WithZero.exp_zero
  have hval : w.valuation (AdjoinRoot (p : K[X])) (u : AdjoinRoot (p : K[X])) = 1 := by
    rw [hudef, IsUnit.unit_spec, W.projFactor_mk_C_sub_X_add_fCofactor x p]
    exact W.valuation_projFactor_torsion_eq_one R p (hS _ hv) hx
      (W.valuation_deriv_eval_eq_one hx (hS _ hv) hd1)
  simpa using w.dvd_toAdd_valuationOfNeZero (n := 2) (z := 1) (by simp [hval])

section

variable [DecidableEq K]

include hS hSd in

lemma μX_component_mem_selmerGroupFactor {x y : K} (h : W.Equation x y) (p : W.f.Factors) :
    AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2 (W.μX x) p ∈
      W.selmerGroupFactor R S p := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · rw [μX_of_eval_f_eq_zero hx, AdjoinRoot.modPowEquivPiFactors_unit]
    exact W.mem_selmerGroupFactor_of_eval_f_eq_zero R S hS hSd hx p
  · rw [μX_of_eval_f_ne_zero hx, AdjoinRoot.modPowEquivPiFactors_unit]
    exact W.mem_selmerGroupFactor_of_eval_f_ne_zero R S hS hSd h hx p

include hS hSd in

theorem range_μ_le_selmerGroupA : (μ (W := W)).range ≤ W.selmerGroupA R S := by
  rintro _ ⟨P, rfl⟩
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P
  rw [μ_apply]
  match P with
  | 0 => rw [μ₀_zero]; exact one_mem _
  | .some x y h =>
    rw [μ₀_some, mem_selmerGroupA_iff]
    exact fun p ↦ W.μX_component_mem_selmerGroupFactor R S hS hSd h.1 p

end



section Step7

variable [(p : W.f.Factors) → Finite (ClassGroup (W.ringOfIntegersFactor R p))]
  [(p : W.f.Factors) → IsMulFG (W.ringOfIntegersFactor R p)ˣ]


theorem finite_selmerGroupFactor (hS : S.Finite) (p : W.f.Factors) :
    Finite (W.selmerGroupFactor R S p) :=
  finite_selmerGroup (W.ringOfIntegersFactor R p) (AdjoinRoot (p : K[X]))
    (HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S) 2
    (HeightOneSpectrum.primesAbove_finite R (W.ringOfIntegersFactor R p) hS)


theorem finite_selmerGroupA (hS : S.Finite) : Finite (W.selmerGroupA R S) := by
  have := Polynomial.Factors.finite W.f_ne_zero
  have (p : W.f.Factors) : Finite (W.selmerGroupFactor R S p) :=
    W.finite_selmerGroupFactor R S hS p
  have : Finite (W.selmerGroupPi R S) := Subgroup.instFinitePi
  exact Subgroup.finite_comap_of_injective
    (AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2).injective (W.selmerGroupPi R S)

variable [DecidableEq K]

include R in

theorem finite_index_range_nsmulAddMonoidHom_two :
    (nsmulAddMonoidHom (α := W.Point) 2).range.FiniteIndex := by
  rw [finite_index_range_nsmulAddMonoidHom_two_iff]
  have := W.finite_selmerGroupA R (W.badPrimes R) (W.finite_badPrimes R)
  exact ((W.selmerGroupA R (W.badPrimes R) : Set W.M).toFinite.subset
    (W.range_μ_le_selmerGroupA R (W.badPrimes R)
      (fun _ hv ↦ W.isIntegralAt_of_notMem_badPrimes R hv)
      (fun _ hv ↦ W.valuation_discr_eq_one_of_notMem_badPrimes R hv))).to_subtype

end Step7

end Selmer

end WeierstrassCurve.Affine

end
end M5
section M6



section





namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

section Northcott

open Height

variable [AdmissibleAbsValues F] [Northcott (logHeight₁ (K := F))] [DecidableEq F]
  [W.toAffine.IsElliptic]


theorem fg_point (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R F]
    [IsFractionRing R F] [W.IsCharNeTwoNF]
    [(p : W.f.Factors) → Finite (ClassGroup (W.ringOfIntegersFactor R p))]
    [(p : W.f.Factors) → IsMulFG (W.ringOfIntegersFactor R p)ˣ] :
    IsAddFG W.Point := by
  have H₂ (P : W.Point) : 0 ≤ P.mwHeight := by
    rw [Point.mwHeight_eq_logHeight P]
    positivity
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.fg_of_descent' (W.finite_index_range_nsmulAddMonoidHom_two R) H₂ hC


theorem fg_point_of_variableChange (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R F]
    [IsFractionRing R F] (C : VariableChange F) [(C • W).IsCharNeTwoNF]
    [(p : (C • W).toAffine.f.Factors) →
      Finite (ClassGroup ((C • W).toAffine.ringOfIntegersFactor R p))]
    [(p : (C • W).toAffine.f.Factors) →
      IsMulFG ((C • W).toAffine.ringOfIntegersFactor R p)ˣ] :
    IsAddFG W.Point := by
  have := fg_point (W := (C • W).toAffine) R
  exact AddGroup.fg_of_surjective (f := (Point.equivVariableChange W C).toAddMonoidHom)
    (Point.equivVariableChange W C).surjective

end Northcott

section NumberField

open NumberField

variable {F : Type*} [Field F] [NumberField F] [DecidableEq F] {W : Affine F}
  [W.toAffine.IsElliptic]


theorem fg_point_of_numberField : IsAddFG W.Point := by
  have := invertibleOfNonzero (two_ne_zero (α := F))
  obtain ⟨C, hC⟩ := exists_variableChange_isCharNeTwoNF (W := W)
  have (p : (C • W).toAffine.f.Factors) :
      Finite (ClassGroup ((C • W).toAffine.ringOfIntegersFactor (𝓞 F) p)) :=
    NumberField.finite_classGroup_integralClosure F (AdjoinRoot (p : Polynomial F))
  have (p : (C • W).toAffine.f.Factors) :
      IsMulFG ((C • W).toAffine.ringOfIntegersFactor (𝓞 F) p)ˣ :=
    NumberField.fg_units_integralClosure F (AdjoinRoot (p : Polynomial F))
  exact fg_point_of_variableChange (𝓞 F) C

end NumberField

end WeierstrassCurve.Affine

end
end M6

instance modN_finite_fix (H : Type*) [AddCommGroup H] [Module.Finite ℤ H] (n : ℕ) : Module.Finite (ZMod n) (ModN H n) :=
  Module.Finite.of_restrictScalars_finite ℤ (ZMod n) (ModN H n)
section M0




section

namespace ECCompute


noncomputable def allBelow (n : Nat) (p : Nat → Bool) : Bool := n.rec true fun m r ↦ (p m).and r


noncomputable def allList {α : Type} (p : α → Bool) : List α → Bool :=
  List.rec true fun a _ r ↦ (p a).and r




noncomputable def passes (x : Nat) : List Nat → Bool :=
  List.rec true (fun i _ r ↦ ((Nat.ble 1 (x.mod i)).or (x.ble i)).and r)


noncomputable def checkPrime (p : Nat) : Bool :=
  (Nat.ble 2 p).and ((p.ble 528).and (passes p [2, 3, 5, 7, 11, 13, 17, 19]))


noncomputable def checkPrimes (labels : List (Nat × Int)) : Bool :=
  allList (fun l ↦ checkPrime l.1) labels




noncomputable def polyEval (cs : List Int) (u : Int) : Int :=
  cs.rec 0 fun c _ acc ↦ c.add (u.mul acc)


noncomputable def polyModL (cs : List Int) (ℓ r : Nat) : Nat :=
  cs.rec 0 fun c _ acc ↦ ((c.emod ℓ).toNat.add (r.mul acc)).mod ℓ


noncomputable def polyModK (cs : List Nat) (ℓ r : Nat) : Nat :=
  cs.rec 0 fun c _ acc ↦ ((c.mod ℓ).add (r.mul acc)).mod ℓ


noncomputable def monicHasNoRootMod (cs : List Int) (ℓ : Nat) : Bool :=
  allBelow ℓ fun r ↦ ((polyModL (cs ++ [1]) ℓ r).beq 0).not




def discrIntK (a₂ a₄ a₆ : Int) : Int :=
  let b2 := a₂.mul 4
  let b4 := a₄.mul 2
  let b6 := a₆.mul 4
  ((((b2.mul b2).mul (((a₂.mul 4).mul a₆).sub (a₄.mul a₄))).neg.sub
      (((b4.mul b4).mul b4).mul 8)).sub ((b6.mul b6).mul 27)).add
    (((b2.mul 9).mul b4).mul b6)


noncomputable def checkLabel (a₂r a₄r a₆r : Nat) (Δ : Int) (p : Nat) (θ : Int) : Bool :=
  let r₂ := a₂r.mod p
  let r₄ := a₄r.mod p
  let r₆ := a₆r.mod p
  ((Nat.mod 6 p).beq 0).not.and
    (((Δ.emod p).beq' 0).not.and
      ((polyModK [r₆, r₄, r₂, 1] p (θ.emod p).toNat).beq 0))


noncomputable def checkLabels (a₂ a₄ a₆ : Int) (P a₂r a₄r a₆r : Nat) (Δ : Int)
    (labels : List (Nat × Int)) : Bool :=
  (Nat.ble 1 P).and
    ((a₂r.beq (a₂.emod (Int.ofNat P)).toNat).and
      ((a₄r.beq (a₄.emod (Int.ofNat P)).toNat).and
        ((a₆r.beq (a₆.emod (Int.ofNat P)).toNat).and
          ((Δ.beq' (discrIntK a₂ a₄ a₆)).and
            (allList (fun l ↦ ((P.mod l.1).beq 0).and (checkLabel a₂r a₄r a₆r Δ l.1 l.2))
              labels)))))




noncomputable def qrMaskGo (p : Nat) : Nat → Nat :=
  Nat.rec 0 (fun k ih ↦ ih.lor (Nat.shiftLeft 1 ((k.succ.mul k.succ).mod p)))


noncomputable def qrMask (p : Nat) : Nat := qrMaskGo p ((p.sub 1).div 2)


noncomputable def alphaResK (p tval xp xm xden : Nat) : Nat :=
  ((xp.mod p).add (p.sub ((xm.add (tval.mul xden)).mod p))).mod p


noncomputable def fderivResK (a₂ a₄ : Int) (p tval : Nat) : Nat :=
  polyModL [a₄, Int.mul 2 a₂, 3] p tval


noncomputable def lambdaBitK (a₂ a₄ : Int) (p qm tval xp xm xden : Nat) : Nat :=
  ((xden.mod p).beq 0).rec
    (((alphaResK p tval xp xm xden).beq 0).rec
      (((qm.shiftRight (alphaResK p tval xp xm xden)).land 1).xor 1)
      (((qm.shiftRight (fderivResK a₂ a₄ p tval)).land 1).xor 1))
    0



namespace F2Invert


noncomputable def invRowK (bi : Nat) (M : List Nat) : Nat :=
  M.rec (motive := fun _ ↦ Nat → Nat) (fun _ ↦ 0)
    (fun m _ ih b ↦ (m.mul (b.land 1)).xor (ih (b.shiftRight 1))) bi


noncomputable def checkInvGo (M : List Nat) (i : Nat) (B : List Nat) : Bool :=
  B.rec (fun _ ↦ true)
    (fun b _ ih i ↦ ((invRowK b M).beq (Nat.shiftLeft 1 i)).and (ih i.succ)) i


noncomputable def checkInv (B M : List Nat) : Bool := checkInvGo M 0 B

end F2Invert




noncomputable def toLs (ls : List (Nat × Int)) (q : List Nat) : List (Nat × Nat × Nat) :=
  List.zipWith (fun l m ↦ (l.1, (l.2.emod l.1).toNat, m)) ls q


noncomputable def checkBRowWord (a₂ a₄ : Int) (xnp xnm xden : Nat)
    (ls : List (Nat × Nat × Nat)) : Nat :=
  ls.rec 0 (fun l _ ih ↦ (lambdaBitK a₂ a₄ l.1 l.2.2 l.2.1 xnp xnm xden).lor (ih.shiftLeft 1))


noncomputable def checkBRow (a₂ a₄ : Int) (xnp xnm xden b : Nat) (ls : List (Nat × Nat × Nat)) :
    Bool :=
  (checkBRowWord a₂ a₄ xnp xnm xden ls).beq b


noncomputable def checkBGo (a₂ a₄ : Int) (ls : List (Nat × Nat × Nat)) (B : List Nat)
    (pt : List (Rat × Rat)) : Bool :=
  B.rec (fun _ ↦ true)
    (fun b _ ih pt ↦ pt.rec true
      (fun p ps _ ↦ (checkBRow a₂ a₄ p.1.num.toNat (-p.1.num).toNat p.1.den b ls).and
        (ih ps))) pt


noncomputable def checkMaskList (ls : List (Nat × Nat × Nat)) : Bool :=
  allList (fun l ↦ (qrMask l.1).beq l.2.2) ls


noncomputable def checkB (a₂ a₄ : Int) (ls : List (Nat × Int)) (q B : List Nat)
    (pt : List (Rat × Rat)) : Bool :=
  (checkMaskList (toLs ls q)).and
    (checkBGo a₂ a₄ (toLs ls q) B pt)




noncomputable def checkPoint (a₂ a₄ a₆ : Int) (x y : Rat) : Bool :=
  let xn := x.num; let xd := x.den
  let yn := y.num; let yd := y.den
  let xd2 := xd.mul xd; let xd3 := xd2.mul xd
  let yd2 := yd.mul yd
  let xn2 := xn.mul xn; let xn3 := xn2.mul xn
  let yn2 := yn.mul yn
  (yn2.mul xd3).beq'
    ((((xn3.mul yd2).add (((a₂.mul xn2).mul xd).mul yd2)).add
        (((a₄.mul xn).mul xd2).mul yd2)).add ((a₆.mul xd3).mul yd2))


noncomputable def checkPoints (a₂ a₄ a₆ : Int) (pts : List (Rat × Rat)) : Bool :=
  allList (fun p ↦ checkPoint a₂ a₄ a₆ p.1 p.2) pts

end ECCompute
end
end M0
section M1






namespace ECCompute

section
variable {n : ℕ} {p : ℕ → Bool}


@[simp] theorem allBelow_zero : allBelow 0 p = true := rfl


@[simp]
theorem allBelow_succ : allBelow (n + 1) p = (p n).and (allBelow n p) := rfl
grind_pattern allBelow_succ => allBelow (n + 1) p


theorem allBelow_iff : allBelow n p ↔ ∀ m < n, p m := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [allBelow_succ, Bool.and_eq_true, ih]
    grind
grind_pattern allBelow_iff => allBelow n p

end

section
variable {α : Type} {p : α → Bool} {l : List α}


@[simp] theorem allList_nil : allList p [] = true := rfl


@[simp]
theorem allList_cons {a : α} : allList p (a :: l) = (p a).and (allList p l) := rfl
grind_pattern allList_cons => allList p (a :: l)


theorem allList_iff : allList p l ↔ ∀ a ∈ l, p a := by
  induction l with
  | nil => simp
  | cons a t ih => rw [allList_cons, Bool.and_eq_true, ih, List.forall_mem_cons]
grind_pattern allList_iff => allList p l

end

end ECCompute
end M1
section M2




section

@[simp]
theorem Nat.mod_eq_mod : Nat.mod a b = a % b := rfl
grind_pattern Nat.mod_eq_mod => Nat.mod a b

@[simp]
theorem Int.sub_eq : Int.sub a b = a - b := rfl
grind_pattern Int.sub_eq => Int.sub a b

@[simp]
theorem Int.neg_eq : Int.neg a = -a := rfl
grind_pattern Int.neg_eq => Int.neg a

@[simp]
theorem Int.emod_eq : Int.emod a b = a % b := rfl
grind_pattern Int.emod_eq => Int.emod a b

@[simp]
theorem Nat.beq_eq_beq : Nat.beq a b = (a == b) := by rw [Bool.eq_iff_iff]; simp
grind_pattern Nat.beq_eq_beq => Nat.beq a b

grind_pattern Nat.add_eq => Nat.add x y
grind_pattern Nat.mul_eq => Nat.mul x y
grind_pattern Nat.ble_eq => Nat.ble x y
grind_pattern Nat.shiftRight_eq' => Nat.shiftRight m n
grind_pattern Nat.land_eq => Nat.land m n
grind_pattern Nat.xor_eq => Nat.xor m n
grind_pattern Int.add_def => Int.add a b
grind_pattern Int.mul_def => Int.mul a b
end
end M2
section M3






namespace ECCompute.F2Invert

open Finset

variable {a b : Bool}


def bId (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp]
lemma bId_false : bId false = 0 := rfl
grind_pattern bId_false => bId false
@[simp]
lemma bId_true : bId true = 1 := rfl
grind_pattern bId_true => bId true
@[simp] lemma bId_xor : bId (a ^^ b) = bId a + bId b := by decide +revert +kernel
@[simp] lemma bId_and : bId (a && b) = bId a * bId b := by decide +revert +kernel

@[simp]
theorem invRowK_nil {b : ℕ} : invRowK b [] = 0 := rfl
grind_pattern invRowK_nil => invRowK b []

@[simp]
theorem invRowK_cons {b m : ℕ} {ms : List ℕ} :
    invRowK b (m :: ms) = m * (b &&& 1) ^^^ invRowK (b >>> 1) ms := rfl
grind_pattern invRowK_cons => invRowK b (m :: ms)


theorem bId_testBit_select {m b j : ℕ} :
    bId ((m * (b &&& 1)).testBit j) = bId (b.testBit 0) * bId (m.testBit j) := by
  rcases Nat.mod_two_eq_zero_or_one b with h | h <;> simp [Nat.and_one_is_mod, h]


theorem bId_invRowK_testBit {ms : List ℕ} {b j : ℕ} :
    bId ((invRowK b ms).testBit j)
      = ∑ k ∈ range ms.length, bId (b.testBit k) * bId ((ms.getD k 0).testBit j) := by
  induction ms generalizing b with
  | nil => simp
  | cons m ms ih =>
    simp only [invRowK_cons, Nat.testBit_xor, bId_xor, bId_testBit_select, List.length_cons,
      sum_range_succ']
    grind

variable {n i i' : ℕ} {B M : List ℕ}

@[simp]
theorem checkInvGo_cons {b : ℕ} {bs : List ℕ} :
    checkInvGo M i (b :: bs) = ((invRowK b M).beq (1 <<< i)).and (checkInvGo M i.succ bs) := rfl
grind_pattern checkInvGo_cons => checkInvGo M i (b :: bs)


def toMat (B : List ℕ) (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j ↦ if (B.getD i 0).testBit j then 1 else 0


theorem toMat_apply {B : List ℕ} {n : ℕ} {i j : Fin n} (h : i.val < B.length) :
    toMat B n i j = if B[i].testBit j then 1 else 0 := by
  rw [toMat, Matrix.of_apply, List.getD_eq_getElem _ _ h, Fin.getElem_fin]


theorem toMat_eq_bId {B : List ℕ} {n : ℕ} {i j : Fin n} :
    toMat B n i j = bId ((B.getD i 0).testBit j) := rfl


theorem checkInvGo_true (hc : checkInvGo M i B) (hi' : i' < B.length) :
    invRowK B[i'] M = 1 <<< (i + i') := by
  induction B generalizing i i' with
  | nil => simp at hi'
  | cons b bs ih => cases i' <;> grind [ih (i := i + 1)]


theorem checkInv_isUnit (hBlen : B.length = n) (hMlen : M.length = n) (h : checkInv B M) :
    IsUnit (toMat B n) := by
  have key : toMat B n * toMat M n = 1 := by
    ext i k
    have hi : i.val < B.length := by grind
    have hrow : invRowK B[i.val] M = 1 <<< i.val := by simpa using checkInvGo_true h hi
    subst hMlen
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [toMat_eq_bId]
    rw [Fin.sum_univ_eq_sum_range
      (fun x ↦ bId ((B.getD i 0).testBit x) * bId ((M.getD x 0).testBit k)), ← bId_invRowK_testBit,
      List.getD_eq_getElem _ _ hi, hrow, Nat.one_shiftLeft]
    grind
  exact .of_mul_eq_one (toMat M n) key

end ECCompute.F2Invert
end M3
section M4





section

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R]


theorem negY_of_a₁_a₃_eq_zero (W : WeierstrassCurve R) (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0)
    {x y : R} : W.toAffine.negY x y = -y := by simp [negY, ha1, ha3]
grind_pattern negY_of_a₁_a₃_eq_zero => W.toAffine.negY x y

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Projective

variable {F : Type*} [Field F] {W : Projective F} {U V : Fin 3 → F}


theorem equiv_of_proportional (hU : W.Nonsingular U) (hV : W.Nonsingular V)
    (hprop : V 2 • U = U 2 • V) : U ≈ V := by
  have hcU0 := congrFun hprop 0
  have hcU1 := congrFun hprop 1
  simp only [Pi.smul_apply, smul_eq_mul] at hcU0 hcU1
  by_cases hUz : U 2 = 0
  · 
    have hVz : V 2 = 0 := by
      rw [nonsingular_of_Z_eq_zero hUz] at hU
      grind [mul_eq_zero]
    exact Setoid.trans (equiv_zero_of_Z_eq_zero hU hUz)
      (Setoid.symm (equiv_zero_of_Z_eq_zero hV hVz))
  · 
    have hVz : V 2 ≠ 0 := fun hVz ↦ by
      rw [nonsingular_of_Z_eq_zero hVz] at hV
      grind [mul_eq_zero]
    exact equiv_of_X_eq_of_Y_eq hUz hVz (by grind) (by grind)


theorem equiv_of_toAffine_eq (hU : W.Nonsingular U) (hV : W.Nonsingular V)
    (h : Point.toAffine W U = Point.toAffine W V) : U ≈ V := by
  classical
  have hUl : W.NonsingularLift ⟦U⟧ := (nonsingularLift_iff U).mpr hU
  have hVl : W.NonsingularLift ⟦V⟧ := (nonsingularLift_iff V).mpr hV
  have hmk : (⟨hUl⟩ : W.Point) = ⟨hVl⟩ := by
    apply (Point.toAffineAddEquiv W).injective
    rw [Point.toAffineAddEquiv_apply, Point.toAffineAddEquiv_apply,
      Point.toAffineLift_eq, Point.toAffineLift_eq]
    exact h
  exact Quotient.exact (congrArg Point.point hmk)

end WeierstrassCurve.Projective

namespace WeierstrassCurve

variable {F : Type*} [Field F] {W : WeierstrassCurve F}


theorem j_eq_iff [W.IsElliptic] {q : F} : W.j = q ↔ W.c₄ ^ 3 = W.Δ * q := by
  rw [j, Units.inv_mul_eq_iff_eq_mul, coe_Δ']


theorem isElliptic_of_Δ_ne_zero (hΔ : W.Δ ≠ 0) : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩

end WeierstrassCurve
end
end M4
section M5






open WeierstrassCurve

namespace WeierstrassCurve


def twoTorsionPoints (W : WeierstrassCurve ℚ) : Set W.toAffine.Point :=
  {P | P + P = 0}

@[simp]
lemma mem_twoTorsionPoints {W : WeierstrassCurve ℚ} {P : W.toAffine.Point} :
    P ∈ W.twoTorsionPoints ↔ P + P = 0 := Iff.rfl

end WeierstrassCurve

namespace ECCompute


def curve (a₂ a₄ a₆ : ℤ) : WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := a₂
  a₃ := 0
  a₄ := a₄
  a₆ := a₆

variable {a₂ a₄ a₆ : ℤ}


abbrev curveQ (a₂ a₄ a₆ : ℤ) : WeierstrassCurve ℚ :=
  (curve a₂ a₄ a₆)⁄ℚ


abbrev curveZMod (a₂ a₄ a₆ : ℤ) (p : ℕ) : WeierstrassCurve (ZMod p) :=
  (curve a₂ a₄ a₆)⁄(ZMod p)

section BaseChange
variable {R : Type*} [CommRing R] [Algebra ℤ R]


theorem curve_baseChange_eq :
    (curve a₂ a₄ a₆).baseChange R = ⟨0, a₂, 0, a₄, a₆⟩ := by
  ext <;> simp [curve, WeierstrassCurve.baseChange]


theorem curve_baseChange_addX {x₁ x₂ ℓ : R} :
    ((curve a₂ a₄ a₆).baseChange R).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - a₂ - x₁ - x₂ := by
  simp only [Affine.addX, curve_baseChange_eq]; grind
grind_pattern curve_baseChange_addX => ((curve a₂ a₄ a₆).baseChange R).toAffine.addX x₁ x₂ ℓ


theorem curve_baseChange_negY {x y : R} :
    ((curve a₂ a₄ a₆).baseChange R).toAffine.negY x y = -y :=
  Affine.negY_of_a₁_a₃_eq_zero _ (by simp [curve_baseChange_eq]) (by simp [curve_baseChange_eq])
grind_pattern curve_baseChange_negY => ((curve a₂ a₄ a₆).baseChange R).toAffine.negY x y


theorem curve_baseChange_addY {x₁ x₂ y₁ ℓ : R} :
    ((curve a₂ a₄ a₆).baseChange R).toAffine.addY x₁ x₂ y₁ ℓ
      = -(ℓ * (((curve a₂ a₄ a₆).baseChange R).toAffine.addX x₁ x₂ ℓ - x₁) + y₁) := by
  simp only [Affine.addY, Affine.negY, Affine.negAddY, curve_baseChange_eq]; grind
grind_pattern curve_baseChange_addY => ((curve a₂ a₄ a₆).baseChange R).toAffine.addY x₁ x₂ y₁ ℓ


theorem curve_baseChange_equation {x y : R}
    (h : ((curve a₂ a₄ a₆).baseChange R).toAffine.Equation x y) :
    y ^ 2 = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ := by grind [Affine.equation_iff, curve_baseChange_eq]
grind_pattern curve_baseChange_equation => ((curve a₂ a₄ a₆).baseChange R).toAffine.Equation x y

end BaseChange


def discrInt (a₂ a₄ a₆ : ℤ) : ℤ :=
  -(4 * a₂) ^ 2 * (4 * a₂ * a₆ - a₄ ^ 2) - 8 * (2 * a₄) ^ 3 - 27 * (4 * a₆) ^ 2 +
    9 * (4 * a₂) * (2 * a₄) * (4 * a₆)


theorem curveQ_Δ_num : (curveQ a₂ a₄ a₆).Δ.num = discrInt a₂ a₄ a₆ := by
  have : (curveQ a₂ a₄ a₆).Δ = discrInt a₂ a₄ a₆ := by
    simp only [Δ, b₂, b₄, b₆, b₈, curve_baseChange_eq, discrInt]; grind
  rw [this, Rat.num_intCast]


theorem map_curveQ : (curve a₂ a₄ a₆).map (Int.castRingHom ℚ) = curveQ a₂ a₄ a₆ := by
  rw [curveQ, baseChange, algebraMap_int_eq]

end ECCompute
end M5
section M6






open WeierstrassCurve

namespace ECCompute

section

open Classical in

public noncomputable def psi (p : ℕ) (a : ZMod p) : ZMod 2 := if IsSquare a then 0 else 1

variable {a₂ a₄ a₆ : ℤ} {p : ℕ}


def fval {R : Type*} [CommRing R] (a₂ a₄ a₆ θ : R) : R :=
  θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆


def fderiv {R : Type*} [CommRing R] (a₂ a₄ θ : R) : R :=
  3 * θ ^ 2 + 2 * a₂ * θ + a₄


public noncomputable def lambda (θ : ZMod p) :
    (curveQ a₂ a₄ a₆).toAffine.Point → ZMod 2
  | .zero => 0
  | .some x _ _ =>
    if (x.den : ZMod p) = 0 then 0
    else
      let α : ZMod p := x.num - θ * x.den
      if α = 0 then psi p (fderiv (a₂ : ZMod p) a₄ θ) else psi p α

@[simp]
theorem lambda_zero {θ : ZMod p} : lambda θ (0 : (curveQ a₂ a₄ a₆).toAffine.Point) = 0 := rfl
grind_pattern lambda_zero => lambda θ (0 : (curveQ a₂ a₄ a₆).toAffine.Point)




structure DescentHyp (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ZMod p) : Prop where
  
  prime : p.Prime
  
  ne_six : ¬ p ∣ 6
  
  discr : ((curveQ a₂ a₄ a₆).Δ.num : ZMod p) ≠ 0
  
  root : fval (a₂ : ZMod p) a₄ a₆ θ = 0

grind_pattern DescentHyp.discr => DescentHyp a₂ a₄ a₆ p θ
grind_pattern DescentHyp.root => DescentHyp a₂ a₄ a₆ p θ

end



section CommRing

variable {R : Type*} [CommRing R] {a₂ a₄ a₆ ℓ m x₁ x₂ x₃ θ : R}


structure Vieta (a₂ a₄ a₆ ℓ m x₁ x₂ x₃ : R) : Prop where
  σ₁ : x₁ + x₂ + x₃ = ℓ ^ 2 - a₂
  σ₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a₄ - 2 * ℓ * m
  σ₃ : x₁ * x₂ * x₃ = m ^ 2 - a₆

grind_pattern Vieta.σ₁ => Vieta a₂ a₄ a₆ ℓ m x₁ x₂ x₃
grind_pattern Vieta.σ₂ => Vieta a₂ a₄ a₆ ℓ m x₁ x₂ x₃
grind_pattern Vieta.σ₃ => Vieta a₂ a₄ a₆ ℓ m x₁ x₂ x₃


theorem cubic_sub_lineSq_eq_prod (hv : Vieta a₂ a₄ a₆ ℓ m x₁ x₂ x₃) {x : R} :
    fval a₂ a₄ a₆ x - (ℓ * x + m) ^ 2 = (x - x₁) * (x - x₂) * (x - x₃) := by
  grind [fval]


theorem prod_sub_theta_eq_lineSq (hv : Vieta a₂ a₄ a₆ ℓ m x₁ x₂ x₃)
    (hθ : fval a₂ a₄ a₆ θ = 0) :
    (x₁ - θ) * (x₂ - θ) * (x₃ - θ) = (ℓ * θ + m) ^ 2 := by
  grind [fval, cubic_sub_lineSq_eq_prod hv]


theorem vieta_of_double_root
    (hpt : (ℓ * x₁ + m) ^ 2 = fval a₂ a₄ a₆ x₁)
    (htan : fderiv a₂ a₄ x₁ = 2 * ℓ * (ℓ * x₁ + m))
    (hx₃ : x₃ = ℓ ^ 2 - a₂ - 2 * x₁) :
    Vieta a₂ a₄ a₆ ℓ m x₁ x₁ x₃ := by
  refine ⟨?_, ?_, ?_⟩ <;> grind [fval, fderiv]

end CommRing

section Field

variable {F : Type*} [Field F] {a₂ a₄ a₆ ℓ m x₁ x₂ x₃ θ : F}


theorem vieta_of_roots (hne : x₁ ≠ x₂)
    (hx₃ : x₃ = ℓ ^ 2 - a₂ - x₁ - x₂)
    (h₁ : (ℓ * x₁ + m) ^ 2 = fval a₂ a₄ a₆ x₁)
    (h₂ : (ℓ * x₂ + m) ^ 2 = fval a₂ a₄ a₆ x₂) :
    Vieta a₂ a₄ a₆ ℓ m x₁ x₂ x₃ := by
  refine ⟨?_, ?_, ?_⟩ <;> grind (ringSteps := 200000) [fval]


theorem fderiv_eq_prod (ℓ m : F) (hv : Vieta a₂ a₄ a₆ ℓ m x₁ x₂ x₃)
    (hθ : fval a₂ a₄ a₆ θ = 0) (h1 : x₁ = θ) :
    fderiv a₂ a₄ θ = (x₂ - θ) * (x₃ - θ) := by
  grind [fval, fderiv, cubic_sub_lineSq_eq_prod hv]

end Field



variable {a₂ a₄ a₆ : ℤ} {p : ℕ}

section Psi

variable {a b : ZMod p}


theorem psi_of_isSquare (ha : IsSquare a) : psi p a = 0 := if_pos ha


theorem psi_mul (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0) :
    psi p (a * b) = psi p a + psi p b := by
  have : Fact p.Prime := ⟨hp⟩
  
  have key : IsSquare (a * b) ↔ (IsSquare a ↔ IsSquare b) := by
    rw [← quadraticChar_one_iff_isSquare (by grind), ← quadraticChar_one_iff_isSquare ha,
      ← quadraticChar_one_iff_isSquare hb, map_mul]
    grind [quadraticChar_dichotomy]
  grind [psi]


theorem psi_mul_sq (hp : p.Prime) (hb : b ≠ 0) : psi p (b ^ 2 * a) = psi p a := by
  have : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne a 0 with rfl | ha
  · rw [mul_zero]
  · rw [psi_mul hp (pow_ne_zero 2 hb) ha, psi_of_isSquare ⟨b, by ring⟩, zero_add]

end Psi

variable {θ : ZMod p}


theorem psi_collinear (hp : p.Prime) {ℓ m x₁ x₂ x₃ : ZMod p}
    (hv : Vieta (a₂ : ZMod p) a₄ a₆ ℓ m x₁ x₂ x₃)
    (hroot : fval (a₂ : ZMod p) a₄ a₆ θ = 0)
    (hx₁ : x₁ ≠ θ) (hx₂ : x₂ ≠ θ) (hx₃ : x₃ ≠ θ) :
    psi p (x₁ - θ) + psi p (x₂ - θ) + psi p (x₃ - θ) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hpm : psi p ((x₁ - θ) * (x₂ - θ) * (x₃ - θ)) = 0 := by
    rw [prod_sub_theta_eq_lineSq hv hroot]; exact psi_of_isSquare ⟨ℓ * θ + m, by ring⟩
  rwa [psi_mul hp (by grind) (by grind), psi_mul hp (by grind) (by grind)] at hpm


theorem fderiv_ne_zero (h : DescentHyp a₂ a₄ a₆ p θ) : fderiv (a₂ : ZMod p) a₄ θ ≠ 0 := by
  intro hfd
  apply h.discr
  simp only [curveQ_Δ_num, discrInt]
  grind [fderiv, fval]

end ECCompute
end M6
section M7





namespace ECCompute


structure Certificate where
  
  a₂ : ℤ
  
  a₄ : ℤ
  
  a₆ : ℤ
  
  P : ℕ
  
  a₂r : ℕ
  
  a₄r : ℕ
  
  a₆r : ℕ
  
  Δ : ℤ
  
  ρ : ℕ
  
  points : List (ℚ × ℚ)
  
  labels : List (ℕ × ℤ)
  
  B : List Nat
  
  M : List Nat
  
  qrMasks : List Nat
  
  t : ℕ
  
  torsionPrime : ℕ


structure Certificate.Valid (c : Certificate) : Prop where
  
  lenP : c.points.length = c.ρ
  
  lenL : c.labels.length = c.ρ
  
  lenB : c.B.length = c.ρ
  
  lenM : c.M.length = c.ρ
  
  lenQ : c.qrMasks.length = c.ρ
  
  pts : checkPoints c.a₂ c.a₄ c.a₆ c.points
  
  primes : checkPrimes c.labels
  
  labels : checkLabels c.a₂ c.a₄ c.a₆ c.P c.a₂r c.a₄r c.a₆r c.Δ c.labels
  
  matrix : checkB c.a₂ c.a₄ c.labels c.qrMasks c.B c.points
  
  inv : F2Invert.checkInv c.B c.M
  
  tors : (curveQ c.a₂ c.a₄ c.a₆).twoTorsionPoints.ncard ≤ 2 ^ c.t

end ECCompute
end M7
section M8






section

open Module

namespace Module


lemma finrank_int_zero_of_finite {D : Type*} [AddCommGroup D] [Finite D] : finrank ℤ D = 0 := by
  have : Module.Finite ℤ D := Module.Finite.of_finite
  rw [finrank_eq_zero_iff_isTorsion, ← isAddTorsion_iff_isTorsion_int]
  exact isAddTorsion_of_finite


lemma finrank_prod_finite {F : Type*} [AddCommGroup F] [Module.Finite ℤ F]
    {D : Type*} [AddCommGroup D] [Finite D] :
    finrank ℤ (F × D) = finrank ℤ F := by
  have hkerD : finrank ℤ (LinearMap.ker (LinearMap.fst ℤ F D)) = 0 := by
    rw [LinearMap.ker_fst, ← (LinearEquiv.ofInjective (LinearMap.inr ℤ F D)
      LinearMap.inr_injective).finrank_eq, finrank_int_zero_of_finite]
  have key := Submodule.finrank_quotient_add_finrank (LinearMap.ker (LinearMap.fst ℤ F D))
  rw [hkerD, add_zero,
    (LinearMap.quotKerEquivOfSurjective _ LinearMap.fst_surjective).finrank_eq] at key
  exact key.symm

end Module

namespace LinearEquiv

variable {R : Type*} [CommRing R] {H K : Type*} [AddCommGroup H] [Module R H]
  [AddCommGroup K] [Module R K]


lemma map_range_lsmul (e : H ≃ₗ[R] K) (a : R) :
    (LinearMap.range (LinearMap.lsmul R H a)).map (e : H →ₗ[R] K) =
      LinearMap.range (LinearMap.lsmul R K a) := by
  ext z
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.lsmul_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨e y, by rw [map_smul]⟩
  · rintro ⟨w, rfl⟩
    exact ⟨a • e.symm w, ⟨e.symm w, rfl⟩, by rw [map_smul, e.apply_symm_apply]⟩


lemma map_torsionBy (e : H ≃ₗ[R] K) (a : R) :
    (Submodule.torsionBy R H a).map (e : H →ₗ[R] K) = Submodule.torsionBy R K a := by
  ext z
  simp only [Submodule.mem_map, Submodule.mem_torsionBy_iff, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← map_smul, hy, map_zero]
  · exact fun hz ↦ ⟨e.symm z, by rw [← map_smul, hz, map_zero], by simp⟩

end LinearEquiv

namespace Submodule

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (a : R)


def prodQuotEquiv (P : Submodule R M) (Q : Submodule R N) :
    HasQuotient.Quotient (M × N) (P.prod Q) ≃ₗ[R] (M ⧸ P) × (N ⧸ Q) := by
  refine LinearEquiv.ofLinearMap
    ((P.prod Q).liftQ (LinearMap.prodMap P.mkQ Q.mkQ) ?_)
    (LinearMap.coprod
      (P.liftQ ((P.prod Q).mkQ.comp (LinearMap.inl R M N)) ?_)
      (Q.liftQ ((P.prod Q).mkQ.comp (LinearMap.inr R M N)) ?_)) ?_ ?_
  · intro z hz
    simpa [LinearMap.mem_ker, Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero, Submodule.mem_prod]
      using hz
  · intro x hx
    simp [LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero, Submodule.mem_prod, hx]
  · intro y hy
    simp [LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero, Submodule.mem_prod, hy]
  · apply LinearMap.ext
    rintro ⟨a, b⟩
    induction a using Submodule.Quotient.induction_on with | H x =>
    induction b using Submodule.Quotient.induction_on with | H y =>
    simp [← Submodule.Quotient.mk_add]
  · apply LinearMap.ext
    intro z
    induction z using Submodule.Quotient.induction_on with | H xy =>
    obtain ⟨x, y⟩ := xy
    simp [← Submodule.Quotient.mk_add]


def prodSubtypeEquiv (S : Submodule R M) (T : Submodule R N) : ↥(S.prod T) ≃ ↥S × ↥T where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


lemma range_lsmul_prod :
    LinearMap.range (LinearMap.lsmul R (M × N) a) =
      (LinearMap.range (LinearMap.lsmul R M a)).prod (LinearMap.range (LinearMap.lsmul R N a)) := by
  have h : LinearMap.lsmul R (M × N) a =
      LinearMap.prodMap (LinearMap.lsmul R M a) (LinearMap.lsmul R N a) := by
    ext p <;> simp [LinearMap.lsmul_apply]
  rw [h, LinearMap.range_prodMap]


lemma torsionBy_prod :
    Submodule.torsionBy R (M × N) a =
      (Submodule.torsionBy R M a).prod (Submodule.torsionBy R N a) := by
  ext ⟨x, y⟩
  simp [Submodule.mem_torsionBy_iff, Submodule.mem_prod, Prod.smul_mk, Prod.ext_iff]


lemma natCard_torsionBy_prod :
    Nat.card (Submodule.torsionBy R (M × N) a) =
      Nat.card (Submodule.torsionBy R M a) * Nat.card (Submodule.torsionBy R N a) := by
  rw [torsionBy_prod, ← Nat.card_prod]
  exact Nat.card_congr (prodSubtypeEquiv _ _)

end Submodule

namespace ModN

variable {H : Type*} [AddCommGroup H] {n : ℕ}


lemma torsionBy_eq_ker : Submodule.torsionBy ℤ H n = LinearMap.ker (LinearMap.lsmul ℤ H n) := rfl

instance [NeZero n] [Module.Finite ℤ H] : Finite (Submodule.torsionBy ℤ H n) :=
  Module.finite_of_fg_torsion _
    (Submodule.torsionBy_isTorsion_nonZeroDivisor _ (by simp [NeZero.ne]))


lemma natCard_modN_of_finite (D : Type*) [AddCommGroup D] [Finite D] :
    Nat.card (ModN D n) = Nat.card (Submodule.torsionBy ℤ D n) := by
  set f := LinearMap.lsmul ℤ D (n : ℤ)
  have hquot : Nat.card (D ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have h1 : Nat.card D = Nat.card (D ⧸ LinearMap.ker f) * Nat.card (LinearMap.ker f) :=
    (LinearMap.ker f).toAddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
  have h2 : Nat.card D = Nat.card (ModN D n) * Nat.card (LinearMap.range f) :=
    (LinearMap.range f).toAddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
  rw [torsionBy_eq_ker]
  have hpos : Nat.card (LinearMap.range f) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0, by simp⟩, inferInstance⟩
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) ?_
  grind

variable {K : Type*} [AddCommGroup K]


lemma natCard_modN_congr (e : H ≃ₗ[ℤ] K) : Nat.card (ModN H n) = Nat.card (ModN K n) :=
  Nat.card_congr (Submodule.Quotient.equiv _ _ e (e.map_range_lsmul n)).toEquiv


lemma natCard_torsionBy_congr (e : H ≃ₗ[ℤ] K) :
    Nat.card (Submodule.torsionBy ℤ H n) = Nat.card (Submodule.torsionBy ℤ K n) := by
  rw [← e.map_torsionBy]
  exact Nat.card_congr (e.submoduleMap (Submodule.torsionBy ℤ H n)).toEquiv

section Prod

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]


lemma natCard_modN_prod :
    Nat.card (ModN (M × N) n) = Nat.card (ModN M n) * Nat.card (ModN N n) := by
  rw [← Nat.card_prod]
  exact Nat.card_congr
    (((Submodule.quotEquivOfEq _ _ (Submodule.range_lsmul_prod (n : ℤ))).toEquiv).trans
      (Submodule.prodQuotEquiv _ _).toEquiv)

end Prod


lemma natCard_torsionBy_eq_one_of_noZeroSMul [NeZero n] (F : Type*) [AddCommGroup F]
    [NoZeroSMulDivisors ℤ F] : Nat.card (Submodule.torsionBy ℤ F n) = 1 := by
  rw [(isSMulRegular_iff_torsionBy_eq_bot F (n : ℤ)).1
    (smul_right_injective F (by simp [NeZero.ne]))]
  exact Nat.card_unique


lemma natCard_modN_of_free_prod_finite [NeZero n]
    {F : Type*} [AddCommGroup F] [Module.Free ℤ F] [Module.Finite ℤ F] [NoZeroSMulDivisors ℤ F]
    {D : Type*} [AddCommGroup D] [Finite D] :
    Nat.card (ModN (F × D) n) =
      n ^ finrank ℤ F * Nat.card (Submodule.torsionBy ℤ (F × D) n) := by
  rw [natCard_modN_prod, Submodule.natCard_torsionBy_prod, ModN.natCard_eq F n,
    natCard_modN_of_finite D, natCard_torsionBy_eq_one_of_noZeroSMul F, one_mul]


theorem natCard_modN [NeZero n] [Module.Finite ℤ H] :
    Nat.card (ModN H n) = n ^ finrank ℤ H * Nat.card (Submodule.torsionBy ℤ H n) := by
  obtain ⟨m, ι, fι, p, hp, ee, ⟨iso⟩⟩ := Module.equiv_free_prod_directSum ℤ H
  set D := DirectSum ι fun i ↦ ℤ ⧸ (ℤ ∙ p i ^ ee i)
  have : ∀ i, NeZero (p i ^ ee i) := fun i ↦ ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have : ∀ i, Finite (ℤ ⧸ (ℤ ∙ (p i ^ ee i))) := fun i ↦
    inferInstanceAs (Finite (ℤ ⧸ Ideal.span {p i ^ ee i}))
  have : Finite D := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  calc Nat.card (ModN H n)
      = Nat.card (ModN ((Fin m →₀ ℤ) × D) n) := natCard_modN_congr iso
    _ = n ^ finrank ℤ (Fin m →₀ ℤ) *
          Nat.card (Submodule.torsionBy ℤ ((Fin m →₀ ℤ) × D) n) :=
        natCard_modN_of_free_prod_finite
    _ = n ^ finrank ℤ H * Nat.card (Submodule.torsionBy ℤ H n) := by
        rw [iso.finrank_eq.trans finrank_prod_finite, natCard_torsionBy_congr iso]

end ModN

end
end M8
section M9






open Module ModN

namespace RankDeduction

variable {ι H : Type*} [AddCommGroup H] [Module.Finite ℤ H] [Finite ι] {p : ℕ}


theorem card_le_finrank_modN (hp : p.Prime) (g : ι → H)
    (φ : H →+ (ι → ZMod p)) (hindep : LinearIndependent (ZMod p) (fun i ↦ φ (g i))) :
    Nat.card ι ≤ finrank (ZMod p) (ModN H p) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype ι := Fintype.ofFinite ι
  have hφ : ∀ h, p • φ h = 0 := fun h ↦ by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]
  set ψ : ModN H p →ₗ[ZMod p] (ι → ZMod p) := ModN.liftEquiv'.symm ⟨φ, hφ⟩
  have hψ : ∀ x, ψ (ModN.mkQ p x) = φ x := fun x ↦ rfl
  have hmk : LinearIndependent (ZMod p) (fun i ↦ ModN.mkQ p (g i)) :=
    LinearIndependent.of_comp ψ (by simpa only [Function.comp_def, hψ] using hindep)
  simpa using hmk.fintype_card_le_finrank


theorem rank_ge_le (hp : p.Prime) {t : ℕ} (g : ι → H)
    (φ : H →+ (ι → ZMod p)) (hindep : LinearIndependent (ZMod p) (fun i ↦ φ (g i)))
    (ht : Nat.card (Submodule.torsionBy ℤ H p) ≤ p ^ t) :
    Nat.card ι ≤ finrank ℤ H + t := by
  have : Fact p.Prime := ⟨hp⟩
  grw [card_le_finrank_modN hp g φ hindep, ← Nat.pow_le_pow_iff_right hp.one_lt]
  calc
    p ^ finrank (ZMod p) (ModN H p)
    _ = Nat.card (ZMod p) ^ finrank (ZMod p) (ModN H p) := by simp
    _ ≤ p ^ (finrank ℤ H + t) := by grw [← Module.natCard_eq_pow_finrank, natCard_modN, ht, pow_add]

end RankDeduction
end M9
section M10






namespace ECCompute

variable {cs : List ℤ} {ℓ r : ℕ}


theorem intResNat_cast {p : ℕ} {z : ℤ} (hp : p ≠ 0) : ((z % p).toNat : ZMod p) = z := by
  have hnn : 0 ≤ z % p := Int.emod_nonneg z (mod_cast hp)
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn, ZMod.intCast_eq_intCast_iff']
  exact Int.emod_emod_of_dvd z dvd_rfl

@[simp]
lemma polyEval_cons {c u : ℤ} : polyEval (c :: cs) u = c + u * polyEval cs u := by
  simp [polyEval]
grind_pattern polyEval_cons => polyEval (c :: cs) u

@[simp]
lemma polyModL_cons {c : ℤ} :
    polyModL (c :: cs) ℓ r = ((c % ℓ).toNat + r * polyModL cs ℓ r) % ℓ := by simp [polyModL]
grind_pattern polyModL_cons => polyModL (c :: cs) ℓ r


theorem polyModL_lt (hℓ : ℓ ≠ 0) : polyModL cs ℓ r < ℓ := by
  cases cs with
  | nil => exact hℓ.bot_lt
  | cons _ _ => exact Nat.mod_lt _ hℓ.bot_lt


theorem polyModL_cast (hl : ℓ ≠ 0) : (polyModL cs ℓ r : ZMod ℓ) = polyEval cs r := by
  induction cs with
  | nil => simp [polyModL, polyEval]
  | cons c t ih => simp [ih, intResNat_cast, hl]


theorem polyModL_beq (hℓ : 1 < ℓ) :
    (polyModL cs ℓ r).beq 0 ↔ (polyEval cs r : ZMod ℓ) = 0 := by
  rw [Nat.beq_eq, ← polyModL_cast (by lia), ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero,
    Nat.mod_eq_of_lt (polyModL_lt (by lia))]


theorem polyEval_modEq {a b : ℤ} (h : (a : ZMod ℓ) = b) :
    (polyEval cs a : ZMod ℓ) = polyEval cs b := by
  induction cs with
  | nil => rfl
  | cons c t ih =>
    rw [polyEval_cons, polyEval_cons]
    grind


theorem no_int_root_of_monicHasNoRootMod (hℓ : 1 < ℓ)
    (h : monicHasNoRootMod cs ℓ) (u : ℤ) : polyEval (cs ++ [1]) u ≠ 0 := by
  rw [monicHasNoRootMod, allBelow_iff] at h
  replace h : ∀ r < ℓ, (polyEval (cs ++ [1]) r : ZMod ℓ) ≠ 0 := by
    simp_rw [ne_eq, ← polyModL_beq hℓ, Bool.not_eq_true]
    grind
  intro hu
  have hℓ0 : (0 : ℤ) < ℓ := by positivity
  set r := u % ℓ with hr
  have hrℓ : r < ℓ := Int.emod_lt_of_pos u hℓ0
  refine h r.toNat (by grind) ?_
  rw [polyEval_modEq, hu, Int.cast_zero]
  simp [r, Int.emod_nonneg _ hℓ0.ne']



open Polynomial in

theorem exists_int_of_aeval_eq_zero {p : ℤ[X]} (hmonic : p.Monic) {x : ℚ}
    (hroot : p.aeval x = 0) : ∃ z : ℤ, (z : ℚ) = x := by
  obtain ⟨z, hz, -⟩ := exists_integer_of_is_root_of_monic hmonic hroot
  exact ⟨z, by simpa only [algebraMap_int_eq, eq_intCast] using hz.symm⟩

open Polynomial in

theorem no_rat_root_of_monicHasNoRootMod {b c : ℤ} (hℓ : 1 < ℓ)
    (h : monicHasNoRootMod [c, b] ℓ) {x : ℚ}
    (hx : x ^ 2 + b * x + c = 0) : False := by
  obtain ⟨z, hz⟩ :=
    exists_int_of_aeval_eq_zero (p := X ^ 2 + C b * X + C c) (by monicity!) (by simpa using hx)
  refine no_int_root_of_monicHasNoRootMod hℓ h z ?_
  have hQ : (polyEval [c, b, 1] z : ℚ) = 0 := by
    simp only [polyEval]
    grind
  exact mod_cast hQ

end ECCompute
end M10
section M11






namespace ECCompute

variable {a₂ a₄ a₆ : ℤ} {p : ℕ} {θ : ℤ}


theorem fval_iff (hp : 1 < p) :
    (polyModL [a₆, a₄, a₂, 1] p (θ.emod p).toNat).beq 0
      ↔ ((θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ : ℤ) : ZMod p) = 0 := by
  have hp0 : p ≠ 0 := by lia
  have hmod : (((θ.emod p).toNat : ℤ) : ZMod p) = θ := by
    rw [Int.cast_natCast]; exact intResNat_cast hp0
  have hpoly : polyEval [a₆, a₄, a₂, 1] θ = θ ^ 3 + a₂ * θ ^ 2 + a₄ * θ + a₆ := by grind [polyEval]
  rw [polyModL_beq hp, polyEval_modEq hmod, hpoly]




theorem discrIntK_eq : discrIntK a₂ a₄ a₆ = discrInt a₂ a₄ a₆ := by grind [discrIntK, discrInt]

@[simp]
theorem polyModK_cons {c : ℕ} {cs : List ℕ} {ℓ r : ℕ} :
    polyModK (c :: cs) ℓ r = (c % ℓ + r * polyModK cs ℓ r) % ℓ := rfl
grind_pattern polyModK_cons => polyModK (c :: cs) ℓ r


theorem polyModK_eq_polyModL {cs : List ℕ} {ℓ r : ℕ} :
    polyModK cs ℓ r = polyModL (cs.map Int.ofNat) ℓ r := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons]; grind [polyModL]




theorem resP_cast {P : ℕ} {a : ℤ} (hP : P ≠ 0) (hpP : p ∣ P) {r : ℕ}
    (hr : r = (a % P).toNat) : (((r % p : ℕ) : ℤ) : ZMod p) = a := by
  rw [Int.cast_natCast]
  have hnn : 0 ≤ a % P := Int.emod_nonneg a (by exact mod_cast hP)
  rw [ZMod.natCast_mod, hr, ← Int.cast_natCast, Int.toNat_of_nonneg hnn,
    ZMod.intCast_eq_intCast_iff']
  exact Int.emod_emod_of_dvd a (by exact mod_cast hpP)


theorem descentHyp_of_checkLabel {P a₂r a₄r a₆r : ℕ} {Δ : ℤ} (hP : P ≠ 0) (hpP : p ∣ P)
    (h₂ : a₂r = (a₂ % P).toNat) (h₄ : a₄r = (a₄ % P).toNat) (h₆ : a₆r = (a₆ % P).toNat)
    (hΔ : Δ = discrInt a₂ a₄ a₆) (h : checkLabel a₂r a₄r a₆r Δ p θ) (hp : p.Prime) :
    DescentHyp a₂ a₄ a₆ p θ := by
  have hp0 : 0 < p := hp.pos
  have hr₂' := resP_cast hP hpP h₂
  have hr₄' := resP_cast hP hpP h₄
  have hr₆' := resP_cast hP hpP h₆
  rw [checkLabel] at h
  simp only [Bool.and_eq_true, Nat.mod_eq_mod] at h
  obtain ⟨h6', hΔ', hf⟩ := h
  refine ⟨hp, ?_, ?_, ?_⟩
  · 
    grind [Nat.dvd_iff_mod_eq_zero]
  · 
    rw [curveQ_Δ_num, Ne, ← hΔ, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
    simpa [Int.beq'_eq] using hΔ'
  · 
    grind [fval_iff, fval, polyModK_eq_polyModL, polyModL_beq]


theorem descentHyp_of_checkLabels {labels : List (ℕ × ℤ)} {P a₂r a₄r a₆r : ℕ} {Δ : ℤ}
    (h : checkLabels a₂ a₄ a₆ P a₂r a₄r a₆r Δ labels) {l : ℕ × ℤ} (hl : l ∈ labels)
    (hp : l.1.Prime) : DescentHyp a₂ a₄ a₆ l.1 l.2 := by
  rw [checkLabels] at h
  simp only [Bool.and_eq_true, Nat.ble_eq, allList_iff, Nat.beq_eq,
    Int.beq'_eq] at h
  obtain ⟨hP, h₂, h₄, h₆, hΔ, hfold⟩ := h
  rw [discrIntK_eq] at hΔ
  obtain ⟨hpd, hchk⟩ := hfold l hl
  exact descentHyp_of_checkLabel (by lia) (Nat.dvd_of_mod_eq_zero (by grind)) h₂ h₄ h₆ hΔ hchk hp

end ECCompute
end M11
section M12





namespace ECCompute

open WeierstrassCurve

variable {a₂ a₄ a₆ : ℤ}


theorem checkPoint_iff {x y : ℚ} :
    checkPoint a₂ a₄ a₆ x y ↔ (curveQ a₂ a₄ a₆).toAffine.Equation x y := by
  have hD : (x.den : ℚ) ^ 3 * (y.den : ℚ) ^ 2 ≠ 0 := by positivity
  simp only [checkPoint, Int.beq'_eq, ← Int.cast_inj (α := ℚ), Int.mul_def, Int.cast_mul,
    Int.add_def, Int.cast_add, baseChange, curve, Affine.equation_iff]
  grind [Rat.mul_den_eq_num, Int.cast_natCast, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, eq_intCast]


theorem checkPoints_iff {pts : List (ℚ × ℚ)} :
    checkPoints a₂ a₄ a₆ pts ↔ ∀ p ∈ pts, (curveQ a₂ a₄ a₆).toAffine.Equation p.1 p.2 := by
  grind [checkPoints, checkPoint_iff]

end ECCompute
end M12
section M13






namespace ECCompute

section
variable {x : ℕ}

@[simp]
theorem passes_nil : passes x [] := rfl
grind_pattern passes_nil => passes x []

@[simp]
theorem passes_cons {a : ℕ} {t : List ℕ} :
    passes x (a :: t) = ((Nat.ble 1 (x % a)).or (x.ble a)).and (passes x t) := rfl
grind_pattern passes_cons => passes x (a :: t)


theorem passes_iff {L : List ℕ} : passes x L ↔ ∀ i ∈ L, x % i ≠ 0 ∨ x ≤ i := by
  induction L <;> grind
grind_pattern passes_iff => passes x L

end


theorem primes_below_23 {p : ℕ} (hlt : p < 23) (hp : p.Prime) :
    p ∈ [2, 3, 5, 7, 11, 13, 17, 19] := by decide +revert +kernel


theorem prime_of_passes {n : ℕ} (h2 : 2 ≤ n) (h529 : n < 529)
    (hpass : passes n [2, 3, 5, 7, 11, 13, 17, 19]) : n.Prime := by
  by_contra hnp
  have hn0 : 0 < n := by lia
  set p := n.minFac
  have hpp : p.Prime := Nat.minFac_prime (by lia)
  have hsq : p ^ 2 ≤ n := Nat.minFac_sq_le_self hn0 hnp
  have hplt23 : p < 23 := lt_of_pow_lt_pow_left' 2 (by grind)
  have hpmem : p ∈ [2, 3, 5, 7, 11, 13, 17, 19] := primes_below_23 hplt23 hpp
  have hpltn : p < n := by nlinarith [hpp.two_le, hsq]
  rcases (passes_iff.mp hpass) p hpmem with hmod | hle
  · exact hmod (Nat.dvd_iff_mod_eq_zero.mp (Nat.minFac_dvd n))
  · lia


theorem checkPrimes_true {ls : List (ℕ × ℤ)} (h : checkPrimes ls) : ∀ l ∈ ls, l.1.Prime := by
  grind [checkPrimes, checkPrime, prime_of_passes]

end ECCompute
end M13
section M14






namespace ECCompute

variable {p a : ℕ} {a₂ a₄ a₆ : ℤ}




def qrLookupBool (qm a : ℕ) : Bool := ((qm.shiftRight a).land 1).beq 1


theorem shiftRight_land_one_eq_one_iff {m : ℕ} : (m >>> a) &&& 1 = 1 ↔ m.testBit a := by
  grind [Nat.shiftRight_eq_div_pow]


@[simp]
theorem qrMaskGo_succ {k : ℕ} :
    qrMaskGo p (k + 1) = qrMaskGo p k ||| 1 <<< ((k + 1) * (k + 1) % p) := rfl
grind_pattern qrMaskGo_succ => qrMaskGo p (k + 1)


theorem testBit_qrMaskGo {f : ℕ} :
    (qrMaskGo p f).testBit a ↔ ∃ j, 1 ≤ j ∧ j ≤ f ∧ j * j % p = a := by
  induction f with
  | zero => simp [qrMaskGo]
  | succ k ih =>
    rw [qrMaskGo_succ, Nat.testBit_lor, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow,
      Bool.or_eq_true, ih, decide_eq_true_eq]
    constructor
    · rintro (⟨j, hj1, hjk, hja⟩ | hb)
      · exact ⟨j, by lia⟩
      · exact ⟨k + 1, by lia⟩
    · rintro ⟨j, hj1, hjk, hja⟩
      obtain h | rfl : j < k + 1 ∨ j = k + 1 := by lia
      · exact Or.inl ⟨j, by lia⟩
      · grind
grind_pattern testBit_qrMaskGo => (qrMaskGo p f).testBit a


theorem exists_sq_iff (hp : p.Prime) (hp2 : p ≠ 2) (ha : a < p) :
    (∃ j, 1 ≤ j ∧ j ≤ (p - 1) / 2 ∧ j * j % p = a) ↔ a ≠ 0 ∧ IsSquare (a : ZMod p) := by
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  constructor
  · rintro ⟨j, hj1, hjk, hja⟩
    have hjp : j < p := by lia
    have hcast : (a : ZMod p) = j * j := by
      rw [← Nat.cast_mul, ← hja, ZMod.natCast_mod, Nat.cast_mul]
    refine ⟨?_, ⟨j, hcast⟩⟩
    rintro rfl
    exact (Nat.le_of_dvd (by lia) (by grind [hp.dvd_mul, Nat.dvd_of_mod_eq_zero hja])).not_gt hjp
  · rintro ⟨ha0, ⟨x, hx⟩⟩
    have hxne : x ≠ 0 := by
      rintro rfl
      exact ha0 (Nat.eq_zero_of_dvd_of_lt (by grind [ZMod.natCast_eq_zero_iff]) ha)
    have : NeZero p := ⟨by lia⟩
    wlog hx' : x.val ≤ (p - 1) / 2 generalizing x
    · exact this (-x) (by grind) (by grind) (by grind [ZMod.neg_val])
    have haeq : x.val * x.val % p = a := by
      have hc : (a : ZMod p) = (x.val * x.val : ℕ) := by rw [Nat.cast_mul, x.natCast_zmod_val, hx]
      grind [Nat.mod_eq_of_lt ha, ZMod.natCast_eq_natCast_iff']
    exact ⟨x.val, by grind [ZMod.val_eq_zero], hx', haeq⟩


theorem qrMask_testBit (hp2 : p ≠ 2) (hp : p.Prime) (ha : a < p) :
    qrMask p >>> a &&& 1 = 1 ↔ a ≠ 0 ∧ IsSquare (a : ZMod p) := by
  rw [shiftRight_land_one_eq_one_iff, qrMask, testBit_qrMaskGo]
  exact exists_sq_iff hp hp2 ha


theorem qrLookupBool_iff (hp2 : p ≠ 2) (hp : p.Prime) (ha : a < p) :
    qrLookupBool (qrMask p) a ↔ (a ≠ 0 ∧ IsSquare (a : ZMod p)) := by
  grind [qrLookupBool, qrMask_testBit]

variable {θ : ZMod p}


theorem mask_eq_psi (hp : p.Prime) (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    (if qrLookupBool (qrMask p) a.val then 0 else 1) = psi p a := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have ha0 : a.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
  simp [qrLookupBool_iff hp2 hp (ZMod.val_lt a), ha0, psi]



section
variable {tval xp xm xden : ℕ}


theorem alphaResK_cast (hp : p ≠ 0) :
    (alphaResK p tval xp xm xden : ZMod p) = xp - (xm + tval * xden) := by
  simp only [alphaResK, Nat.mod_eq_mod, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, ZMod.natCast_mod,
    Nat.cast_add, Nat.cast_sub (Nat.mod_lt _ hp.bot_lt).le, ZMod.natCast_self, Nat.cast_mul]
  ring


theorem alphaResK_eq_val (hp : p ≠ 0) {x : ℚ}
    (htval : tval = θ) (hxnum : x.num = xp - xm) (hxden : xden = x.den) :
    alphaResK p tval xp xm xden = (x.num - θ * x.den).val := by
  have hcast : (alphaResK p tval xp xm xden : ZMod p) = x.num - θ * x.den := by
    rw [alphaResK_cast hp, ← htval, ← hxden]
    have : (x.num : ZMod p) = xp - xm := by rw [hxnum]; push_cast; ring
    grind
  have hlt : alphaResK p tval xp xm xden < p := Nat.mod_lt _ hp.bot_lt
  rw [← hcast, ZMod.val_cast_of_lt hlt]


theorem fderivResK_cast (hp : p ≠ 0) (htval : tval = θ) :
    (fderivResK a₂ a₄ p tval : ZMod p) = fderiv (a₂ : ZMod p) a₄ θ := by
  simp only [fderivResK]
  rw [polyModL_cast hp]
  simp only [polyEval, Int.add_def, Int.mul_def]
  subst htval
  rw [fderiv]
  push_cast
  ring


theorem fderivResK_eq_val (hp : p ≠ 0) (htval : tval = θ) :
    fderivResK a₂ a₄ p tval = (fderiv (a₂ : ZMod p) a₄ θ).val := by
  have hlt : fderivResK a₂ a₄ p tval < p := by simp only [fderivResK]; exact polyModL_lt hp
  rw [← fderivResK_cast hp htval, ZMod.val_cast_of_lt hlt]


theorem lambdaBitK_eq_zero_or_one {qm : ℕ} :
    lambdaBitK a₂ a₄ p qm tval xp xm xden = 0 ∨ lambdaBitK a₂ a₄ p qm tval xp xm xden = 1 := by
  simp only [lambdaBitK, Bool.rec_eq, Nat.shiftRight_eq', Nat.land_eq, Nat.xor_eq,
    Nat.mod_eq_mod, Nat.beq_eq_beq, Nat.and_one_is_mod]
  grind [Nat.mod_two_eq_zero_or_one]


theorem lambdaBitK_eq (hyp : DescentHyp a₂ a₄ a₆ p θ) {x y : ℚ}
    (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y)
    (htval : tval = θ) (hxnum : x.num = xp - xm) (hxden : xden = x.den) :
    (lambdaBitK a₂ a₄ p (qrMask p) tval xp xm xden : ZMod 2) = lambda θ (.some x y h) := by
  have hp : p ≠ 0 := hyp.prime.ne_zero
  have hp2 : p ≠ 2 := fun hp ↦ hyp.ne_six (hp ▸ ⟨3, rfl⟩)
  have halpha := alphaResK_eq_val hp htval hxnum hxden
  have hden : xden % p = 0 ↔ (x.den : ZMod p) = 0 := by
    rw [hxden, ← Nat.dvd_iff_mod_eq_zero, ZMod.natCast_eq_zero_iff]
  have key (a : ℕ) : ((qrMask p >>> a % 2 ^^^ 1 : ℕ) : ZMod 2) =
      if qrLookupBool (qrMask p) a then 0 else 1 := by
    have hbit : (qrMask p >>> a % 2 ^^^ 1 : ℕ) = if qrLookupBool (qrMask p) a then 0 else 1 := by
      grind [qrLookupBool, Nat.mod_two_eq_zero_or_one]
    rw [hbit]
    simp only [apply_ite (Nat.cast : ℕ → ZMod 2), Nat.cast_zero, Nat.cast_one]
  simp only [lambdaBitK, Bool.rec_eq, Nat.shiftRight_eq', Nat.land_eq, Nat.xor_eq,
    Nat.mod_eq_mod, Nat.beq_eq_beq, Nat.and_one_is_mod, apply_ite (Nat.cast : ℕ → ZMod 2),
    Nat.cast_zero, key]
  rw [lambda]
  grind [mask_eq_psi, hyp.prime, ZMod.val_eq_zero, fderivResK_eq_val, fderiv_ne_zero]

end

end ECCompute
end M14
section M15






namespace ECCompute

variable {a₂ a₄ : ℤ} {xnp xnm xden b : ℕ} {ls : List (ℕ × ℕ × ℕ)} {B : List ℕ}
  {pt : List (ℚ × ℚ)}

@[simp]
theorem checkBRowWord_nil : checkBRowWord a₂ a₄ xnp xnm xden [] = 0 := rfl
grind_pattern checkBRowWord_nil => checkBRowWord a₂ a₄ xnp xnm xden []

@[simp]
theorem checkBRowWord_cons {l : ℕ × ℕ × ℕ} :
    checkBRowWord a₂ a₄ xnp xnm xden (l :: ls) =
      lambdaBitK a₂ a₄ l.1 l.2.2 l.2.1 xnp xnm xden |||
        checkBRowWord a₂ a₄ xnp xnm xden ls <<< 1 := rfl
grind_pattern checkBRowWord_cons => checkBRowWord a₂ a₄ xnp xnm xden (l :: ls)

@[simp]
theorem checkBGo_cons_cons {bs : List ℕ} {p : ℚ × ℚ} {ps : List (ℚ × ℚ)} :
    checkBGo a₂ a₄ ls (b :: bs) (p :: ps) =
      (checkBRow a₂ a₄ p.1.num.toNat (-p.1.num).toNat p.1.den b ls).and
        (checkBGo a₂ a₄ ls bs ps) := rfl
grind_pattern checkBGo_cons_cons => checkBGo a₂ a₄ ls (b :: bs) (p :: ps)

variable {i j : ℕ}


theorem testBit_checkBRowWord (hj : j < ls.length) :
    (checkBRowWord a₂ a₄ xnp xnm xden ls).testBit j ↔
      lambdaBitK a₂ a₄ ls[j].1 ls[j].2.2 ls[j].2.1 xnp xnm xden = 1 := by
  induction ls generalizing j with
  | nil => simp at hj
  | cons l ls ih =>
    cases j with
    | zero =>
      rw [checkBRowWord_cons, Nat.testBit_or, Nat.testBit_shiftLeft, List.getElem_cons_zero]
      grind [lambdaBitK_eq_zero_or_one]
    | succ k =>
      rw [checkBRowWord_cons, Nat.testBit_or, Nat.testBit_shiftLeft, List.getElem_cons_succ,
        Nat.add_sub_cancel]
      obtain hb | hb := lambdaBitK_eq_zero_or_one (a₂ := a₂) (a₄ := a₄) (p := l.1) (qm := l.2.2)
        (tval := l.2.1) (xp := xnp) (xm := xnm) (xden := xden) <;>
        simp [hb, Nat.testBit_succ, ih (by simpa using hj)]


theorem checkBRow_true (hb : checkBRow a₂ a₄ xnp xnm xden b ls) (hj : j < ls.length) :
    b.testBit j ↔ lambdaBitK a₂ a₄ ls[j].1 ls[j].2.2 ls[j].2.1 xnp xnm xden = 1 := by
  grind [checkBRow, testBit_checkBRowWord]


theorem checkBGo_row (h : checkBGo a₂ a₄ ls B pt) (hi : i < B.length) (hip : i < pt.length) :
    checkBRow a₂ a₄ pt[i].1.num.toNat (-pt[i].1.num).toNat pt[i].1.den B[i] ls := by
  induction B generalizing pt i with grind [cases List]


theorem checkB_true {ρ : ℕ} {ls : List (ℕ × ℤ)} {q : List ℕ}
    (hBlen : B.length = ρ) (hplen : pt.length = ρ) (hllen : ls.length = ρ)
    (hqlen : q.length = ρ)
    (h : checkB a₂ a₄ ls q B pt) (i j : Fin ρ) :
    F2Invert.toMat B ρ i j =
      (lambdaBitK a₂ a₄ ls[j].1 (qrMask ls[j].1) (ls[j].2 % ls[j].1).toNat
        pt[i].1.num.toNat (-pt[i].1.num).toNat pt[i].1.den : ZMod 2) := by
  rw [checkB, Bool.and_eq_true] at h
  set ns := toLs ls q with hnsdef
  have hns : ns.length = ρ := by rw [hnsdef, toLs, List.length_zipWith, hllen, hqlen, Nat.min_self]
  have hgetN : ns[j] = (ls[j].1, (ls[j].2 % ls[j].1).toNat, q[j]) := by simp [hnsdef, toLs]
  obtain ⟨hmask, hgo⟩ := h
  
  have hqok : qrMask ls[j].1 = q[j] := by
    have : qrMask ns[j].1 = ns[j].2.2 := by grind [checkMaskList, List.getElem_mem]
    rwa [hgetN] at this
  
  have hrow := checkBGo_row (i := i) hgo (by lia) (by lia)
  have hcell : (B[i] : ℕ).testBit j ↔ _ := checkBRow_true hrow (by lia)
  simp only [← Fin.getElem_fin] at hcell
  simp only [hgetN] at hcell
  rw [F2Invert.toMat_apply (by lia), hqok]
  obtain hb | hb := lambdaBitK_eq_zero_or_one (a₂ := a₂) (a₄ := a₄) (p := ls[j].1) (qm := q[j])
    (tval := (ls[j].2 % ls[j].1).toNat) (xp := pt[i].1.num.toNat) (xm := (-pt[i].1.num).toNat)
    (xden := pt[i].1.den) <;> simp [-Fin.getElem_fin, hcell, hb]

end ECCompute
end M15
section M16





section

open Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)


lemma eval_twoTorsionPolynomial_toPoly {x : F} :
    W.twoTorsionPolynomial.toPoly.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [twoTorsionPolynomial, Cubic.toPoly]
grind_pattern eval_twoTorsionPolynomial_toPoly => W.twoTorsionPolynomial.toPoly.eval x


theorem Y_eq_negY_of_add_self [DecidableEq F] {x y : F} (h : W.toAffine.Nonsingular x y)
    (hP : (Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h = 0) :
    y = W.toAffine.negY x y := by
  by_contra hne
  rw [Affine.Point.add_self_of_Y_ne hne] at hP
  exact Affine.Point.some_ne_zero _ hP


theorem isRoot_twoTorsionPolynomial_of_add_self [DecidableEq F] {x y : F}
    (h : W.toAffine.Nonsingular x y)
    (hP : (Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h = 0) :
    W.twoTorsionPolynomial.toPoly.IsRoot x := by
  rw [IsRoot.def, eval_twoTorsionPolynomial_toPoly, b₂, b₄, b₆]
  have hy : y = W.toAffine.negY x y := Y_eq_negY_of_add_self W h hP
  rw [Affine.negY] at hy
  have he : 2 * y + W.a₁ * x + W.a₃ = 0 := by linear_combination hy
  have heq := h.left
  rw [Affine.equation_iff] at heq
  linear_combination (2 * y + W.a₁ * x + W.a₃) * he - 4 * heq


theorem isRoot_twoTorsionPolynomial_iff [DecidableEq F] (h2 : (2 : F) ≠ 0) (hΔ : W.Δ ≠ 0)
    {x : F} :
    W.twoTorsionPolynomial.toPoly.IsRoot x ↔
      ∃ y, ∃ h : W.toAffine.Nonsingular x y,
        (Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h = 0 := by
  refine ⟨fun hroot ↦ ?_, fun ⟨y, hns, hP⟩ ↦ isRoot_twoTorsionPolynomial_of_add_self W hns hP⟩
  have h4 : (4 : F) ≠ 0 := by
    have h22 : (4 : F) = 2 * 2 := by norm_num
    rw [h22]
    exact mul_ne_zero h2 h2
  rw [IsRoot.def, eval_twoTorsionPolynomial_toPoly, b₂, b₄, b₆] at hroot
  obtain ⟨y, he⟩ : ∃ y : F, 2 * y + W.a₁ * x + W.a₃ = 0 :=
    ⟨(-W.a₁ * x - W.a₃) / 2, by field_simp; ring⟩
  have heq : W.toAffine.Equation x y := by
    rw [Affine.equation_iff]
    have h4G : (4 : F) * (y ^ 2 + W.a₁ * x * y + W.a₃ * y
        - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) = 0 := by
      linear_combination (2 * y + W.a₁ * x + W.a₃) * he - hroot
    linear_combination (mul_eq_zero.mp h4G).resolve_left h4
  exact ⟨y, (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp heq,
    Affine.Point.add_self_of_Y_eq (by rw [Affine.negY]; linear_combination he)⟩

end WeierstrassCurve

end
end M16
section M17






namespace ECCompute

open WeierstrassCurve Affine Polynomial

variable {a₂ a₄ a₆ : ℤ}




lemma polyEval_monicCubic_cast {b c d r : ℤ} :
    (polyEval [d, c, b, 1] r : ℚ) = r ^ 3 + b * r ^ 2 + c * r + d := by
  simp only [polyEval]
  grind


theorem twoTorsion_y_eq_zero_and_root {x y : ℚ}
    (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hP : Point.some x y h ∈ (curveQ a₂ a₄ a₆).twoTorsionPoints) :
    y = 0 ∧ x ∈ (⟨1, a₂, a₄, a₆⟩ : Cubic ℚ).roots := by
  have hmonic : (⟨1, a₂, a₄, a₆⟩ : Cubic ℚ).toPoly.Monic := Cubic.monic_of_a_eq_one' ..
  have hy : y = (curveQ a₂ a₄ a₆).toAffine.negY x y := Y_eq_negY_of_add_self (curveQ a₂ a₄ a₆) h hP
  have hy0 : y = 0 := by grind [negY, curve_baseChange_eq]
  refine ⟨hy0, ?_⟩
  rw [Cubic.mem_roots_iff hmonic.ne_zero]
  grind [curve_baseChange_equation, h.1]


theorem twoTorsion_xcoord_mem_roots (x y : ℚ)
    (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hP : Point.some x y h ∈ (curveQ a₂ a₄ a₆).twoTorsionPoints) :
    x ∈ (⟨1, a₂, a₄, a₆⟩ : Cubic ℚ).roots.toFinset :=
  Multiset.mem_toFinset.mpr (twoTorsion_y_eq_zero_and_root h hP).2


theorem card_twoTorsion_le_of_xcoords {Sx : Finset ℚ}
    (hx : ∀ (x y : ℚ) (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y),
        Point.some x y h + Point.some x y h = 0 → x ∈ Sx) :
    (curveQ a₂ a₄ a₆).twoTorsionPoints.Finite ∧
      (curveQ a₂ a₄ a₆).twoTorsionPoints.ncard ≤ Sx.card + 1 := by
  classical
  set W := curveQ a₂ a₄ a₆
  set T : Set W.toAffine.Point := W.twoTorsionPoints with hT
  set ι : W.toAffine.Point → Option ℚ := fun
    | .zero => none
    | .some x _ _ => some x with hιdef
  set S : Finset (Option ℚ) := Sx.insertNone with hS
  have hinj : Set.InjOn ι T := by
    intro P hP P' hP' hEq
    obtain _ | ⟨x, y, h⟩ := P
    · grind
    obtain _ | ⟨x', y', h'⟩ := P'
    · simp [hιdef] at hEq
    simp only [hιdef, Option.some.injEq] at hEq
    subst hEq
    obtain ⟨rfl, _⟩ := twoTorsion_y_eq_zero_and_root h hP
    obtain ⟨rfl, _⟩ := twoTorsion_y_eq_zero_and_root h' hP'
    rfl
  have himg : ι '' T ⊆ S := by
    rintro o ⟨P, hP, rfl⟩
    obtain _ | ⟨x, y, h⟩ := P
    · simp [hιdef, hS]
    · simp only [hιdef, hS, Finset.mem_coe, Finset.some_mem_insertNone]
      exact hx x y h hP
  refine ⟨Set.Finite.of_finite_image (S.finite_toSet.subset himg) hinj, ?_⟩
  rw [← hinj.ncard_image]
  grw [Set.ncard_le_ncard himg S.finite_toSet, Set.ncard_coe_finset S, Finset.card_insertNone Sx]


instance : Finite (curveQ a₂ a₄ a₆).twoTorsionPoints :=
  (card_twoTorsion_le_of_xcoords twoTorsion_xcoord_mem_roots).1.to_subtype



variable {ℓ : ℕ} {R : ℤ}




theorem card_twoTorsion_le_one_of_monicHasNoRootMod (hℓ : 1 < ℓ)
    (h : monicHasNoRootMod [64 * a₆, 16 * a₄, 4 * a₂] ℓ) :
    (curveQ a₂ a₄ a₆).twoTorsionPoints.ncard ≤ 1 := by
  suffices ∀ (x y : ℚ) (hns : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y),
      Point.some x y hns + Point.some x y hns = 0 → x ∈ (∅ : Finset ℚ) by
    simpa using (card_twoTorsion_le_of_xcoords this).2
  intro x y hns hP
  obtain ⟨hy0, -⟩ := twoTorsion_y_eq_zero_and_root hns hP
  have hxr : x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ = 0 := by grind [curve_baseChange_equation hns.1]
  
  obtain ⟨z, hz⟩ := exists_int_of_aeval_eq_zero (p := X ^ 3 + C a₂ * X ^ 2 + C a₄ * X + C a₆)
    (by monicity!) (by simpa using hxr)
  
  refine (no_int_root_of_monicHasNoRootMod hℓ h (4 * z) ?_).elim
  have hQ : (polyEval [64 * a₆, 16 * a₄, 4 * a₂, 1] (4 * z) : ℚ) = 0 := by
    grind [polyEval_monicCubic_cast]
  exact mod_cast hQ




theorem card_twoTorsion_le_two_of_root_cofactor
    (hR : polyEval [a₆, a₄, a₂, 1] R = 0) (hℓ : 1 < ℓ)
    (hq : monicHasNoRootMod [a₄ + R * (a₂ + R), a₂ + R] ℓ) :
    (curveQ a₂ a₄ a₆).twoTorsionPoints.ncard ≤ 2 := by
  suffices ∀ (x y : ℚ) (hns : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y),
      Point.some x y hns + Point.some x y hns = 0 → x ∈ ({(R : ℚ)} : Finset ℚ) by
    simpa using (card_twoTorsion_le_of_xcoords this).2
  
  intro x y hns hP
  obtain ⟨-, hroot⟩ := twoTorsion_y_eq_zero_and_root _ hP
  rw [Cubic.mem_roots_iff (Cubic.monic_of_a_eq_one' ..).ne_zero] at hroot
  have hRQ : (R : ℚ) ^ 3 + a₂ * R ^ 2 + a₄ * R + a₆ = 0 := by
    rw [← polyEval_monicCubic_cast]
    exact mod_cast hR
  grind [no_rat_root_of_monicHasNoRootMod]




theorem certTorsionBound_zero (hp : Nat.blt 1 ℓ)
    (h : monicHasNoRootMod [64 * a₆, 16 * a₄, 4 * a₂] ℓ) :
    (curveQ a₂ a₄ a₆).twoTorsionPoints.ncard ≤ 2 ^ 0 :=
  card_twoTorsion_le_one_of_monicHasNoRootMod (by simpa using hp) h


theorem certTorsionBound_one (hp : Nat.blt 1 ℓ)
    (hR : (polyEval [a₆, a₄, a₂, 1] R).beq' 0)
    (hq : monicHasNoRootMod [a₄ + R * (a₂ + R), a₂ + R] ℓ) :
    (curveQ a₂ a₄ a₆).twoTorsionPoints.ncard ≤ 2 ^ 1 :=
  card_twoTorsion_le_two_of_root_cofactor (by simpa [Int.beq'_eq] using hR) (by simpa using hp) hq


theorem certTorsionBound_two : (curveQ a₂ a₄ a₆).twoTorsionPoints.ncard ≤ 2 ^ 2 := by
  change (curveQ a₂ a₄ a₆).twoTorsionPoints.ncard ≤ 4
  grw [(card_twoTorsion_le_of_xcoords twoTorsion_xcoord_mem_roots).2, Cubic.card_roots_le]

end ECCompute
end M17
section M18







section

namespace Rat

variable {p : ℕ}


theorem mem_padicInteger_iff [Fact p.Prime] {x : ℚ} :
    x ∈ (Rat.padicValuation p).integer ↔ (x.den : ZMod p) ≠ 0 := by
  rw [Valuation.mem_integer_iff, Rat.padicValuation_le_one_iff, Ne, ZMod.natCast_eq_zero_iff]

variable {x y : ℚ}


theorem den_add_ne_zero (hp : p.Prime) (hx : (x.den : ZMod p) ≠ 0)
    (hy : (y.den : ZMod p) ≠ 0) : ((x + y).den : ZMod p) ≠ 0 :=
  have : Fact p.Prime := ⟨hp⟩
  mem_padicInteger_iff.mp (add_mem (mem_padicInteger_iff.mpr hx) (mem_padicInteger_iff.mpr hy))


theorem den_sub_ne_zero (hp : p.Prime) (hx : (x.den : ZMod p) ≠ 0)
    (hy : (y.den : ZMod p) ≠ 0) : ((x - y).den : ZMod p) ≠ 0 :=
  have : Fact p.Prime := ⟨hp⟩
  mem_padicInteger_iff.mp (sub_mem (mem_padicInteger_iff.mpr hx) (mem_padicInteger_iff.mpr hy))


theorem den_mul_ne_zero (hp : p.Prime) (hx : (x.den : ZMod p) ≠ 0)
    (hy : (y.den : ZMod p) ≠ 0) : ((x * y).den : ZMod p) ≠ 0 :=
  have : Fact p.Prime := ⟨hp⟩
  mem_padicInteger_iff.mp (mul_mem (mem_padicInteger_iff.mpr hx) (mem_padicInteger_iff.mpr hy))


theorem den_pow_ne_zero (hp : p.Prime) (hx : (x.den : ZMod p) ≠ 0) (n : ℕ) :
    ((x ^ n).den : ZMod p) ≠ 0 :=
  have : Fact p.Prime := ⟨hp⟩
  mem_padicInteger_iff.mp (pow_mem (mem_padicInteger_iff.mpr hx) n)


end Rat

end
end M18
section M19






open WeierstrassCurve

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ}


theorem den_isSquare {x y : ℚ} (h : (curveQ a₂ a₄ a₆).toAffine.Equation x y) :
    ∃ w : ℕ, x.den = w ^ 2 ∧ y.den = w ^ 3 := by
  set N : ℤ := x.num ^ 3 + x.den * (a₂ * x.num ^ 2 + a₄ * x.num * x.den + a₆ * x.den ^ 2)
  have key : y.num ^ 2 * x.den ^ 3 = y.den ^ 2 * N := by
    qify [N]
    grind [x.mul_den_eq_num, y.mul_den_eq_num]
  have h₁ : IsCoprime ↑x.den N := x.isCoprime_num_den.symm.pow_right.add_mul_left_right _
  have heq : (x.den : ℤ) ^ 3 = y.den ^ 2 := Int.dvd_antisymm (by positivity) (by positivity)
    (h₁.pow_left.dvd_of_dvd_mul_left ⟨y.num ^ 2, by grind⟩)
    (y.isCoprime_num_den.symm.pow.dvd_of_dvd_mul_left ⟨N, key⟩)
  exact Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow (by grind) (mod_cast heq)



public noncomputable def xbar (p : ℕ) [Fact p.Prime] (x : ℚ) : ZMod p := (x : ZMod p)

variable {p : ℕ}


theorem ydenom_eq_zero_iff (hp : p.Prime) {x y : ℚ}
    (h : (curveQ a₂ a₄ a₆).toAffine.Equation x y) :
    (y.den : ZMod p) = 0 ↔ (x.den : ZMod p) = 0 := by
  obtain ⟨w, hxw, hyw⟩ := den_isSquare h
  simp only [ZMod.natCast_eq_zero_iff]
  grind [hp.prime.dvd_pow_iff_dvd]

end ECCompute
end M19
section M20





open WeierstrassCurve Projective

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ}




def intRep (x y : ℚ) (w : ℕ) : Fin 3 → ℤ := ![x.num * w, y.num, w ^ 3]


theorem map_curve_toProjective :
    (curve a₂ a₄ a₆).toProjective.map (Int.castRingHom ℚ) = (curveQ a₂ a₄ a₆).toProjective :=
  map_curveQ

variable {x y : ℚ} {w : ℕ}


theorem intRep_map_ℚ (hxden : x.den = w ^ 2) (hyden : y.den = w ^ 3) :
    Int.castRingHom ℚ ∘ intRep x y w = (w ^ 3 : ℚ) • ![x, y, 1] := by
  simp [intRep, comp_fin3, ← Rat.mul_den_eq_num, hxden, hyden]
  grind


theorem intRep_equation (h : (curveQ a₂ a₄ a₆).toAffine.Equation x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    (curve a₂ a₄ a₆).toProjective.Equation (intRep x y w) := by
  have hw : w ≠ 0 := by grind [Rat.den_ne_zero]
  rwa [← map_equation _ (Int.castRingHom ℚ).injective_int, intRep_map_ℚ hden hden',
    equation_smul _ (isUnit_iff_ne_zero.2 (by positivity)), equation_some,
    map_curve_toProjective]


@[simp] theorem intRep_zero : intRep x y w 0 = x.num * w := by simp [intRep]

@[simp] theorem intRep_one : intRep x y w 1 = y.num := by simp [intRep]

@[simp] theorem intRep_two : intRep x y w 2 = w ^ 3 := by simp [intRep]

variable {p : ℕ}



section
variable [Fact p.Prime]

theorem intRep_coord_zero (hden : x.den = w ^ 2) (hwne : (w : ZMod p) ≠ 0) :
    (Int.castRingHom (ZMod p) ∘ intRep x y w) 0
      / (Int.castRingHom (ZMod p) ∘ intRep x y w) 2 = x := by
  simp [field, Rat.cast_def, hden]

theorem intRep_coord_one (hden' : y.den = w ^ 3) :
    (Int.castRingHom (ZMod p) ∘ intRep x y w) 1
      / (Int.castRingHom (ZMod p) ∘ intRep x y w) 2 = y := by
  simp [field, Rat.cast_def, hden']

end


theorem map_Δ_ne (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    (curveZMod a₂ a₄ a₆ p).Δ ≠ 0 := by
  simpa [WeierstrassCurve.baseChange, map_Δ, eq_intCast] using hΔ




theorem red_nonsingular (hp : p.Prime) (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    (curveZMod a₂ a₄ a₆ p).toProjective.Nonsingular (Int.castRingHom (ZMod p) ∘ intRep x y w) := by
  have : Fact p.Prime := ⟨hp⟩
  have hEq : (curveZMod a₂ a₄ a₆ p).toProjective.Equation
      (Int.castRingHom (ZMod p) ∘ intRep x y w) :=
    (intRep_equation h.1 hden hden').map (Int.castRingHom (ZMod p))
  by_cases hwz : (w : ZMod p) = 0
  · 
    have hz0 : (Int.castRingHom (ZMod p) ∘ intRep x y w) 2 = 0 := by simp [hwz]
    rw [nonsingular_of_Z_eq_zero hz0]
    refine ⟨hEq, Or.inr ?_⟩
    have hYne : (Int.castRingHom (ZMod p) ∘ intRep x y w) 1 ≠ 0 := by
      simp only [Function.comp_apply, intRep_one, eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hpy
      have hpw3 : (p : ℤ) ∣ (y.den : ℤ) := by
        rwa [Int.natCast_dvd_natCast, hden', hp.prime.dvd_pow_iff_dvd three_ne_zero,
          ← ZMod.natCast_eq_zero_iff]
      grind [Int.isUnit_iff, y.isCoprime_num_den.isUnit_of_dvd' hpy hpw3, hp.two_le]
    rw [X_eq_zero_of_Z_eq_zero hEq hz0]
    simpa using pow_ne_zero 2 hYne
  · 
    rw [nonsingular_of_Z_ne_zero (by simp [hwz])]
    exact (Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (map_Δ_ne hΔ)).mp ((equation_of_Z_ne_zero (by simp [hwz])).mp hEq)

section
variable [Fact p.Prime]




public noncomputable def repr (p : ℕ) [Fact p.Prime] :
    (curveQ a₂ a₄ a₆).toAffine.Point → Fin 3 → ZMod p
  | .zero => ![0, 1, 0]
  | .some x y h => Int.castRingHom (ZMod p) ∘ intRep x y (den_isSquare h.1).choose


theorem repr_zero : repr p (.zero : (curveQ a₂ a₄ a₆).toAffine.Point) = ![0, 1, 0] := by
  simp [repr]


theorem repr_some (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    repr p (.some x y h) = Int.castRingHom (ZMod p) ∘ intRep x y w := by
  obtain rfl : w = (den_isSquare h.1).choose :=
    Nat.pow_left_injective two_ne_zero (hden.symm.trans (den_isSquare h.1).choose_spec.1)
  rfl


theorem repr_nonsingular (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (P : (curveQ a₂ a₄ a₆).toAffine.Point) :
    (curveZMod a₂ a₄ a₆ p).toProjective.Nonsingular (repr p P) := by
  cases P with
  | zero => exact nonsingular_zero
  | some x y h =>
    obtain ⟨w, hden, hden'⟩ := den_isSquare h.1
    rw [repr_some h hden hden']
    exact red_nonsingular Fact.out hΔ h hden hden'




public noncomputable def redP (p : ℕ) [Fact p.Prime]
    (P : (curveQ a₂ a₄ a₆).toAffine.Point) :
    (curveZMod a₂ a₄ a₆ p).toAffine.Point :=
  Point.toAffine (curveZMod a₂ a₄ a₆ p).toProjective (repr p P)


theorem redP_eq_toAffine (P : (curveQ a₂ a₄ a₆).toAffine.Point) :
    redP p P = Point.toAffine (curveZMod a₂ a₄ a₆ p).toProjective (repr p P) := by simp only [redP]

@[simp]
theorem redP_zero : redP p (0 : (curveQ a₂ a₄ a₆).toAffine.Point) = 0 := by
  rw [redP_eq_toAffine]; exact Point.toAffine_zero


theorem redP_of_den_zero (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hd : (x.den : ZMod p) = 0) :
    redP p (.some x y h) = 0 := by
  obtain ⟨w, hden, hden'⟩ := den_isSquare h.1
  rw [redP_eq_toAffine, repr_some h hden hden']
  exact Point.toAffine_of_Z_eq_zero (by simpa [hden] using hd)


theorem red_nonsingular_affine (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) ≠ 0) :
    (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular x y := by
  obtain ⟨w, hden, hden'⟩ := den_isSquare h.1
  have hwne : (w : ZMod p) ≠ 0 := by simpa [hden] using hd
  have hns := red_nonsingular Fact.out hΔ h hden hden'
  rwa [nonsingular_of_Z_ne_zero (by simp [hwne]), intRep_coord_zero hden hwne,
    intRep_coord_one hden'] at hns


theorem redP_of_den_ne (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) ≠ 0) :
    redP p (.some x y h)
      = .some x y (red_nonsingular_affine hΔ h hd) := by
  obtain ⟨w, hden, hden'⟩ := den_isSquare h.1
  have hwne : (w : ZMod p) ≠ 0 := by simpa [hden] using hd
  have hns := red_nonsingular Fact.out hΔ h hden hden'
  rw [redP_eq_toAffine, repr_some h hden hden', Point.toAffine_of_Z_ne_zero hns (by simp [hwne])]
  simp only [intRep_coord_zero hden hwne, intRep_coord_one hden']

end

end ECCompute
end M20
section M21





open WeierstrassCurve

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ} {p : ℕ}



section
open Rat

variable {x₁ y₁ x₂ y₂ : ℚ}

section
variable [Fact p.Prime]




theorem cast_secant_num (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0) :
    ((x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄).den : ZMod p) ≠ 0
      ∧ ((x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄ : ℚ) : ZMod p)
        = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄ := by
  have hx1sq : ((x₁ ^ 2 : ℚ).den : ZMod p) ≠ 0 := den_pow_ne_zero Fact.out hd1 2
  have hx2sq : ((x₂ ^ 2 : ℚ).den : ZMod p) ≠ 0 := den_pow_ne_zero Fact.out hd2 2
  have hprod : ((x₁ * x₂ : ℚ).den : ZMod p) ≠ 0 := den_mul_ne_zero Fact.out hd1 hd2
  have esum : ((x₁ + x₂ : ℚ).den : ZMod p) ≠ 0 := den_add_ne_zero Fact.out hd1 hd2
  have e1 := den_add_ne_zero Fact.out hx1sq hprod
  have e2 := den_add_ne_zero Fact.out e1 hx2sq
  have e3 : ((a₂ * (x₁ + x₂)).den : ZMod p) ≠ 0 := den_mul_ne_zero Fact.out (by simp) esum
  have e4 := den_add_ne_zero Fact.out e2 e3
  refine ⟨den_add_ne_zero Fact.out e4 (by simp), ?_⟩
  simp [cast_add_of_ne_zero, cast_mul_of_ne_zero, *]


theorem slope_mul_add_eq (hne : x₁ ≠ x₂)
    (h₁ : (curveQ a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curveQ a₂ a₄ a₆).toAffine.Equation x₂ y₂) :
    (curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ * (y₁ + y₂)
      = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄ := by grind [Affine.slope_of_X_ne]


theorem reduced_slope_den (hne : x₁ ≠ x₂)
    (h₁ : (curveQ a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curveQ a₂ a₄ a₆).toAffine.Equation x₂ y₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hdy1 : (y₁.den : ZMod p) ≠ 0) (hdy2 : (y₂.den : ZMod p) ≠ 0)
    (hy2 : (y₁ : ZMod p) + y₂ ≠ 0) :
    (((curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0 := by
  have hy12 : y₁ + y₂ ≠ 0 := by
    intro h0; apply hy2; rw [← cast_add_of_ne_zero hdy1 hdy2, h0, cast_zero]
  have halt : (curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂
      = (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄) / (y₁ + y₂) := by
    rw [eq_div_iff hy12]; exact slope_mul_add_eq hne h₁ h₂
  have hy2' : ((y₁ + y₂ : ℚ) : ZMod p) ≠ 0 := by rwa [cast_add_of_ne_zero hdy1 hdy2]
  have hinv : ((y₁ + y₂ : ℚ)⁻¹.den : ZMod p) ≠ 0 := by
    rw [Rat.den_inv_of_ne_zero hy12, ne_eq, ZMod.natCast_eq_zero_iff, ← Int.natCast_dvd_natCast,
      Int.dvd_natAbs, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h ↦ hy2' (by rw [Rat.cast_def, h, zero_div])
  rw [halt, div_eq_mul_inv]
  exact den_mul_ne_zero Fact.out (cast_secant_num hd1 hd2).1 hinv


theorem reduced_tangent_eqs (hne : x₁ ≠ x₂)
    (h₁ : (curveQ a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curveQ a₂ a₄ a₆).toAffine.Equation x₂ y₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hdy1 : (y₁.den : ZMod p) ≠ 0) (hdy2 : (y₂.den : ZMod p) ≠ 0)
    (hℓden : (((curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0)
    (hd3 : (((curveQ a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0) :
    ((curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ : ZMod p) ^ 2
        = (curveQ a₂ a₄ a₆).toAffine.addX x₁ x₂
            ((curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)
          + a₂ + x₁ + x₂
      ∧ ((curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ : ZMod p) * (y₁ + y₂)
        = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄ := by
  set ℓ := (curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  refine ⟨?_, ?_⟩
  · have hqeq : ℓ ^ 2 = (curveQ a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ + a₂ + x₁ + x₂ := by grind
    have hc := congrArg (Rat.cast : ℚ → ZMod p) hqeq
    rwa [cast_pow,
      cast_add_of_ne_zero
        (den_add_ne_zero Fact.out (den_add_ne_zero Fact.out hd3 (by simp)) hd1) hd2,
      cast_add_of_ne_zero (den_add_ne_zero Fact.out hd3 (by simp)) hd1,
      cast_add_of_ne_zero hd3 (by simp), cast_intCast] at hc
  · have hℓmul : ℓ * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄ := by
      rw [hℓdef]; exact slope_mul_add_eq hne h₁ h₂
    have hc := congrArg (Rat.cast : ℚ → ZMod p) hℓmul
    rwa [cast_mul_of_ne_zero hℓden (den_add_ne_zero Fact.out hdy1 hdy2),
      cast_add_of_ne_zero hdy1 hdy2, (cast_secant_num hd1 hd2).2] at hc

end


theorem slope_den_of_addX_den (hp : p.Prime)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hd3 : (((curveQ a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0) :
    (((curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  set ℓ := (curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂
  have he : ℓ ^ 2 = (curveQ a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ + a₂ + x₁ + x₂ := by grind
  have hℓ2 : ((ℓ ^ 2 : ℚ).den : ZMod p) ≠ 0 := by
    rw [he]
    exact den_add_ne_zero hp (den_add_ne_zero hp (den_add_ne_zero hp hd3 (by simp)) hd1) hd2
  rw [den_pow, Nat.cast_pow] at hℓ2
  exact fun h ↦ hℓ2 (by grind)


theorem addX_den_ne (hp : p.Prime) {ℓ : ℚ} (hℓden : (ℓ.den : ZMod p) ≠ 0)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (haddX : (curveQ a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - a₂ - x₁ - x₂) :
    (((curveQ a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ).den : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [haddX]
  exact den_sub_ne_zero hp (den_sub_ne_zero hp (den_sub_ne_zero hp
    (den_pow_ne_zero hp hℓden 2) (by simp)) hd1) hd2

section
variable [Fact p.Prime]




theorem curveZMod_slope_eq {ℓ : ZMod p} {x₁ y₁ : ZMod p}
    (hYneg : y₁ ≠ (curveZMod a₂ a₄ a₆ p).toAffine.negY x₁ y₁)
    (h2Yne : y₁ + y₁ ≠ 0)
    (htan : ℓ * (y₁ + y₁) = x₁ ^ 2 + x₁ * x₁ + x₁ ^ 2 + a₂ * (x₁ + x₁) + a₄) :
    (curveZMod a₂ a₄ a₆ p).toAffine.slope x₁ x₁ y₁ y₁ = ℓ := by
  refine mul_right_cancel₀ h2Yne ?_
  rw [Affine.slope_of_Y_ne rfl hYneg]
  simp only [curve_baseChange_eq]
  grind


theorem addY_cast_eq {ℓ : ℚ} (hℓden : (ℓ.den : ZMod p) ≠ 0)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hdy1 : (y₁.den : ZMod p) ≠ 0)
    (hd3 : (((curveQ a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ).den : ZMod p) ≠ 0) :
    ((curveQ a₂ a₄ a₆).toAffine.addY x₁ x₂ y₁ ℓ : ZMod p)
      = -(ℓ * ((curveQ a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ - x₁) + y₁) := by
  rw [curve_baseChange_addY, cast_neg,
    cast_add_of_ne_zero (den_mul_ne_zero Fact.out hℓden (den_sub_ne_zero Fact.out hd3 hd1)) hdy1,
    cast_mul_of_ne_zero hℓden (den_sub_ne_zero Fact.out hd3 hd1), cast_sub_of_ne_zero hd3 hd1]

end
end



section




theorem cast_num_eq {q : ℚ} {w k : ℕ} (hd : q.den = w ^ k) : (q.num : ℚ) = q * w ^ k := by
  rw [(div_eq_iff (mod_cast q.den_ne_zero)).mp (Rat.num_div_den q), hd]; grind


theorem not_dvd_num (hp : p.Prime) {q : ℚ} {w : ℤ} (hd : (q.den : ℤ) = w ^ 2) (hpw : (p : ℤ) ∣ w) :
    ¬ (p : ℤ) ∣ q.num := by
  intro hdvd
  have hcop : IsCoprime q.num (w ^ 2) := by
    rw [← hd, Int.isCoprime_iff_nat_coprime]; simpa using q.reduced
  exact absurd (Int.isUnit_iff.mp
    (hcop.isUnit_of_dvd' hdvd (hpw.trans (dvd_pow_self w two_ne_zero))))
    (by have := hp.two_le; lia)

variable {x y : ℚ}


theorem kernel_point_data (hp : p.Prime)
    (h : (curveQ a₂ a₄ a₆).toAffine.Equation x y) (hd : (x.den : ZMod p) = 0) :
    ∃ w : ℤ, (x.num : ℚ) = x * w ^ 2 ∧ (y.num : ℚ) = y * w ^ 3
      ∧ (p : ℤ) ∣ w ∧ ¬ (p : ℤ) ∣ x.num ∧ w ≠ 0 := by
  obtain ⟨w, hxd, hyd⟩ := den_isSquare h
  have hpw : (p : ℤ) ∣ (w : ℤ) :=
    mod_cast hp.dvd_of_dvd_pow (hxd ▸ (ZMod.natCast_eq_zero_iff _ p).mp hd)
  have hwne : w ≠ 0 := by grind [Rat.den_ne_zero]
  exact ⟨w, cast_num_eq hxd, cast_num_eq hyd, hpw, not_dvd_num hp (by grind) hpw, by positivity⟩


theorem int_curve_relation {A B E : ℤ}
    (hcv : y ^ 2 = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hA : (A : ℚ) = x * E ^ 2) (hB : (B : ℚ) = y * E ^ 3) :
    B ^ 2 = A ^ 3 + a₂ * A ^ 2 * E ^ 2 + a₄ * A * E ^ 4 + a₆ * E ^ 6 := by
  have hq : (B : ℚ) ^ 2 = (A : ℚ) ^ 3 + a₂ * (A : ℚ) ^ 2 * (E : ℚ) ^ 2
      + a₄ * (A : ℚ) * (E : ℚ) ^ 4 + a₆ * (E : ℚ) ^ 6 := by grind
  exact mod_cast hq



section
variable {x₁ y₁ x₂ y₂ : ℚ} {A B C D E G : ℤ}


theorem not_dvd_W_cert (hpZ : Prime (p : ℤ))
    (hpA : ¬ (p : ℤ) ∣ A) (hpC : ¬ (p : ℤ) ∣ C) (hpE : (p : ℤ) ∣ E) :
    ¬ (p : ℤ) ∣ (-A ^ 2 * C ^ 2 + a₄ * A * C * E ^ 2 * G ^ 2
      + a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 + C * E ^ 2)) := by
  intro hdvd
  have hrest : (p : ℤ) ∣ (-A ^ 2 * C ^ 2 + a₄ * A * C * E ^ 2 * G ^ 2
      + a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 + C * E ^ 2) + A ^ 2 * C ^ 2) := by
    have heq : -A ^ 2 * C ^ 2 + a₄ * A * C * E ^ 2 * G ^ 2
          + a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 + C * E ^ 2) + A ^ 2 * C ^ 2
        = E ^ 2 * G ^ 2 * (a₄ * A * C + a₆ * (A * G ^ 2 + C * E ^ 2)) := by grind
    rw [heq]
    exact ((hpE.trans (dvd_pow_self E two_ne_zero)).mul_right (G ^ 2)).mul_right _
  have hAC : (p : ℤ) ∣ A ^ 2 * C ^ 2 := by simpa using dvd_sub hrest hdvd
  grind [Prime.dvd_of_dvd_pow, Prime.dvd_mul]


theorem K_ne_zero (hne : x₁ ≠ x₂)
    (hA : (A : ℚ) = x₁ * E ^ 2) (hC : (C : ℚ) = x₂ * G ^ 2)
    (hEQ : (E : ℚ) ≠ 0) (hGQ : (G : ℚ) ≠ 0) :
    A * G ^ 2 - C * E ^ 2 ≠ 0 := fun h ↦ hne <| by
  have h0 : ((A * G ^ 2 - C * E ^ 2 : ℤ) : ℚ) = 0 := by rw [h]; simp
  push_cast at h0
  grind [mul_right_cancel₀, pow_ne_zero]


theorem addX_single_fraction {ℓ x₃ : ℚ}
    (hℓ : ℓ * (x₁ - x₂) = y₁ - y₂) (haddX : x₃ = ℓ ^ 2 - a₂ - x₁ - x₂)
    (hcv1 : y₁ ^ 2 = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (hcv2 : y₂ ^ 2 = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆)
    (hA : (A : ℚ) = x₁ * E ^ 2) (hB : (B : ℚ) = y₁ * E ^ 3)
    (hC : (C : ℚ) = x₂ * G ^ 2) (hD : (D : ℚ) = y₂ * G ^ 3) :
    x₃ * ((A * C * (A * G ^ 2 - C * E ^ 2) ^ 2 : ℤ) : ℚ)
      = (((A * D * E - B * C * G) ^ 2
        - a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 - C * E ^ 2) ^ 2 : ℤ) : ℚ) := by
  rw [haddX]
  push_cast
  rw [hA, hB, hC, hD]
  linear_combination
    ((E : ℚ) ^ 6 * (G : ℚ) ^ 6 * (x₁ * x₂ * (ℓ * x₁ - ℓ * x₂ + y₁ - y₂))) * hℓ
      + ((E : ℚ) ^ 6 * (G : ℚ) ^ 6 * (x₂ * (x₁ - x₂))) * hcv1
      + ((E : ℚ) ^ 6 * (G : ℚ) ^ 6 * (-x₁ * (x₁ - x₂))) * hcv2




theorem padicValRat_num_cert (hp : p.Prime) {N K M : ℤ}
    (hcrux : padicValInt p N < padicValInt p K) (hN0 : N ≠ 0) (hK0 : K ≠ 0) :
    padicValRat p (N ^ 2 - M * K ^ 2 : ℤ) = 2 * padicValInt p N ∧ N ^ 2 - M * K ^ 2 ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain rfl | hM := eq_or_ne M 0
  · simp [hN0]
  have : padicValRat p (N ^ 2 : ℤ) < padicValRat p (-(M * K ^ 2 : ℤ)) := by
    simp [padicValRat.mul, hM, hK0]; grind
  have hne : N ^ 2 ≠ M * K ^ 2 := by contrapose! this; simp [this]
  have hne' : (↑(N ^ 2 : ℤ) + -↑(M * K ^ 2) : ℚ) ≠ 0 := by qify at hne; grind
  refine ⟨?_, by grind only⟩
  rw [Int.cast_sub, sub_eq_add_neg, padicValRat.add_eq_of_lt hne' _ _ this]
  all_goals simp [*]


theorem den_zero_of_cert (hp : p.Prime) {x₃ : ℚ} {K N M : ℤ}
    (hMain : x₃ * ((A * C * K ^ 2 : ℤ) : ℚ) = ((N ^ 2 - M * K ^ 2 : ℤ) : ℚ))
    (hpA : ¬ (p : ℤ) ∣ A) (hpC : ¬ (p : ℤ) ∣ C)
    (hcrux : padicValInt p N < padicValInt p K)
    (hA0 : A ≠ 0) (hC0 : C ≠ 0) (hK0 : K ≠ 0) (hN0 : N ≠ 0) :
    (x₃.den : ZMod p) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hNumvalQ, hNum0⟩ := padicValRat_num_cert hp (M := M) hcrux hN0 hK0
  have hDenval : padicValInt p (A * C * K ^ 2) = 2 * padicValInt p K := by
    rw [padicValInt.mul (mul_ne_zero hA0 hC0) (pow_ne_zero 2 hK0), padicValInt.mul hA0 hC0,
      padicValInt.eq_zero_of_not_dvd hpA, padicValInt.eq_zero_of_not_dvd hpC,
      pow_two, padicValInt.mul hK0 hK0]
    grind
  have hDen3Q : ((A * C * K ^ 2 : ℤ) : ℚ) ≠ 0 :=
    mod_cast mul_ne_zero (mul_ne_zero hA0 hC0) (pow_ne_zero 2 hK0)
  have hx3div : x₃ = ((N ^ 2 - M * K ^ 2 : ℤ) : ℚ) / ((A * C * K ^ 2 : ℤ) : ℚ) := by
    rw [eq_div_iff hDen3Q]; exact hMain
  have hx3neg : padicValRat p x₃ < 0 := by
    rw [hx3div, padicValRat.div (mod_cast hNum0) hDen3Q, hNumvalQ, padicValRat.of_int, hDenval]
    grind
  have hden0 : padicValNat p x₃.den ≠ 0 := by rw [padicValRat_def] at hx3neg; lia
  exact (ZMod.natCast_eq_zero_iff _ p).mpr (dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr hden0))


theorem crux_of_int_relations (hpZ : Prime (p : ℤ))
    (hne : x₁ ≠ x₂) (hA : (A : ℚ) = x₁ * E ^ 2) (hC : (C : ℚ) = x₂ * G ^ 2)
    (hEne : (E : ℚ) ≠ 0) (hGne : (G : ℚ) ≠ 0) (hpE : (p : ℤ) ∣ E) (hpG : (p : ℤ) ∣ G)
    (hpA : ¬ (p : ℤ) ∣ A) (hpC : ¬ (p : ℤ) ∣ C)
    (hCR1 : B ^ 2 = A ^ 3 + a₂ * A ^ 2 * E ^ 2 + a₄ * A * E ^ 4 + a₆ * E ^ 6)
    (hCR2 : D ^ 2 = C ^ 3 + a₂ * C ^ 2 * G ^ 2 + a₄ * C * G ^ 4 + a₆ * G ^ 6) :
    padicValInt p (A * D * E - B * C * G) < padicValInt p (A * G ^ 2 - C * E ^ 2)
      ∧ A * D * E - B * C * G ≠ 0 ∧ A * G ^ 2 - C * E ^ 2 ≠ 0 := by
  have : Fact p.Prime := ⟨Nat.prime_iff_prime_int.mpr hpZ⟩
  set K : ℤ := A * G ^ 2 - C * E ^ 2 with hKdef
  set N : ℤ := A * D * E - B * C * G
  set W : ℤ := -A ^ 2 * C ^ 2 + a₄ * A * C * E ^ 2 * G ^ 2
    + a₆ * E ^ 2 * G ^ 2 * (A * G ^ 2 + C * E ^ 2) with hWdef
  have hI2 : N * (A * D * E + B * C * G) = K * W := by grind
  have hpS : (p : ℤ) ∣ (A * D * E + B * C * G) :=
    dvd_add (hpE.mul_left (A * D)) (hpG.mul_left (B * C))
  have hpW : ¬ (p : ℤ) ∣ W := hWdef ▸ not_dvd_W_cert hpZ hpA hpC hpE
  have hW0 : W ≠ 0 := fun h ↦ hpW (h ▸ dvd_zero _)
  have hK0 : K ≠ 0 := hKdef ▸ K_ne_zero hne hA hC hEne hGne
  have hprodne : N * (A * D * E + B * C * G) ≠ 0 := hI2 ▸ mul_ne_zero hK0 hW0
  have hN0 : N ≠ 0 := left_ne_zero_of_mul hprodne
  refine ⟨?_, hN0, hK0⟩
  replace hI2 := congr(padicValInt p $hI2)
  rw [padicValInt.mul hN0 (by lia), padicValInt.mul hK0 hW0,
    padicValInt.eq_zero_of_not_dvd hpW] at hI2
  have : 1 ≤ padicValInt p (A * D * E + B * C * G) := by
    have hne : (A * D * E + B * C * G) ≠ 0 := by grind
    haveI : Fact p.Prime := ⟨Nat.prime_iff_prime_int.mpr hpZ⟩
    unfold padicValInt
    exact one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hne) (Int.natCast_dvd.mp hpS)
  grind

end




theorem den_addX_both_kernel (hp : p.Prime) {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curveQ a₂ a₄ a₆).toAffine.Equation x₁ y₁)
    (h₂ : (curveQ a₂ a₄ a₆).toAffine.Equation x₂ y₂)
    (hne : x₁ ≠ x₂) (hd1 : (x₁.den : ZMod p) = 0) (hd2 : (x₂.den : ZMod p) = 0) :
    (((curveQ a₂ a₄ a₆).toAffine.addX x₁ x₂
        ((curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) = 0 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set ℓ := (curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂
  set x₃ := (curveQ a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ with hx3def
  have hℓ : ℓ * (x₁ - x₂) = y₁ - y₂ := by grind [Affine.slope_of_X_ne]
  have haddX : x₃ = ℓ ^ 2 - a₂ - x₁ - x₂ := by rw [hx3def, curve_baseChange_addX]
  have hcv1 := curve_baseChange_equation h₁
  have hcv2 := curve_baseChange_equation h₂
  obtain ⟨E, hA, hB, hpE, hpA, hEne⟩ := kernel_point_data hp h₁ hd1
  obtain ⟨G, hC, hD, hpG, hpC, hGne⟩ := kernel_point_data hp h₂ hd2
  set A : ℤ := x₁.num
  set B : ℤ := y₁.num
  set C : ℤ := x₂.num
  set D : ℤ := y₂.num
  
  have hCR1 : B ^ 2 = A ^ 3 + a₂ * A ^ 2 * E ^ 2 + a₄ * A * E ^ 4 + a₆ * E ^ 6 :=
    int_curve_relation hcv1 hA hB
  have hCR2 : D ^ 2 = C ^ 3 + a₂ * C ^ 2 * G ^ 2 + a₄ * C * G ^ 4 + a₆ * G ^ 6 :=
    int_curve_relation hcv2 hC hD
  set K : ℤ := A * G ^ 2 - C * E ^ 2 with hKdef
  set N : ℤ := A * D * E - B * C * G with hNdef
  
  have hMain : x₃ * ((A * C * K ^ 2 : ℤ) : ℚ) = ((N ^ 2 - a₆ * E ^ 2 * G ^ 2 * K ^ 2 : ℤ) : ℚ) := by
    rw [hKdef, hNdef]; exact addX_single_fraction hℓ haddX hcv1 hcv2 hA hB hC hD
  
  obtain ⟨hcrux, hN0, hK0⟩ := crux_of_int_relations hpZ hne hA hC
    (mod_cast hEne) (mod_cast hGne) hpE hpG hpA hpC hCR1 hCR2
  exact den_zero_of_cert hp (M := a₆ * E ^ 2 * G ^ 2) hMain hpA hpC hcrux
    (fun h ↦ hpA (h ▸ dvd_zero _)) (fun h ↦ hpC (h ▸ dvd_zero _)) hK0 hN0
end



section
open Projective

variable [Fact p.Prime]


theorem toAffine_g_intRep {x y : ℚ} {w : ℕ}
    (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y)
    (hden : x.den = w ^ 2) (hden' : y.den = w ^ 3) :
    Point.toAffine (curveQ a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ intRep x y w)
      = .some x y h := by
  have hw : w ≠ 0 := by grind [Rat.den_ne_zero]
  rw [intRep_map_ℚ hden hden',
    Point.toAffine_smul _ (isUnit_iff_ne_zero.2 (by positivity)),
    Point.toAffine_some ((nonsingular_some x y).mpr h)]


theorem nonsingular_of_toAffine_some {U : Fin 3 → ℤ} {X Y : ℚ}
    {hR : (curveQ a₂ a₄ a₆).toAffine.Nonsingular X Y}
    (hU : Point.toAffine (curveQ a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ U) = .some X Y hR) :
    (curveQ a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ U) := by
  grind [Point.toAffine_of_singular, Affine.Point.some_ne_zero]


theorem int_smul_eq_of_toAffine_eq {S T : Fin 3 → ℤ} {X Y : ℚ}
    {hR : (curveQ a₂ a₄ a₆).toAffine.Nonsingular X Y}
    (hS : Point.toAffine (curveQ a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ S) = .some X Y hR)
    (hT : Point.toAffine (curveQ a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ T) = .some X Y hR) :
    T 2 • S = S 2 • T := by
  have key : ∀ U : Fin 3 → ℤ,
      Point.toAffine (curveQ a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ U)
        = .some X Y hR → (U 0 : ℚ) = X * U 2 ∧ (U 1 : ℚ) = Y * U 2 := by
    intro U hU
    have hg : ∀ i, (Int.castRingHom ℚ ∘ U) i = (U i : ℚ) := fun i ↦ by simp [Function.comp_apply]
    have hUz : (Int.castRingHom ℚ ∘ U) 2 ≠ 0 := by
      grind [Point.toAffine_of_Z_eq_zero, Affine.Point.some_ne_zero]
    have hns : (curveQ a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ U) :=
      nonsingular_of_toAffine_some hU
    rw [Point.toAffine_of_Z_ne_zero hns hUz, Affine.Point.some.injEq] at hU
    rw [hg] at hUz
    exact ⟨(div_eq_iff hUz).mp (hg 0 ▸ hU.1), (div_eq_iff hUz).mp (hg 1 ▸ hU.2)⟩
  obtain ⟨hS0, hS1⟩ := key S hS
  obtain ⟨hT0, hT1⟩ := key T hT
  funext i
  fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul] <;> qify <;> grind


theorem repr_equiv_of_toAffine (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (R : (curveQ a₂ a₄ a₆).toAffine.Point) {T : Fin 3 → ℤ}
    (hnsp : (curveZMod a₂ a₄ a₆ p).toProjective.Nonsingular (Int.castRingHom (ZMod p) ∘ T))
    (hnsq : (curveQ a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ T))
    (hTℚ : Point.toAffine (curveQ a₂ a₄ a₆).toProjective (Int.castRingHom ℚ ∘ T) = R) :
    repr p R ≈ Int.castRingHom (ZMod p) ∘ T := by
  cases R with
  | zero =>
    have hTz : (Int.castRingHom ℚ ∘ T) 2 = 0 := by
      grind [Point.toAffine_of_Z_ne_zero, Affine.Point.some_ne_zero]
    have hTz' : T 2 = 0 := by simpa [Function.comp_apply] using hTz
    have hfTz : (Int.castRingHom (ZMod p) ∘ T) 2 = 0 := by simp [Function.comp_apply, hTz']
    rw [repr_zero]
    exact Setoid.symm (equiv_zero_of_Z_eq_zero hnsp hfTz)
  | some X Y hR =>
    obtain ⟨w₃, hd3, hd3'⟩ := den_isSquare hR.1
    have hid : T 2 • intRep X Y w₃ = intRep X Y w₃ 2 • T :=
      int_smul_eq_of_toAffine_eq (toAffine_g_intRep hR hd3 hd3') hTℚ
    have hprop : (Int.castRingHom (ZMod p) ∘ T) 2 • (Int.castRingHom (ZMod p) ∘ intRep X Y w₃)
        = (Int.castRingHom (ZMod p) ∘ intRep X Y w₃) 2 • (Int.castRingHom (ZMod p) ∘ T) := by
      simpa only [comp_smul, Function.comp_apply] using
        congrArg (fun Q : Fin 3 → ℤ ↦ Int.castRingHom (ZMod p) ∘ Q) hid
    have hns_repr := repr_nonsingular hΔ (.some X Y hR)
    rw [repr_some hR hd3 hd3'] at hns_repr ⊢
    exact equiv_of_proportional hns_repr hnsp hprop


theorem sum_repr_equiv (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0) {V : Fin 3 → ℤ}
    {A B : Fin 3 → ℚ} (P Q : (curveQ a₂ a₄ a₆).toAffine.Point)
    (hnsA : (curveQ a₂ a₄ a₆).toProjective.Nonsingular A)
    (hnsB : (curveQ a₂ a₄ a₆).toProjective.Nonsingular B)
    (hgadd : Int.castRingHom ℚ ∘ V = (curveQ a₂ a₄ a₆).toProjective.add A B)
    (haffA : Point.toAffine (curveQ a₂ a₄ a₆).toProjective A = P)
    (haffB : Point.toAffine (curveQ a₂ a₄ a₆).toProjective B = Q)
    (hadd : (curveZMod a₂ a₄ a₆ p).toProjective.add
      (repr p P) (repr p Q) = Int.castRingHom (ZMod p) ∘ V) :
    repr p (P + Q) ≈ Int.castRingHom (ZMod p) ∘ V := by
  have hnsp : (curveZMod a₂ a₄ a₆ p).toProjective.Nonsingular (Int.castRingHom (ZMod p) ∘ V) := by
    rw [← hadd]
    exact nonsingular_add (repr_nonsingular hΔ _) (repr_nonsingular hΔ _)
  have hnsq : (curveQ a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ V) := by
    grind [nonsingular_add]
  exact repr_equiv_of_toAffine hΔ _ hnsp hnsq (by grind [Point.toAffine_add])



variable {x₁ y₁ x₂ y₂ : ℚ}


theorem y_eq_negY_of_X_eq
    (h₁ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) (hx12 : x₁ = x₂)
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curveQ a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂) :
    y₁ = (curveQ a₂ a₄ a₆).toAffine.negY x₂ y₂ := by
  grind [Affine.Y_eq_of_X_eq h₁.1 h₂.1 hx12, Affine.Point.some.injEq]


theorem redP_add_tangent_two_torsion (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h₁ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) (hne : x₁ ≠ x₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hdy1 : (y₁.den : ZMod p) ≠ 0) (hdy2 : (y₂.den : ZMod p) ≠ 0)
    (hXbar : (x₁ : ZMod p) = x₂) (hYbar : (y₁ : ZMod p) = y₂)
    (hYneg : (y₁ : ZMod p) = (curveZMod a₂ a₄ a₆ p).toAffine.negY x₁ y₁) :
    redP p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redP p (.some x₁ y₁ h₁) + redP p (.some x₁ y₁ h₁) := by
  rw [redP_of_den_ne hΔ h₁ hd1, Affine.Point.add_of_Y_eq rfl hYneg, Affine.Point.add_of_X_ne hne]
  apply redP_of_den_zero (Affine.nonsingular_add h₁ h₂ (fun hxy ↦ hne hxy.left))
  by_contra hd3_s
  obtain ⟨-, htan⟩ :=
    reduced_tangent_eqs hne h₁.1 h₂.1 hd1 hd2 hdy1 hdy2
      (slope_den_of_addX_den Fact.out hd1 hd2 hd3_s) hd3_s
  have hYeq : (y₁ : ZMod p) = -y₁ := hYneg.trans curve_baseChange_negY
  have hY0 : (y₁ : ZMod p) + y₂ = 0 := by grind
  rw [hY0, mul_zero] at htan
  have hns : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular (x₁ : ZMod p) (y₁ : ZMod p) :=
    red_nonsingular_affine hΔ h₁ hd1
  simp only [Affine.nonsingular_iff, curve_baseChange_eq] at hns
  grind


theorem redP_add_tangent_generic (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h₁ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) (hne : x₁ ≠ x₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hd2 : (x₂.den : ZMod p) ≠ 0)
    (hdy1 : (y₁.den : ZMod p) ≠ 0) (hdy2 : (y₂.den : ZMod p) ≠ 0)
    (hXbar : (x₁ : ZMod p) = x₂) (hYbar : (y₁ : ZMod p) = y₂)
    (hYneg : ¬ (y₁ : ZMod p) = (curveZMod a₂ a₄ a₆ p).toAffine.negY x₁ y₁) :
    redP p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redP p (.some x₁ y₁ h₁) + redP p (.some x₁ y₁ h₁) := by
  have hslX : (curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
    Affine.slope_of_X_ne hne
  set ℓ : ℚ := (y₁ - y₂) / (x₁ - x₂)
  have hy2 : (y₁ : ZMod p) + y₂ ≠ 0 := by grind
  have hℓden_s : (((curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂).den : ZMod p) ≠ 0 :=
    reduced_slope_den hne h₁.1 h₂.1 hd1 hd2 hdy1 hdy2 hy2
  have hℓden : (ℓ.den : ZMod p) ≠ 0 := by rwa [← hslX]
  have hd3 : (((curveQ a₂ a₄ a₆).toAffine.addX x₁ x₂ ℓ).den : ZMod p) ≠ 0 :=
    addX_den_ne Fact.out hℓden hd1 hd2 curve_baseChange_addX
  have hd3_s : (((curveQ a₂ a₄ a₆).toAffine.addX x₁ x₂
      ((curveQ a₂ a₄ a₆).toAffine.slope x₁ x₂ y₁ y₂)).den : ZMod p) ≠ 0 := by rwa [hslX]
  obtain ⟨hS2, htan⟩ := reduced_tangent_eqs hne h₁.1 h₂.1 hd1 hd2 hdy1 hdy2 hℓden_s hd3_s
  rw [hslX] at hS2 htan
  have h2Yne : (y₁ : ZMod p) + y₁ ≠ 0 := by grind
  rw [← hXbar, ← hYbar] at htan
  grind [curveZMod_slope_eq hYneg h2Yne htan, addY_cast_eq hℓden hd1 hdy1 hd3,
    Affine.nonsingular_add h₁ h₂ (fun hxy ↦ hne hxy.left), Affine.Point.add_of_X_ne,
    redP_of_den_ne, Affine.Point.add_of_Y_ne]


theorem redP_add_kernel
    (h₁ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curveQ a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂)
    (hd1 : (x₁.den : ZMod p) = 0) (hd2 : (x₂.den : ZMod p) = 0) :
    redP p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) = 0 := by
  obtain rfl | hx12 := eq_or_ne x₁ x₂
  · rw [Affine.Point.add_of_Y_eq rfl (y_eq_negY_of_X_eq h₁ h₂ rfl hPQ), redP_zero]
  · rw [Affine.Point.add_of_X_ne hx12]
    exact redP_of_den_zero _ (den_addX_both_kernel Fact.out h₁.1 h₂.1 hx12 hd1 hd2)


theorem redP_add_neg (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h₁ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curveQ a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂)
    (hd1 : (x₁.den : ZMod p) ≠ 0) (hx12 : x₁ = x₂) (hYbar : (y₁ : ZMod p) = y₂) :
    redP p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redP p (.some x₁ y₁ h₁) + redP p (.some x₁ y₁ h₁) := by
  have hy : y₁ = (curveQ a₂ a₄ a₆).toAffine.negY x₂ y₂ := y_eq_negY_of_X_eq h₁ h₂ hx12 hPQ
  rw [Affine.Point.add_of_Y_eq hx12 hy, redP_zero, redP_of_den_ne hΔ h₁ hd1]
  have hyneg : (y₁ : ZMod p) = (curveZMod a₂ a₄ a₆ p).toAffine.negY
      (x₁ : ZMod p) (y₁ : ZMod p) := by
    have hcast : (y₁ : ZMod p) = -y₂ := by
      rw [hy, Affine.negY_of_a₁_a₃_eq_zero _ rfl rfl, Rat.cast_neg]
    grind
  rw [Affine.Point.add_of_Y_eq rfl hyneg]


theorem redP_add_tangent (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h₁ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hred : redP p (.some x₁ y₁ h₁) = redP p (.some x₂ y₂ h₂))
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curveQ a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂) :
    redP p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redP p (.some x₁ y₁ h₁) + redP p (.some x₂ y₂ h₂) := by
  by_cases hd1 : (x₁.den : ZMod p) = 0
  · 
    have hQ0 : redP p (.some x₂ y₂ h₂) = 0 := by rw [← hred]; exact redP_of_den_zero h₁ hd1
    have hd2 : (x₂.den : ZMod p) = 0 := by grind [redP_of_den_ne, Affine.Point.some_ne_zero]
    rw [redP_of_den_zero h₁ hd1, hQ0, add_zero]
    exact redP_add_kernel h₁ h₂ hPQ hd1 hd2
  · 
    have hd2 : (x₂.den : ZMod p) ≠ 0 := by
      grind [redP_of_den_ne, redP_of_den_zero, Affine.Point.some_ne_zero]
    rw [redP_of_den_ne hΔ h₁ hd1, redP_of_den_ne hΔ h₂ hd2, Affine.Point.some.injEq] at hred
    obtain ⟨hXbar, hYbar⟩ := hred
    
    have hQeqP : redP p (.some x₂ y₂ h₂) = redP p (.some x₁ y₁ h₁) := by
      rw [redP_of_den_ne hΔ h₁ hd1, redP_of_den_ne hΔ h₂ hd2, Affine.Point.some.injEq]
      exact ⟨hXbar.symm, hYbar.symm⟩
    rw [hQeqP]
    obtain rfl | hx12 := eq_or_ne x₁ x₂
    · 
      exact redP_add_neg hΔ h₁ h₂ hPQ hd1 rfl hYbar
    · 
      
      have hp : p.Prime := Fact.out
      have hdy1 : (y₁.den : ZMod p) ≠ 0 := by grind [ydenom_eq_zero_iff, h₁.1]
      have hdy2 : (y₂.den : ZMod p) ≠ 0 := by grind [ydenom_eq_zero_iff, h₂.1]
      by_cases hYneg : (y₁ : ZMod p) = (curveZMod a₂ a₄ a₆ p).toAffine.negY
          (x₁ : ZMod p) (y₁ : ZMod p)
      · exact redP_add_tangent_two_torsion hΔ h₁ h₂ hx12 hd1 hd2 hdy1 hdy2 hXbar hYbar hYneg
      · exact redP_add_tangent_generic hΔ h₁ h₂ hx12 hd1 hd2 hdy1 hdy2 hXbar hYbar hYneg




theorem redP_map_add_double (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    {w₁ : ℕ} (h₁ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (hden1 : x₁.den = w₁ ^ 2) (hden1' : y₁.den = w₁ ^ 3)
    (hns1 : (curveQ a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ intRep x₁ y₁ w₁))
    (hadd : (curveZMod a₂ a₄ a₆ p).toProjective.add
        (repr p (.some x₁ y₁ h₁)) (repr p (.some x₁ y₁ h₁))
      = Int.castRingHom (ZMod p) ∘ (curve a₂ a₄ a₆).toProjective.dblXYZ (intRep x₁ y₁ w₁)) :
    repr p (.some x₁ y₁ h₁ + .some x₁ y₁ h₁)
      ≈ Int.castRingHom (ZMod p) ∘ (curve a₂ a₄ a₆).toProjective.dblXYZ (intRep x₁ y₁ w₁) := by
  have hgadd : Int.castRingHom ℚ ∘ (curve a₂ a₄ a₆).toProjective.dblXYZ (intRep x₁ y₁ w₁)
      = (curveQ a₂ a₄ a₆).toProjective.add (Int.castRingHom ℚ ∘ intRep x₁ y₁ w₁)
          (Int.castRingHom ℚ ∘ intRep x₁ y₁ w₁) := by
    rw [add_self, ← map_curveQ]
    exact (map_dblXYZ (Int.castRingHom ℚ) _).symm
  exact sum_repr_equiv hΔ _ _ hns1 hns1 hgadd
    (toAffine_g_intRep h₁ hden1 hden1')
    (toAffine_g_intRep h₁ hden1 hden1') hadd


theorem redP_map_add_secant (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    {w₁ w₂ : ℕ} (h₁ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (hden1 : x₁.den = w₁ ^ 2) (hden1' : y₁.den = w₁ ^ 3)
    (hden2 : x₂.den = w₂ ^ 2) (hden2' : y₂.den = w₂ ^ 3)
    (hns1 : (curveQ a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ intRep x₁ y₁ w₁))
    (hns2 : (curveQ a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ intRep x₂ y₂ w₂))
    (heq : ¬ repr p (.some x₁ y₁ h₁) ≈ repr p (.some x₂ y₂ h₂)) :
    repr p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      ≈ Int.castRingHom (ZMod p) ∘ (curve a₂ a₄ a₆).toProjective.addXYZ (intRep x₁ y₁ w₁)
          (intRep x₂ y₂ w₂) := by
  have hℚne : ¬ Int.castRingHom ℚ ∘ intRep x₁ y₁ w₁ ≈ Int.castRingHom ℚ ∘ intRep x₂ y₂ w₂ := by
    intro hℚeq
    apply heq
    have hpt : (Affine.Point.some x₁ y₁ h₁ : (curveQ a₂ a₄ a₆).toAffine.Point)
        = .some x₂ y₂ h₂ := by
      rw [← toAffine_g_intRep h₁ hden1 hden1', ← toAffine_g_intRep h₂ hden2 hden2']
      exact Point.toAffine_of_equiv hℚeq
    exact hpt ▸ Setoid.refl (repr p (.some x₁ y₁ h₁))
  have hadd : (curveZMod a₂ a₄ a₆ p).toProjective.add
        (repr p (.some x₁ y₁ h₁)) (repr p (.some x₂ y₂ h₂))
      = Int.castRingHom (ZMod p) ∘ (curve a₂ a₄ a₆).toProjective.addXYZ (intRep x₁ y₁ w₁)
          (intRep x₂ y₂ w₂) := by
    rw [add_of_not_equiv heq, repr_some h₁ hden1 hden1', repr_some h₂ hden2 hden2']
    exact map_addXYZ (Int.castRingHom (ZMod p)) _ _
  have hgaddXYZ : (curveQ a₂ a₄ a₆).toProjective.addXYZ (Int.castRingHom ℚ ∘ intRep x₁ y₁ w₁)
        (Int.castRingHom ℚ ∘ intRep x₂ y₂ w₂)
      = Int.castRingHom ℚ ∘ (curve a₂ a₄ a₆).toProjective.addXYZ (intRep x₁ y₁ w₁)
          (intRep x₂ y₂ w₂) := by rw [← map_curveQ]; exact map_addXYZ (Int.castRingHom ℚ) _ _
  have hgadd : Int.castRingHom ℚ ∘ (curve a₂ a₄ a₆).toProjective.addXYZ (intRep x₁ y₁ w₁)
        (intRep x₂ y₂ w₂)
      = (curveQ a₂ a₄ a₆).toProjective.add (Int.castRingHom ℚ ∘ intRep x₁ y₁ w₁)
          (Int.castRingHom ℚ ∘ intRep x₂ y₂ w₂) := by
    rw [← hgaddXYZ]; exact (add_of_not_equiv hℚne).symm
  exact sum_repr_equiv hΔ _ _ hns1 hns2 hgadd
    (toAffine_g_intRep h₁ hden1 hden1') (toAffine_g_intRep h₂ hden2 hden2') hadd


theorem redP_map_add_tangent_case (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    {w₁ : ℕ} (h₁ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂)
    (heq : repr p (.some x₁ y₁ h₁) ≈ repr p (.some x₂ y₂ h₂))
    (hPQ : (Affine.Point.some x₁ y₁ h₁ : (curveQ a₂ a₄ a₆).toAffine.Point) ≠ .some x₂ y₂ h₂)
    (hadd : (curveZMod a₂ a₄ a₆ p).toProjective.add
        (repr p (.some x₁ y₁ h₁)) (repr p (.some x₂ y₂ h₂))
      = Int.castRingHom (ZMod p) ∘ (curve a₂ a₄ a₆).toProjective.dblXYZ (intRep x₁ y₁ w₁)) :
    repr p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      ≈ Int.castRingHom (ZMod p) ∘ (curve a₂ a₄ a₆).toProjective.dblXYZ (intRep x₁ y₁ w₁) := by
  have hred : redP p (.some x₁ y₁ h₁) = redP p (.some x₂ y₂ h₂) := by
    rw [redP_eq_toAffine, redP_eq_toAffine]; exact Point.toAffine_of_equiv heq
  have hnspV : (curveZMod a₂ a₄ a₆ p).toProjective.Nonsingular
      (Int.castRingHom (ZMod p) ∘ (curve a₂ a₄ a₆).toProjective.dblXYZ (intRep x₁ y₁ w₁)) := by
    rw [← hadd]
    exact nonsingular_add (repr_nonsingular hΔ _) (repr_nonsingular hΔ _)
  refine equiv_of_toAffine_eq (repr_nonsingular hΔ _) hnspV ?_
  rw [← redP_eq_toAffine, ← hadd,
    Point.toAffine_add (repr_nonsingular hΔ _) (repr_nonsingular hΔ _),
    ← redP_eq_toAffine, ← redP_eq_toAffine]
  exact redP_add_tangent hΔ h₁ h₂ hred hPQ


theorem redP_map_add_some (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (h₁ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x₂ y₂) :
    redP p (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = redP p (.some x₁ y₁ h₁) + redP p (.some x₂ y₂ h₂) := by
  obtain ⟨w₁, hden1, hden1'⟩ := den_isSquare h₁.1
  obtain ⟨w₂, hden2, hden2'⟩ := den_isSquare h₂.1
  have hns1 : (curveQ a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ intRep x₁ y₁ w₁) :=
    nonsingular_of_toAffine_some (toAffine_g_intRep h₁ hden1 hden1')
  have hns2 : (curveQ a₂ a₄ a₆).toProjective.Nonsingular (Int.castRingHom ℚ ∘ intRep x₂ y₂ w₂) :=
    nonsingular_of_toAffine_some (toAffine_g_intRep h₂ hden2 hden2')
  rw [redP_eq_toAffine, redP_eq_toAffine (.some x₁ y₁ h₁),
    redP_eq_toAffine (.some x₂ y₂ h₂),
    ← Point.toAffine_add (repr_nonsingular hΔ _) (repr_nonsingular hΔ _)]
  refine Point.toAffine_of_equiv ?_
  by_cases heq : repr p (.some x₁ y₁ h₁) ≈ repr p (.some x₂ y₂ h₂)
  · 
    have hadd : (curveZMod a₂ a₄ a₆ p).toProjective.add
          (repr p (.some x₁ y₁ h₁)) (repr p (.some x₂ y₂ h₂))
        = Int.castRingHom (ZMod p) ∘ (curve a₂ a₄ a₆).toProjective.dblXYZ (intRep x₁ y₁ w₁) := by
      rw [add_of_equiv heq, repr_some h₁ hden1 hden1']
      exact map_dblXYZ (Int.castRingHom (ZMod p)) _
    rw [hadd]
    by_cases hPQ : (Affine.Point.some x₁ y₁ h₁ : (curveQ a₂ a₄ a₆).toAffine.Point) = .some x₂ y₂ h₂
    · rw [← hPQ] at hadd ⊢; exact redP_map_add_double hΔ h₁ hden1 hden1' hns1 hadd
    · exact redP_map_add_tangent_case hΔ h₁ h₂ heq hPQ hadd
  · rw [add_of_not_equiv heq, repr_some h₁ hden1 hden1', repr_some h₂ hden2 hden2', curveZMod,
      WeierstrassCurve.baseChange, algebraMap_int_eq, map_addXYZ (Int.castRingHom (ZMod p))]
    exact redP_map_add_secant hΔ h₁ h₂ hden1 hden1' hden2 hden2' hns1 hns2 heq


theorem redP_map_add (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0)
    (P Q : (curveQ a₂ a₄ a₆).toAffine.Point) :
    redP p (P + Q) = redP p P + redP p Q := by
  cases P with
  | zero => rw [← Affine.Point.zero_def, zero_add, redP_zero, zero_add]
  | some x₁ y₁ h₁ =>
  cases Q with
  | zero => rw [← Affine.Point.zero_def, add_zero, redP_zero, add_zero]
  | some x₂ y₂ h₂ => exact redP_map_add_some hΔ h₁ h₂


public noncomputable def redHom (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    (curveQ a₂ a₄ a₆).toAffine.Point →+ (curveZMod a₂ a₄ a₆ p).toAffine.Point where
  toFun := redP p
  map_zero' := redP_zero
  map_add' := by exact redP_map_add hΔ

@[simp] theorem redHom_apply (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0) (x : (curveQ a₂ a₄ a₆).toAffine.Point) :
    redHom hΔ x = redP p x := rfl
end

end ECCompute
end M21
section M22





open WeierstrassCurve Affine

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ} {p : ℕ}



public noncomputable def εpFinite (a₂ a₄ a₆ : ℤ) (p : ℕ) (θ : ZMod p) :
    (curveZMod a₂ a₄ a₆ p).toAffine.Point → ZMod 2
  | .zero => 0
  | .some X _ _ => if X = θ then psi p (fderiv a₂ a₄ θ) else psi p (X - θ)

variable {θ x y x₁ y₁ x₂ y₂ : ZMod p}

@[simp]
theorem εpFinite_zero : εpFinite a₂ a₄ a₆ p θ 0 = 0 := rfl

theorem εpFinite_some (h : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular x y) :
    εpFinite a₂ a₄ a₆ p θ (.some x y h) = if x = θ then psi p (fderiv a₂ a₄ θ) else psi p (x - θ) :=
  rfl


theorem equation_curveZMod (h : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular x y) :
    y ^ 2 = fval (R := ZMod p) a₂ a₄ a₆ x := by
  simpa [fval] using curve_baseChange_equation h.1
grind_pattern equation_curveZMod => (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular x y


theorem DescentHyp.ne_two (h : DescentHyp a₂ a₄ a₆ p θ) : p ≠ 2 := fun hp ↦ h.ne_six (hp ▸ ⟨3, rfl⟩)


theorem εp_x_indep
    (h₁ : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular x₂ y₂) (hx : x₁ = x₂) :
    εpFinite a₂ a₄ a₆ p θ (.some x₁ y₁ h₁) = εpFinite a₂ a₄ a₆ p θ (.some x₂ y₂ h₂) := by
  subst hx; rfl


theorem εp_sum_of_vieta (h : DescentHyp a₂ a₄ a₆ p θ) {ℓ m x₃ : ZMod p}
    (hv : Vieta (a₂ : ZMod p) a₄ a₆ ℓ m x₁ x₂ x₃) :
    (if x₃ = θ then psi p (fderiv a₂ a₄ θ) else psi p (x₃ - θ))
      = (if x₁ = θ then psi p (fderiv a₂ a₄ θ) else psi p (x₁ - θ))
        + (if x₂ = θ then psi p (fderiv a₂ a₄ θ) else psi p (x₂ - θ)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hθroot := h.root
  have hfd_ne : fderiv (a₂ : ZMod p) a₄ θ ≠ 0 := fderiv_ne_zero h
  have hfd1 : x₁ = θ → fderiv (a₂ : ZMod p) a₄ θ = (x₂ - θ) * (x₃ - θ) :=
    fderiv_eq_prod ℓ m hv hθroot
  have hfd2 : x₂ = θ → fderiv (a₂ : ZMod p) a₄ θ = (x₁ - θ) * (x₃ - θ) :=
    fderiv_eq_prod ℓ m ⟨by grind, by grind, by grind⟩ hθroot
  have hfd3 : x₃ = θ → fderiv (a₂ : ZMod p) a₄ θ = (x₁ - θ) * (x₂ - θ) :=
    fderiv_eq_prod ℓ m ⟨by grind, by grind, by grind⟩ hθroot
  obtain rfl | c1 := eq_or_ne x₁ θ
  · rw [if_neg (by grind), if_pos rfl, if_neg (by grind), hfd1 rfl,
      psi_mul h.prime (by grind) (by grind)]
    grind
  obtain rfl | c2 := eq_or_ne x₂ θ
  · rw [if_neg (by grind), if_neg c1, if_pos rfl, hfd2 rfl,
      psi_mul h.prime (by grind) (by grind)]
    grind
  obtain rfl | c3 := eq_or_ne x₃ θ
  · rw [if_pos rfl, if_neg c1, if_neg c2, hfd3 rfl,
      psi_mul h.prime (by grind) (by grind)]
  · rw [if_neg c3, if_neg c1, if_neg c2]
    grind [psi_collinear h.prime hv h.root c1 c2 c3]


theorem εpFinite_map_add_of_X_ne [Fact p.Prime] (h : DescentHyp a₂ a₄ a₆ p θ)
    (h₁ : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular x₁ y₁)
    (h₂ : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular x₂ y₂) (hne : x₁ ≠ x₂) :
    εpFinite a₂ a₄ a₆ p θ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = εpFinite a₂ a₄ a₆ p θ (.some x₁ y₁ h₁) + εpFinite a₂ a₄ a₆ p θ (.some x₂ y₂ h₂) := by
  simp only [Point.add_of_X_ne hne, εpFinite_some]
  set ℓ := (curveZMod a₂ a₄ a₆ p).toAffine.slope x₁ x₂ y₁ y₂ with hℓdef
  set x₃ := (curveZMod a₂ a₄ a₆ p).toAffine.addX x₁ x₂ ℓ with hx3def
  have hℓmul : ℓ * (x₁ - x₂) = y₁ - y₂ := by
    rw [hℓdef, slope_of_X_ne hne, div_mul_cancel₀ _ (by grind)]
  have hx3 : x₃ = ℓ ^ 2 - a₂ - x₁ - x₂ := by rw [hx3def, curve_baseChange_addX]
  exact εp_sum_of_vieta (m := y₁ - ℓ * x₁) h (vieta_of_roots hne hx3 (by grind) (by grind))


theorem εp_double_of_vieta (h : DescentHyp a₂ a₄ a₆ p θ) {ℓ m x x₃ : ZMod p} (hXθ : x ≠ θ)
    (hv : Vieta (a₂ : ZMod p) a₄ a₆ ℓ m x x x₃) :
    (if x₃ = θ then psi p (fderiv a₂ a₄ θ) else psi p (x₃ - θ)) = 0 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hθroot := h.root
  obtain rfl | c3 := eq_or_ne x₃ θ
  · rw [fderiv_eq_prod ℓ m (x₂ := x) (x₃ := x) ⟨by grind, by grind, by grind⟩ hθroot rfl]
    simp [psi_of_isSquare]
  rw [if_neg c3]
  have hpm : psi p ((x - θ) * (x - θ) * (x₃ - θ)) = 0 := by
    rw [prod_sub_theta_eq_lineSq hv hθroot]
    exact psi_of_isSquare ⟨ℓ * θ + m, by ring⟩
  rwa [← sq, psi_mul_sq h.prime (by grind)] at hpm


theorem εpFinite_double [Fact p.Prime] (h : DescentHyp a₂ a₄ a₆ p θ) {x y : ZMod p}
    (hP : (curveZMod a₂ a₄ a₆ p).toAffine.Nonsingular x y) (hy0 : y ≠ 0) :
    εpFinite a₂ a₄ a₆ p θ (.some x y hP + .some x y hP) = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by simp [ZMod.ringChar_zmod_n, h.ne_two])
  have hyne : y ≠ (curveZMod a₂ a₄ a₆ p).toAffine.negY x y := by grind
  simp only [Point.add_self_of_Y_ne hyne, εpFinite_some]
  set ℓ := (curveZMod a₂ a₄ a₆ p).toAffine.slope x x y y with hℓdef
  set x₃ := (curveZMod a₂ a₄ a₆ p).toAffine.addX x x ℓ with hx3def
  have hℓ : ℓ * (2 * y) = fderiv (a₂ : ZMod p) a₄ x := by
    rw [hℓdef, slope_of_Y_ne rfl hyne]
    simp only [curve_baseChange_eq]
    grind [fderiv]
  have hx3 : x₃ = ℓ ^ 2 - a₂ - 2 * x := by grind
  exact εp_double_of_vieta (m := y - ℓ * x) h (by grind)
    (vieta_of_double_root (by grind) (by grind) hx3)


theorem εpFinite_map_add [Fact p.Prime] (h : DescentHyp a₂ a₄ a₆ p θ)
    (P Q : (curveZMod a₂ a₄ a₆ p).toAffine.Point) :
    εpFinite a₂ a₄ a₆ p θ (P + Q) = εpFinite a₂ a₄ a₆ p θ P + εpFinite a₂ a₄ a₆ p θ Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [← Point.zero_def, zero_add, εpFinite_zero, zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [← Point.zero_def, add_zero, εpFinite_zero, add_zero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (curveZMod a₂ a₄ a₆ p).toAffine.negY x₂ y₂
  · 
    rw [Point.add_of_Y_eq hxy.1 hxy.2, εpFinite_zero, εp_x_indep h₁ h₂ hxy.1,
      CharTwo.add_self_eq_zero]
  · obtain rfl | hne := eq_or_ne x₁ x₂
    · 
      rw [εp_x_indep h₂ h₁ rfl, CharTwo.add_self_eq_zero]
      grind [εpFinite_double]
    · 
      exact εpFinite_map_add_of_X_ne h h₁ h₂ hne


public noncomputable def εpHom [Fact p.Prime] (h : DescentHyp a₂ a₄ a₆ p θ) :
    (curveZMod a₂ a₄ a₆ p).toAffine.Point →+ ZMod 2 where
  toFun := εpFinite a₂ a₄ a₆ p θ
  map_zero' := by exact εpFinite_zero
  map_add' := by exact εpFinite_map_add h

@[simp] theorem εpHom_apply [Fact p.Prime] (h : DescentHyp a₂ a₄ a₆ p θ) (P : (curveZMod a₂ a₄ a₆ p).toAffine.Point) :
    εpHom h P = εpFinite a₂ a₄ a₆ p θ P := rfl

end ECCompute
end M22
section M23





open WeierstrassCurve

namespace ECCompute

variable {a₂ a₄ a₆ : ℤ} {p : ℕ} {θ : ZMod p}




theorem lambda_some_of_den_ne [Fact p.Prime] {x y : ℚ}
    (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) ≠ 0) :
    lambda θ (.some x y h)
      = if xbar p x = θ then psi p (fderiv (R := ZMod p) a₂ a₄ θ) else psi p (xbar p x - θ) := by
  obtain ⟨w, hxden, _⟩ := den_isSquare h.1
  have hw : (w : ZMod p) ≠ 0 := by intro h0; apply hd; rw [hxden]; grind
  have hnum : (x.num : ZMod p) = xbar p x * x.den := by
    rw [xbar, Rat.cast_def, div_mul_cancel₀ _ hd]
  have halpha : x.num - θ * x.den = (w : ZMod p) ^ 2 * (xbar p x - θ) := by rw [hnum, hxden]; grind
  grind [lambda, psi_mul_sq Fact.out]


theorem lambda_some_of_den_zero {x y : ℚ}
    (h : (curveQ a₂ a₄ a₆).toAffine.Nonsingular x y) (hd : (x.den : ZMod p) = 0) :
    lambda θ (.some x y h) = 0 := by simp only [lambda, if_pos hd]




noncomputable def redCharHom [Fact p.Prime] (h : DescentHyp a₂ a₄ a₆ p θ)
    (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0) :
    (curveQ a₂ a₄ a₆).toAffine.Point →+ ZMod 2 :=
  (εpHom h).comp (redHom hΔ)


theorem lambda_eq_εp_red [Fact p.Prime] (h : DescentHyp a₂ a₄ a₆ p θ)
    (hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0) (P : (curveQ a₂ a₄ a₆).toAffine.Point) :
    lambda θ P = redCharHom h hΔ P := by
  cases P with
  | zero => rw [← Affine.Point.zero_def, lambda_zero, map_zero]
  | some x y hns =>
    rw [redCharHom, AddMonoidHom.comp_apply, redHom_apply]
    by_cases hd : (x.den : ZMod p) = 0
    · grind [lambda_some_of_den_zero, redP_of_den_zero]
    · grind [lambda_some_of_den_ne, redP_of_den_ne, εpHom_apply, εpFinite_some, xbar]


theorem lambda_map_add (h : DescentHyp a₂ a₄ a₆ p θ)
    (P Q : (curveQ a₂ a₄ a₆).toAffine.Point) :
    lambda θ (P + Q) = lambda θ P + lambda θ Q := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hΔ : ((curve a₂ a₄ a₆).Δ : ZMod p) ≠ 0 := by
    grind [Rat.num_intCast, map_curveQ, map_Δ, eq_intCast]
  grind [lambda_eq_εp_red h hΔ]


public noncomputable def lambdaHom (h : DescentHyp a₂ a₄ a₆ p θ) :
    (curveQ a₂ a₄ a₆).toAffine.Point →+ ZMod 2 where
  toFun := lambda θ
  map_zero' := lambda_zero
  map_add' := by exact lambda_map_add h

@[simp] theorem lambdaHom_apply (h : DescentHyp a₂ a₄ a₆ p θ) (P : (curveQ a₂ a₄ a₆).toAffine.Point) :
    lambdaHom h P = lambda θ P := rfl

end ECCompute
end M23
section M24





section

namespace WeierstrassCurve
open Affine

variable {x y x₁ x₂ y₁ y₂ : ℚ}

namespace VariableChange

variable (C : VariableChange ℚ)


def mapX (x : ℚ) : ℚ := (C.u : ℚ)⁻¹ ^ 2 * (x - C.r)


def mapY (x y : ℚ) : ℚ := (C.u : ℚ)⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)


def mapSlope (ℓ : ℚ) : ℚ := (C.u : ℚ)⁻¹ * (ℓ - C.s)


def invX (X : ℚ) : ℚ := (C.u : ℚ) ^ 2 * X + C.r


def invY (X Y : ℚ) : ℚ := (C.u : ℚ) ^ 3 * Y + (C.u : ℚ) ^ 2 * C.s * X + C.t

variable {C}

lemma u_ne_zero : (C.u : ℚ) ≠ 0 := C.u.ne_zero
grind_pattern u_ne_zero => (C.u : ℚ)

lemma mapX_invX : C.mapX (C.invX x) = x := by grind [mapX, invX]
grind_pattern mapX_invX => C.mapX (C.invX x)

lemma mapY_invY : C.mapY (C.invX x) (C.invY x y) = y := by grind [mapY, invX, invY]
grind_pattern mapY_invY => C.mapY (C.invX x) (C.invY x y)

lemma invX_mapX : C.invX (C.mapX x) = x := by grind [mapX, invX]
grind_pattern invX_mapX => C.invX (C.mapX x)

lemma invY_mapY : C.invY (C.mapX x) (C.mapY x y) = y := by grind [mapX, mapY, invY]
grind_pattern invY_mapY => C.invY (C.mapX x) (C.mapY x y)

lemma mapX_injective : C.mapX.Injective := by grind [Function.Injective, mapX]

theorem mapY_injective : (C.mapY x).Injective := by grind [Function.Injective, mapY]

end VariableChange

open VariableChange

variable {W : WeierstrassCurve ℚ} {C : VariableChange ℚ}


theorem equation_variableChange_iff :
    W.toAffine.Equation x y ↔ (C • W).toAffine.Equation (C.mapX x) (C.mapY x y) := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne_zero
  rw [equation_iff, equation_iff, mapX, mapY, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆]
  grind [Units.val_inv_eq_inv_val]


theorem nonsingular_variableChange_iff :
    W.toAffine.Nonsingular x y ↔ (C • W).toAffine.Nonsingular (C.mapX x) (C.mapY x y) := by
  have hu : (C.u : ℚ) ≠ 0 := u_ne_zero
  rw [nonsingular_iff', nonsingular_iff', ← equation_variableChange_iff, mapX, mapY,
    variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]
  grind [Units.val_inv_eq_inv_val]



theorem variableChange_negY :
    (C • W).toAffine.negY (C.mapX x) (C.mapY x y) = C.mapY x (W.toAffine.negY x y) := by
  simp only [negY, mapX, mapY, variableChange_a₁, variableChange_a₃]
  grind [Units.val_inv_eq_inv_val]
grind_pattern variableChange_negY => (C • W).toAffine.negY (C.mapX x) (C.mapY x y)

theorem variableChange_addX {ℓ : ℚ} :
    (C • W).toAffine.addX (C.mapX x₁) (C.mapX x₂) (C.mapSlope ℓ)
      = C.mapX (W.toAffine.addX x₁ x₂ ℓ) := by
  simp only [addX, mapX, mapSlope, variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
  grind
grind_pattern variableChange_addX => (C • W).toAffine.addX (C.mapX x₁) (C.mapX x₂) (C.mapSlope ℓ)

theorem variableChange_addY {ℓ : ℚ} :
    (C • W).toAffine.addY (C.mapX x₁) (C.mapX x₂) (C.mapY x₁ y₁) (C.mapSlope ℓ)
      = C.mapY (W.toAffine.addX x₁ x₂ ℓ) (W.toAffine.addY x₁ x₂ y₁ ℓ) := by
  simp only [addY, negAddY, addX, negY, mapX, mapY, mapSlope, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  grind
grind_pattern variableChange_addY => (C • W).toAffine.addY (C.mapX x₁) (C.mapX x₂) (C.mapY x₁ y₁) (C.mapSlope ℓ)

theorem variableChange_slope (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope (C.mapX x₁) (C.mapX x₂) (C.mapY x₁ y₁) (C.mapY x₂ y₂)
      = C.mapSlope (W.toAffine.slope x₁ x₂ y₁ y₂) := by
  obtain rfl | hx := eq_or_ne x₁ x₂
  · have hy : y₁ ≠ W.toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    obtain rfl : y₁ = y₂ := Y_eq_of_Y_ne h₁ h₂ rfl hy
    have hy' : C.mapY x₁ y₁ ≠ (C • W).toAffine.negY (C.mapX x₁) (C.mapY x₁ y₁) := by
      rw [variableChange_negY]; exact fun h ↦ hy (mapY_injective h)
    have hs : C.mapSlope
          ((3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.toAffine.negY x₁ y₁))
        = ((C.u : ℚ)⁻¹
            * ((3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁)
              - C.s * (y₁ - W.toAffine.negY x₁ y₁))) / (y₁ - W.toAffine.negY x₁ y₁) := by
      rw [mapSlope]; field_simp [u_ne_zero]
    rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy, hs, div_eq_div_iff (sub_ne_zero.mpr hy') (sub_ne_zero.mpr hy)]
    simp only [negY, mapX, mapY, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, Units.val_inv_eq_inv_val]
    ring
  · have hs : C.mapSlope ((y₁ - y₂) / (x₁ - x₂))
        = ((C.u : ℚ)⁻¹ * (y₁ - y₂ - C.s * (x₁ - x₂))) / (x₁ - x₂) := by
      rw [mapSlope]; field_simp [u_ne_zero]
    rw [slope_of_X_ne (fun h ↦ hx (mapX_injective h)), slope_of_X_ne hx, hs, div_eq_div_iff (sub_ne_zero.mpr (fun h ↦ hx (mapX_injective h))) (sub_ne_zero.mpr hx)]
    grind [mapX, mapY]



namespace VariableChange


def pointAddEquiv (C : VariableChange ℚ) : W.toAffine.Point ≃+ (C • W).toAffine.Point :=
  AddEquiv.mk'
    { toFun := fun
        | .zero => .zero
        | .some x y h => .some (C.mapX x) (C.mapY x y) (nonsingular_variableChange_iff.mp h)
      invFun := fun
        | .zero => .zero
        | .some X Y h => .some (C.invX X) (C.invY X Y)
            (nonsingular_variableChange_iff.mpr (by rwa [mapX_invX, mapY_invY]))
      left_inv := by grind
      right_inv := by grind }
    (by
      rintro P Q
      rcases P with _ | ⟨x₁, y₁, hp₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, hp₂⟩
      any_goals rfl
      simp only [Equiv.coe_fn_mk]
      grind [mapX_injective, mapY_injective, Point.add_some, variableChange_slope hp₁.1 hp₂.1, Point.zero_def, Point.add_of_Y_eq])

end VariableChange

end WeierstrassCurve

end
end M24
section M25





namespace ECCompute

open WeierstrassCurve Module



def HasRankGE (W : WeierstrassCurve ℚ) (n : ℕ) : Prop :=
  ∃ H : Submodule ℤ W.toAffine.Point, Module.Finite ℤ H ∧ n ≤ finrank ℤ H


theorem hasRankGE_of_addEquiv {W₁ W₂ : WeierstrassCurve ℚ}
    (e : W₁.toAffine.Point ≃+ W₂.toAffine.Point) {n : ℕ} (h : HasRankGE W₂ n) :
    HasRankGE W₁ n := by
  obtain ⟨H, hfin, hle⟩ := h
  
  let el : W₁.toAffine.Point ≃ₗ[ℤ] W₂.toAffine.Point := e.toIntLinearEquiv
  set emap := el.symm.submoduleMap H
  refine ⟨H.map (el.symm : W₂.toAffine.Point →ₗ[ℤ] W₁.toAffine.Point), ?_, ?_⟩
  · exact Module.Finite.equiv emap
  · rwa [← emap.finrank_eq]

variable {a₂ a₄ a₆ : ℤ}
variable {c : Certificate} {pt : Fin c.ρ → ℚ × ℚ} {ls : Fin c.ρ → ℕ × ℤ}


theorem card_torsionBy_le (H : Submodule ℤ (curveQ a₂ a₄ a₆).toAffine.Point) :
    Nat.card (Submodule.torsionBy ℤ H 2) ≤ (curveQ a₂ a₄ a₆).twoTorsionPoints.ncard := by
  have hmap (x : Submodule.torsionBy ℤ H 2) :
      (x : (curveQ a₂ a₄ a₆).toAffine.Point) ∈ (curveQ a₂ a₄ a₆).twoTorsionPoints := by
    rw [mem_twoTorsionPoints, ← two_zsmul, ← Submodule.coe_smul, Submodule.smul_coe_torsionBy,
      Submodule.coe_zero]
  refine Nat.card_le_card_of_injective (fun x ↦ ⟨x, hmap x⟩) fun a b hab ↦ ?_
  grind


theorem hasRankGE_of_certificate {a₁ a₂ a₃ a₄ a₆ : ℤ} (c : Certificate)
    (W : WeierstrassCurve ℚ)
    (hW : W = ⟨a₁, a₂, a₃, a₄, a₆⟩) (h₂ : a₁ ^ 2 + 4 * a₂ = c.a₂)
    (h₄ : 16 * a₄ + 8 * a₁ * a₃ = c.a₄) (h₆ : 64 * a₆ + 16 * a₃ ^ 2 = c.a₆)
    (hc : c.Valid) :
    HasRankGE W (c.ρ - c.t) := by
  obtain ⟨hlenP, hlenL, hlenB, hlenM, hlenQ, hpt, hlsP, hlsC, hB, hinv, htors⟩ := hc
  subst hW
  suffices this : HasRankGE (curveQ c.a₂ c.a₄ c.a₆) (c.ρ - c.t) by
    set W : WeierstrassCurve ℚ := ⟨a₁, a₂, a₃, a₄, a₆⟩
    
    
    set C : VariableChange ℚ := ⟨(Units.mk0 2 two_ne_zero)⁻¹, 0, 0, 0⟩ * W.toCharNeTwoNF with hC
    have hsm : C • W = curveQ c.a₂ c.a₄ c.a₆ := by
      rw [hC, mul_smul, ← h₂, ← h₄, ← h₆]
      ext <;>
      simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
        variableChange_a₆, curve] <;>
      grind
    exact hasRankGE_of_addEquiv C.pointAddEquiv (hsm ▸ this)
  clear h₂ h₄ h₆ a₁ a₂ a₃ a₄ a₆
  rw [checkPoints_iff] at hpt
  set pt : Fin c.ρ → ℚ × ℚ := fun i ↦ c.points[i]
  set ls : Fin c.ρ → ℕ × ℤ := fun j ↦ c.labels[j]
  replace hlsP (j : Fin c.ρ) : (ls j).1.Prime := checkPrimes_true hlsP _ (List.getElem_mem _)
  replace hlsC (j : Fin c.ρ) : DescentHyp c.a₂ c.a₄ c.a₆ (ls j).1 (ls j).2 :=
    descentHyp_of_checkLabels hlsC (List.getElem_mem _) (hlsP j)
  replace hpt (i : Fin c.ρ) : (curveQ c.a₂ c.a₄ c.a₆).toAffine.Equation (pt i).1 (pt i).2 :=
    hpt _ (List.getElem_mem _)
  have hBmat : ∀ i j, F2Invert.toMat c.B c.ρ i j =
      (lambdaBitK c.a₂ c.a₄ (ls j).1 (qrMask (ls j).1) ((ls j).2 % (ls j).1).toNat
        (pt i).1.num.toNat (-(pt i).1.num).toNat (pt i).1.den : ZMod 2) :=
    checkB_true hlenB hlenP hlenL hlenQ hB
  set E : Type := (curveQ c.a₂ c.a₄ c.a₆).toAffine.Point
  set φ : E →+ (Fin c.ρ → ZMod 2) := AddMonoidHom.pi (fun j ↦ lambdaHom (hlsC j)) with hφ
  rcases Nat.eq_zero_or_pos c.ρ with hρ0 | hρpos
  · exact ⟨⊥, inferInstance, by simp [hρ0]⟩
  have hΔ : (curveQ c.a₂ c.a₄ c.a₆).Δ ≠ 0 := fun hΔ0 ↦ (hlsC ⟨0, hρpos⟩).discr (by simp [hΔ0])
  have hns (i) : (curveQ c.a₂ c.a₄ c.a₆).toAffine.Nonsingular (pt i).1 (pt i).2 :=
    (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (hpt i)
  let (eq := hg) g (i : Fin c.ρ) : E := .some (pt i).1 (pt i).2 (hns i)
  
  have hindep : LinearIndependent (ZMod 2) (fun i ↦ φ (g i)) := by
    have hrow : (fun i ↦ φ (g i)) = (F2Invert.toMat c.B c.ρ).row := by
      ext i j
      rw [hφ, AddMonoidHom.pi_apply, lambdaHom_apply, hg,
        ← lambdaBitK_eq (hlsC j) (hns i) (intResNat_cast (hlsC j).prime.ne_zero)
          (Int.toNat_sub_toNat_neg (pt i).1.num).symm rfl]
      simp [hBmat]
    rw [hrow]
    exact Matrix.linearIndependent_rows_of_isUnit (F2Invert.checkInv_isUnit hlenB hlenM hinv)
  set H : Submodule ℤ E := Submodule.span ℤ (Set.range g)
  have hHfin : Module.Finite ℤ H := Module.Finite.span_of_finite ℤ (Set.finite_range g)
  refine ⟨H, hHfin, ?_⟩
  simpa using RankDeduction.rank_ge_le (H := H) Nat.prime_two
    (fun i ↦ ⟨g i, Submodule.subset_span (Set.mem_range_self i)⟩) (φ.comp H.subtype.toAddMonoidHom)
    hindep ((card_torsionBy_le H).trans htors)

end ECCompute
end M25
section FinalCert
open ECCompute

def cert30 : Certificate :=
  ⟨1, (-3228304564166696785337518400971747855236939151916843761828888880), 73670908105027748206942683265556686408682622908883237555764712993774693011662614867268664920128, 42887521588562570648295424700481414891906269031715704388583, 1, 10735890762157642271397932290169336413343176524170317307862, 36527601366042435070449260607381291651125966117088505606566, (-191343252501744710920469253053814914740155826184846428623900020092320359440533580599707968891295963191620494429021063155251675277422524386688835954909991049781810155674792116441160089600000000), 30,
   [(mkRat (-19044816639564553135916213063624) 1, mkRat 358114123694263771402133216462218238703109056000 1), (mkRat (-56633690158166265878355117706184) 1, mkRat 273598674034013653639722800994395277712042913280 1), (mkRat (-46090669433586249681692521328264) 1, mkRat (-352920560186856875901912458711349403332068205120) 1), (mkRat (-819358127708905078848488198264) 1, mkRat (-276252593859621552797207215959167259260115615120) 1), (mkRat 15597296204910114130141731648376 1, mkRat 164658822822979356999444763434713602250045400000 1), (mkRat 599405473151905339480032301157536 1, mkRat (-14611541825186308445759626336475667948431404695720) 1), (mkRat 961760962938364536929303884766776 1, mkRat 29775534592129286495275085670033388580710216243200 1), (mkRat 233784219676682999903768417505784 9, mkRat (-2313163017577931330905321290903980935900730662400) 27), (mkRat 102570646408585917835381839717376 1, mkRat (-906454890606391795742456424446215433835441957000) 1), (mkRat 102883540314455695556811479976376 1, mkRat (-911348524035744305410792629104362359893118864000) 1), (mkRat 19825658361187824918336401358387256 1, mkRat 2791512941961582532308373359685319636306252603343360 1), (mkRat 2903859287976417177910738681320376 1, mkRat (-156451905071631302151346076506752469044627526224000) 1), (mkRat 83208764547778707988543317496 1, mkRat 270928561519031950619711335113205563765299499840 1), (mkRat 316209273329634260082104593545784 9, mkRat (-1623857771616251382474046258431517603095642097600) 27), (mkRat (-44928981362651101554142039123544) 1, mkRat (-357800365272587961336513420828859502212639319760) 1), (mkRat 33449825355091261261340958102456 1, mkRat (-55779804918926390303308578755641485870056261760) 1), (mkRat 8046634862572152774430036098136 1, mkRat 219578974955456095500008051232155777458381930080 1), (mkRat 20110781761139577843189433336830904 529, mkRat (-933430813131166076277690043929002298570178918080000) 12167), (mkRat 98596577070260662113756273766216 1, mkRat 844900322550270438394427272380187868358960703920 1), (mkRat (-48845557682436172100035267874264) 1, mkRat 338849804929279884100990994050317148047693783120 1), (mkRat 31194769560691815284303124427072504 1369, mkRat (-5534960364550581339315869425572769453327068774349440) 50653), (mkRat 348631971262962137013755224180864 9, mkRat 2217115030334725281178303715304440590613451543080 27), (mkRat 30786757706172245427369935940751 1, mkRat 58841476683003015635939735479019645493983346000 1), (mkRat 981237121392165295258674984419704 25, mkRat 10772008230563330713856551084706542613223225451008 125), (mkRat (-1375512305297568636146477425304) 1, mkRat (-279479656222233760329111021828320918679470603760) 1), (mkRat 2176847231669361157617805080376 1, mkRat (-258173774033814654131873092258933454440467744000) 1), (mkRat 81144865538608157215776681968666104 9409, mkRat (-196745879217974147433000090921230282036583636496706880) 912673), (mkRat (-102232652816072078963100973874402359496) 1760929, mkRat 597656396656267273763979862347476652379553284300831756800 2336752783), (mkRat 18185059495455317534148450136087395198424 398521369, mkRat (-1163094110634556260183818966340441145895999285622419870462880) 7955682089347), (mkRat 6836656260185627094480216410738344 169, mkRat 211602113371266392521587023407197354597225050437200 2197)],
   [(11, 1), (17, 6), (19, 7), (29, 16), (37, 12), (43, 22), (43, 25), (61, 30), (61, 42), (73, 24), (79, 35), (89, 78), (97, 0), (101, 44), (101, 69), (103, 72), (113, 56), (127, 26), (131, 94), (137, 119), (151, 17), (173, 21), (193, 43), (197, 168), (211, 68), (211, 70), (223, 90), (223, 140), (229, 16), (241, 30)],
   [378605199, 578124500, 388331486, 635932721, 1027160946, 983561330, 183981031, 833542940, 106719772, 954038022, 1046174334, 658173737, 258934303, 673352970, 327073635, 400514346, 1015763599, 1025012189, 486612391, 55456891, 126738063, 498672703, 364696878, 686625088, 478441222, 645078520, 221147019, 56164890, 906566252, 852103239],
   [675174253, 645729316, 51198641, 425079237, 831427801, 31817238, 858014823, 965747943, 746432424, 835081614, 311730302, 534197852, 1073586700, 76808714, 52265468, 414394258, 801795508, 296789684, 207770920, 785071880, 953460418, 782861638, 457721759, 555330693, 441249265, 263365286, 214587218, 918706920, 611460464, 259879651],
   [570, 107286, 199410, 332473074, 96068509338, 3678700564050, 3678700564050, 1662926210933060154, 1662926210933060154, 9059857384996697084766, 89932533647391829339958, 526807005835216593886842678, 152076272278209298711361952606, 1550432784880709368503235994226, 1550432784880709368503235994226, 1760368345969468176824550810518, 8586949319576899938239170417650582, 30790515292689894969866990722818747158, 736595995152387833549853625256200223418, 144045494737659012533968429665233398647702, 425021430996567349671854096638566139059703606, 6959499201072490563778903106400207980707536372360786, 12141444129520299540464513365627305638510449038044929807326, 118293807873742757827437296739134280345237452048103702628050, 1276851644109113882183330310376468972669945505335701621656087154, 1276851644109113882183330310376468972669945505335701621656087154, 2341578194317687999480691957418079046404556494213344638229394998166, 2341578194317687999480691957418079046404556494213344638229394998166, 622496887405363581323637999554697472253602734436003095745513373030970, 3503677951953348316105854456354073289344456812647089274464254465766954878],
   0, 23⟩


theorem cert30_valid : cert30.Valid :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
   certTorsionBound_zero (ℓ := 23) (by decide +kernel) (by decide +kernel)⟩

theorem rank30 : HasRankGE (⟨1, 0, 0, -201769035260418549083594900060734240952308696994802735114305555,
    1151107939141058565733479426024323225135665982951300586808823640527729578307228357301072889377⟩ : WeierstrassCurve ℚ) 30 :=
  hasRankGE_of_certificate (a₁ := 1) (a₂ := 0) (a₃ := 0) cert30 _ rfl rfl rfl rfl cert30_valid

end FinalCert


section FinalBridge
open ECCompute

theorem OMA.solution : type_of% @EllipticCurveRank.WeierstrassCurve.thirty_le_rank_ranksunbounded30 := by
  have h30 : HasRankGE EllipticCurveRank.WeierstrassCurve.ranksunbounded30 30 := rank30
  obtain ⟨H, hHfin, hH⟩ := h30
  have hfg : IsAddFG (EllipticCurveRank.WeierstrassCurve.ranksunbounded30).Point :=
    WeierstrassCurve.Affine.fg_point_of_numberField
  haveI : Module.Finite ℤ (EllipticCurveRank.WeierstrassCurve.ranksunbounded30).Point :=
    Module.Finite.iff_addGroup_fg.mpr hfg
  exact hH.trans (Submodule.finrank_le H)

end FinalBridge
