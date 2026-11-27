import FormalConjectures.ErdosProblems.«131»
import Mathlib

/-!
A rank reduction for the Pham–Zakharov bound. In the one-dimensional
application of their irreducible-set and convex-position arguments, a
large rank-one configuration would have a sparse half-line at every point.
Its median rules this out. In ranks at least four, merely counting the
points of the enclosing box gives the quarter exponent. This leaves the
box theorem only in dimensions two and three.
All logarithms are natural. The extraction and the two box bounds below are separate unproved inputs. See arXiv:2410.14624v2, Theorem 2,
Lemma 10, and the rank-increase estimate in the proof of Theorem 2.
-/

open Filter Topology Finset
namespace OMA.R_Erdos131_erdos_131_variants_pham_zakharov_R1

/-- One-dimensional extraction with arbitrary fixed logarithmic losses.
The box is translated and its side lengths need not agree. In rank one,
the coordinate set has a sparse half-line at each of its points. -/
def H1 : Prop :=
  ∀ σ : ℝ, 0 < σ → ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop,
  ∀ A : Finset ℕ, A ⊆ Icc 1 N →
    (∀ a ∈ A, ∀ T ⊆ A.erase a, T.Nonempty → ∑ x ∈ T, x ≠ a * T.card) →
    (1 / 4 + σ) * Real.log N < Real.log A.card →
    ∃ (d : ℕ) (hd : 0 < d) (lo hi : Fin d → ℤ) (S : Finset (Fin d → ℤ)),
      S ⊆ Icc lo hi ∧ 5 ≤ S.card ∧
      (∀ a ∈ S, ∀ T ⊆ S.erase a, T.Nonempty → ∑ x ∈ T, x ≠ T.card • a) ∧
      Real.log A.card ≤ Real.log S.card + δ * Real.log N ∧
      Real.log (Icc lo hi).card + ((d : ℝ) - 1) * Real.log A.card ≤
        (1 + δ) * Real.log N ∧
      (d = 1 → let P := S.image (fun x => x ⟨0, hd⟩)
               ∀ a ∈ P, 4 * (P.filter (· < a)).card ≤ P.card ∨
                         4 * (P.filter (a < ·)).card ≤ P.card)

/-- The planar non-averaging box bound with a multiplicative
constant, expressed on a logarithmic scale. -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ,
    ∀ (lo hi : Fin 2 → ℤ) (S : Finset (Fin 2 → ℤ)),
      S ⊆ Icc lo hi → S.Nonempty →
      (∀ a ∈ S, ∀ T ⊆ S.erase a, T.Nonempty → ∑ x ∈ T, x ≠ T.card • a) →
      3 * Real.log S.card ≤ (1 + δ) * Real.log (Icc lo hi).card + C

/-- The three-dimensional non-averaging box bound with a multiplicative
constant, expressed on a logarithmic scale. -/
def H3 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ,
    ∀ (lo hi : Fin 3 → ℤ) (S : Finset (Fin 3 → ℤ)),
      S ⊆ Icc lo hi → S.Nonempty →
      (∀ a ∈ S, ∀ T ⊆ S.erase a, T.Nonempty → ∑ x ∈ T, x ≠ T.card • a) →
      4 * Real.log S.card ≤ (2 + δ) * Real.log (Icc lo hi).card + C

/-- A proper progression need only have unique coordinates on the selected
points. The linear map from the whole coefficient lattice can have a kernel. -/
theorem affine_pullback {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [DecidableEq G] [DecidableEq H] (p : G →+ H) (b : H) (S : Finset G)
    (inj : Set.InjOn (fun x => p x + b) (S : Set G))
    (good : ∀ y ∈ S.image (fun x => p x + b),
      ∀ U ⊆ (S.image (fun x => p x + b)).erase y, U.Nonempty →
        ∑ z ∈ U, z ≠ U.card • y) :
    ∀ a ∈ S, ∀ T ⊆ S.erase a, T.Nonempty → ∑ x ∈ T, x ≠ T.card • a := by
  intro a ha T hT hne heq
  let f (x : G) := p x + b
  have hsub : T ⊆ S := fun x hx => (mem_erase.mp (hT hx)).2
  have injT : Set.InjOn f (T : Set G) := inj.mono hsub
  have card : (T.image f).card = T.card := card_image_of_injOn injT
  have hmap : T.image f ⊆ (S.image f).erase (f a) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    refine mem_erase.mpr ⟨?_, mem_image_of_mem f (hsub hx)⟩
    exact fun h => (mem_erase.mp (hT hx)).1 (inj (hsub hx) ha h)
  apply good (f a) (mem_image_of_mem f ha) (T.image f) hmap (hne.image f)
  rw [sum_image (fun _ hx _ hy h => injT hx hy h), card]
  change ∑ x ∈ T, (p x + b) = T.card • (p a + b)
  simp only [sum_add_distrib, sum_const, nsmul_add]
  apply congrArg (· + T.card • b)
  simpa only [map_sum, map_nsmul] using congrArg p heq

/-- A common signed subset sum on opposite sides of a partition gives
a forbidden average, as used in the inverse-structure argument. -/
theorem separated_subset_sums {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G)
    (good : ∀ a ∈ S, ∀ T ⊆ S.erase a, T.Nonempty → ∑ x ∈ T, x ≠ T.card • a)
    {a : G} (ha : a ∈ S) {U V : Finset G}
    (hu : U ⊆ S.erase a) (hv : V ⊆ S.erase a) (hd : Disjoint U V)
    (hne : U.Nonempty) :
    ∑ x ∈ U, (x - a) ≠ ∑ y ∈ V, (a - y) := by
  intro eq
  apply good a ha (U ∪ V) (union_subset hu hv) (hne.mono subset_union_left)
  rw [sum_union hd, card_union_of_disjoint hd, add_nsmul]
  have hright : (∑ y ∈ V, (a - y)) = V.card • a - ∑ y ∈ V, y := by
    calc
      (∑ y ∈ V, (a - y)) = (∑ _y ∈ V, a) - (∑ y ∈ V, y) :=
        sum_sub_distrib (fun _ : G => a) (fun y : G => y)
      _ = _ := by rw [sum_const]
  rw [hright] at eq
  simp only [sum_sub_distrib, sum_const] at eq
  have hsum := sub_eq_sub_iff_add_eq_add.mp eq
  simpa only [add_comm (V.card • a) (U.card • a)] using hsum

/-- A median in any ordered set of at least five points has more than a
quarter of the points strictly on either side. -/
theorem median_obstruction (P : Finset ℤ) (hP : 5 ≤ P.card) :
    ∃ a ∈ P, P.card < 4 * (P.filter (· < a)).card ∧
             P.card < 4 * (P.filter (a < ·)).card := by
  let k := (P.card - 1) / 2
  let f := P.orderEmbOfFin rfl
  let mid : Fin P.card := ⟨k, by dsimp [k]; omega⟩
  have hfour : P.card < 4 * k := by dsimp [k]; omega
  let left (i : Fin k) : Fin P.card := ⟨i.val, by have := i.isLt; dsimp [k] at *; omega⟩
  let right (i : Fin k) : Fin P.card := ⟨k + 1 + i.val, by
    have := i.isLt; dsimp [k] at *; omega⟩
  let l (i : Fin k) : ↥(P.filter (· < f mid)) := ⟨f (left i), mem_filter.mpr
    ⟨P.orderEmbOfFin_mem rfl _, f.strictMono (show left i < mid from i.isLt)⟩⟩
  let r (i : Fin k) : ↥(P.filter (f mid < ·)) := ⟨f (right i), mem_filter.mpr
    ⟨P.orderEmbOfFin_mem rfl _, f.strictMono (show mid < right i by
      change k < k + 1 + i.val; omega)⟩⟩
  have hl : Function.Injective l := by
    intro i j h
    apply Fin.ext
    have he := congrArg (fun x : ↥(P.filter (· < f mid)) => (x : ℤ)) h
    change f (left i) = f (left j) at he
    exact congrArg (fun x : Fin P.card => x.val) (show left i = left j from f.injective he)
  have hr : Function.Injective r := by
    intro i j h
    have he := congrArg (fun x : ↥(P.filter (f mid < ·)) => (x : ℤ)) h
    change f (right i) = f (right j) at he
    have eq := congrArg (fun x : Fin P.card => x.val) (show right i = right j from f.injective he)
    change k + 1 + i.val = k + 1 + j.val at eq
    exact Fin.ext (Nat.add_left_cancel eq)
  have hl' : k ≤ (P.filter (· < f mid)).card := by
    simpa using Fintype.card_le_of_injective l hl
  have hr' : k ≤ (P.filter (f mid < ·)).card := by
    simpa using Fintype.card_le_of_injective r hr
  exact ⟨f mid, P.orderEmbOfFin_mem rfl _, by omega, by omega⟩

/-- The finite optimization, with absolute errors measured on the same
logarithmic scale. Equality at zero loss occurs in dimensions 2 and 3. -/
theorem rank_bound {d : ℕ} (hd : 2 ≤ d) (hD : d ≤ 3)
    {m u v L e : ℝ} (he : 0 ≤ e)
    (hsize : m ≤ u + e)
    (hvol : v + ((d : ℝ) - 1) * m ≤ L + e)
    (hbox : ((d : ℝ) + 1) * u ≤ ((d : ℝ) - 1) * v + 3 * e) :
    m ≤ L / 4 + 3 * e := by
  interval_cases d <;> norm_num at hvol hbox <;> linarith

theorem log_bound (h₁ : H1) (h₂ : H2) (h₃ : H3) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.log (Erdos131.F N) ≤ (1 / 4 + ε) * Real.log N := by
  let δ := min (1 / 8 : ℝ) (ε / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ₁ : δ ≤ 1 / 8 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  obtain ⟨C₂, box₂⟩ := h₂ δ hδ
  obtain ⟨C₃, box₃⟩ := h₃ δ hδ
  let C := max C₂ C₃
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [h₁ ε hε δ hδ, hlog.eventually_ge_atTop (C / δ),
      eventually_ge_atTop 2] with N extract hcost hN
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have he : 0 ≤ δ * Real.log N := mul_nonneg hδ.le hL.le
  have hc : C ≤ δ * Real.log N := by
    have := (div_le_iff₀ hδ).mp hcost
    linarith
  by_contra! hbig
  obtain ⟨A, hA, hnd, hcard⟩ := Erdos131.exists_card_eq_F N
  rw [← hcard] at hbig
  have hna : ∀ a ∈ A, ∀ T ⊆ A.erase a, T.Nonempty → ∑ x ∈ T, x ≠ a * T.card := by
    intro a ha T hT hn eq
    exact hnd a ha T hT hn ⟨T.card, eq⟩
  obtain ⟨d, hd, lo, hi, S, hsub, h5, hgood, hsize, hvol, hthin⟩ := extract A hA hna hbig
  have hS : S.Nonempty := card_pos.mp (by omega)
  have hm : 0 ≤ Real.log A.card := by nlinarith [mul_nonneg hε.le hL.le]
  have h2 : 2 ≤ d := by
    by_contra! hsmall
    have hd1 : d = 1 := by omega
    let f (x : Fin d → ℤ) := x ⟨0, hd⟩
    have hf : Function.Injective f := by
      intro x y hxy
      funext i
      have eq : i = ⟨0, hd⟩ := Fin.ext (by have := i.isLt; omega)
      simpa [eq, f] using hxy
    have hcardP : (S.image f).card = S.card := card_image_of_injective _ hf
    obtain ⟨a, ha, hl, hr⟩ := median_obstruction (S.image f) (hcardP ▸ h5)
    exact (hthin hd1 a ha).elim (not_le_of_gt hl) (not_le_of_gt hr)
  by_cases h4 : 4 ≤ d
  · have hdR : (4 : ℝ) ≤ d := by exact_mod_cast h4
    have hu : Real.log S.card ≤ Real.log (Icc lo hi).card :=
      Real.log_le_log (by exact_mod_cast (show 0 < S.card by omega))
        (by exact_mod_cast card_le_card hsub)
    nlinarith only [hsize, hvol, hu, hbig, mul_nonneg (sub_nonneg.mpr hdR) hm,
      mul_nonneg (sub_nonneg.mpr hδε) hL.le, mul_nonneg hε.le hL.le]
  have hD : d ≤ 3 := by omega
  have hv' : Real.log (Icc lo hi).card ≤ 2 * Real.log N := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [mul_nonneg (sub_nonneg.mpr hdR) hm,
      mul_nonneg (sub_nonneg.mpr hδ₁) hL.le]
  have hbox : ((d : ℝ) + 1) * Real.log S.card ≤
      ((d : ℝ) - 1 + δ) * Real.log (Icc lo hi).card + C := by
    interval_cases d
    · norm_num
      exact (box₂ lo hi S hsub hS hgood).trans (by dsimp [C]; gcongr; exact le_max_left _ _)
    · norm_num
      exact (box₃ lo hi S hsub hS hgood).trans (by dsimp [C]; gcongr; exact le_max_right _ _)
  have hb : ((d : ℝ) + 1) * Real.log S.card ≤
      ((d : ℝ) - 1) * Real.log (Icc lo hi).card + 3 * (δ * Real.log N) := by
    nlinarith only [hbox, hc, mul_le_mul_of_nonneg_left hv' hδ.le]
  have hm' := rank_bound (L := Real.log N) h2 hD he hsize (by linarith only [hvol]) hb
  nlinarith only [hm', hbig, mul_nonneg (sub_nonneg.mpr hδε) hL.le,
    mul_nonneg hε.le hL.le]

theorem main : H1 → H2 → H3 → type_of% @Erdos131.erdos_131.variants.pham_zakharov := by
  intro h₁ h₂ h₃
  let f (N : ℕ) := max 0 (Real.log (Erdos131.F N) / Real.log N - 1 / 4)
  refine ⟨f, ?_, ?_⟩
  · refine Metric.tendsto_nhds.mpr ?_
    intro ε hε
    filter_upwards [log_bound h₁ h₂ h₃ (ε / 2) (by positivity), eventually_ge_atTop 2]
      with N hb hN
    have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hr := (div_le_iff₀ hL).mpr hb
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_left _ _ : 0 ≤ f N)]
    exact max_lt hε (by linarith)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hF : 0 < (Erdos131.F N : ℝ) := by
      exact_mod_cast (Erdos131.one_le_F (by omega : 1 ≤ N))
    apply (Real.log_le_log_iff hF (Real.rpow_pos_of_pos hp _)).mp
    rw [Real.log_rpow hp]
    have hle := le_max_right 0 (Real.log (Erdos131.F N) / Real.log N - 1 / 4)
    apply (div_le_iff₀ hL).mp
    dsimp [f]
    linarith

end OMA.R_Erdos131_erdos_131_variants_pham_zakharov_R1
