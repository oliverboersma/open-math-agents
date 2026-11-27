import FormalConjectures.ErdosProblems.«107»
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- Credit: @skhakim

/-!
# Holmsen–Mojarrad–Pach–Tardos Upper Bound for the Erdős–Szekeres Problem

We prove `Erdos107.variants.hmpt_bound`: there exists `r : ℕ → ℝ` with
`r =O[atTop] (fun n => Real.sqrt (n * Real.log n))` such that for all `n ≥ 3`,
`Erdos107.f n ≤ 2 ^ (n + r n)`.

The proof follows Holmsen, Mojarrad, Pach, and Tardos (J. Eur. Math. Soc. 2020,
arXiv:1710.11415), specialized directly to Euclidean `ℝ²` via signed areas (`orient`)
and the 2D barycentric identity (`orient_bary`):
1. 2D orientation, Carathéodory 4-point characterization of `ConvexIndep`, and
   counterclockwise cyclic ordering of convex `k`-gons.
2. Transitive coloring cup-cap theorem (`|S| > choose (a + b - 4) (a - 2)`) and the
   weak `4 ^ m` Erdős–Szekeres bound.
3. Double-counting convex clustering (`∏ i, |P_i| ≥ N ^ k / 2 ^ (8 * k ^ 2)`).
4. Orthogonal vertical (`≺_v`) and horizontal (`≺_h`) partial orders on each spike
   via two ray-slope functions, giving `|P_i| ≤ v_i * h_i` by Erdős–Szekeres
   monotone-subsequence pigeonhole.
5. Left/right vertical chains (`b_i + a_{i+1} < n`) and inner/outer horizontal chains
   (`d_i < n`, `∑ c_i < 2 * n`), combined into the asymptotic `2 ^ (n + O(√(n log n)))`
   bound.
-/

open Finset Filter EuclideanGeometry
open scoped Classical EuclideanGeometry

namespace HMPT

/- ### Section 1: 2D Orientation and Convex Position -/

/-- Twice the signed area of triangle `(a, b, c)` in `ℝ²`. -/
def orient (a b c : ℝ²) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

lemma orient_swap₂₃ (a b c : ℝ²) : orient a c b = -orient a b c := by
  simp only [orient]; ring

lemma orient_swap₁₂ (a b c : ℝ²) : orient b a c = -orient a b c := by
  simp only [orient]; ring

lemma orient_cyclic (a b c : ℝ²) : orient a b c = orient b c a := by
  simp only [orient]; ring

lemma orient_self₁₂ (a c : ℝ²) : orient a a c = 0 := by
  simp only [orient]; ring

lemma orient_self₁₃ (a b : ℝ²) : orient a b a = 0 := by
  simp only [orient]; ring

lemma orient_self₂₃ (a b : ℝ²) : orient a b b = 0 := by
  simp only [orient]; ring

/-- The 2D barycentric / Grassmann–Plücker identity. -/
lemma orient_bary (a b c p q z : ℝ²) :
    orient a b c * orient p q z =
      orient b c z * orient p q a +
      orient c a z * orient p q b +
      orient a b z * orient p q c := by
  simp only [orient]; ring

lemma orient_ne_zero_of_not_collinear {a b c : ℝ²}
    (hnc : ¬ Collinear ℝ ({a, b, c} : Set ℝ²)) : orient a b c ≠ 0 := by
  intro h0
  apply hnc
  by_cases hab : a = b
  · subst hab
    have : ({a, a, c} : Set ℝ²) = {a, c} := by ext x; simp
    rw [this]
    exact collinear_pair ℝ a c
  have hne : b 0 - a 0 ≠ 0 ∨ b 1 - a 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hab
    ext i
    fin_cases i
    · change a 0 = b 0; linarith
    · change a 1 = b 1; linarith
  have hcol : ∃ r : ℝ, c - a = r • (b - a) := by
    rcases hne with hx | hy
    · refine ⟨(c 0 - a 0) / (b 0 - a 0), ?_⟩
      ext i
      fin_cases i
      · change c 0 - a 0 = ((c 0 - a 0) / (b 0 - a 0)) * (b 0 - a 0)
        field_simp
      · change c 1 - a 1 = ((c 0 - a 0) / (b 0 - a 0)) * (b 1 - a 1)
        simp only [orient] at h0
        field_simp
        linarith
    · refine ⟨(c 1 - a 1) / (b 1 - a 1), ?_⟩
      ext i
      fin_cases i
      · change c 0 - a 0 = ((c 1 - a 1) / (b 1 - a 1)) * (b 0 - a 0)
        simp only [orient] at h0
        field_simp
        linarith
      · change c 1 - a 1 = ((c 1 - a 1) / (b 1 - a 1)) * (b 1 - a 1)
        field_simp
  obtain ⟨r, hr⟩ := hcol
  rw [collinear_iff_of_mem (Set.mem_insert a _)]
  refine ⟨b - a, ?_⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · refine ⟨r, ?_⟩
    rw [vadd_eq_add, ← hr]
    abel

/-- If `orient a b` strictly separates `p` from all of `S`, then `p ∉ convexHull ℝ S`. -/
lemma not_mem_convexHull_of_orient_lt {a b p : ℝ²} {S : Set ℝ²}
    (hp : orient a b p < 0) (hS : ∀ q ∈ S, 0 ≤ orient a b q) :
    p ∉ convexHull ℝ S := by
  intro hmem
  have hconv : Convex ℝ {z : ℝ² | 0 ≤ orient a b z} := by
    intro x hx y hy u v hu hv huv
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    have hid : orient a b (u • x + v • y) = u * orient a b x + v * orient a b y := by
      simp only [orient, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have : (b 0 - a 0) * (u * x 1 + v * y 1 - a 1) - (b 1 - a 1) * (u * x 0 + v * y 0 - a 0) =
          u * ((b 0 - a 0) * (x 1 - a 1) - (b 1 - a 1) * (x 0 - a 0)) +
          v * ((b 0 - a 0) * (y 1 - a 1) - (b 1 - a 1) * (y 0 - a 0)) +
          (1 - u - v) * ((b 0 - a 0) * (-a 1) - (b 1 - a 1) * (-a 0)) := by ring
      rw [this, show (1 : ℝ) - u - v = 0 by linarith, zero_mul, add_zero]
    rw [hid]
    nlinarith
  have hsub : convexHull ℝ S ⊆ {z : ℝ² | 0 ≤ orient a b z} :=
    convexHull_min (fun q hq => hS q hq) hconv
  have := hsub hmem
  simp only [Set.mem_ofPred_eq] at this
  linarith

lemma not_mem_convexHull_of_orient_gt {a b p : ℝ²} {S : Set ℝ²}
    (hp : 0 < orient a b p) (hS : ∀ q ∈ S, orient a b q ≤ 0) :
    p ∉ convexHull ℝ S := by
  apply not_mem_convexHull_of_orient_lt (a := b) (b := a)
  · rw [orient_swap₁₂]; linarith
  · intro q hq; rw [orient_swap₁₂]; linarith [hS q hq]

/-- If `orient a b c > 0` and `p` is on the positive side of all three edges of `(a, b, c)`,
then `p ∈ convexHull ℝ {a, b, c}`. -/
lemma mem_convexHull_triple_of_orient_pos {a b c p : ℝ²}
    (habc : 0 < orient a b c)
    (hab : 0 ≤ orient a b p) (hbc : 0 ≤ orient b c p) (hca : 0 ≤ orient c a p) :
    p ∈ convexHull ℝ ({a, b, c} : Set ℝ²) := by
  let Δ := orient a b c
  let α := orient b c p / Δ
  let β := orient c a p / Δ
  let γ := orient a b p / Δ
  have hα : 0 ≤ α := div_nonneg hbc habc.le
  have hβ : 0 ≤ β := div_nonneg hca habc.le
  have hγ : 0 ≤ γ := div_nonneg hab habc.le
  have hsum : α + β + γ = 1 := by
    dsimp [α, β, γ, Δ]
    rw [← add_div, ← add_div, div_eq_one_iff_eq habc.ne']
    simp only [orient]; ring
  have hcomb : α • a + β • b + γ • c = p := by
    have hne : orient a b c ≠ 0 := habc.ne'
    ext i
    fin_cases i
    · change α * a 0 + β * b 0 + γ * c 0 = p 0
      dsimp [α, β, γ, Δ]
      field_simp
      simp only [orient]; ring
    · change α * a 1 + β * b 1 + γ * c 1 = p 1
      dsimp [α, β, γ, Δ]
      field_simp
      simp only [orient]; ring
  have hmem : ∀ s : Set ℝ², Convex ℝ s → ({a, b, c} : Set ℝ²) ⊆ s → p ∈ s := by
    intro s hs hsub
    rw [← hcomb]
    have ha : a ∈ s := hsub (by simp)
    have hb : b ∈ s := hsub (by simp)
    have hc : c ∈ s := hsub (by simp)
    by_cases hαβ : α + β = 0
    · have hα0 : α = 0 := by linarith
      have hβ0 : β = 0 := by linarith
      have hγ1 : γ = 1 := by linarith
      simpa [hα0, hβ0, hγ1] using hc
    · have hpos : 0 < α + β := lt_of_le_of_ne (by linarith) (Ne.symm hαβ)
      have hab_mem : (α / (α + β)) • a + (β / (α + β)) • b ∈ s :=
        hs ha hb (div_nonneg hα hpos.le) (div_nonneg hβ hpos.le) (by field_simp)
      have hfull := hs hab_mem hc hpos.le hγ (by linarith)
      have heq : (α + β) • ((α / (α + β)) • a + (β / (α + β)) • b) + γ • c =
          α • a + β • b + γ • c := by
        rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hpos.ne',
          mul_div_cancel₀ _ hpos.ne']
      rwa [heq] at hfull
  exact hmem (convexHull ℝ {a, b, c}) (convex_convexHull ℝ _) (subset_convexHull ℝ _)

/-- If `d ∈ convexHull ℝ {a, b, c}` and `{a, b, c, d}` is `NonTrilinear` with `d ∉ {a, b, c}`,
then `orient a b c`, `orient a b d`, `orient b c d`, `orient c a d` all have the same strict sign. -/
lemma orient_same_sign_of_mem_convexHull_triple {a b c d : ℝ²}
    (hnt : NonTrilinear ({a, b, c, d} : Set ℝ²))
    (hd : d ∈ convexHull ℝ ({a, b, c} : Set ℝ²))
    (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (0 < orient a b c ∧ 0 < orient a b d ∧ 0 < orient b c d ∧ 0 < orient c a d) ∨
    (orient a b c < 0 ∧ orient a b d < 0 ∧ orient b c d < 0 ∧ orient c a d < 0) := by
  have hnc : ∀ x y z : ℝ², x ∈ ({a, b, c, d} : Set ℝ²) → y ∈ ({a, b, c, d} : Set ℝ²) →
      z ∈ ({a, b, c, d} : Set ℝ²) → x ≠ y → y ≠ z → x ≠ z → orient x y z ≠ 0 := by
    intro x y z hx hy hz hxy hyz hxz
    exact orient_ne_zero_of_not_collinear (hnt hx hy hz hxy hyz hxz)
  have habc_ne : orient a b c ≠ 0 := hnc a b c (by simp) (by simp) (by simp) hab hbc hac
  have habd_ne : orient a b d ≠ 0 := hnc a b d (by simp) (by simp) (by simp) hab hdb.symm hda.symm
  have hbcd_ne : orient b c d ≠ 0 := hnc b c d (by simp) (by simp) (by simp) hbc hdc.symm hdb.symm
  have hcad_ne : orient c a d ≠ 0 := hnc c a d (by simp) (by simp) (by simp) hac.symm hda.symm hdc.symm
  rcases lt_or_gt_of_ne habc_ne with hneg | hpos
  · right
    refine ⟨hneg, ?_, ?_, ?_⟩
    · by_contra! h
      exact not_mem_convexHull_of_orient_gt (lt_of_le_of_ne h habd_ne.symm)
        (by intro q hq; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
            rcases hq with rfl | rfl | rfl
            · rw [orient_self₁₃]
            · rw [orient_self₂₃]
            · exact hneg.le) hd
    · by_contra! h
      exact not_mem_convexHull_of_orient_gt (lt_of_le_of_ne h hbcd_ne.symm)
        (by intro q hq; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
            rcases hq with rfl | rfl | rfl
            · rw [← orient_cyclic]; exact hneg.le
            · rw [orient_self₁₃]
            · rw [orient_self₂₃]) hd
    · by_contra! h
      exact not_mem_convexHull_of_orient_gt (lt_of_le_of_ne h hcad_ne.symm)
        (by intro q hq; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
            rcases hq with rfl | rfl | rfl
            · rw [orient_self₂₃]
            · rw [orient_cyclic]; exact hneg.le
            · rw [orient_self₁₃]) hd
  · left
    refine ⟨hpos, ?_, ?_, ?_⟩
    · by_contra! h
      exact not_mem_convexHull_of_orient_lt (lt_of_le_of_ne h habd_ne)
        (by intro q hq; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
            rcases hq with rfl | rfl | rfl
            · rw [orient_self₁₃]
            · rw [orient_self₂₃]
            · exact hpos.le) hd
    · by_contra! h
      exact not_mem_convexHull_of_orient_lt (lt_of_le_of_ne h hbcd_ne)
        (by intro q hq; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
            rcases hq with rfl | rfl | rfl
            · rw [← orient_cyclic]; exact hpos.le
            · rw [orient_self₁₃]
            · rw [orient_self₂₃]) hd
    · by_contra! h
      exact not_mem_convexHull_of_orient_lt (lt_of_le_of_ne h hcad_ne)
        (by intro q hq; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
            rcases hq with rfl | rfl | rfl
            · rw [orient_self₂₃]
            · rw [orient_cyclic]; exact hpos.le
            · rw [orient_self₁₃]) hd

/-- Key 4-point lemma: if `d ∈ convexHull ℝ {a, b, c}` (general position), then `b` and `c`
lie on strictly opposite sides of the line `(a, d)`. -/
lemma orient_opposite_of_mem_convexHull_triple {a b c d : ℝ²}
    (hnt : NonTrilinear ({a, b, c, d} : Set ℝ²))
    (hd : d ∈ convexHull ℝ ({a, b, c} : Set ℝ²))
    (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    orient a d b * orient a d c < 0 := by
  rcases orient_same_sign_of_mem_convexHull_triple hnt hd hda hdb hdc hab hbc hac with
    ⟨_, habd, _, hcad⟩ | ⟨_, habd, _, hcad⟩
  · have h1 : orient a d b < 0 := by rw [orient_swap₂₃]; linarith
    have h2 : 0 < orient a d c := by rw [orient_cyclic, orient_cyclic]; exact hcad
    nlinarith
  · have h1 : 0 < orient a d b := by rw [orient_swap₂₃]; linarith
    have h2 : orient a d c < 0 := by rw [orient_cyclic, orient_cyclic]; exact hcad
    nlinarith

/-- Contrapositive: if `b` and `c` are on the same side of line `(a, d)`, then
`d ∉ convexHull ℝ {a, b, c}`. -/
lemma not_mem_convexHull_triple_of_same_side {a b c d : ℝ²}
    (hnt : NonTrilinear ({a, b, c, d} : Set ℝ²))
    (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hsame : 0 < orient a d b * orient a d c) :
    d ∉ convexHull ℝ ({a, b, c} : Set ℝ²) := by
  intro hd
  have hopp := orient_opposite_of_mem_convexHull_triple hnt hd hda hdb hdc hab hbc hac
  linarith

/-- 2D Carathéodory characterization: a `NonTrilinear` set `S` is `ConvexIndep` iff no
point of `S` lies in the convex hull of three other distinct points of `S`. -/
lemma convexIndep_of_forall_triple {S : Set ℝ²} (hnt : NonTrilinear S)
    (h : ∀ a b c d : ℝ², a ∈ S → b ∈ S → c ∈ S → d ∈ S →
      d ≠ a → d ≠ b → d ≠ c → a ≠ b → b ≠ c → a ≠ c →
      d ∉ convexHull ℝ ({a, b, c} : Set ℝ²)) :
    ConvexIndep S := by
  intro d hd hmem
  rw [convexHull_eq_union] at hmem
  simp only [Set.mem_iUnion, exists_prop] at hmem
  obtain ⟨t, ht_sub, ht_ind, hd_t⟩ := hmem
  have ht_card : t.card ≤ 3 := by
    calc t.card
        = Fintype.card t := (Fintype.card_coe t).symm
      _ ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → ℝ²))) + 1 :=
          AffineIndependent.card_le_finrank_succ ht_ind
      _ ≤ Module.finrank ℝ ℝ² + 1 := Nat.add_le_add_right (Submodule.finrank_le _) 1
      _ = 3 := by rw [finrank_euclideanSpace_fin]
  have ht_pos : 0 < t.card := by
    by_contra h0
    have hte : t = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hte
    simp at hd_t
  have hcard_cases : t.card = 1 ∨ t.card = 2 ∨ t.card = 3 := by omega
  rcases hcard_cases with h1 | h2 | h3
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    simp only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] at hd_t
    have ha : a ∈ S \ {d} := ht_sub (by simp)
    exact ha.2 hd_t.symm
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
    have ha : a ∈ S \ {d} := ht_sub (by simp)
    have hb : b ∈ S \ {d} := ht_sub (by simp)
    have hda : d ≠ a := fun heq => ha.2 heq.symm
    have hdb : d ≠ b := fun heq => hb.2 heq.symm
    have haff : d ∈ affineSpan ℝ ({a, b} : Set ℝ²) := by
      have hcoe : (({a, b} : Finset ℝ²) : Set ℝ²) = ({a, b} : Set ℝ²) := by simp
      have hd_s : d ∈ convexHull ℝ ({a, b} : Set ℝ²) := hcoe ▸ hd_t
      exact convexHull_subset_affineSpan _ hd_s
    have hcol : Collinear ℝ ({d, a, b} : Set ℝ²) := by
      rw [collinear_insert_iff_of_mem_affineSpan haff]
      exact collinear_pair ℝ a b
    exact hnt hd ha.1 hb.1 hda hab hdb hcol
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h3
    have ha : a ∈ S \ {d} := ht_sub (by simp)
    have hb : b ∈ S \ {d} := ht_sub (by simp)
    have hc : c ∈ S \ {d} := ht_sub (by simp)
    exact h a b c d ha.1 hb.1 hc.1 hd
      (fun heq => ha.2 heq.symm) (fun heq => hb.2 heq.symm) (fun heq => hc.2 heq.symm)
      hab hbc hac (by simpa using hd_t)

/- ### Section 2: Counterclockwise Convex Polygons and Spikes -/

/-- A sequence `x : Fin k → ℝ²` is strictly counterclockwise convex if every increasing
triple has strictly positive `orient`. -/
def IsCcw (x : Fin k → ℝ²) : Prop :=
  ∀ ⦃i j l : Fin k⦄, i < j → j < l → 0 < orient (x i) (x j) (x l)

lemma IsCcw.injective {k : ℕ} {x : Fin k → ℝ²} (hk : 3 ≤ k) (hx : IsCcw x) :
    Function.Injective x := by
  intro i j hij
  by_contra hne
  wlog hlt : i < j generalizing i j
  · exact this hij.symm (Ne.symm hne) (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne))
  -- Find a third index l ≠ i, j
  have hex : ∃ l : Fin k, l ≠ i ∧ l ≠ j := by
    have hcard : ({i, j} : Finset (Fin k)).card = 2 := Finset.card_pair hne
    have hlt' : ({i, j} : Finset (Fin k)).card < (Finset.univ : Finset (Fin k)).card := by
      rw [hcard, Finset.card_univ, Fintype.card_fin]; omega
    obtain ⟨l, _, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt'
    exact ⟨l, by simpa using hl⟩
  obtain ⟨l, hli, hlj⟩ := hex
  rcases lt_or_gt_of_ne hli with h1 | h1
  · have hpos := hx h1 hlt
    rw [hij, orient_self₂₃] at hpos; linarith
  · rcases lt_or_gt_of_ne hlj with h2 | h2
    · have hpos := hx h1 h2
      rw [hij, orient_self₁₃] at hpos; linarith
    · have hpos := hx hlt h2
      rw [hij, orient_self₁₂] at hpos; linarith

lemma IsCcw.orient_cyc {k : ℕ} {x : Fin k → ℝ²} (hx : IsCcw x)
    {a b c : Fin k} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hcyc : (b.val + k - a.val) % k < (c.val + k - a.val) % k) :
    0 < orient (x a) (x b) (x c) := by
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
  have h1 : (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b) := by
    have hne1 : a.val ≠ b.val := fun h => hab (Fin.ext h)
    have hne2 : b.val ≠ c.val := fun h => hbc (Fin.ext h)
    have hne3 : a.val ≠ c.val := fun h => hac (Fin.ext h)
    by_cases hba : a.val < b.val <;> by_cases hca : a.val < c.val
    · have hmb : (b.val + k - a.val) % k = b.val - a.val := by
        rw [show b.val + k - a.val = k + (b.val - a.val) by omega, Nat.add_mod_left,
            Nat.mod_eq_of_lt (by omega)]
      have hmc : (c.val + k - a.val) % k = c.val - a.val := by
        rw [show c.val + k - a.val = k + (c.val - a.val) by omega, Nat.add_mod_left,
            Nat.mod_eq_of_lt (by omega)]
      rw [hmb, hmc] at hcyc; left; exact ⟨Fin.lt_def.mpr hba, Fin.lt_def.mpr (by omega)⟩
    · have hmb : (b.val + k - a.val) % k = b.val - a.val := by
        rw [show b.val + k - a.val = k + (b.val - a.val) by omega, Nat.add_mod_left,
            Nat.mod_eq_of_lt (by omega)]
      have hmc : (c.val + k - a.val) % k = c.val + k - a.val := Nat.mod_eq_of_lt (by omega)
      right; right; exact ⟨Fin.lt_def.mpr (by omega), Fin.lt_def.mpr hba⟩
    · have hmb : (b.val + k - a.val) % k = b.val + k - a.val := Nat.mod_eq_of_lt (by omega)
      have hmc : (c.val + k - a.val) % k = c.val - a.val := by
        rw [show c.val + k - a.val = k + (c.val - a.val) by omega, Nat.add_mod_left,
            Nat.mod_eq_of_lt (by omega)]
      rw [hmb, hmc] at hcyc; omega
    · have hmb : (b.val + k - a.val) % k = b.val + k - a.val := Nat.mod_eq_of_lt (by omega)
      have hmc : (c.val + k - a.val) % k = c.val + k - a.val := Nat.mod_eq_of_lt (by omega)
      rw [hmb, hmc] at hcyc; right; left; exact ⟨Fin.lt_def.mpr (by omega), Fin.lt_def.mpr (by omega)⟩
  rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hx h1 h2
  · rw [orient_cyclic]; exact hx h1 h2
  · rw [orient_cyclic, orient_cyclic]; exact hx h1 h2

/-- Any finite `ConvexIndep`, `NonTrilinear` set `X` of size `k ≥ 3` can be ordered
counterclockwise as `x : Fin k → ℝ²` with `IsCcw x`. -/
lemma exists_ccw_ordering {X : Finset ℝ²} {k : ℕ} (hk : 3 ≤ k) (hcard : X.card = k)
    (hnt : NonTrilinear (X : Set ℝ²)) (hconv : ConvexIndep (X : Set ℝ²)) :
    ∃ x : Fin k → ℝ², IsCcw x ∧ (∀ i, x i ∈ X) ∧ Function.Injective x := by
  have hne : X.Nonempty := Finset.card_pos.mp (by omega)
  -- Pick x₀ minimizing (p 0, p 1) lexicographically
  let lexLe (p q : ℝ²) : Prop := p 0 < q 0 ∨ (p 0 = q 0 ∧ p 1 ≤ q 1)
  have hlex_total : ∀ p q, lexLe p q ∨ lexLe q p := by
    intro p q; rcases lt_trichotomy (p 0) (q 0) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases le_total (p 1) (q 1) with h1 | h1
      · exact Or.inl (Or.inr ⟨h, h1⟩)
      · exact Or.inr (Or.inr ⟨h.symm, h1⟩)
    · exact Or.inr (Or.inl h)
  have hlex_trans : ∀ p q r, lexLe p q → lexLe q r → lexLe p r := by
    intro p q r h1 h2
    rcases h1 with h1 | ⟨h1a, h1b⟩ <;> rcases h2 with h2 | ⟨h2a, h2b⟩
    · exact Or.inl (h1.trans h2)
    · exact Or.inl (h2a ▸ h1)
    · exact Or.inl (h1a.symm ▸ h2)
    · exact Or.inr ⟨h1a.trans h2a, h1b.trans h2b⟩
  -- Find lex minimum x₀ in X by induction on finsets
  have hex_min_aux : ∀ S : Finset ℝ², S.Nonempty → ∃ x₀ ∈ S, ∀ p ∈ S, lexLe x₀ p := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro h; exact (Finset.not_nonempty_empty h).elim
    | @insert a s has ih =>
      intro _
      by_cases hs : s.Nonempty
      · obtain ⟨m, hm, hmin⟩ := ih hs
        rcases hlex_total a m with ham | hma
        · exact ⟨a, Finset.mem_insert_self a s, fun p hp => by
            rcases Finset.mem_insert.mp hp with rfl | hp'
            · exact Or.inr ⟨rfl, le_rfl⟩
            · exact hlex_trans a m p ham (hmin p hp')⟩
        · exact ⟨m, Finset.mem_insert_of_mem hm, fun p hp => by
            rcases Finset.mem_insert.mp hp with rfl | hp'
            · exact hma
            · exact hmin p hp'⟩
      · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst hse
        exact ⟨a, by simp, fun p hp => by
          rw [Finset.mem_singleton.mp hp]; exact Or.inr ⟨rfl, le_rfl⟩⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hex_min_aux X hne
  let R := X.erase x₀
  have hR_card : R.card = k - 1 := by rw [Finset.card_erase_of_mem hx₀, hcard]
  -- On R, `orient x₀ p q > 0` is a strict total order!
  have hor_trans : ∀ p ∈ R, ∀ q ∈ R, ∀ r ∈ R,
      0 < orient x₀ p q → 0 < orient x₀ q r → 0 < orient x₀ p r := by
    intro p hp q hq r hr hpq hqr
    have hpX : p ∈ X := Finset.mem_of_mem_erase hp
    have hqX : q ∈ X := Finset.mem_of_mem_erase hq
    have hrX : r ∈ X := Finset.mem_of_mem_erase hr
    have hp0 : x₀ 0 ≤ p 0 := by rcases hmin p hpX with h | ⟨h, _⟩ <;> linarith
    have hq0 : x₀ 0 ≤ q 0 := by rcases hmin q hqX with h | ⟨h, _⟩ <;> linarith
    have hr0 : x₀ 0 ≤ r 0 := by rcases hmin r hrX with h | ⟨h, _⟩ <;> linarith
    have hpx : p ≠ x₀ := Finset.ne_of_mem_erase hp
    have hqx : q ≠ x₀ := Finset.ne_of_mem_erase hq
    have hrx : r ≠ x₀ := Finset.ne_of_mem_erase hr
    have hdp : 0 ≤ p 0 - x₀ 0 := by linarith
    have hdq : 0 ≤ q 0 - x₀ 0 := by linarith
    have hdr : 0 ≤ r 0 - x₀ 0 := by linarith
    -- Key identity: (q 0 - x₀ 0) * orient x₀ p r = (r 0 - x₀ 0) * orient x₀ p q + (p 0 - x₀ 0) * orient x₀ q r
    have hid : (q 0 - x₀ 0) * orient x₀ p r =
        (r 0 - x₀ 0) * orient x₀ p q + (p 0 - x₀ 0) * orient x₀ q r := by
      simp only [orient]; ring
    by_cases hq_eq : q 0 = x₀ 0
    · -- q is vertically above x₀, so q 1 > x₀ 1, hence orient x₀ p q = (p 0 - x₀ 0)*(q 1 - x₀ 1) > 0
      -- and orient x₀ q r = -(q 1 - x₀ 1)*(r 0 - x₀ 0) ≤ 0, contradicting hqr > 0!
      have hq1 : x₀ 1 < q 1 := by
        rcases hmin q hqX with h | ⟨_, h1⟩
        · linarith
        · refine lt_of_le_of_ne h1 ?_
          intro heq; apply hqx; ext i; fin_cases i <;> [exact hq_eq; exact heq.symm]
      have hqr_le : orient x₀ q r ≤ 0 := by
        simp only [orient, hq_eq, sub_self, zero_mul, zero_sub]
        nlinarith
      linarith
    · have hq_pos : 0 < q 0 - x₀ 0 := lt_of_le_of_ne hdq (fun h => hq_eq (by linarith))
      by_cases hpr_zero : p 0 - x₀ 0 = 0 ∧ r 0 - x₀ 0 = 0
      · -- Both p and r have x-coord equal to x₀ 0, so x₀, p, r are collinear!
        have hpq_ne : p ≠ r := by
          intro h; subst h; rw [orient_swap₂₃] at hqr; linarith
        have hcol : Collinear ℝ ({x₀, p, r} : Set ℝ²) := by
          rw [collinear_iff_of_mem (Set.mem_insert x₀ _)]
          refine ⟨EuclideanSpace.single 1 1, ?_⟩
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with hzx | hzp | hzr
          · rw [hzx]; exact ⟨0, by simp⟩
          · rw [hzp]; refine ⟨p 1 - x₀ 1, ?_⟩
            ext i; fin_cases i
            · change p 0 = (p 1 - x₀ 1) * (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 0 + x₀ 0
              simp [EuclideanSpace.single]; linarith [hpr_zero.1]
            · change p 1 = (p 1 - x₀ 1) * (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 1 + x₀ 1
              simp [EuclideanSpace.single]
          · rw [hzr]; refine ⟨r 1 - x₀ 1, ?_⟩
            ext i; fin_cases i
            · change r 0 = (r 1 - x₀ 1) * (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 0 + x₀ 0
              simp [EuclideanSpace.single]; linarith [hpr_zero.2]
            · change r 1 = (r 1 - x₀ 1) * (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 1 + x₀ 1
              simp [EuclideanSpace.single]
        exact (hnt hx₀ hpX hrX hpx.symm hpq_ne hrx.symm hcol).elim
      · have hpos_rhs : 0 < (r 0 - x₀ 0) * orient x₀ p q + (p 0 - x₀ 0) * orient x₀ q r := by
          by_cases hr0' : r 0 - x₀ 0 = 0
          · have hp0' : 0 < p 0 - x₀ 0 :=
              lt_of_le_of_ne hdp (fun h => hpr_zero ⟨h.symm, hr0'⟩)
            nlinarith
          · have hr0'' : 0 < r 0 - x₀ 0 := lt_of_le_of_ne hdr (Ne.symm hr0')
            nlinarith
        nlinarith
  -- Sort R by `orient x₀ p q > 0` by induction on Finset cardinality
  have hsort : ∀ (S : Finset ℝ²), S ⊆ R →
      ∃ f : Fin S.card → ℝ², (∀ i, f i ∈ S) ∧ Function.Injective f ∧
        ∀ ⦃i j : Fin S.card⦄, i < j → 0 < orient x₀ (f i) (f j) := by
    intro S
    induction hn : S.card generalizing S with
    | zero =>
      intro _
      refine ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | succ m ih =>
      intro hSR
      have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
      -- Pick minimum element of S under `orient x₀ · · > 0`
      have hex_minS_aux : ∀ T : Finset ℝ², T.Nonempty → T ⊆ R →
          ∃ u ∈ T, ∀ v ∈ T, v ≠ u → 0 < orient x₀ u v := by
        clear ih hn hSR hSne
        intro T
        induction T using Finset.induction_on with
        | empty => intro h _; exact (Finset.not_nonempty_empty h).elim
        | @insert a t hat iht =>
          intro _ hTR
          by_cases ht : t.Nonempty
          · have htR : t ⊆ R := fun z hz => hTR (Finset.mem_insert_of_mem hz)
            have haR : a ∈ R := hTR (Finset.mem_insert_self a t)
            obtain ⟨u, hu, humin⟩ := iht ht htR
            have huR : u ∈ R := htR hu
            have hau : a ≠ u := fun h => hat (h ▸ hu)
            have hne0 : orient x₀ a u ≠ 0 := orient_ne_zero_of_not_collinear
              (hnt hx₀ (Finset.mem_of_mem_erase haR) (Finset.mem_of_mem_erase huR)
                (Finset.ne_of_mem_erase haR).symm hau (Finset.ne_of_mem_erase huR).symm)
            rcases lt_or_gt_of_ne hne0 with hneg | hpos
            · refine ⟨u, Finset.mem_insert_of_mem hu, fun v hv hvu => ?_⟩
              rcases Finset.mem_insert.mp hv with rfl | hvt
              · rw [orient_swap₂₃]; linarith
              · exact humin v hvt hvu
            · refine ⟨a, Finset.mem_insert_self a t, fun v hv hva => ?_⟩
              rcases Finset.mem_insert.mp hv with rfl | hvt
              · exact (hva rfl).elim
              · by_cases hvu : v = u
                · rwa [hvu]
                · exact hor_trans a haR u huR v (htR hvt) hpos (humin v hvt hvu)
          · have hte : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
            subst hte
            exact ⟨a, by simp, fun v hv hne => (hne (Finset.mem_singleton.mp hv)).elim⟩
      obtain ⟨u, huS, humin⟩ := hex_minS_aux S hSne hSR
      let S' := S.erase u
      have hS'card : S'.card = m := by rw [Finset.card_erase_of_mem huS, hn]; omega
      obtain ⟨f', hf'mem, hf'inj, hf'ord⟩ := ih S' hS'card
        (fun z hz => hSR (Finset.mem_of_mem_erase hz))
      let g : Fin (m + 1) → ℝ² := Fin.cons u f'
      refine ⟨g, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases huS (fun j => Finset.mem_of_mem_erase (hf'mem j)) i
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i
        · refine Fin.cases (fun _ => rfl) (fun j h => ?_) j
          simp only [g, Fin.cons_zero, Fin.cons_succ] at h
          exact (Finset.ne_of_mem_erase (hf'mem j) h.symm).elim
        · refine Fin.cases (fun h => ?_) (fun j h => ?_) j
          · simp only [g, Fin.cons_zero, Fin.cons_succ] at h
            exact (Finset.ne_of_mem_erase (hf'mem i) h).elim
          · simp only [g, Fin.cons_succ] at h
            exact congrArg Fin.succ (hf'inj h)
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i
        · refine Fin.cases (fun h => (lt_irrefl _ h).elim) (fun j _ => ?_) j
          simp only [g, Fin.cons_zero, Fin.cons_succ]
          have hm := hf'mem j
          exact humin _ (Finset.mem_of_mem_erase hm) (Finset.ne_of_mem_erase hm)
        · refine Fin.cases (fun h => (Nat.not_lt_zero _ (Fin.lt_def.mp h)).elim) (fun j hlt' => ?_) j
          simp only [g, Fin.cons_succ]
          exact hf'ord (Fin.lt_def.mpr (by have := Fin.lt_def.mp hlt'; dsimp at this; omega))
  obtain ⟨f, hfmem, hfinj, hford⟩ := hsort R Subset.rfl
  let x : Fin k → ℝ² := fun i =>
    if h0 : i.val = 0 then x₀
    else f ⟨i.val - 1, by rw [hR_card]; omega⟩
  have hx_mem : ∀ i, x i ∈ X := by
    intro i; dsimp [x]; split_ifs with h0
    · exact hx₀
    · exact Finset.mem_of_mem_erase (hfmem _)
  have hx_inj : Function.Injective x := by
    intro i j hij
    dsimp [x] at hij
    split_ifs at hij with hi hj hj
    · exact Fin.ext (by omega)
    · exact (Finset.ne_of_mem_erase (hfmem _) hij.symm).elim
    · exact (Finset.ne_of_mem_erase (hfmem _) hij).elim
    · have := hfinj hij
      exact Fin.ext (by have := congrArg Fin.val this; dsimp at this; omega)
  refine ⟨x, ?_, hx_mem, hx_inj⟩
  intro i j l hij hjl
  have hij_v : i.val < j.val := Fin.lt_def.mp hij
  have hjl_v : j.val < l.val := Fin.lt_def.mp hjl
  by_cases hi0 : i.val = 0
  · have hj0 : j.val ≠ 0 := by omega
    have hl0 : l.val ≠ 0 := by omega
    simp only [x, hi0, hj0, hl0, ↓reduceDIte]
    exact hford (Fin.lt_def.mpr (by dsimp; omega))
  · have hj0 : j.val ≠ 0 := by omega
    have hl0 : l.val ≠ 0 := by omega
    have h0i : 0 < orient x₀ (x i) (x j) := by
      simp only [x, hi0, hj0, ↓reduceDIte]
      exact hford (Fin.lt_def.mpr (by dsimp; omega))
    have h0j : 0 < orient x₀ (x j) (x l) := by
      simp only [x, hj0, hl0, ↓reduceDIte]
      exact hford (Fin.lt_def.mpr (by dsimp; omega))
    have h0l : 0 < orient x₀ (x i) (x l) := by
      simp only [x, hi0, hl0, ↓reduceDIte]
      exact hford (Fin.lt_def.mpr (by dsimp; omega))
    have hne : orient (x i) (x j) (x l) ≠ 0 := orient_ne_zero_of_not_collinear
      (hnt (hx_mem i) (hx_mem j) (hx_mem l)
        (hx_inj.ne hij.ne) (hx_inj.ne hjl.ne) (hx_inj.ne (hij.trans hjl).ne))
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hmem : x j ∈ convexHull ℝ ({x₀, x i, x l} : Set ℝ²) := by
        apply mem_convexHull_triple_of_orient_pos h0l h0i.le
        · rw [orient_swap₂₃]; linarith
        · rw [orient_cyclic]; exact h0j.le
      have hsub : ({x₀, x i, x l} : Set ℝ²) ⊆ (X : Set ℝ²) \ {x j} := by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hzx | hzi | hzl
        · rw [hzx]; refine ⟨hx₀, ?_⟩
          intro h
          have hx0 : x ⟨0, by omega⟩ = x₀ := by simp [x]
          have heq : j = ⟨0, by omega⟩ := hx_inj (h.symm.trans hx0.symm)
          exact hj0 (congrArg Fin.val heq)
        · rw [hzi]; exact ⟨hx_mem i, hx_inj.ne hij.ne⟩
        · rw [hzl]; exact ⟨hx_mem l, hx_inj.ne hjl.ne.symm⟩
      exact (hconv (x j) (hx_mem j) (convexHull_mono hsub hmem)).elim
    · exact hpos

/-- `inSpike x i p` means `p` sits in the `i`-th spike of the counterclockwise `k`-gon `x`,
expressed directly by its orientation against every directed chord `(x a, x b)`. -/
def inSpike {k : ℕ} (x : Fin k → ℝ²) (i : Fin k) (p : ℝ²) : Prop :=
  ∀ a b : Fin k, a ≠ b →
    if (i.val + k - a.val) % k < (b.val + k - a.val) % k
    then orient (x a) (x b) p < 0
    else 0 < orient (x a) (x b) p

/-- Helper: cyclic distance on `Fin k` equals `(b - a).val`! -/
lemma fin_cyc_dist_eq_sub {k : ℕ} [NeZero k] (a b : Fin k) :
    (b.val + k - a.val) % k = (b - a).val := by
  have ha := a.isLt; have hb := b.isLt
  rw [Fin.val_sub]
  have : b.val + k - a.val = k - a.val + b.val := by omega
  rw [this]

lemma fin_val_ofNat_of_lt {k : ℕ} [NeZero k] (d : ℕ) (hd : d < k) :
    (Fin.ofNat k d).val = d := by
  simp [Nat.mod_eq_of_lt hd]

lemma fin_one_add_one {k : ℕ} [NeZero k] : (1 : Fin k) + 1 = 2 := by
  apply Fin.ext
  change ((1 % k) + (1 % k)) % k = 2 % k
  rw [Nat.mod_add_mod, Nat.add_mod_mod]

lemma fin_two_add_one {k : ℕ} [NeZero k] : (2 : Fin k) + 1 = 3 := by
  apply Fin.ext
  change ((2 % k) + (1 % k)) % k = 3 % k
  rw [Nat.mod_add_mod, Nat.add_mod_mod]

lemma fin_val_one_of_ge {k : ℕ} [NeZero k] (hk : 2 ≤ k) :
    (1 : Fin k).val = 1 := by
  change (Fin.ofNat k 1).val = 1
  exact fin_val_ofNat_of_lt 1 (by omega)

lemma fin_sub_add_cancel_cyc {k : ℕ} [NeZero k] (a b c : Fin k) :
    ((a + b) - (a + c) : Fin k) = b - c := by abel

lemma fin_ne_add_one {k : ℕ} [NeZero k] (hk : 2 ≤ k) (i : Fin k) : i ≠ i + 1 := by
  intro h; have h0 := congrArg (fun z : Fin k => (z - i).val) h
  simp only [sub_self, add_sub_cancel_left, Fin.val_zero, fin_val_one_of_ge hk] at h0; omega

lemma fin_ne_sub_one {k : ℕ} [NeZero k] (hk : 2 ≤ k) (i : Fin k) : i - 1 ≠ i := by
  intro h; exact fin_ne_add_one hk (i - 1) (by simpa [sub_add_cancel] using h)

lemma inSpike_disjoint {k : ℕ} [NeZero k] (hk : 3 ≤ k) {x : Fin k → ℝ²}
    {i j : Fin k} (hij : i ≠ j) {p : ℝ²} (hi : inSpike x i p) (hj : inSpike x j p) : False := by
  have h1 : (1 : Fin k).val = 1 := fin_val_one_of_ge (by omega)
  have hne : i ≠ i + 1 := fin_ne_add_one (by omega) i
  have hlt1 : (i.val + k - i.val) % k < ((i + 1).val + k - i.val) % k := by
    rw [fin_cyc_dist_eq_sub, fin_cyc_dist_eq_sub, sub_self, add_sub_cancel_left, Fin.val_zero, h1]
    omega
  have hlt2 : ¬ ((j.val + k - i.val) % k < ((i + 1).val + k - i.val) % k) := by
    rw [fin_cyc_dist_eq_sub, fin_cyc_dist_eq_sub, add_sub_cancel_left, h1]
    have hne0 : j - i ≠ 0 := sub_ne_zero.mpr hij.symm
    have hpos : 0 < (j - i).val := Nat.pos_of_ne_zero (fun h => hne0 (Fin.ext h))
    omega
  have ha := hi i (i + 1) hne; rw [if_pos hlt1] at ha
  have hb := hj i (i + 1) hne; rw [if_neg hlt2] at hb
  linarith

lemma inSpike_edge_lt {k : ℕ} [NeZero k] (hk : 3 ≤ k) {x : Fin k → ℝ²}
    {i : Fin k} {p : ℝ²} (hi : inSpike x i p) :
    orient (x i) (x (i + 1)) p < 0 := by
  have h1 : (1 : Fin k).val = 1 := fin_val_one_of_ge (by omega)
  have hne : i ≠ i + 1 := fin_ne_add_one (by omega) i
  have hlt : (i.val + k - i.val) % k < ((i + 1).val + k - i.val) % k := by
    rw [fin_cyc_dist_eq_sub, fin_cyc_dist_eq_sub, sub_self, add_sub_cancel_left, Fin.val_zero, h1]
    omega
  have h := hi i (i + 1) hne; rwa [if_pos hlt] at h

lemma inSpike_other_edge_gt {k : ℕ} [NeZero k] (hk : 3 ≤ k) {x : Fin k → ℝ²}
    {i j : Fin k} (hij : j ≠ i) {p : ℝ²} (hi : inSpike x i p) :
    0 < orient (x j) (x (j + 1)) p := by
  have h1 : (1 : Fin k).val = 1 := fin_val_one_of_ge (by omega)
  have hne : j ≠ j + 1 := fin_ne_add_one (by omega) j
  have hnot : ¬ ((i.val + k - j.val) % k < ((j + 1).val + k - j.val) % k) := by
    rw [fin_cyc_dist_eq_sub, fin_cyc_dist_eq_sub, add_sub_cancel_left, h1]
    have hne0 : i - j ≠ 0 := sub_ne_zero.mpr hij.symm
    have hpos : 0 < (i - j).val := Nat.pos_of_ne_zero (fun h => hne0 (Fin.ext h))
    omega
  have h := hi j (j + 1) hne; rwa [if_neg hnot] at h

lemma fin_val_neg_ofNat {k : ℕ} [NeZero k] (d : ℕ) (hd : 0 < d) (hdk : d < k) :
    (-(Fin.ofNat k d)).val = k - d := by
  rw [Fin.val_neg, fin_val_ofNat_of_lt d hdk]
  have hne : Fin.ofNat k d ≠ 0 := by
    intro h; have hv := congrArg Fin.val h
    rw [fin_val_ofNat_of_lt d hdk, Fin.val_zero] at hv; omega
  rw [if_neg hne]

lemma fin_ofNat_1 {k : ℕ} [NeZero k] : Fin.ofNat k 1 = (1 : Fin k) := rfl
lemma fin_ofNat_2 {k : ℕ} [NeZero k] : Fin.ofNat k 2 = (2 : Fin k) := rfl
lemma fin_ofNat_3 {k : ℕ} [NeZero k] : Fin.ofNat k 3 = (3 : Fin k) := rfl

lemma inSpike_base_gt {k : ℕ} [NeZero k] (hk : 4 ≤ k) {x : Fin k → ℝ²}
    {i : Fin k} {p : ℝ²} (hi : inSpike x i p) :
    0 < orient (x (i + 2)) (x (i - 1)) p := by
  have hd1 : (i - (i + 2) : Fin k).val = k - 2 := by
    rw [show (i - (i + 2) : Fin k) = -(Fin.ofNat k 2) by rw [fin_ofNat_2]; abel]
    exact fin_val_neg_ofNat 2 (by omega) (by omega)
  have hd2 : ((i - 1) - (i + 2) : Fin k).val = k - 3 := by
    rw [show ((i - 1) - (i + 2) : Fin k) = -(Fin.ofNat k 3) by
      rw [fin_ofNat_3, ← fin_two_add_one, ← fin_one_add_one]; abel]
    exact fin_val_neg_ofNat 3 (by omega) (by omega)
  have hne : i + 2 ≠ i - 1 := by
    intro h
    have h0 := congrArg (fun z : Fin k => (z - (i + 2)).val) h.symm
    rw [hd2, sub_self, Fin.val_zero] at h0; omega
  have h := hi (i + 2) (i - 1) hne
  rw [fin_cyc_dist_eq_sub, fin_cyc_dist_eq_sub, hd1, hd2, if_neg (by omega)] at h
  exact h

lemma inSpike_diag_gt {k : ℕ} [NeZero k] (hk : 4 ≤ k) {x : Fin k → ℝ²}
    {i : Fin k} {p : ℝ²} (hi : inSpike x i p) :
    0 < orient (x (i + 1)) (x (i - 1)) p := by
  have hd1 : (i - (i + 1) : Fin k).val = k - 1 := by
    rw [show (i - (i + 1) : Fin k) = -(Fin.ofNat k 1) by rw [fin_ofNat_1]; abel]
    exact fin_val_neg_ofNat 1 (by omega) (by omega)
  have hd2 : ((i - 1) - (i + 1) : Fin k).val = k - 2 := by
    rw [show ((i - 1) - (i + 1) : Fin k) = -(Fin.ofNat k 2) by
      rw [fin_ofNat_2, ← fin_one_add_one]; abel]
    exact fin_val_neg_ofNat 2 (by omega) (by omega)
  have hne : i + 1 ≠ i - 1 := by
    intro h
    have h0 := congrArg (fun z : Fin k => (z - (i + 1)).val) h.symm
    rw [hd2, sub_self, Fin.val_zero] at h0; omega
  have h := hi (i + 1) (i - 1) hne
  rw [fin_cyc_dist_eq_sub, fin_cyc_dist_eq_sub, hd1, hd2, if_neg (by omega)] at h
  exact h

lemma inSpike_diag2_gt {k : ℕ} [NeZero k] (hk : 4 ≤ k) {x : Fin k → ℝ²}
    {i : Fin k} {p : ℝ²} (hi : inSpike x i p) :
    0 < orient (x (i + 2)) (x i) p := by
  have hd1 : (i - (i + 2) : Fin k).val = k - 2 := by
    rw [show (i - (i + 2) : Fin k) = -(Fin.ofNat k 2) by rw [fin_ofNat_2]; abel]
    exact fin_val_neg_ofNat 2 (by omega) (by omega)
  have hne : i + 2 ≠ i := by
    intro h
    have h0 := congrArg (fun z : Fin k => (z - (i + 2)).val) h.symm
    rw [hd1, sub_self, Fin.val_zero] at h0; omega
  have h := hi (i + 2) i hne
  rwa [if_neg (lt_irrefl _)] at h

lemma inSpike_next_diag_gt {k : ℕ} [NeZero k] (hk : 4 ≤ k) {x : Fin k → ℝ²}
    {i : Fin k} {z : ℝ²} (hz : inSpike x (i + 1) z) :
    0 < orient (x (i + 2)) (x i) z := by
  have hd1 : ((i + 1) - (i + 2) : Fin k).val = k - 1 := by
    rw [show ((i + 1) - (i + 2) : Fin k) = -(Fin.ofNat k 1) by
      rw [fin_ofNat_1, ← fin_one_add_one]; abel]
    exact fin_val_neg_ofNat 1 (by omega) (by omega)
  have hd2 : (i - (i + 2) : Fin k).val = k - 2 := by
    rw [show (i - (i + 2) : Fin k) = -(Fin.ofNat k 2) by rw [fin_ofNat_2]; abel]
    exact fin_val_neg_ofNat 2 (by omega) (by omega)
  have hne : i + 2 ≠ i := by
    intro h
    have h0 := congrArg (fun z : Fin k => (z - (i + 2)).val) h.symm
    rw [hd2, sub_self, Fin.val_zero] at h0; omega
  have h := hz (i + 2) i hne
  rw [fin_cyc_dist_eq_sub, fin_cyc_dist_eq_sub, hd1, hd2, if_neg (by omega)] at h
  exact h

lemma inSpike_prev_diag_gt {k : ℕ} [NeZero k] (hk : 4 ≤ k) {x : Fin k → ℝ²}
    {i : Fin k} {z : ℝ²} (hz : inSpike x (i - 1) z) :
    0 < orient (x (i + 1)) (x (i - 1)) z := by
  have hd2 : ((i - 1) - (i + 1) : Fin k).val = k - 2 := by
    rw [show ((i - 1) - (i + 1) : Fin k) = -(Fin.ofNat k 2) by
      rw [fin_ofNat_2, ← fin_one_add_one]; abel]
    exact fin_val_neg_ofNat 2 (by omega) (by omega)
  have hne : i + 1 ≠ i - 1 := by
    intro h
    have h0 := congrArg (fun z : Fin k => (z - (i + 1)).val) h.symm
    rw [hd2, sub_self, Fin.val_zero] at h0; omega
  have h := hz (i + 1) (i - 1) hne
  rwa [if_neg (lt_irrefl _)] at h

lemma inSpike_far_base_lt {k : ℕ} [NeZero k] (hk : 4 ≤ k) {x : Fin k → ℝ²}
    {i j : Fin k} (hj1 : j ≠ i - 1) (hj2 : j ≠ i) (hj3 : j ≠ i + 1)
    {z : ℝ²} (hz : inSpike x j z) :
    orient (x (i + 2)) (x (i - 1)) z < 0 := by
  have hd_b : ((i - 1) - (i + 2) : Fin k).val = k - 3 := by
    rw [show ((i - 1) - (i + 2) : Fin k) = -(Fin.ofNat k 3) by
      rw [fin_ofNat_3, ← fin_two_add_one, ← fin_one_add_one]; abel]
    exact fin_val_neg_ofNat 3 (by omega) (by omega)
  have hne : i + 2 ≠ i - 1 := by
    intro h
    have h0 := congrArg (fun z : Fin k => (z - (i + 2)).val) h.symm
    rw [hd_b, sub_self, Fin.val_zero] at h0; omega
  have hd_j : (j - (i + 2) : Fin k).val < k - 3 := by
    have hlt := (j - (i + 2)).isLt
    by_contra! hge
    have hcases : (j - (i + 2)).val = k - 3 ∨ (j - (i + 2)).val = k - 2 ∨ (j - (i + 2)).val = k - 1 := by omega
    rcases hcases with h1 | h2 | h3
    · apply hj1
      have heq : j - (i + 2) = (i - 1) - (i + 2) := Fin.ext (by rw [h1, hd_b])
      exact sub_left_inj.mp heq
    · apply hj2
      have hd2 : (i - (i + 2) : Fin k).val = k - 2 := by
        rw [show (i - (i + 2) : Fin k) = -(Fin.ofNat k 2) by rw [fin_ofNat_2]; abel]
        exact fin_val_neg_ofNat 2 (by omega) (by omega)
      have heq : j - (i + 2) = i - (i + 2) := Fin.ext (by rw [h2, hd2])
      exact sub_left_inj.mp heq
    · apply hj3
      have hd3 : ((i + 1) - (i + 2) : Fin k).val = k - 1 := by
        rw [show ((i + 1) - (i + 2) : Fin k) = -(Fin.ofNat k 1) by
          rw [fin_ofNat_1, ← fin_one_add_one]; abel]
        exact fin_val_neg_ofNat 1 (by omega) (by omega)
      have heq : j - (i + 2) = (i + 1) - (i + 2) := Fin.ext (by rw [h3, hd3])
      exact sub_left_inj.mp heq
  have h := hz (i + 2) (i - 1) hne
  rw [fin_cyc_dist_eq_sub, fin_cyc_dist_eq_sub, hd_b, if_pos hd_j] at h
  exact h

/-- Positive orientations among the four consecutive vertices `x (i - 1), x i, x (i + 1), x (i + 2)`. -/
lemma ccw_quad {k : ℕ} [NeZero k] (hk : 4 ≤ k) {x : Fin k → ℝ²} (hx : IsCcw x) (i : Fin k) :
    0 < orient (x (i - 1)) (x i) (x (i + 1)) ∧
    0 < orient (x i) (x (i + 1)) (x (i + 2)) ∧
    0 < orient (x (i + 1)) (x (i + 2)) (x (i - 1)) ∧
    0 < orient (x (i + 2)) (x (i - 1)) (x i) ∧
    0 < orient (x (i - 1)) (x i) (x (i + 2)) ∧
    0 < orient (x (i - 1)) (x (i + 1)) (x (i + 2)) := by
  let a : Fin k := i - 1
  have aux : ∀ r s t : ℕ, r < s → s < t → t < k →
      0 < orient (x (a + Fin.ofNat k r)) (x (a + Fin.ofNat k s)) (x (a + Fin.ofNat k t)) := by
    intro r s t hrs hst htk
    have hne : ∀ u v : ℕ, u < v → v < k → a + Fin.ofNat k u ≠ a + Fin.ofNat k v := by
      intro u v huv hvk h
      have h0 := congrArg Fin.val (add_left_cancel h)
      rw [fin_val_ofNat_of_lt u (by omega), fin_val_ofNat_of_lt v hvk] at h0; omega
    apply hx.orient_cyc (hne r s hrs (by omega)) (hne s t hst htk) (hne r t (by omega) htk)
    rw [fin_cyc_dist_eq_sub, fin_cyc_dist_eq_sub, fin_sub_add_cancel_cyc, fin_sub_add_cancel_cyc]
    have hsr : (Fin.ofNat k s - Fin.ofNat k r).val = s - r := by
      rw [Fin.val_sub, fin_val_ofNat_of_lt s (by omega), fin_val_ofNat_of_lt r (by omega)]
      rw [show k - r + s = k + (s - r) by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have htr : (Fin.ofNat k t - Fin.ofNat k r).val = t - r := by
      rw [Fin.val_sub, fin_val_ofNat_of_lt t htk, fin_val_ofNat_of_lt r (by omega)]
      rw [show k - r + t = k + (t - r) by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega
  have ha0 : i - 1 = a + Fin.ofNat k 0 := by change i - 1 = (i - 1) + 0; abel
  have ha1 : i = a + Fin.ofNat k 1 := by rw [fin_ofNat_1]; dsimp [a]; abel
  have ha2 : i + 1 = a + Fin.ofNat k 2 := by rw [fin_ofNat_2, ← fin_one_add_one]; dsimp [a]; abel
  have ha3 : i + 2 = a + Fin.ofNat k 3 := by
    rw [fin_ofNat_3, ← fin_two_add_one, ← fin_one_add_one]; dsimp [a]; abel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha2, ha0, ha1]; exact aux 0 1 2 (by omega) (by omega) (by omega)
  · rw [ha3, ha2, ha1]; exact aux 1 2 3 (by omega) (by omega) (by omega)
  · rw [orient_cyclic, orient_cyclic, ha3, ha2, ha0]; exact aux 0 2 3 (by omega) (by omega) (by omega)
  · rw [orient_cyclic, ha3, ha0, ha1]; exact aux 0 1 3 (by omega) (by omega) (by omega)
  · rw [ha3, ha0, ha1]; exact aux 0 1 3 (by omega) (by omega) (by omega)
  · rw [ha3, ha2, ha0]; exact aux 0 2 3 (by omega) (by omega) (by omega)

/- ### Section 3: Transitive Coloring Cup–Cap Theorem and Weak Erdős–Szekeres -/

/-- Generalized Erdős–Szekeres cup-cap theorem for transitive 2-colorings of ordered triples. -/
theorem transitive_cup_cap {α : Type*} [LinearOrder α] (C : α → α → α → Prop)
    (hT1 : ∀ ⦃a b c d : α⦄, a < b → b < c → c < d →
      C a b c → C b c d → C a b d ∧ C a c d)
    (hT2 : ∀ ⦃a b c d : α⦄, a < b → b < c → c < d →
      ¬ C a b c → ¬ C b c d → ¬ C a b d ∧ ¬ C a c d) :
    ∀ (s : ℕ) (a b : ℕ), a + b = s → 2 ≤ a → 2 ≤ b →
      ∀ S : Finset α, Nat.choose (a + b - 4) (a - 2) < S.card →
        (∃ A ⊆ S, A.card = a ∧ ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x < y → y < z → C x y z) ∨
        (∃ B ⊆ S, B.card = b ∧ ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x < y → y < z → ¬ C x y z) := by
  intro s
  induction s with
  | zero => intro a b h ha _; omega
  | succ s ih =>
    intro a b hab ha hb S hS
    by_cases ha2 : a = 2
    · subst ha2
      have h1 : 1 < S.card := by
        simpa [show 2 + b - 4 = b - 2 by omega] using hS
      obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq (show 2 ≤ S.card by omega)
      left
      refine ⟨A, hAS, hAcard, fun x hx y hy z hz hxy hyz => ?_⟩
      exfalso
      have hsub : ({x, y, z} : Finset α) ⊆ A := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> assumption
      have h3 : ({x, y, z} : Finset α).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair hyz.ne]
        simp [hxy.ne, (hxy.trans hyz).ne]
      have := Finset.card_le_card hsub; omega
    · by_cases hb2 : b = 2
      · subst hb2
        have h1 : 1 < S.card := by
          have : Nat.choose (a + 2 - 4) (a - 2) = 1 := by
            rw [show a + 2 - 4 = a - 2 by omega, Nat.choose_self]
          omega
        obtain ⟨B, hBS, hBcard⟩ := Finset.exists_subset_card_eq (show 2 ≤ S.card by omega)
        right
        refine ⟨B, hBS, hBcard, fun x hx y hy z hz hxy hyz => ?_⟩
        exfalso
        have hsub : ({x, y, z} : Finset α) ⊆ B := by
          intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl <;> assumption
        have h3 : ({x, y, z} : Finset α).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair hyz.ne]
          simp [hxy.ne, (hxy.trans hyz).ne]
        have := Finset.card_le_card hsub; omega
      · -- Both a ≥ 3 and b ≥ 3
        have ha3 : 3 ≤ a := by omega
        have hb3 : 3 ≤ b := by omega
        let E := S.filter fun m =>
          ∃ A ⊆ S, A.card = a - 1 ∧ m ∈ A ∧ (∀ x ∈ A, x ≤ m) ∧
            ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x < y → y < z → C x y z
        by_cases hE : Nat.choose (a + (b - 1) - 4) (a - 2) < E.card
        · rcases ih a (b - 1) (by omega) ha (by omega) E hE with ⟨A, hAE, hAc, hAC⟩ | ⟨B, hBE, hBc, hBC⟩
          · exact Or.inl ⟨A, hAE.trans (Finset.filter_subset _ _), hAc, hAC⟩
          · have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
            let y₁ := B.min' hBne
            have hy₁B : y₁ ∈ B := Finset.min'_mem B hBne
            have hy₁E : y₁ ∈ E := hBE hy₁B
            obtain ⟨_, A, hAS, hAc, hy₁A, hy₁max, hAC⟩ := Finset.mem_filter.mp hy₁E
            -- A has size a - 1 ≥ 2, so A.erase y₁ is nonempty; let u = max of A.erase y₁
            have hA'ne : (A.erase y₁).Nonempty := by
              rw [← Finset.card_pos, Finset.card_erase_of_mem hy₁A]; omega
            let u := (A.erase y₁).max' hA'ne
            have huA' : u ∈ A.erase y₁ := Finset.max'_mem _ hA'ne
            have huA : u ∈ A := Finset.mem_of_mem_erase huA'
            have hu_lt : u < y₁ := lt_of_le_of_ne (hy₁max u huA) (Finset.ne_of_mem_erase huA')
            -- B has size b - 1 ≥ 2, so B.erase y₁ is nonempty; let y₂ = min of B.erase y₁
            have hB'ne : (B.erase y₁).Nonempty := by
              rw [← Finset.card_pos, Finset.card_erase_of_mem hy₁B]; omega
            let y₂ := (B.erase y₁).min' hB'ne
            have hy₂B' : y₂ ∈ B.erase y₁ := Finset.min'_mem _ hB'ne
            have hy₂B : y₂ ∈ B := Finset.mem_of_mem_erase hy₂B'
            have hy₁_lt_y₂ : y₁ < y₂ :=
              lt_of_le_of_ne (Finset.min'_le B y₂ hy₂B) (Ne.symm (Finset.ne_of_mem_erase hy₂B'))
            by_cases hC : C u y₁ y₂
            · -- Extend A by y₂ to size a!
              left
              have hy₂_notA : y₂ ∉ A := fun hm => (lt_irrefl y₁) (lt_of_lt_of_le hy₁_lt_y₂ (hy₁max y₂ hm))
              refine ⟨insert y₂ A, Finset.insert_subset (Finset.filter_subset _ _ (hBE hy₂B)) hAS,
                by rw [Finset.card_insert_of_notMem hy₂_notA, hAc]; omega, ?_⟩
              intro x hx y hy z hz hxy hyz
              rcases Finset.mem_insert.mp hz with rfl | hzA
              · rcases Finset.mem_insert.mp hy with rfl | hyA
                · exact (lt_irrefl y₂ hyz).elim
                · rcases Finset.mem_insert.mp hx with rfl | hxA
                  · exact (lt_irrefl y₂ (hxy.trans hyz)).elim
                  · -- x < y ≤ y₁ < y₂, with x, y ∈ A
                    by_cases hy_eq : y = y₁
                    · subst hy_eq
                      by_cases hx_eq : x = u
                      · rwa [hx_eq]
                      · have hxu : x < u := lt_of_le_of_ne
                          (Finset.le_max' _ x (Finset.mem_erase.mpr ⟨hxy.ne, hxA⟩)) hx_eq
                        exact (hT1 hxu hu_lt hy₁_lt_y₂ (hAC x hxA u huA y₁ hy₁A hxu hu_lt) hC).2
                    · have hy_lt : y < y₁ := lt_of_le_of_ne (hy₁max y hyA) hy_eq
                      have hyu : y ≤ u := Finset.le_max' _ y (Finset.mem_erase.mpr ⟨hy_eq, hyA⟩)
                      have hCy : C y y₁ y₂ := by
                        rcases lt_or_eq_of_le hyu with hlt | rfl
                        · exact (hT1 hlt hu_lt hy₁_lt_y₂ (hAC y hyA u huA y₁ hy₁A hlt hu_lt) hC).2
                        · exact hC
                      exact (hT1 hxy hy_lt hy₁_lt_y₂ (hAC x hxA y hyA y₁ hy₁A hxy hy_lt) hCy).1
              · rcases Finset.mem_insert.mp hy with rfl | hyA
                · exact (not_lt_of_ge (hy₁max z hzA) (hy₁_lt_y₂.trans hyz)).elim
                · rcases Finset.mem_insert.mp hx with rfl | hxA
                  · exact (not_lt_of_ge (hy₁max z hzA) (hy₁_lt_y₂.trans (hxy.trans hyz))).elim
                  · exact hAC x hxA y hyA z hzA hxy hyz
            · -- Extend B by u to size b!
              right
              have hu_notB : u ∉ B := fun hm => (lt_irrefl u) (lt_of_lt_of_le hu_lt (Finset.min'_le B u hm))
              refine ⟨insert u B, Finset.insert_subset (hAS huA) (hBE.trans (Finset.filter_subset _ _)),
                by rw [Finset.card_insert_of_notMem hu_notB, hBc]; omega, ?_⟩
              intro x hx y hy z hz hxy hyz
              rcases Finset.mem_insert.mp hx with rfl | hxB
              · rcases Finset.mem_insert.mp hy with rfl | hyB
                · exact (lt_irrefl u hxy).elim
                · rcases Finset.mem_insert.mp hz with rfl | hzB
                  · exact (lt_irrefl u (hxy.trans hyz)).elim
                  · by_cases hy_eq : y = y₁
                    · subst hy_eq
                      by_cases hz_eq : z = y₂
                      · rwa [hz_eq]
                      · have hy₂z : y₂ < z := lt_of_le_of_ne
                          (Finset.min'_le _ z (Finset.mem_erase.mpr ⟨hyz.ne.symm, hzB⟩)) (Ne.symm hz_eq)
                        exact (hT2 hu_lt hy₁_lt_y₂ hy₂z hC (hBC y₁ hy₁B y₂ hy₂B z hzB hy₁_lt_y₂ hy₂z)).1
                    · have hy₁_lt_y : y₁ < y :=
                        lt_of_le_of_ne (Finset.min'_le B y hyB) (Ne.symm hy_eq)
                      have hy₂_le_y : y₂ ≤ y :=
                        Finset.min'_le _ y (Finset.mem_erase.mpr ⟨hy_eq, hyB⟩)
                      have hCy : ¬ C u y₁ y := by
                        rcases lt_or_eq_of_le hy₂_le_y with hlt | rfl
                        · exact (hT2 hu_lt hy₁_lt_y₂ hlt hC (hBC y₁ hy₁B y₂ hy₂B y hyB hy₁_lt_y₂ hlt)).1
                        · exact hC
                      exact (hT2 hu_lt hy₁_lt_y hyz hCy (hBC y₁ hy₁B y hyB z hzB hy₁_lt_y hyz)).2
              · rcases Finset.mem_insert.mp hy with rfl | hyB
                · exact (not_lt_of_ge (Finset.min'_le B x hxB) (hxy.trans hu_lt)).elim
                · rcases Finset.mem_insert.mp hz with rfl | hzB
                  · exact (not_lt_of_ge (Finset.min'_le B x hxB) ((hxy.trans hyz).trans hu_lt)).elim
                  · exact hBC x hxB y hyB z hzB hxy hyz
        · -- Complement S \ E is large enough for (a - 1, b)
          push Not at hE
          have hpascal : Nat.choose (a + b - 4) (a - 2) =
              Nat.choose (a + (b - 1) - 4) (a - 2) + Nat.choose ((a - 1) + b - 4) ((a - 1) - 2) := by
            have h1 : a + b - 4 = (a + b - 5) + 1 := by omega
            have h2 : a - 2 = (a - 3) + 1 := by omega
            have h3 : a + (b - 1) - 4 = a + b - 5 := by omega
            have h4 : (a - 1) + b - 4 = a + b - 5 := by omega
            have h5 : (a - 1) - 2 = a - 3 := by omega
            rw [h1, h2, h3, h4, h5, Nat.choose_succ_succ, add_comm]
          have hSE_card : Nat.choose ((a - 1) + b - 4) ((a - 1) - 2) < (S \ E).card := by
            have hsub : E ⊆ S := Finset.filter_subset _ _
            have hdiff := Finset.card_sdiff_add_card_eq_card hsub
            omega
          rcases ih (a - 1) b (by omega) (by omega) hb (S \ E) hSE_card with
            ⟨A, hASE, hAc, hAC⟩ | ⟨B, hBSE, hBc, hBC⟩
          · -- Contradiction: max of A belongs to E!
            have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
            let m := A.max' hAne
            have hmA : m ∈ A := Finset.max'_mem A hAne
            have hmSE : m ∈ S \ E := hASE hmA
            have hmE : m ∈ E := Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hmSE).1,
              A, hASE.trans Finset.sdiff_subset, hAc, hmA, fun x hx => Finset.le_max' A x hx, hAC⟩
            exact ((Finset.mem_sdiff.mp hmSE).2 hmE).elim
          · exact Or.inr ⟨B, hBSE.trans Finset.sdiff_subset, hBc, hBC⟩

/-- Lexicographic order on `ℝ²` (used only to apply `transitive_cup_cap` for the weak `4^m` bound). -/
def ptLex (p : ℝ²) : ℝ ×ₗ ℝ := _root_.toLex (p 0, p 1)

lemma ptLex_injective : Function.Injective ptLex := by
  intro p q h
  have h0 : p 0 = q 0 := congrArg (fun x : ℝ ×ₗ ℝ => (ofLex x).1) h
  have h1 : p 1 = q 1 := congrArg (fun x : ℝ ×ₗ ℝ => (ofLex x).2) h
  ext i; fin_cases i
  · exact h0
  · exact h1

lemma lex_lt_iff (p q : ℝ²) : ptLex p < ptLex q ↔ p 0 < q 0 ∨ (p 0 = q 0 ∧ p 1 < q 1) := by
  simp [ptLex, Prod.Lex.lt_iff]

/-- On lexicographically ordered general-position points, `orient > 0` vs `orient < 0`
is a transitive coloring, and any monochromatic subset is `ConvexIndep`. -/
lemma orient_lex_transitive {a b c d : ℝ²}
    (hab : ptLex a < ptLex b) (hbc : ptLex b < ptLex c) (hcd : ptLex c < ptLex d)
    (h1 : 0 < orient a b c) (h2 : 0 < orient b c d) :
    0 < orient a b d ∧ 0 < orient a c d := by
  rw [lex_lt_iff] at hab hbc hcd
  have hba : 0 ≤ b 0 - a 0 := by rcases hab with h | ⟨h, _⟩ <;> linarith
  have hcb : 0 ≤ c 0 - b 0 := by rcases hbc with h | ⟨h, _⟩ <;> linarith
  have hdc : 0 ≤ d 0 - c 0 := by rcases hcd with h | ⟨h, _⟩ <;> linarith
  have hab_lt : a 0 < b 0 := by
    rcases hab with h | ⟨heq, hlt⟩
    · exact h
    · have : orient a b c ≤ 0 := by
        simp only [orient, heq, sub_self, zero_mul, zero_sub]
        nlinarith
      linarith
  have hbc_lt : b 0 < c 0 := by
    rcases hbc with h | ⟨heq, hlt⟩
    · exact h
    · have : orient b c d ≤ 0 := by
        simp only [orient, heq, sub_self, zero_mul, zero_sub]
        nlinarith
      linarith
  have hid1 : (c 0 - b 0) * orient a b d =
      (d 0 - b 0) * orient a b c + (b 0 - a 0) * orient b c d := by
    simp only [orient]; ring
  have hid2 : (c 0 - b 0) * orient a c d =
      (d 0 - c 0) * orient a b c + (c 0 - a 0) * orient b c d := by
    simp only [orient]; ring
  constructor <;> nlinarith

lemma orient_lex_transitive_neg {a b c d : ℝ²}
    (hab : ptLex a < ptLex b) (hbc : ptLex b < ptLex c) (hcd : ptLex c < ptLex d)
    (h1 : orient a b c < 0) (h2 : orient b c d < 0) :
    orient a b d < 0 ∧ orient a c d < 0 := by
  rw [lex_lt_iff] at hab hbc hcd
  have hba : 0 ≤ b 0 - a 0 := by rcases hab with h | ⟨h, _⟩ <;> linarith
  have hcb : 0 ≤ c 0 - b 0 := by rcases hbc with h | ⟨h, _⟩ <;> linarith
  have hdc : 0 ≤ d 0 - c 0 := by rcases hcd with h | ⟨h, _⟩ <;> linarith
  have hbc_lt : b 0 < c 0 := by
    rcases hbc with h | ⟨heq, hlt⟩
    · exact h
    · have : 0 ≤ orient a b c := by
        simp only [orient]
        have : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) =
            (b 0 - a 0) * (c 1 - b 1) := by rw [heq]; ring
        rw [this]; nlinarith
      linarith
  have hcd_lt : c 0 < d 0 := by
    rcases hcd with h | ⟨heq, hlt⟩
    · exact h
    · have : 0 ≤ orient b c d := by
        simp only [orient]
        have : (c 0 - b 0) * (d 1 - b 1) - (c 1 - b 1) * (d 0 - b 0) =
            (c 0 - b 0) * (d 1 - c 1) := by rw [heq]; ring
        rw [this]; nlinarith
      linarith
  have hid1 : (c 0 - b 0) * orient a b d =
      (d 0 - b 0) * orient a b c + (b 0 - a 0) * orient b c d := by
    simp only [orient]; ring
  have hid2 : (c 0 - b 0) * orient a c d =
      (d 0 - c 0) * orient a b c + (c 0 - a 0) * orient b c d := by
    simp only [orient]; ring
  constructor <;> nlinarith

/-- Any linearly ordered subset where all increasing triples have positive (or all negative)
`orient` is `ConvexIndep`. -/
lemma convexIndep_of_monotone_orient_pos {α : Type*} [LinearOrder α]
    {S : Set ℝ²} (hnt : NonTrilinear S) (φ : ℝ² → α) (hφ : Set.InjOn φ S)
    (hpos : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, φ a < φ b → φ b < φ c → 0 < orient a b c) :
    ConvexIndep S := by
  have hcore : ∀ a b c d : ℝ², a ∈ S → b ∈ S → c ∈ S → d ∈ S →
      d ≠ a → d ≠ b → d ≠ c → φ a < φ b → φ b < φ c →
      d ∉ convexHull ℝ ({a, b, c} : Set ℝ²) := by
    intro a b c d ha hb hc hd hda hdb hdc hab' hbc'
    have hab : a ≠ b := fun h => by rw [h] at hab'; exact lt_irrefl _ hab'
    have hbc : b ≠ c := fun h => by rw [h] at hbc'; exact lt_irrefl _ hbc'
    have hac : a ≠ c := fun h => by
      have hlt := hab'.trans hbc'; rw [h] at hlt; exact lt_irrefl _ hlt
    have hnt4 : NonTrilinear ({a, b, c, d} : Set ℝ²) :=
      Set.Triplewise.mono (by intro z hz; simp at hz; rcases hz with rfl | rfl | rfl | rfl <;> assumption) hnt
    rcases lt_or_gt_of_ne (fun heq => hda (hφ hd ha heq)) with hda' | had'
    · apply not_mem_convexHull_triple_of_same_side hnt4 hda hdb hdc hab hbc hac
      have h1 := hpos d hd a ha b hb hda' hab'
      have h2 := hpos d hd a ha c hc hda' (hab'.trans hbc')
      have h1' : orient a d b = -orient d a b := orient_swap₁₂ d a b
      have h2' : orient a d c = -orient d a c := orient_swap₁₂ d a c
      nlinarith
    · rcases lt_or_gt_of_ne (fun heq => hdb (hφ hd hb heq)) with hdb' | hbd'
      · apply not_mem_convexHull_triple_of_same_side hnt4 hda hdb hdc hab hbc hac
        have h1 := hpos a ha d hd b hb had' hdb'
        have h2 := hpos a ha d hd c hc had' (hdb'.trans hbc')
        nlinarith
      · rcases lt_or_gt_of_ne (fun heq => hdc (hφ hd hc heq)) with hdc' | hcd'
        · have hset : ({a, b, c} : Set ℝ²) = {c, a, b} := by ext z; simp; tauto
          rw [hset]
          apply not_mem_convexHull_triple_of_same_side
            (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4)
            hdc hda hdb hac.symm hab hbc.symm
          have h1 := hpos a ha d hd c hc (hab'.trans hbd') hdc'
          have h2 := hpos b hb d hd c hc hbd' hdc'
          have h1' : orient c d a = -orient a d c := by simp only [orient]; ring
          have h2' : orient c d b = -orient b d c := by simp only [orient]; ring
          nlinarith
        · have hset : ({a, b, c} : Set ℝ²) = {c, a, b} := by ext z; simp; tauto
          rw [hset]
          apply not_mem_convexHull_triple_of_same_side
            (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4)
            hdc hda hdb hac.symm hab hbc.symm
          have h1 := hpos a ha c hc d hd (hab'.trans hbc') hcd'
          have h2 := hpos b hb c hc d hd hbc' hcd'
          have h1' : orient c d a = orient a c d := by rw [orient_cyclic, orient_cyclic]
          have h2' : orient c d b = orient b c d := by rw [orient_cyclic, orient_cyclic]
          nlinarith
  apply convexIndep_of_forall_triple hnt
  intro a b c d ha hb hc hd hda hdb hdc hab hbc hac
  rcases lt_or_gt_of_ne (fun h => hab (hφ ha hb h)) with hab' | hba'
  · rcases lt_or_gt_of_ne (fun h => hbc (hφ hb hc h)) with hbc' | hcb'
    · exact hcore a b c d ha hb hc hd hda hdb hdc hab' hbc'
    · rcases lt_or_gt_of_ne (fun h => hac (hφ ha hc h)) with hac' | hca'
      · rw [show ({a, b, c} : Set ℝ²) = {a, c, b} by ext z; simp; tauto]
        exact hcore a c b d ha hc hb hd hda hdc hdb hac' hcb'
      · rw [show ({a, b, c} : Set ℝ²) = {c, a, b} by ext z; simp; tauto]
        exact hcore c a b d hc ha hb hd hdc hda hdb hca' hab'
  · rcases lt_or_gt_of_ne (fun h => hac (hφ ha hc h)) with hac' | hca'
    · rw [show ({a, b, c} : Set ℝ²) = {b, a, c} by ext z; simp; tauto]
      exact hcore b a c d hb ha hc hd hdb hda hdc hba' hac'
    · rcases lt_or_gt_of_ne (fun h => hbc (hφ hb hc h)) with hbc' | hcb'
      · rw [show ({a, b, c} : Set ℝ²) = {b, c, a} by ext z; simp; tauto]
        exact hcore b c a d hb hc ha hd hdb hdc hda hbc' hca'
      · rw [show ({a, b, c} : Set ℝ²) = {c, b, a} by ext z; simp; tauto]
        exact hcore c b a d hc hb ha hd hdc hdb hda hcb' hba'

lemma convexIndep_of_monotone_orient_neg {α : Type*} [LinearOrder α]
    {S : Set ℝ²} (hnt : NonTrilinear S) (φ : ℝ² → α) (hφ : Set.InjOn φ S)
    (hneg : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, φ a < φ b → φ b < φ c → orient a b c < 0) :
    ConvexIndep S := by
  apply convexIndep_of_monotone_orient_pos (α := OrderDual α) hnt (OrderDual.toDual ∘ φ)
    (fun a ha b hb h => hφ ha hb h)
  intro a ha b hb c hc hab hbc
  have h := hneg c hc b hb a ha hbc hab
  have hsym : orient a b c = -orient c b a := by simp only [orient]; ring
  linarith

/-- Weak Erdős–Szekeres bound: `4 ^ m` general-position points contain a convex `m`-gon. -/
theorem weak_erdos_szekeres {m : ℕ} (hm : 2 ≤ m) {P : Finset ℝ²}
    (hnt : NonTrilinear (P : Set ℝ²)) (hcard : 4 ^ m ≤ P.card) :
    HasConvexNGon m (P : Set ℝ²) := by
  let S := P.image ptLex
  have hScard : S.card = P.card := Finset.card_image_of_injective P ptLex_injective
  have hchoose : Nat.choose (m + m - 4) (m - 2) < S.card := by
    rw [hScard]
    have h1 : Nat.choose (m + m - 4) (m - 2) ≤ 2 ^ (m + m - 4) := Nat.choose_le_two_pow _ _
    have h2 : 2 ^ (m + m - 4) < 4 ^ m := by
      have : 4 ^ m = 2 ^ (2 * m) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      rw [this]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  let inv : ℝ ×ₗ ℝ → ℝ² := fun x => !₂[(ofLex x).1, (ofLex x).2]
  have hinv_ptLex : ∀ p : ℝ², inv (ptLex p) = p := by
    intro p; ext i; fin_cases i
    · change (ofLex (ptLex p)).1 = p 0; rfl
    · change (ofLex (ptLex p)).2 = p 1; rfl
  have hptLex_inv : ∀ x : ℝ ×ₗ ℝ, ptLex (inv x) = x := by
    intro x; cases x; rfl
  let T : Finset {x // x ∈ S} := Finset.univ
  have hTcard : Nat.choose (m + m - 4) (m - 2) < T.card := by
    simpa [T, Fintype.card_coe] using hchoose
  have hinv_mem : ∀ x : {x // x ∈ S}, inv x.val ∈ P := by
    intro x
    obtain ⟨p, hp, hpeq⟩ := Finset.mem_image.mp x.property
    rw [← hpeq, hinv_ptLex]; exact hp
  have hinv_inj : Function.Injective (fun z : {x // x ∈ S} => inv z.val) := by
    intro z₁ z₂ hz
    apply Subtype.ext
    have := congrArg ptLex hz
    rwa [hptLex_inv, hptLex_inv] at this
  let C' : {x // x ∈ S} → {x // x ∈ S} → {x // x ∈ S} → Prop :=
    fun a b c => 0 < orient (inv a.val) (inv b.val) (inv c.val)
  have hT1' : ∀ ⦃a b c d : {x // x ∈ S}⦄, a < b → b < c → c < d →
      C' a b c → C' b c d → C' a b d ∧ C' a c d := by
    intro a b c d hab hbc hcd h1 h2
    exact orient_lex_transitive (by rw [hptLex_inv, hptLex_inv]; exact hab)
      (by rw [hptLex_inv, hptLex_inv]; exact hbc)
      (by rw [hptLex_inv, hptLex_inv]; exact hcd) h1 h2
  have hT2' : ∀ ⦃a b c d : {x // x ∈ S}⦄, a < b → b < c → c < d →
      ¬ C' a b c → ¬ C' b c d → ¬ C' a b d ∧ ¬ C' a c d := by
    intro a b c d hab hbc hcd h1 h2
    have hne : ∀ u v w : {x // x ∈ S}, u < v → v < w → orient (inv u.val) (inv v.val) (inv w.val) ≠ 0 := by
      intro u v w huv hvw
      exact orient_ne_zero_of_not_collinear
        (hnt (hinv_mem u) (hinv_mem v) (hinv_mem w)
          (hinv_inj.ne huv.ne) (hinv_inj.ne hvw.ne) (hinv_inj.ne (huv.trans hvw).ne))
    have h1' : orient (inv a.val) (inv b.val) (inv c.val) < 0 :=
      lt_of_le_of_ne (le_of_not_gt h1) (hne a b c hab hbc)
    have h2' : orient (inv b.val) (inv c.val) (inv d.val) < 0 :=
      lt_of_le_of_ne (le_of_not_gt h2) (hne b c d hbc hcd)
    have hres := orient_lex_transitive_neg (by rw [hptLex_inv, hptLex_inv]; exact hab)
      (by rw [hptLex_inv, hptLex_inv]; exact hbc)
      (by rw [hptLex_inv, hptLex_inv]; exact hcd) h1' h2'
    exact ⟨not_lt.mpr hres.1.le, not_lt.mpr hres.2.le⟩
  rcases transitive_cup_cap C' hT1' hT2' (m + m) m m rfl hm hm T hTcard with
    ⟨A, _, hAc, hAC⟩ | ⟨B, _, hBc, hBC⟩
  · let Q := A.image (fun z => inv z.val)
    have hQsub : (Q : Set ℝ²) ⊆ (P : Set ℝ²) := by
      intro p hp; obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hp; exact hinv_mem z
    refine ⟨Q, by rw [Finset.card_image_of_injective _ hinv_inj, hAc], hQsub, ?_⟩
    apply convexIndep_of_monotone_orient_pos (Set.Triplewise.mono hQsub hnt)
      ptLex (ptLex_injective.injOn)
    intro p hp q hq r hr hpq hqr
    obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hbA, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨c, hcA, rfl⟩ := Finset.mem_image.mp hr
    rw [hptLex_inv, hptLex_inv] at hpq hqr
    exact hAC a haA b hbA c hcA hpq hqr
  · let Q := B.image (fun z => inv z.val)
    have hQsub : (Q : Set ℝ²) ⊆ (P : Set ℝ²) := by
      intro p hp; obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hp; exact hinv_mem z
    refine ⟨Q, by rw [Finset.card_image_of_injective _ hinv_inj, hBc], hQsub, ?_⟩
    apply convexIndep_of_monotone_orient_neg (Set.Triplewise.mono hQsub hnt)
      ptLex (ptLex_injective.injOn)
    intro p hp q hq r hr hpq hqr
    obtain ⟨a, haB, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hbB, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨c, hcB, rfl⟩ := Finset.mem_image.mp hr
    rw [hptLex_inv, hptLex_inv] at hpq hqr
    have hnot := hBC a haB b hbB c hcB hpq hqr
    have hne := orient_ne_zero_of_not_collinear
      (hnt (hinv_mem a) (hinv_mem b) (hinv_mem c)
        (hinv_inj.ne (fun h => hpq.ne (congrArg Subtype.val h)))
        (hinv_inj.ne (fun h => hqr.ne (congrArg Subtype.val h)))
        (hinv_inj.ne (fun h => (hpq.trans hqr).ne (congrArg Subtype.val h))))
    exact lt_of_le_of_ne (le_of_not_gt hnot) hne

/- ### Section 4: Convex Clustering (HMPT Theorem 2.3) -/

/-- HMPT Theorem 2.3: Any general-position set `P` of size `N ≥ 2 ^ (4 * k)` (`k ≥ 3`)
contains a counterclockwise convex `k`-gon `x` whose spike subsets `P_i = {p ∈ P | inSpike x i p}`
satisfy `N ^ k ≤ 2 ^ (8 * k ^ 2) * ∏ i, (P_i).card`. -/
theorem convex_clustering {k : ℕ} [NeZero k] (hk : 3 ≤ k) {P : Finset ℝ²}
    (hnt : NonTrilinear (P : Set ℝ²)) (hN : 2 ^ (4 * k) ≤ P.card) :
    ∃ x : Fin k → ℝ², IsCcw x ∧ (∀ i, x i ∈ P) ∧ Function.Injective x ∧
      (P.card : ℝ) ^ k ≤
        (2 : ℝ) ^ (8 * k ^ 2) * ∏ i : Fin k, ((P.filter (inSpike x i)).card : ℝ) := by
  let N := P.card
  let M := 4 ^ (2 * k)
  have hM_eq : M = 2 ^ (4 * k) := by
    dsimp [M]; rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  have hMN : M ≤ N := hM_eq ▸ hN
  have h2k_le_M : 2 * k ≤ M := by
    have h1 : 2 * k ≤ 2 ^ (2 * k) := Nat.le_of_lt Nat.lt_two_pow_self
    have h2 : 2 ^ (2 * k) ≤ 2 ^ (4 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  -- Collection of all convex 2k-gons inside P
  let C2k : Finset (Finset ℝ²) := (P.powersetCard (2 * k)).filter (fun (Y : Finset ℝ²) => ConvexIndep (Y : Set ℝ²))
  -- Double counting: each M-subset of P contains at least one Y ∈ C2k,
  -- and each Y ∈ C2k lies in Nat.choose (N - 2k) (M - 2k) subsets of size M.
  have hdouble : Nat.choose N M ≤ C2k.card * Nat.choose (N - 2 * k) (M - 2 * k) := by
    have h1 : (P.powersetCard M).card ≤
        ∑ Y ∈ C2k, ((P.powersetCard M).filter (fun Q => Y ⊆ Q)).card := by
      calc (P.powersetCard M).card
          = ∑ Q ∈ P.powersetCard M, 1 := by simp
        _ ≤ ∑ Q ∈ P.powersetCard M, (C2k.filter (fun Y => Y ⊆ Q)).card := by
            apply Finset.sum_le_sum
            intro Q hQ
            obtain ⟨hQP, hQM⟩ := Finset.mem_powersetCard.mp hQ
            have hQnt : NonTrilinear (Q : Set ℝ²) := Set.Triplewise.mono hQP hnt
            obtain ⟨Y, hYc, hYQ, hYconv⟩ := weak_erdos_szekeres (by omega : 2 ≤ 2 * k) hQnt (by omega)
            have hYQ' : Y ⊆ Q := by exact_mod_cast hYQ
            have hYC : Y ∈ C2k := Finset.mem_filter.mpr
              ⟨Finset.mem_powersetCard.mpr ⟨hYQ'.trans hQP, hYc⟩, hYconv⟩
            exact Finset.card_pos.mpr ⟨Y, Finset.mem_filter.mpr ⟨hYC, hYQ'⟩⟩
        _ = ∑ Y ∈ C2k, ((P.powersetCard M).filter (fun Q => Y ⊆ Q)).card := by
            simp only [Finset.card_filter]
            exact Finset.sum_comm
    have h2 : ∀ Y ∈ C2k, ((P.powersetCard M).filter (fun Q => Y ⊆ Q)).card =
        Nat.choose (N - 2 * k) (M - 2 * k) := by
      intro Y hY
      obtain ⟨hYP, hYc⟩ := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hY).1
      -- Bijection between {Q ⊆ P | |Q| = M ∧ Y ⊆ Q} and (P \ Y).powersetCard (M - 2k)
      have hcard_sdiff : (P \ Y).card = N - 2 * k := by
        rw [Finset.card_sdiff_of_subset hYP, hYc]
      rw [← hcard_sdiff, ← Finset.card_powersetCard]
      apply Finset.card_bij (fun Q _ => Q \ Y)
      · intro Q hQ
        obtain ⟨hQ1, hYQ⟩ := Finset.mem_filter.mp hQ
        obtain ⟨hQP, hQM⟩ := Finset.mem_powersetCard.mp hQ1
        exact Finset.mem_powersetCard.mpr
          ⟨Finset.sdiff_subset_sdiff hQP Subset.rfl, by rw [Finset.card_sdiff_of_subset hYQ, hQM, hYc]⟩
      · intro Q₁ hQ₁ Q₂ hQ₂ heq
        have hY1 := (Finset.mem_filter.mp hQ₁).2
        have hY2 := (Finset.mem_filter.mp hQ₂).2
        rw [← Finset.sdiff_union_of_subset hY1, ← Finset.sdiff_union_of_subset hY2, heq]
      · intro R hR
        obtain ⟨hRsub, hRcard⟩ := Finset.mem_powersetCard.mp hR
        have hdisj : Disjoint R Y := Finset.disjoint_of_subset_left hRsub disjoint_sdiff_self_left
        refine ⟨R ∪ Y, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
          ⟨Finset.union_subset (hRsub.trans Finset.sdiff_subset) hYP,
           by rw [Finset.card_union_of_disjoint hdisj, hRcard, hYc]; omega⟩,
          Finset.subset_union_right⟩, ?_⟩
        exact Finset.union_sdiff_cancel_right hdisj
    rw [Finset.card_powersetCard] at h1
    calc Nat.choose N M
        ≤ ∑ Y ∈ C2k, ((P.powersetCard M).filter (fun Q => Y ⊆ Q)).card := h1
      _ = ∑ _Y ∈ C2k, Nat.choose (N - 2 * k) (M - 2 * k) := Finset.sum_congr rfl h2
      _ = C2k.card * Nat.choose (N - 2 * k) (M - 2 * k) := by simp
  -- Next: map each Y ∈ C2k to its even-indexed convex k-gon X ⊂ Y (using exists_ccw_ordering)
  let Ck : Finset (Finset ℝ²) := (P.powersetCard k).filter (fun (X : Finset ℝ²) => ConvexIndep (X : Set ℝ²))
  -- For each Y ∈ C2k, pick a canonical ccw ordering y : Fin (2*k) → ℝ²
  have hY_ord : ∀ Y ∈ C2k, ∃ y : Fin (2 * k) → ℝ², IsCcw y ∧ (∀ i, y i ∈ Y) ∧ Function.Injective y := by
    intro Y hY
    obtain ⟨hY1, hYconv⟩ := Finset.mem_filter.mp hY
    obtain ⟨hYP, hYc⟩ := Finset.mem_powersetCard.mp hY1
    exact exists_ccw_ordering (by omega) hYc (Set.Triplewise.mono hYP hnt) hYconv
  -- Define support(Y) = {y (2*i) | i : Fin k} ∈ Ck
  let supp : Finset ℝ² → Finset ℝ² := fun Y =>
    if hY : Y ∈ C2k then
      let y := (hY_ord Y hY).choose
      Finset.univ.image (fun i : Fin k => y ⟨2 * i.val, by omega⟩)
    else ∅
  have hsupp_mem : ∀ Y ∈ C2k, supp Y ∈ Ck := by
    intro Y hY
    simp only [supp, dif_pos hY]
    set y := (hY_ord Y hY).choose
    have hy : IsCcw y ∧ (∀ i, y i ∈ Y) ∧ Function.Injective y := (hY_ord Y hY).choose_spec
    have hinj : Function.Injective (fun i : Fin k => y ⟨2 * i.val, by omega⟩) := by
      intro i j h; have := hy.2.2 h; exact Fin.ext (by have := congrArg Fin.val this; dsimp at this; omega)
    have hY1 := (Finset.mem_filter.mp hY).1
    have hYconv := (Finset.mem_filter.mp hY).2
    have hYP := (Finset.mem_powersetCard.mp hY1).1
    have hsubY : Finset.univ.image (fun i : Fin k => y ⟨2 * i.val, by omega⟩) ⊆ Y := by
      intro p hp; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp; exact hy.2.1 _
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨hsubY.trans hYP, by rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]⟩, ?_⟩
    intro a ha hmem
    have haY : a ∈ (Y : Set ℝ²) := hsubY ha
    have hsub : (↑(Finset.univ.image (fun i : Fin k => y ⟨2 * i.val, by omega⟩)) : Set ℝ²) \ {a} ⊆
        (Y : Set ℝ²) \ {a} := Set.sdiff_subset_sdiff_left (by exact_mod_cast hsubY)
    exact hYconv a haY (convexHull_mono hsub hmem)
  -- Pigeonhole: there is X ∈ Ck supported by ≥ C2k.card / Ck.card elements of C2k
  have hCk_ne : Ck.Nonempty := by
    have hC2k_pos : 0 < C2k.card := by
      by_contra h0
      have hc0 : C2k.card = 0 := by omega
      rw [hc0, zero_mul] at hdouble
      have hpos : 0 < Nat.choose N M := Nat.choose_pos hMN
      omega
    obtain ⟨Y, hY⟩ := Finset.card_pos.mp hC2k_pos
    exact ⟨supp Y, hsupp_mem Y hY⟩
  have hsum_fib : C2k.card = ∑ X ∈ Ck, (C2k.filter (fun Y => supp Y = X)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext Y; simp only [Finset.mem_biUnion, Finset.mem_filter]
      exact ⟨fun hY => ⟨supp Y, hsupp_mem Y hY, hY, rfl⟩, fun ⟨_, _, hY, _⟩ => hY⟩
    · intro X₁ _ X₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro Y h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  obtain ⟨X, hXCk, hXmax⟩ := Finset.exists_max_image Ck
    (fun X => (C2k.filter (fun Y => supp Y = X)).card) hCk_ne
  have hXbound : C2k.card ≤ Ck.card * (C2k.filter (fun Y => supp Y = X)).card := by
    rw [hsum_fib]
    calc ∑ X' ∈ Ck, (C2k.filter (fun Y => supp Y = X')).card
        ≤ ∑ _X' ∈ Ck, (C2k.filter (fun Y => supp Y = X)).card :=
          Finset.sum_le_sum (fun X' hX' => hXmax X' hX')
      _ = Ck.card * (C2k.filter (fun Y => supp Y = X)).card := by simp
  -- Take one witness Y₀ with supp Y₀ = X (must exist since C2k.card > 0)
  have hfib_pos : 0 < (C2k.filter (fun Y => supp Y = X)).card := by
    by_contra h0
    have hc0 : (C2k.filter (fun Y => supp Y = X)).card = 0 := by omega
    rw [hc0, mul_zero] at hXbound
    have hc2 : C2k.card = 0 := by omega
    rw [hc2, zero_mul] at hdouble
    exact (Nat.choose_pos hMN).not_ge hdouble
  -- Order X counterclockwise using `exists_ccw_ordering`
  obtain ⟨hX1, hXconv⟩ := Finset.mem_filter.mp hXCk
  obtain ⟨hXP, hXcard⟩ := Finset.mem_powersetCard.mp hX1
  obtain ⟨x, hx_ccw, hx_mem, hx_inj⟩ := exists_ccw_ordering hk hXcard (Set.Triplewise.mono hXP hnt) hXconv
  -- For EVERY Y ∈ C2k with supp Y = X, its odd points form a tuple in ∏ i, (P.filter (inSpike x i))!
  -- Crucial: the cyclic order of X inside y matches x up to a cyclic shift!
  -- Wait: if y's even points equal X as a set, and both y_even and x are IsCcw on X,
  -- then y_even = x ∘ shift!
  have hccw_shift : ∀ (u v : Fin k → ℝ²), IsCcw u → IsCcw v →
      (∀ i, ∃ j, u i = v j) → Function.Injective u → Function.Injective v →
      ∃ s : Fin k, ∀ i : Fin k, u i = v (i + s) := by
    intro u v hu hv hsurj hu_inj hv_inj
    -- Find s with u 0 = v s
    obtain ⟨s, hs⟩ := hsurj 0
    -- For every i, define σ i as the unique j with u i = v j.
    choose σ hσ using hsurj
    have hσ_inj : Function.Injective σ := by
      intro i j hij; apply hu_inj; rw [hσ i, hσ j, hij]
    have hσ0 : σ 0 = s := hv_inj ((hσ 0).symm.trans hs)
    -- For 0 < i < j, orient (v s) (v (σ i)) (v (σ j)) = orient (u 0) (u i) (u j) > 0,
    -- which forces cyclic distance from s to σ i < cyclic distance from s to σ j!
    have hdist_mono : ∀ ⦃i j : Fin k⦄, (0 : Fin k) < i → i < j →
        ((σ i).val + k - s.val) % k < ((σ j).val + k - s.val) % k := by
      intro i j h0i hij
      have hpos : 0 < orient (v s) (v (σ i)) (v (σ j)) := by
        rw [← hs, ← hσ i, ← hσ j]; exact hu h0i hij
      by_contra! hge
      have hne1 : s ≠ σ i := by rw [← hσ0]; exact hσ_inj.ne h0i.ne
      have hne2 : σ i ≠ σ j := hσ_inj.ne hij.ne
      have hne3 : s ≠ σ j := by rw [← hσ0]; exact hσ_inj.ne (h0i.trans hij).ne
      have hne_mod : ((σ j).val + k - s.val) % k ≠ ((σ i).val + k - s.val) % k := by
        intro heq
        have hi' := (σ i).isLt; have hj' := (σ j).isLt; have hs' := s.isLt
        have hval : (σ i).val = (σ j).val := by
          by_cases h1 : s.val ≤ (σ i).val <;> by_cases h2 : s.val ≤ (σ j).val
          · have e1 : ((σ i).val + k - s.val) % k = (σ i).val - s.val := by
              rw [show (σ i).val + k - s.val = k + ((σ i).val - s.val) by omega,
                  Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            have e2 : ((σ j).val + k - s.val) % k = (σ j).val - s.val := by
              rw [show (σ j).val + k - s.val = k + ((σ j).val - s.val) by omega,
                  Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            omega
          · have e1 : ((σ i).val + k - s.val) % k = (σ i).val - s.val := by
              rw [show (σ i).val + k - s.val = k + ((σ i).val - s.val) by omega,
                  Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            have e2 : ((σ j).val + k - s.val) % k = (σ j).val + k - s.val := Nat.mod_eq_of_lt (by omega)
            omega
          · have e1 : ((σ i).val + k - s.val) % k = (σ i).val + k - s.val := Nat.mod_eq_of_lt (by omega)
            have e2 : ((σ j).val + k - s.val) % k = (σ j).val - s.val := by
              rw [show (σ j).val + k - s.val = k + ((σ j).val - s.val) by omega,
                  Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            omega
          · have e1 : ((σ i).val + k - s.val) % k = (σ i).val + k - s.val := Nat.mod_eq_of_lt (by omega)
            have e2 : ((σ j).val + k - s.val) % k = (σ j).val + k - s.val := Nat.mod_eq_of_lt (by omega)
            omega
        exact hne2 (Fin.ext hval)
      have hneg := hv.orient_cyc hne3 hne2.symm hne1 (lt_of_le_of_ne hge hne_mod)
      rw [orient_swap₂₃] at hneg
      linarith
    -- The function f(i) = ((σ i).val + k - s.val) % k is strictly increasing on Fin k → Fin k,
    -- hence f(i) = i for all i!
    let f : Fin k → ℕ := fun i => ((σ i).val + k - s.val) % k
    have hf0 : f 0 = 0 := by
      simp only [f, hσ0, show s.val + k - s.val = k by omega, Nat.mod_self]
    have hf_strict : StrictMono f := by
      intro i j hij
      by_cases hi0 : i = 0
      · subst hi0; rw [hf0]
        have hne : σ j ≠ s := by rw [← hσ0]; exact hσ_inj.ne hij.ne.symm
        have hj' := (σ j).isLt; have hs' := s.isLt
        have hne' : (σ j).val ≠ s.val := fun h => hne (Fin.ext h)
        dsimp [f]
        by_cases hcmp : s.val < (σ j).val
        · rw [show (σ j).val + k - s.val = k + ((σ j).val - s.val) by omega,
              Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]; omega
        · rw [Nat.mod_eq_of_lt (by omega)]; omega
      · exact hdist_mono (Fin.lt_def.mpr (Nat.pos_of_ne_zero (fun h => hi0 (Fin.ext h)))) hij
    have hf_eq : ∀ i : Fin k, f i = i.val := by
      have hge : ∀ i : Fin k, i.val ≤ f i := by
        intro i; induction h : i.val generalizing i with
        | zero => omega
        | succ m ihm =>
          have hprev := ihm ⟨m, by omega⟩ rfl
          have hlt := hf_strict (Fin.lt_def.mpr (by dsimp; omega) : (⟨m, by omega⟩ : Fin k) < i)
          omega
      have hle : ∀ i : Fin k, f i ≤ i.val := by
        intro i
        suffices ∀ d : ℕ, ∀ j : Fin k, j.val + d = k - 1 → f j + d ≤ k - 1 by
          have hi := i.isLt
          have := this (k - 1 - i.val) i (by omega); omega
        intro d
        induction d with
        | zero => intro j hj; have : f j < k := Nat.mod_lt _ (by omega); omega
        | succ d ihd =>
          intro j hj
          have hj1 : j.val + 1 < k := by omega
          have hnext := ihd ⟨j.val + 1, hj1⟩ (by dsimp; omega)
          have hlt := hf_strict (Fin.lt_def.mpr (by dsimp; omega) : j < ⟨j.val + 1, hj1⟩)
          omega
      intro i; exact le_antisymm (hle i) (hge i)
    refine ⟨s, fun i => ?_⟩
    rw [hσ i]
    congr 1
    apply Fin.ext
    have hfi := hf_eq i
    dsimp [f] at hfi
    have hi' := i.isLt; have hs' := s.isLt; have hσ' := (σ i).isLt
    rw [Fin.val_add]
    by_cases hcmp : s.val ≤ (σ i).val
    · rw [show (σ i).val + k - s.val = k + ((σ i).val - s.val) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hfi
      rw [show i.val + s.val = (σ i).val by omega, Nat.mod_eq_of_lt hσ']
    · rw [Nat.mod_eq_of_lt (by omega)] at hfi
      rw [show i.val + s.val = (σ i).val + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hσ']
  -- Inject `C2k.filter (supp · = X)` into `Fintype.piFinset (fun i : Fin k => P.filter (inSpike x i))`!
  have hfib_le_prod : (C2k.filter (fun Y => supp Y = X)).card ≤
      ∏ i : Fin k, (P.filter (inSpike x i)).card := by
    rw [← Fintype.card_piFinset]
    let Pi := Fintype.piFinset (fun i : Fin k => P.filter (inSpike x i))
    have hmap : ∀ Y ∈ C2k.filter (fun Y => supp Y = X),
        ∃ g : Fin k → ℝ², (∀ i, g i ∈ P.filter (inSpike x i)) ∧
          Y = X ∪ Finset.univ.image g := by
      intro Y hY
      obtain ⟨hYC, hYsupp⟩ := Finset.mem_filter.mp hY
      have hY1 := (Finset.mem_filter.mp hYC).1
      obtain ⟨hYP, hYcard⟩ := Finset.mem_powersetCard.mp hY1
      set y := (hY_ord Y hYC).choose
      have hy : IsCcw y ∧ (∀ i, y i ∈ Y) ∧ Function.Injective y := (hY_ord Y hYC).choose_spec
      have hX_eq : Finset.univ.image (fun i : Fin k => y ⟨2 * i.val, by omega⟩) = X := by
        simpa [supp, dif_pos hYC] using hYsupp
      let u : Fin k → ℝ² := fun i => y ⟨2 * i.val, by omega⟩
      have hu_ccw : IsCcw u := fun a b c hab hbc =>
        hy.1 (Fin.lt_def.mpr (by dsimp; have := Fin.lt_def.mp hab; omega))
          (Fin.lt_def.mpr (by dsimp; have := Fin.lt_def.mp hbc; omega))
      have hu_inj : Function.Injective u := fun a b h => by
        have := hy.2.2 h; exact Fin.ext (by have := congrArg Fin.val this; dsimp at this; omega)
      have hsurj : ∀ i, ∃ j, u i = x j := by
        intro i
        have huX : u i ∈ X := by rw [← hX_eq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
        have hX_img : Finset.univ.image x = X :=
          Finset.eq_of_subset_of_card_le
            (fun p hp => by obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp; exact hx_mem j)
            (by rw [Finset.card_image_of_injective _ hx_inj, Finset.card_univ, Fintype.card_fin, hXcard])
        rw [← hX_img] at huX
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp huX
        exact ⟨j, hj.symm⟩
      obtain ⟨s, hs⟩ := hccw_shift u x hu_ccw hx_ccw hsurj hu_inj hx_inj
      -- Define g(j) = y(2 * (j - s) + 1)
      let g : Fin k → ℝ² := fun j => y ⟨2 * (j - s).val + 1, by omega⟩
      refine ⟨g, ?_, ?_⟩
      · intro j
        refine Finset.mem_filter.mpr ⟨hYP (hy.2.1 _), ?_⟩
        intro a b hab
        -- Rewrite x a = u (a - s) = y (2*(a-s)) and x b = u (b - s) = y (2*(b-s))!
        have hxa : x a = y ⟨2 * (a - s).val, by omega⟩ := by
          have := hs (a - s); simp [u] at this; exact this.symm
        have hxb : x b = y ⟨2 * (b - s).val, by omega⟩ := by
          have := hs (b - s); simp [u] at this; exact this.symm
        rw [hxa, hxb]
        have hcyc_eq : ∀ u v : Fin k, ((u - s).val + k - (v - s).val) % k = (u.val + k - v.val) % k := by
          intro u v
          rw [fin_cyc_dist_eq_sub, fin_cyc_dist_eq_sub]
          congr 1; abel
        rw [← hcyc_eq j a, ← hcyc_eq b a]
        set a' := (a - s).val
        set b' := (b - s).val
        set j' := (j - s).val
        have ha' : a' < k := (a - s).isLt
        have hb' : b' < k := (b - s).isLt
        have hj' : j' < k := (j - s).isLt
        have hne_ab' : a' ≠ b' := fun h => hab (by
          have : a - s = b - s := Fin.ext h; simpa using congrArg (· + s) this)
        have he1 : (2 * j' + 1 + 2 * k - 2 * a') % (2 * k) = 2 * ((j' + k - a') % k) + 1 := by
          by_cases h1 : a' ≤ j'
          · have hA : (j' + k - a') % k = j' - a' := by
              rw [show j' + k - a' = k + (j' - a') by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            have hB : (2 * j' + 1 + 2 * k - 2 * a') % (2 * k) = 2 * (j' - a') + 1 := by
              rw [show 2 * j' + 1 + 2 * k - 2 * a' = 2 * k + (2 * (j' - a') + 1) by omega,
                  Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            rw [hA, hB]
          · have hA : (j' + k - a') % k = j' + k - a' := Nat.mod_eq_of_lt (by omega)
            have hB : (2 * j' + 1 + 2 * k - 2 * a') % (2 * k) = 2 * (j' + k - a') + 1 := by
              rw [show 2 * j' + 1 + 2 * k - 2 * a' = 2 * (j' + k - a') + 1 by omega,
                  Nat.mod_eq_of_lt (by omega)]
            rw [hA, hB]
        have he2 : (2 * b' + 2 * k - 2 * a') % (2 * k) = 2 * ((b' + k - a') % k) := by
          by_cases h1 : a' ≤ b'
          · have hA : (b' + k - a') % k = b' - a' := by
              rw [show b' + k - a' = k + (b' - a') by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            have hB : (2 * b' + 2 * k - 2 * a') % (2 * k) = 2 * (b' - a') := by
              rw [show 2 * b' + 2 * k - 2 * a' = 2 * k + 2 * (b' - a') by omega,
                  Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            rw [hA, hB]
          · have hA : (b' + k - a') % k = b' + k - a' := Nat.mod_eq_of_lt (by omega)
            have hB : (2 * b' + 2 * k - 2 * a') % (2 * k) = 2 * (b' + k - a') := by
              rw [show 2 * b' + 2 * k - 2 * a' = 2 * (b' + k - a') by omega,
                  Nat.mod_eq_of_lt (by omega)]
            rw [hA, hB]
        split_ifs with hlt
        · have hlt' : (j' + k - a') % k < (b' + k - a') % k := hlt
          rw [orient_swap₂₃]
          have hpos := hy.1.orient_cyc (a := ⟨2 * a', by omega⟩) (b := ⟨2 * j' + 1, by omega⟩)
            (c := ⟨2 * b', by omega⟩) (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
            (by simp [Fin.ext_iff]; omega) (by dsimp; rw [he1, he2]; omega)
          linarith
        · push Not at hlt
          have hlt' : (b' + k - a') % k ≤ (j' + k - a') % k := hlt
          exact hy.1.orient_cyc (a := ⟨2 * a', by omega⟩) (b := ⟨2 * b', by omega⟩)
            (c := ⟨2 * j' + 1, by omega⟩) (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
            (by simp [Fin.ext_iff]; omega) (by dsimp; rw [he1, he2]; omega)
      · -- Y = X ∪ image g
        have hY_img : Finset.univ.image y = Y :=
          Finset.eq_of_subset_of_card_le
            (fun p hp => by obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hp; exact hy.2.1 t)
            (by rw [Finset.card_image_of_injective _ hy.2.2, Finset.card_univ, Fintype.card_fin, hYcard])
        rw [← hY_img, ← hX_eq]
        ext p; simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨t, rfl⟩
          by_cases he : t.val % 2 = 0
          · left; exact ⟨⟨t.val / 2, by omega⟩, by congr 1; apply Fin.ext; dsimp; omega⟩
          · right; refine ⟨⟨t.val / 2, by omega⟩ + s, ?_⟩
            simp only [g, add_sub_cancel_right]
            congr 1; apply Fin.ext; dsimp; omega
        · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
          · exact ⟨⟨2 * i.val, by omega⟩, rfl⟩
          · exact ⟨⟨2 * (j - s).val + 1, by omega⟩, rfl⟩
    choose Φ hΦmem hΦeq using hmap
    apply Finset.card_le_card_of_injOn (fun Y => if hY : Y ∈ C2k.filter (fun Y => supp Y = X) then Φ Y hY else fun _ => 0)
    · intro Y hY
      have hY' : Y ∈ C2k.filter (fun Y => supp Y = X) := hY
      change (if h : Y ∈ C2k.filter (fun Y => supp Y = X) then Φ Y h else fun _ => 0) ∈ Pi
      rw [dif_pos hY', Fintype.mem_piFinset]
      exact hΦmem Y hY'
    · intro Y₁ hY₁ Y₂ hY₂ heq
      have h1 : Y₁ ∈ C2k.filter (fun Y => supp Y = X) := hY₁
      have h2 : Y₂ ∈ C2k.filter (fun Y => supp Y = X) := hY₂
      dsimp only at heq
      rw [dif_pos h1, dif_pos h2] at heq
      rw [hΦeq Y₁ h1, hΦeq Y₂ h2, heq]
  -- Combine the numerical bounds!
  refine ⟨x, hx_ccw, fun i => hXP (hx_mem i), hx_inj, ?_⟩
  have hCk_le : Ck.card ≤ Nat.choose N k := by
    calc Ck.card ≤ (P.powersetCard k).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = Nat.choose N k := Finset.card_powersetCard k P
  -- Use: choose N M * choose M (2k) = choose N (2k) * choose (N - 2k) (M - 2k)
  have hcomb_id : Nat.choose N M * Nat.choose M (2 * k) =
      Nat.choose N (2 * k) * Nat.choose (N - 2 * k) (M - 2 * k) := by
    have h1 := Nat.choose_mul_factorial_mul_factorial hMN
    have h2 := Nat.choose_mul_factorial_mul_factorial h2k_le_M
    have h3 := Nat.choose_mul_factorial_mul_factorial (h2k_le_M.trans hMN)
    have h4 := Nat.choose_mul_factorial_mul_factorial (show M - 2 * k ≤ N - 2 * k by omega)
    have hsub : N - 2 * k - (M - 2 * k) = N - M := by omega
    rw [hsub] at h4
    have hpos : 0 < (2 * k).factorial * (M - 2 * k).factorial * (N - M).factorial * M.factorial * (N - 2 * k).factorial := by
      positivity
    have hmul : (Nat.choose N M * Nat.choose M (2 * k)) *
        ((2 * k).factorial * (M - 2 * k).factorial * (N - M).factorial * M.factorial * (N - 2 * k).factorial) =
        (Nat.choose N (2 * k) * Nat.choose (N - 2 * k) (M - 2 * k)) *
        ((2 * k).factorial * (M - 2 * k).factorial * (N - M).factorial * M.factorial * (N - 2 * k).factorial) := by
      calc (Nat.choose N M * Nat.choose M (2 * k)) *
            ((2 * k).factorial * (M - 2 * k).factorial * (N - M).factorial * M.factorial * (N - 2 * k).factorial)
          = (Nat.choose N M * M.factorial * (N - M).factorial) *
            (Nat.choose M (2 * k) * (2 * k).factorial * (M - 2 * k).factorial) * (N - 2 * k).factorial := by ring
        _ = N.factorial * M.factorial * (N - 2 * k).factorial := by rw [h1, h2]
        _ = (Nat.choose N (2 * k) * (2 * k).factorial * (N - 2 * k).factorial) *
            (Nat.choose (N - 2 * k) (M - 2 * k) * (M - 2 * k).factorial * (N - M).factorial) * M.factorial := by
            rw [h3, h4]; ring
        _ = (Nat.choose N (2 * k) * Nat.choose (N - 2 * k) (M - 2 * k)) *
            ((2 * k).factorial * (M - 2 * k).factorial * (N - M).factorial * M.factorial * (N - 2 * k).factorial) := by ring
    exact Nat.eq_of_mul_eq_mul_right hpos hmul
  have hpos_den : 0 < Nat.choose (N - 2 * k) (M - 2 * k) :=
    Nat.choose_pos (by omega)
  have hC2k_mul : Nat.choose N (2 * k) ≤ C2k.card * Nat.choose M (2 * k) := by
    have h1 : Nat.choose N M * Nat.choose M (2 * k) ≤
        C2k.card * Nat.choose (N - 2 * k) (M - 2 * k) * Nat.choose M (2 * k) :=
      Nat.mul_le_mul_right _ hdouble
    rw [hcomb_id] at h1
    have h2 : Nat.choose N (2 * k) * Nat.choose (N - 2 * k) (M - 2 * k) ≤
        (C2k.card * Nat.choose M (2 * k)) * Nat.choose (N - 2 * k) (M - 2 * k) := by
      linarith
    exact Nat.le_of_mul_le_mul_right h2 hpos_den
  -- Also: N^k * choose N k ≤ choose N (2k) * ... wait: let's prove directly in ℕ/ℝ:
  -- choose N (2k) / (choose M (2k) * choose N k) ≥ N^k / 2^(8k^2)!
  -- Simpler: Nat.choose N (2k) * (2k)! ≥ (N - 2k + 1)^(2k), and Nat.choose M (2k) * (2k)! ≤ M^(2k),
  -- and Nat.choose N k * k! ≤ N^k!
  -- Actually: (N - 2k)^(2k) / (M^(2k) * N^k) is tricky when N = M = 2^(4k)!
  -- Use the EXACT inequality from ES-v2.tex line 340:
  -- choose N (2k) / choose M (2k) = ∏_{j < 2k} (N - j) / (M - j) ≥ (N / M)^(2k)!
  -- Because for N ≥ M > j, (N - j) / (M - j) ≥ N / M  <==>  M*(N - j) ≥ N*(M - j) <==> j*N ≥ j*M!
  have hratio : (N : ℝ) ^ (2 * k) * (Nat.choose M (2 * k) : ℝ) ≤
      (M : ℝ) ^ (2 * k) * (Nat.choose N (2 * k) : ℝ) := by
    have hdesc : ∀ (r : ℕ), r ≤ M →
        (N : ℝ) ^ r * (Nat.descFactorial M r : ℝ) ≤ (M : ℝ) ^ r * (Nat.descFactorial N r : ℝ) := by
      intro r
      induction r with
      | zero => intro _; simp
      | succ r ihr =>
        intro hr
        rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
        push_cast
        have hstep : (N : ℝ) * ((M - r : ℕ) : ℝ) ≤ (M : ℝ) * ((N - r : ℕ) : ℝ) := by
          have hMr : (r : ℝ) ≤ M := by exact_mod_cast (show r ≤ M by omega)
          have hNr : (r : ℝ) ≤ N := by exact_mod_cast (show r ≤ N by omega)
          rw [Nat.cast_sub (by omega : r ≤ M), Nat.cast_sub (by omega : r ≤ N)]
          have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
          nlinarith
        have hprev := ihr (by omega)
        have h1 : 0 ≤ (N : ℝ) ^ r * (Nat.descFactorial M r : ℝ) := by positivity
        have h2 : 0 ≤ (M : ℝ) * ((N - r : ℕ) : ℝ) := by positivity
        calc (N : ℝ) ^ r * (N : ℝ) * (((M - r : ℕ) : ℝ) * (Nat.descFactorial M r : ℝ))
            = ((N : ℝ) ^ r * (Nat.descFactorial M r : ℝ)) * ((N : ℝ) * ((M - r : ℕ) : ℝ)) := by ring
          _ ≤ ((M : ℝ) ^ r * (Nat.descFactorial N r : ℝ)) * ((M : ℝ) * ((N - r : ℕ) : ℝ)) :=
              mul_le_mul hprev hstep (by positivity) (by positivity)
          _ = (M : ℝ) ^ r * (M : ℝ) * (((N - r : ℕ) : ℝ) * (Nat.descFactorial N r : ℝ)) := by ring
    have hd := hdesc (2 * k) h2k_le_M
    have hchM : (Nat.descFactorial M (2 * k) : ℝ) = (Nat.choose M (2 * k) : ℝ) * ((2 * k).factorial : ℝ) := by
      exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose M (2 * k)).trans (mul_comm _ _)
    have hchN : (Nat.descFactorial N (2 * k) : ℝ) = (Nat.choose N (2 * k) : ℝ) * ((2 * k).factorial : ℝ) := by
      exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose N (2 * k)).trans (mul_comm _ _)
    rw [hchM, hchN] at hd
    have hfac : (0 : ℝ) < ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (2 * k)
    nlinarith
  have hchM_pos : (0 : ℝ) < (Nat.choose M (2 * k) : ℝ) := by
    exact_mod_cast Nat.choose_pos h2k_le_M
  have hC2k_real : (N : ℝ) ^ (2 * k) ≤ (M : ℝ) ^ (2 * k) * (C2k.card : ℝ) := by
    have h1 : (Nat.choose N (2 * k) : ℝ) ≤ (C2k.card : ℝ) * (Nat.choose M (2 * k) : ℝ) := by
      exact_mod_cast hC2k_mul
    have h2 : (M : ℝ) ^ (2 * k) * (Nat.choose N (2 * k) : ℝ) ≤
        (M : ℝ) ^ (2 * k) * ((C2k.card : ℝ) * (Nat.choose M (2 * k) : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (N : ℝ) ^ (2 * k) * (Nat.choose M (2 * k) : ℝ) ≤
        ((M : ℝ) ^ (2 * k) * (C2k.card : ℝ)) * (Nat.choose M (2 * k) : ℝ) := by linarith
    exact le_of_mul_le_mul_right h3 hchM_pos
  have hCk_real : (Ck.card : ℝ) ≤ (N : ℝ) ^ k := by
    have h1 : Ck.card ≤ N ^ k := hCk_le.trans (Nat.choose_le_pow N k)
    exact_mod_cast h1
  have hM_pow : (M : ℝ) ^ (2 * k) = (2 : ℝ) ^ (8 * k ^ 2) := by
    rw [hM_eq]; push_cast; rw [← pow_mul]; congr 1; ring
  have hprod_real : ((C2k.filter (fun Y => supp Y = X)).card : ℝ) ≤
      ∏ i : Fin k, ((P.filter (inSpike x i)).card : ℝ) := by
    exact_mod_cast hfib_le_prod
  have hXbound_real : (C2k.card : ℝ) ≤ (Ck.card : ℝ) * ((C2k.filter (fun Y => supp Y = X)).card : ℝ) := by
    exact_mod_cast hXbound
  have hN_pos : (0 : ℝ) < (N : ℝ) ^ k := by
    have : 0 < N := lt_of_lt_of_le (by positivity) hN
    positivity
  have hfinal : (N : ℝ) ^ k * (N : ℝ) ^ k ≤
      (N : ℝ) ^ k * ((2 : ℝ) ^ (8 * k ^ 2) * ∏ i : Fin k, ((P.filter (inSpike x i)).card : ℝ)) := by
    calc (N : ℝ) ^ k * (N : ℝ) ^ k
        = (N : ℝ) ^ (2 * k) := by rw [← pow_add, two_mul]
      _ ≤ (M : ℝ) ^ (2 * k) * (C2k.card : ℝ) := hC2k_real
      _ = (2 : ℝ) ^ (8 * k ^ 2) * (C2k.card : ℝ) := by rw [hM_pow]
      _ ≤ (2 : ℝ) ^ (8 * k ^ 2) * ((Ck.card : ℝ) * ((C2k.filter (fun Y => supp Y = X)).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hXbound_real (by positivity)
      _ ≤ (2 : ℝ) ^ (8 * k ^ 2) * ((N : ℝ) ^ k * ∏ i : Fin k, ((P.filter (inSpike x i)).card : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hCk_real hprod_real (by positivity) (by positivity)) (by positivity)
      _ = (N : ℝ) ^ k * ((2 : ℝ) ^ (8 * k ^ 2) * ∏ i : Fin k, ((P.filter (inSpike x i)).card : ℝ)) := by ring
  exact le_of_mul_le_mul_left hfinal hN_pos

/- ### Section 5: Vertical and Horizontal Partial Orders & Erdős–Szekeres Pigeonhole -/

/-- Orthogonal vertical and horizontal orders on spike `i` of `x`. -/
def vLt {k : ℕ} [NeZero k] (x : Fin k → ℝ²) (i : Fin k) (p q : ℝ²) : Prop :=
  0 < orient (x (i + 2)) p q ∧ orient (x (i - 1)) p q < 0

def hLt {k : ℕ} [NeZero k] (x : Fin k → ℝ²) (i : Fin k) (p q : ℝ²) : Prop :=
  orient (x (i + 2)) p q < 0 ∧ orient (x (i - 1)) p q < 0

/-- Ray-slope function from `A` relative to base vector `B - A`. -/
noncomputable def raySlope (A B p : ℝ²) : ℝ :=
  ((p 0 - A 0) * (B 0 - A 0) + (p 1 - A 1) * (B 1 - A 1)) / orient A B p

lemma orient_eq_raySlope_diff {A B p q : ℝ²} (hp : 0 < orient A B p) (hq : 0 < orient A B q) :
    orient A p q < 0 ↔ raySlope A B p < raySlope A B q := by
  -- Identity: ((B 0 - A 0)^2 + (B 1 - A 1)^2) * orient A p q =
  --   orient A B p * orient A B q * (raySlope A B p - raySlope A B q)
  have hAB : 0 < (B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2 := by
    by_contra h
    have h0 : B 0 - A 0 = 0 ∧ B 1 - A 1 = 0 := by
      constructor <;> nlinarith [sq_nonneg (B 0 - A 0), sq_nonneg (B 1 - A 1)]
    have : orient A B p = 0 := by simp [orient, h0.1, h0.2]
    linarith
  have hid : ((B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2) * orient A p q =
      orient A B p * orient A B q * (raySlope A B p - raySlope A B q) := by
    dsimp [raySlope]
    have hpne : orient A B p ≠ 0 := hp.ne'
    have hqne : orient A B q ≠ 0 := hq.ne'
    field_simp
    simp only [orient]
    ring
  have hprod : 0 < orient A B p * orient A B q := mul_pos hp hq
  constructor <;> intro h <;> nlinarith

lemma orient_B_eq_raySlope_diff {A B p q : ℝ²} (hp : 0 < orient A B p) (hq : 0 < orient A B q) :
    orient B p q < 0 ↔ raySlope B A p < raySlope B A q := by
  have hp' : orient B A p < 0 := by rw [orient_swap₁₂]; linarith
  have hq' : orient B A q < 0 := by rw [orient_swap₁₂]; linarith
  have hAB : 0 < (A 0 - B 0) ^ 2 + (A 1 - B 1) ^ 2 := by
    by_contra h
    have h0 : A 0 - B 0 = 0 ∧ A 1 - B 1 = 0 := by
      constructor <;> nlinarith [sq_nonneg (A 0 - B 0), sq_nonneg (A 1 - B 1)]
    have h1 : orient A B p = 0 := by
      simp only [orient]
      have e0 : B 0 - A 0 = -(A 0 - B 0) := by ring
      have e1 : B 1 - A 1 = -(A 1 - B 1) := by ring
      rw [e0, e1, h0.1, h0.2]; ring
    linarith
  have hid : ((A 0 - B 0) ^ 2 + (A 1 - B 1) ^ 2) * orient B p q =
      orient B A p * orient B A q * (raySlope B A p - raySlope B A q) := by
    dsimp [raySlope]
    have hpne : orient B A p ≠ 0 := hp'.ne
    have hqne : orient B A q ≠ 0 := hq'.ne
    field_simp
    simp only [orient]
    ring
  have hprod : 0 < orient B A p * orient B A q := mul_pos_of_neg_of_neg hp' hq'
  constructor <;> intro h <;> nlinarith

/-- Erdős–Szekeres monotone subsequence pigeonhole: for two real functions `f, g` on a finset `S`
taking distinct values on distinct elements, `|S| ≤ v * h`, where `v` (resp. `h`) is the max
length of a chain increasing in `g` and decreasing (resp. increasing) in `f`. -/
lemma dilworth_two_functions {α : Type*} (S : Finset α) (f g : α → ℝ)
    (hf : Set.InjOn f (S : Set α)) (hg : Set.InjOn g (S : Set α))
    (v h : ℕ)
    (hv : ∀ C ⊆ S, (∀ x ∈ C, ∀ y ∈ C, g x < g y → f y < f x) → C.card ≤ v)
    (hh : ∀ C ⊆ S, (∀ x ∈ C, ∀ y ∈ C, g x < g y → f x < f y) → C.card ≤ h) :
    S.card ≤ v * h := by
  let Vset (x : α) : Finset (Finset α) :=
    S.powerset.filter fun C => x ∈ C ∧ (∀ y ∈ C, g y ≤ g x) ∧
      (∀ a ∈ C, ∀ b ∈ C, g a < g b → f b < f a)
  let Hset (x : α) : Finset (Finset α) :=
    S.powerset.filter fun C => x ∈ C ∧ (∀ y ∈ C, g y ≤ g x) ∧
      (∀ a ∈ C, ∀ b ∈ C, g a < g b → f a < f b)
  let dv (x : α) : ℕ := (Vset x).sup Finset.card
  let dh (x : α) : ℕ := (Hset x).sup Finset.card
  have hdv_pos : ∀ x ∈ S, 1 ≤ dv x := by
    intro x hx
    have h1 : ({x} : Finset α) ∈ Vset x := by
      simp [Vset, Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff.mpr hx]
    have := Finset.le_sup (f := Finset.card) h1
    simpa [dv] using this
  have hdh_pos : ∀ x ∈ S, 1 ≤ dh x := by
    intro x hx
    have h1 : ({x} : Finset α) ∈ Hset x := by
      simp [Hset, Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff.mpr hx]
    have := Finset.le_sup (f := Finset.card) h1
    simpa [dh] using this
  have hdv_le : ∀ x ∈ S, dv x ≤ v := by
    intro x _
    apply Finset.sup_le
    intro C hC
    obtain ⟨hCS, _, _, hord⟩ := Finset.mem_filter.mp hC
    exact hv C (Finset.mem_powerset.mp hCS) hord
  have hdh_le : ∀ x ∈ S, dh x ≤ h := by
    intro x _
    apply Finset.sup_le
    intro C hC
    obtain ⟨hCS, _, _, hord⟩ := Finset.mem_filter.mp hC
    exact hh C (Finset.mem_powerset.mp hCS) hord
  have hinj : Set.InjOn (fun x => (dv x, dh x)) (S : Set α) := by
    intro x hx y hy heq
    by_contra hne
    wlog hxy : g x < g y generalizing x y
    · exact this hy hx heq.symm (Ne.symm hne)
        (lt_of_le_of_ne (le_of_not_gt hxy) (fun h => hne (hg hx hy h.symm)))
    rcases lt_or_gt_of_ne (fun h => hne (hf hx hy h)) with hfxy | hfyx
    · have hneF : (Hset x).Nonempty :=
        ⟨{x}, by simp [Hset, Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff.mpr hx]⟩
      obtain ⟨C, hCF, hCmax⟩ := Finset.exists_max_image (Hset x) Finset.card hneF
      have hdh_eq : dh x = C.card :=
        le_antisymm (Finset.sup_le fun D hD => hCmax D hD) (Finset.le_sup (f := Finset.card) hCF)
      obtain ⟨hCS, hxC, hgx, hord⟩ := Finset.mem_filter.mp hCF
      have hy_notC : y ∉ C := fun hm => not_lt_of_ge (hgx y hm) hxy
      have hins : insert y C ∈ Hset y := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hy (Finset.mem_powerset.mp hCS)),
          Finset.mem_insert_self y C, ?_, ?_⟩
        · intro z hz; rcases Finset.mem_insert.mp hz with rfl | hzC
          · exact le_rfl
          · exact (hgx z hzC).trans hxy.le
        · intro a ha b hb hab
          rcases Finset.mem_insert.mp ha with rfl | haC
          · rcases Finset.mem_insert.mp hb with rfl | hbC
            · exact (lt_irrefl _ hab).elim
            · exact (not_lt_of_ge ((hgx b hbC).trans hxy.le) hab).elim
          · rcases Finset.mem_insert.mp hb with rfl | hbC
            · by_cases hax : a = x
              · rwa [hax]
              · have hga : g a < g x := lt_of_le_of_ne (hgx a haC)
                  (fun h => hax (hg (Finset.mem_powerset.mp hCS haC) hx h))
                exact (hord a haC x hxC hga).trans hfxy
            · exact hord a haC b hbC hab
      have hle : C.card + 1 ≤ dh y := by
        have := Finset.le_sup (f := Finset.card) hins
        rwa [Finset.card_insert_of_notMem hy_notC] at this
      have heq' : dh x = dh y := congrArg Prod.snd heq
      omega
    · have hneF : (Vset x).Nonempty :=
        ⟨{x}, by simp [Vset, Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff.mpr hx]⟩
      obtain ⟨C, hCF, hCmax⟩ := Finset.exists_max_image (Vset x) Finset.card hneF
      have hdv_eq : dv x = C.card :=
        le_antisymm (Finset.sup_le fun D hD => hCmax D hD) (Finset.le_sup (f := Finset.card) hCF)
      obtain ⟨hCS, hxC, hgx, hord⟩ := Finset.mem_filter.mp hCF
      have hy_notC : y ∉ C := fun hm => not_lt_of_ge (hgx y hm) hxy
      have hins : insert y C ∈ Vset y := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hy (Finset.mem_powerset.mp hCS)),
          Finset.mem_insert_self y C, ?_, ?_⟩
        · intro z hz; rcases Finset.mem_insert.mp hz with rfl | hzC
          · exact le_rfl
          · exact (hgx z hzC).trans hxy.le
        · intro a ha b hb hab
          rcases Finset.mem_insert.mp ha with rfl | haC
          · rcases Finset.mem_insert.mp hb with rfl | hbC
            · exact (lt_irrefl _ hab).elim
            · exact (not_lt_of_ge ((hgx b hbC).trans hxy.le) hab).elim
          · rcases Finset.mem_insert.mp hb with rfl | hbC
            · by_cases hax : a = x
              · rwa [hax]
              · have hga : g a < g x := lt_of_le_of_ne (hgx a haC)
                  (fun h => hax (hg (Finset.mem_powerset.mp hCS haC) hx h))
                exact hfyx.trans (hord a haC x hxC hga)
            · exact hord a haC b hbC hab
      have hle : C.card + 1 ≤ dv y := by
        have := Finset.le_sup (f := Finset.card) hins
        rwa [Finset.card_insert_of_notMem hy_notC] at this
      have heq' : dv x = dv y := congrArg Prod.fst heq
      omega
  have hsub : S.image (fun x => (dv x, dh x)) ⊆ Finset.Icc 1 v ×ˢ Finset.Icc 1 h := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hdv_pos x hx, hdv_le x hx⟩,
      Finset.mem_Icc.mpr ⟨hdh_pos x hx, hdh_le x hx⟩⟩
  calc S.card = (S.image (fun x => (dv x, dh x))).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 v ×ˢ Finset.Icc 1 h).card := Finset.card_le_card hsub
    _ = v * h := by simp [Finset.card_product]

/- ### Section 6: Separation Lemmas & Joining Chains (HMPT Obs. 3.3–3.7) -/

/-- HMPT Observation 3.3 (Vertical separation): if `p ≺_v q` in spike `S_i`, then
`orient p q z > 0` on `S_{i+1}` and `orient p q z < 0` on `S_{i-1}`. -/
lemma vertical_sep_next {k : ℕ} [NeZero k] (hk : 4 ≤ k) {x : Fin k → ℝ²} (hx : IsCcw x)
    {i : Fin k} {p q z : ℝ²} (_hp : inSpike x i p) (hq : inSpike x i q)
    (hpq : vLt x i p q) (hz : inSpike x (i + 1) z) :
    0 < orient p q z := by
  let B := x (i - 1); let C := x i; let D := x (i + 1); let A := x (i + 2)
  obtain ⟨_, hCDA, _, _, _, _⟩ := ccw_quad hk hx i
  have hABq : 0 < orient A B q := inSpike_base_gt hk hq
  have hDAq : 0 < orient D A q := by
    have h := inSpike_other_edge_gt (by omega) (fin_ne_add_one (by omega) i).symm hq
    simpa [D, A, add_assoc, fin_one_add_one] using h
  have hDBq : 0 < orient D B q := inSpike_diag_gt hk hq
  have hpqA : 0 < orient p q A := by
    have : orient p q A = orient A p q := by simp only [orient]; ring
    linarith [hpq.1]
  have hpqB : orient p q B < 0 := by
    have : orient p q B = orient B p q := by simp only [orient]; ring
    linarith [hpq.2]
  -- Step 1: orient p q D > 0 using orient_bary on (A, B, q) and (q, D, p)
  have hpqD : 0 < orient p q D := by
    have hb := orient_bary A B q q D p
    have h1 : orient q D p = orient p q D := by simp only [orient]; ring
    have h2 : orient B q p = -orient B p q := by simp only [orient]; ring
    have h3 : orient q D A = orient D A q := by simp only [orient]; ring
    have h4 : orient q A p = orient A p q := by simp only [orient]; ring
    have h5 : orient q D B = orient D B q := by simp only [orient]; ring
    have h6 : orient q D q = 0 := orient_self₁₃ q D
    rw [h1, h2, h3, h4, h5, h6, mul_zero, add_zero] at hb
    nlinarith [hpq.1, hpq.2]
  -- Step 2: orient p q C < 0 using orient_bary on (A, B, q) and (q, C, p)
  have hBCq : 0 < orient B C q := by
    have h := inSpike_other_edge_gt (by omega) (fin_ne_sub_one (by omega) i) hq
    simpa [B, C, sub_add_cancel] using h
  have hACq : 0 < orient A C q := inSpike_diag2_gt hk hq
  have hpqC : orient p q C < 0 := by
    have hb := orient_bary A B q q C p
    have h1 : orient q C p = orient p q C := by simp only [orient]; ring
    have h2 : orient B q p = -orient B p q := by simp only [orient]; ring
    have h3 : orient q C A = -orient A C q := by simp only [orient]; ring
    have h4 : orient q A p = orient A p q := by simp only [orient]; ring
    have h5 : orient q C B = -orient B C q := by simp only [orient]; ring
    have h6 : orient q C q = 0 := orient_self₁₃ q C
    rw [h1, h2, h3, h4, h5, h6, mul_zero, add_zero] at hb
    nlinarith [hpq.1, hpq.2]
  -- Step 3: orient p q z > 0 using orient_bary on (C, D, A) and (p, q, z)
  have hDAz : orient D A z < 0 := by
    have h := inSpike_edge_lt (by omega) hz
    simpa [D, A, add_assoc, fin_one_add_one] using h
  have hCDz : 0 < orient C D z := inSpike_other_edge_gt (by omega) (fin_ne_add_one (by omega) i) hz
  have hACz : 0 < orient A C z := inSpike_next_diag_gt hk hz
  have hb := orient_bary C D A p q z
  nlinarith

lemma vertical_sep_prev {k : ℕ} [NeZero k] (hk : 4 ≤ k) {x : Fin k → ℝ²} (hx : IsCcw x)
    {i : Fin k} {p q z : ℝ²} (_hp : inSpike x i p) (hq : inSpike x i q)
    (hpq : vLt x i p q) (hz : inSpike x (i - 1) z) :
    orient p q z < 0 := by
  let B := x (i - 1); let C := x i; let D := x (i + 1); let A := x (i + 2)
  obtain ⟨hBCD, _, _, _, _, _⟩ := ccw_quad hk hx i
  have hABq : 0 < orient A B q := inSpike_base_gt hk hq
  have hDAq : 0 < orient D A q := by
    have h := inSpike_other_edge_gt (by omega) (fin_ne_add_one (by omega) i).symm hq
    simpa [D, A, add_assoc, fin_one_add_one] using h
  have hDBq : 0 < orient D B q := inSpike_diag_gt hk hq
  have hBCq : 0 < orient B C q := by
    have h := inSpike_other_edge_gt (by omega) (fin_ne_sub_one (by omega) i) hq
    simpa [B, C, sub_add_cancel] using h
  have hACq : 0 < orient A C q := inSpike_diag2_gt hk hq
  have hpqB : orient p q B < 0 := by
    have : orient p q B = orient B p q := by simp only [orient]; ring
    linarith [hpq.2]
  have hpqD : 0 < orient p q D := by
    have hb := orient_bary A B q q D p
    have h1 : orient q D p = orient p q D := by simp only [orient]; ring
    have h2 : orient B q p = -orient B p q := by simp only [orient]; ring
    have h3 : orient q D A = orient D A q := by simp only [orient]; ring
    have h4 : orient q A p = orient A p q := by simp only [orient]; ring
    have h5 : orient q D B = orient D B q := by simp only [orient]; ring
    have h6 : orient q D q = 0 := orient_self₁₃ q D
    rw [h1, h2, h3, h4, h5, h6, mul_zero, add_zero] at hb
    nlinarith [hpq.1, hpq.2]
  have hpqC : orient p q C < 0 := by
    have hb := orient_bary A B q q C p
    have h1 : orient q C p = orient p q C := by simp only [orient]; ring
    have h2 : orient B q p = -orient B p q := by simp only [orient]; ring
    have h3 : orient q C A = -orient A C q := by simp only [orient]; ring
    have h4 : orient q A p = orient A p q := by simp only [orient]; ring
    have h5 : orient q C B = -orient B C q := by simp only [orient]; ring
    have h6 : orient q C q = 0 := orient_self₁₃ q C
    rw [h1, h2, h3, h4, h5, h6, mul_zero, add_zero] at hb
    nlinarith [hpq.1, hpq.2]
  have hBCz : orient B C z < 0 := by
    have h := inSpike_edge_lt (by omega) hz
    simpa [B, C, sub_add_cancel] using h
  have hCDz : 0 < orient C D z := inSpike_other_edge_gt (by omega) (fin_ne_sub_one (by omega) i).symm hz
  have hDBz : 0 < orient D B z := inSpike_prev_diag_gt hk hz
  have hb := orient_bary B C D p q z
  nlinarith

/-- HMPT Observation 3.4 (Horizontal separation): if `p ≺_h q` in spike `S_i`, then
`orient p q z < 0` for all `z ∈ S_j` with `j ∉ {i - 1, i, i + 1}`. -/
lemma horizontal_sep {k : ℕ} [NeZero k] (hk : 4 ≤ k) {x : Fin k → ℝ²} (hx : IsCcw x)
    {i j : Fin k} (hj1 : j ≠ i - 1) (hj2 : j ≠ i) (hj3 : j ≠ i + 1)
    {p q z : ℝ²} (hp : inSpike x i p) (hpq : hLt x i p q) (hz : inSpike x j z) :
    orient p q z < 0 := by
  let B := x (i - 1); let C := x i; let D := x (i + 1); let A := x (i + 2)
  obtain ⟨_, _, _, _, hBCA, hBDA⟩ := ccw_quad hk hx i
  have hABp : 0 < orient A B p := inSpike_base_gt hk hp
  have hABz : orient A B z < 0 := inSpike_far_base_lt hk hj1 hj2 hj3 hz
  have hBCp : 0 < orient B C p := by
    have h := inSpike_other_edge_gt (by omega) (fin_ne_sub_one (by omega) i) hp
    simpa [B, C, sub_add_cancel] using h
  have hDAp : 0 < orient D A p := by
    have h := inSpike_other_edge_gt (by omega) (fin_ne_add_one (by omega) i).symm hp
    simpa [D, A, add_assoc, fin_one_add_one] using h
  have hBCz : 0 < orient B C z := by
    have h := inSpike_other_edge_gt (by omega) hj1.symm hz
    simpa [B, C, sub_add_cancel] using h
  have hDAz : 0 < orient D A z := by
    have h := inSpike_other_edge_gt (by omega) hj3.symm hz
    simpa [D, A, add_assoc, fin_one_add_one] using h
  have hBpz : 0 < orient B p z := by
    have hb := orient_bary B C A B p z
    have h1 : orient B p B = 0 := orient_self₁₃ B p
    have h2 : orient B p C = -orient B C p := by simp only [orient]; ring
    have h3 : orient B p A = orient A B p := by simp only [orient]; ring
    rw [h1, mul_zero, zero_add, h2, h3] at hb
    nlinarith
  have hpAz : 0 < orient p A z := by
    have hb := orient_bary D A B p A z
    have hDAB : 0 < orient D A B := by
      have : orient D A B = orient B D A := by simp only [orient]; ring
      linarith
    have h1 : orient p A D = -orient D A p := by simp only [orient]; ring
    have h2 : orient p A A = 0 := orient_self₂₃ p A
    have h3 : orient p A B = orient A B p := by simp only [orient]; ring
    rw [h1, h2, mul_zero, add_zero, h3] at hb
    nlinarith
  have hpqA : orient p q A < 0 := by
    have : orient p q A = orient A p q := by simp only [orient]; ring
    linarith [hpq.1]
  have hpqB : orient p q B < 0 := by
    have : orient p q B = orient B p q := by simp only [orient]; ring
    linarith [hpq.2]
  have hb := orient_bary A B p p q z
  rw [orient_self₁₃ p q, mul_zero, add_zero] at hb
  nlinarith

/-- Universal transitivity lemma for both vertical and horizontal chains:
if `orient B p_a p_b < 0` for all `a < b`, then `orient p_a p_b p_c < 0` (and `> 0`) is transitive! -/
lemma orient_chain_transitive_neg {B p₁ p₂ p₃ p₄ : ℝ²}
    (hB12 : orient B p₁ p₂ < 0) (hB13 : orient B p₁ p₃ < 0)
    (hB23 : orient B p₂ p₃ < 0) (hB24 : orient B p₂ p₄ < 0) (hB34 : orient B p₃ p₄ < 0)
    (h123 : orient p₁ p₂ p₃ < 0) (h234 : orient p₂ p₃ p₄ < 0) :
    orient p₁ p₂ p₄ < 0 ∧ orient p₁ p₃ p₄ < 0 := by
  have hB32 : 0 < orient B p₃ p₂ := by
    have : orient B p₃ p₂ = -orient B p₂ p₃ := by simp only [orient]; ring
    linarith
  have h324 : 0 < orient p₃ p₂ p₄ := by
    have : orient p₃ p₂ p₄ = -orient p₂ p₃ p₄ := by simp only [orient]; ring
    linarith
  constructor
  · have hb := orient_bary B p₃ p₂ p₁ p₂ p₄
    have h1 : orient p₁ p₂ B = orient B p₁ p₂ := by simp only [orient]; ring
    have h2 : orient p₂ B p₄ = -orient B p₂ p₄ := by simp only [orient]; ring
    have h3 : orient p₁ p₂ p₂ = 0 := orient_self₂₃ p₁ p₂
    rw [h1, h2, h3, mul_zero, add_zero] at hb
    nlinarith
  · have hb := orient_bary B p₃ p₂ p₁ p₃ p₄
    have h1 : orient p₁ p₃ B = orient B p₁ p₃ := by simp only [orient]; ring
    have h2 : orient p₁ p₃ p₃ = 0 := orient_self₂₃ p₁ p₃
    have h3 : orient p₁ p₃ p₂ = -orient p₁ p₂ p₃ := by simp only [orient]; ring
    rw [h1, h2, mul_zero, add_zero, h3] at hb
    nlinarith

lemma orient_chain_transitive_pos {B p₁ p₂ p₃ p₄ : ℝ²}
    (hB12 : orient B p₁ p₂ < 0) (hB13 : orient B p₁ p₃ < 0)
    (hB23 : orient B p₂ p₃ < 0) (hB24 : orient B p₂ p₄ < 0) (hB34 : orient B p₃ p₄ < 0)
    (h123 : 0 < orient p₁ p₂ p₃) (h234 : 0 < orient p₂ p₃ p₄) :
    0 < orient p₁ p₂ p₄ ∧ 0 < orient p₁ p₃ p₄ := by
  have hB32 : 0 < orient B p₃ p₂ := by
    have : orient B p₃ p₂ = -orient B p₂ p₃ := by simp only [orient]; ring
    linarith
  have h324 : orient p₃ p₂ p₄ < 0 := by
    have : orient p₃ p₂ p₄ = -orient p₂ p₃ p₄ := by simp only [orient]; ring
    linarith
  constructor
  · have hb := orient_bary B p₃ p₂ p₁ p₂ p₄
    have h1 : orient p₁ p₂ B = orient B p₁ p₂ := by simp only [orient]; ring
    have h2 : orient p₂ B p₄ = -orient B p₂ p₄ := by simp only [orient]; ring
    have h3 : orient p₁ p₂ p₂ = 0 := orient_self₂₃ p₁ p₂
    rw [h1, h2, h3, mul_zero, add_zero] at hb
    nlinarith
  · have hb := orient_bary B p₃ p₂ p₁ p₃ p₄
    have h1 : orient p₁ p₃ B = orient B p₁ p₃ := by simp only [orient]; ring
    have h2 : orient p₁ p₃ p₃ = 0 := orient_self₂₃ p₁ p₃
    have h3 : orient p₁ p₃ p₂ = -orient p₁ p₂ p₃ := by simp only [orient]; ring
    rw [h1, h2, mul_zero, add_zero, h3] at hb
    nlinarith

private lemma mul_pos_of_mul_same_sign {s x y : ℝ} (hx : 0 < s * x) (hy : 0 < s * y) : 0 < x * y := by
  have hxy : 0 < s ^ 2 * (x * y) := by nlinarith
  have hs2 : 0 < s ^ 2 := by
    by_contra h
    have hs0 : s = 0 := by nlinarith [sq_nonneg s]
    rw [hs0, zero_mul] at hx; exact lt_irrefl 0 hx
  exact pos_of_mul_pos_right hxy hs2.le

/-- Unified 3-in-same-chain + 1-outside exclusion lemma (handles `s = 1` and `s = -1`). -/
private lemma not_mem_conv_three_chain {lt : ℝ² → ℝ² → Prop} {C : Finset ℝ²} {s : ℝ}
    {u v w z : ℝ²} (hu : u ∈ C) (hv : v ∈ C) (hw : w ∈ C)
    (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (hnt : NonTrilinear ({u, v, w, z} : Set ℝ²))
    (hchain : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → lt a b ∨ lt b a)
    (htriple : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, lt a b → lt b c → 0 < s * orient a b c)
    (hsep : ∀ a ∈ C, ∀ b ∈ C, lt a b → 0 < s * orient a b z) :
    u ∉ convexHull ℝ ({v, w, z} : Set ℝ²) := by
  have hnt_vwz : NonTrilinear ({v, w, z, u} : Set ℝ²) :=
    Set.Triplewise.mono (by intro t ht; simp at ht ⊢; tauto) hnt
  have hnt_wvz : NonTrilinear ({w, v, z, u} : Set ℝ²) :=
    Set.Triplewise.mono (by intro t ht; simp at ht ⊢; tauto) hnt
  rcases hchain u hu v hv huv with huv' | hvu' <;> rcases hchain u hu w hw huw with huw' | hwu'
  · rcases hchain v hv w hw hvw with hvw' | hwv'
    · have h1 := htriple u hu v hv w hw huv' hvw'
      have h2 := hsep u hu v hv huv'
      apply not_mem_convexHull_triple_of_same_side hnt_vwz huv huw huz hvw hwz hvz
      have e1 : orient v u w = -orient u v w := by simp only [orient]; ring
      have e2 : orient v u z = -orient u v z := by simp only [orient]; ring
      rw [e1, e2, neg_mul_neg]; exact mul_pos_of_mul_same_sign h1 h2
    · have h1 := htriple u hu w hw v hv huw' hwv'
      have h2 := hsep u hu w hw huw'
      rw [show ({v, w, z} : Set ℝ²) = {w, v, z} by ext t; simp; tauto]
      apply not_mem_convexHull_triple_of_same_side hnt_wvz huw huv huz hvw.symm hvz hwz
      have e1 : orient w u v = -orient u w v := by simp only [orient]; ring
      have e2 : orient w u z = -orient u w z := by simp only [orient]; ring
      rw [e1, e2, neg_mul_neg]; exact mul_pos_of_mul_same_sign h1 h2
  · have h1 := htriple w hw u hu v hv hwu' huv'
    have h2 := hsep w hw u hu hwu'
    rw [show ({v, w, z} : Set ℝ²) = {w, v, z} by ext t; simp; tauto]
    apply not_mem_convexHull_triple_of_same_side hnt_wvz huw huv huz hvw.symm hvz hwz
    exact mul_pos_of_mul_same_sign h1 h2
  · have h1 := htriple v hv u hu w hw hvu' huw'
    have h2 := hsep v hv u hu hvu'
    apply not_mem_convexHull_triple_of_same_side hnt_vwz huv huw huz hvw hwz hvz
    exact mul_pos_of_mul_same_sign h1 h2
  · rcases hchain v hv w hw hvw with hvw' | hwv'
    · have h1 := htriple v hv w hw u hu hvw' hwu'
      have h2 := hsep w hw u hu hwu'
      rw [show ({v, w, z} : Set ℝ²) = {w, v, z} by ext t; simp; tauto]
      apply not_mem_convexHull_triple_of_same_side hnt_wvz huw huv huz hvw.symm hvz hwz
      have e1 : orient w u v = orient v w u := by simp only [orient]; ring
      rw [e1]; exact mul_pos_of_mul_same_sign h1 h2
    · have h1 := htriple w hw v hv u hu hwv' hvu'
      have h2 := hsep v hv u hu hvu'
      apply not_mem_convexHull_triple_of_same_side hnt_vwz huv huw huz hvw hwz hvz
      have e1 : orient v u w = orient w v u := by simp only [orient]; ring
      rw [e1]; exact mul_pos_of_mul_same_sign h1 h2

/-- HMPT Observation 3.5: joining a right convex chain `R ⊆ P_i` (`orient > 0`) and a
left convex chain `L ⊆ P_{i+1}` (`orient < 0`) yields a `ConvexIndep` set. -/
lemma joining_verticals {k : ℕ} [NeZero k] (hk : 4 ≤ k) {x : Fin k → ℝ²} (hx : IsCcw x)
    {i : Fin k} {R L : Finset ℝ²}
    (hnt : NonTrilinear ((R ∪ L : Finset ℝ²) : Set ℝ²))
    (hR_spike : ∀ p ∈ R, inSpike x i p)
    (hL_spike : ∀ p ∈ L, inSpike x (i + 1) p)
    (hR_chain : ∀ p ∈ R, ∀ q ∈ R, p ≠ q → vLt x i p q ∨ vLt x i q p)
    (hL_chain : ∀ p ∈ L, ∀ q ∈ L, p ≠ q → vLt x (i + 1) p q ∨ vLt x (i + 1) q p)
    (hR_right : ∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ R, vLt x i a b → vLt x i b c → 0 < orient a b c)
    (hL_left : ∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ L, vLt x (i + 1) a b → vLt x (i + 1) b c → orient a b c < 0) :
    ConvexIndep ((R ∪ L : Finset ℝ²) : Set ℝ²) := by
  have hdisj : Disjoint R L := by
    rw [Finset.disjoint_left]
    intro p hpR hpL
    exact inSpike_disjoint (by omega) (fin_ne_add_one (by omega) i) (hR_spike p hpR) (hL_spike p hpL)
  apply convexIndep_of_forall_triple hnt
  intro a b c d ha hb hc hd hda hdb hdc hab hbc hac
  have hnt4 : NonTrilinear ({a, b, c, d} : Set ℝ²) :=
    Set.Triplewise.mono (by intro z hz; simp at hz; rcases hz with rfl | rfl | rfl | rfl <;> assumption) hnt
  have hR_conv : ConvexIndep (R : Set ℝ²) := by
    apply convexIndep_of_monotone_orient_pos (Set.Triplewise.mono (by simp) hnt)
      (raySlope (x (i - 1)) (x (i + 2)))
    · intro p hp q hq heq
      by_contra hne
      rcases hR_chain p hp q hq hne with h | h
      · have hlt := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hR_spike p hp))
          (inSpike_base_gt hk (hR_spike q hq))).mp h.2
        linarith
      · have hlt := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hR_spike q hq))
          (inSpike_base_gt hk (hR_spike p hp))).mp h.2
        linarith
    · intro p hp q hq r hr hpq hqr
      have hpq' : vLt x i p q := by
        have hne : p ≠ q := fun h => by rw [h] at hpq; exact lt_irrefl _ hpq
        rcases hR_chain p hp q hq hne with h | h
        · exact h
        · have := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hR_spike q hq))
            (inSpike_base_gt hk (hR_spike p hp))).mp h.2
          linarith
      have hqr' : vLt x i q r := by
        have hne : q ≠ r := fun h => by rw [h] at hqr; exact lt_irrefl _ hqr
        rcases hR_chain q hq r hr hne with h | h
        · exact h
        · have := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hR_spike r hr))
            (inSpike_base_gt hk (hR_spike q hq))).mp h.2
          linarith
      exact hR_right p hp q hq r hr hpq' hqr'
  have hL_conv : ConvexIndep (L : Set ℝ²) := by
    apply convexIndep_of_monotone_orient_neg (Set.Triplewise.mono (by simp) hnt)
      (raySlope (x ((i + 1) - 1)) (x ((i + 1) + 2)))
    · intro p hp q hq heq
      by_contra hne
      rcases hL_chain p hp q hq hne with h | h
      · have hlt := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hL_spike p hp))
          (inSpike_base_gt hk (hL_spike q hq))).mp h.2
        linarith
      · have hlt := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hL_spike q hq))
          (inSpike_base_gt hk (hL_spike p hp))).mp h.2
        linarith
    · intro p hp q hq r hr hpq hqr
      have hpq' : vLt x (i + 1) p q := by
        have hne : p ≠ q := fun h => by rw [h] at hpq; exact lt_irrefl _ hpq
        rcases hL_chain p hp q hq hne with h | h
        · exact h
        · have := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hL_spike q hq))
            (inSpike_base_gt hk (hL_spike p hp))).mp h.2
          linarith
      have hqr' : vLt x (i + 1) q r := by
        have hne : q ≠ r := fun h => by rw [h] at hqr; exact lt_irrefl _ hqr
        rcases hL_chain q hq r hr hne with h | h
        · exact h
        · have := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hL_spike r hr))
            (inSpike_base_gt hk (hL_spike q hq))).mp h.2
          linarith
      exact hL_left p hp q hq r hr hpq' hqr'
  have hsepRL : ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∀ w₁ ∈ L, ∀ w₂ ∈ L, 0 < orient u v w₁ * orient u v w₂ := by
    intro u hu v hv huv w₁ hw₁ w₂ hw₂
    rcases hR_chain u hu v hv huv with h | h
    · have h1 := vertical_sep_next hk hx (hR_spike u hu) (hR_spike v hv) h (hL_spike w₁ hw₁)
      have h2 := vertical_sep_next hk hx (hR_spike u hu) (hR_spike v hv) h (hL_spike w₂ hw₂)
      nlinarith
    · have h1 := vertical_sep_next hk hx (hR_spike v hv) (hR_spike u hu) h (hL_spike w₁ hw₁)
      have h2 := vertical_sep_next hk hx (hR_spike v hv) (hR_spike u hu) h (hL_spike w₂ hw₂)
      have e1 : orient u v w₁ = -orient v u w₁ := by simp only [orient]; ring
      have e2 : orient u v w₂ = -orient v u w₂ := by simp only [orient]; ring
      rw [e1, e2]; nlinarith
  have hsepLR : ∀ u ∈ L, ∀ v ∈ L, u ≠ v → ∀ w₁ ∈ R, ∀ w₂ ∈ R, 0 < orient u v w₁ * orient u v w₂ := by
    intro u hu v hv huv w₁ hw₁ w₂ hw₂
    have hR' : ∀ w ∈ R, inSpike x ((i + 1) - 1) w := by simpa [add_sub_cancel_right] using hR_spike
    rcases hL_chain u hu v hv huv with h | h
    · have h1 := vertical_sep_prev hk hx (hL_spike u hu) (hL_spike v hv) h (hR' w₁ hw₁)
      have h2 := vertical_sep_prev hk hx (hL_spike u hu) (hL_spike v hv) h (hR' w₂ hw₂)
      nlinarith
    · have h1 := vertical_sep_prev hk hx (hL_spike v hv) (hL_spike u hu) h (hR' w₁ hw₁)
      have h2 := vertical_sep_prev hk hx (hL_spike v hv) (hL_spike u hu) h (hR' w₂ hw₂)
      have e1 : orient u v w₁ = -orient v u w₁ := by simp only [orient]; ring
      have e2 : orient u v w₂ = -orient v u w₂ := by simp only [orient]; ring
      rw [e1, e2]; nlinarith
  have h3R1L : ∀ u v w : ℝ², u ∈ R → v ∈ R → w ∈ R → ∀ z ∈ L,
      u ≠ v → v ≠ w → u ≠ w → u ≠ z → v ≠ z → w ≠ z →
      NonTrilinear ({u, v, w, z} : Set ℝ²) → u ∉ convexHull ℝ ({v, w, z} : Set ℝ²) :=
    fun u v w hu hv hw z hz huv hvw huw huz hvz hwz hnt' =>
      not_mem_conv_three_chain (s := (1 : ℝ)) hu hv hw huv huw huz hvw hvz hwz hnt' hR_chain
        (fun p hp q hq r hr hpq hqr => by simpa using hR_right p hp q hq r hr hpq hqr)
        (fun p hp q hq hpq => by simpa using vertical_sep_next hk hx (hR_spike p hp) (hR_spike q hq) hpq (hL_spike z hz))
  have h3L1R : ∀ u v w : ℝ², u ∈ L → v ∈ L → w ∈ L → ∀ z ∈ R,
      u ≠ v → v ≠ w → u ≠ w → u ≠ z → v ≠ z → w ≠ z →
      NonTrilinear ({u, v, w, z} : Set ℝ²) → u ∉ convexHull ℝ ({v, w, z} : Set ℝ²) := by
    intro u v w hu hv hw z hz huv hvw huw huz hvz hwz hnt'
    have hz' : inSpike x ((i + 1) - 1) z := by simpa [add_sub_cancel_right] using hR_spike z hz
    exact not_mem_conv_three_chain (s := (-1 : ℝ)) hu hv hw huv huw huz hvw hvz hwz hnt' hL_chain
      (fun p hp q hq r hr hpq hqr => by have := hL_left p hp q hq r hr hpq hqr; linarith)
      (fun p hp q hq hpq => by have := vertical_sep_prev hk hx (hL_spike p hp) (hL_spike q hq) hpq hz'; linarith)
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha hb hc hd
  have hne_i : i ≠ i + 1 := fin_ne_add_one (by omega) i
  rcases hd with hdR | hdL
  · rcases ha with haR | haL <;> rcases hb with hbR | hbL <;> rcases hc with hcR | hcL
    · exact fun hm => hR_conv d hdR (convexHull_mono (by
        intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact ⟨haR, hda.symm⟩
        · exact ⟨hbR, hdb.symm⟩
        · exact ⟨hcR, hdc.symm⟩) hm)
    · exact h3R1L d a b hdR haR hbR c hcL hda hab hdb hdc hac hbc
        (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4)
    · rw [show ({a, b, c} : Set ℝ²) = {a, c, b} by ext z; simp; tauto]
      exact h3R1L d a c hdR haR hcR b hbL hda hac hdc hdb hab hbc.symm
        (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4)
    · exact not_mem_convexHull_triple_of_same_side hnt4 hda hdb hdc hab hbc hac
        (hsepRL a haR d hdR hda.symm b hbL c hcL)
    · rw [show ({a, b, c} : Set ℝ²) = {b, c, a} by ext z; simp; tauto]
      exact h3R1L d b c hdR hbR hcR a haL hdb hbc hdc hda hab.symm hac.symm
        (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4)
    · rw [show ({a, b, c} : Set ℝ²) = {b, a, c} by ext z; simp; tauto]
      exact not_mem_convexHull_triple_of_same_side
        (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4)
        hdb hda hdc hab.symm hac hbc
        (hsepRL b hbR d hdR hdb.symm a haL c hcL)
    · rw [show ({a, b, c} : Set ℝ²) = {c, a, b} by ext z; simp; tauto]
      exact not_mem_convexHull_triple_of_same_side
        (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4)
        hdc hda hdb hac.symm hab hbc.symm
        (hsepRL c hcR d hdR hdc.symm a haL b hbL)
    · apply not_mem_convexHull_of_orient_lt (inSpike_edge_lt (by omega) (hR_spike d hdR))
      intro q hq; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl <;>
        exact (inSpike_other_edge_gt (by omega) hne_i (hL_spike _ ‹_›)).le
  · rcases ha with haR | haL <;> rcases hb with hbR | hbL <;> rcases hc with hcR | hcL
    · apply not_mem_convexHull_of_orient_lt (inSpike_edge_lt (by omega) (hL_spike d hdL))
      intro q hq; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl <;>
        exact (inSpike_other_edge_gt (by omega) hne_i.symm (hR_spike _ ‹_›)).le
    · rw [show ({a, b, c} : Set ℝ²) = {c, a, b} by ext z; simp; tauto]
      exact not_mem_convexHull_triple_of_same_side
        (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4)
        hdc hda hdb hac.symm hab hbc.symm
        (hsepLR c hcL d hdL hdc.symm a haR b hbR)
    · rw [show ({a, b, c} : Set ℝ²) = {b, a, c} by ext z; simp; tauto]
      exact not_mem_convexHull_triple_of_same_side
        (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4)
        hdb hda hdc hab.symm hac hbc
        (hsepLR b hbL d hdL hdb.symm a haR c hcR)
    · rw [show ({a, b, c} : Set ℝ²) = {b, c, a} by ext z; simp; tauto]
      exact h3L1R d b c hdL hbL hcL a haR hdb hbc hdc hda hab.symm hac.symm
        (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4)
    · exact not_mem_convexHull_triple_of_same_side hnt4 hda hdb hdc hab hbc hac
        (hsepLR a haL d hdL hda.symm b hbR c hcR)
    · rw [show ({a, b, c} : Set ℝ²) = {a, c, b} by ext z; simp; tauto]
      exact h3L1R d a c hdL haL hcL b hbR hda hac hdc hdb hab hbc.symm
        (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4)
    · exact h3L1R d a b hdL haL hbL c hcR hda hab hdb hdc hac hbc
        (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4)
    · exact fun hm => hL_conv d hdL (convexHull_mono (by
        intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact ⟨haL, hda.symm⟩
        · exact ⟨hbL, hdb.symm⟩
        · exact ⟨hcL, hdc.symm⟩) hm)

/-- HMPT Observation 3.7: for even `k ≥ 4`, joining inner convex chains `A i ⊆ P_i`
over indices of the same parity (`i.val % 2 = r`) yields a `ConvexIndep` set. -/
lemma joining_horizontals {k : ℕ} [NeZero k] (hk : 4 ≤ k) (heven : k % 2 = 0)
    {x : Fin k → ℝ²} (hx : IsCcw x) (r : ℕ) (A : Fin k → Finset ℝ²)
    (I : Finset (Fin k)) (hI : ∀ i ∈ I, i.val % 2 = r)
    (hnt : NonTrilinear ((I.biUnion A : Finset ℝ²) : Set ℝ²))
    (hA_spike : ∀ i ∈ I, ∀ p ∈ A i, inSpike x i p)
    (hA_chain : ∀ i ∈ I, ∀ p ∈ A i, ∀ q ∈ A i, p ≠ q → hLt x i p q ∨ hLt x i q p)
    (hA_inner : ∀ i ∈ I, ∀ a ∈ A i, ∀ b ∈ A i, ∀ c ∈ A i, hLt x i a b → hLt x i b c → orient a b c < 0) :
    ConvexIndep ((I.biUnion A : Finset ℝ²) : Set ℝ²) := by
  have hfar : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → j ≠ i - 1 ∧ j ≠ i ∧ j ≠ i + 1 := by
    intro i hi j hj hij
    refine ⟨?_, hij.symm, ?_⟩
    · intro h
      have h1 : (1 : Fin k).val = 1 := fin_val_one_of_ge (by omega)
      have hval := congrArg Fin.val h
      simp only [Fin.val_sub, h1] at hval
      have hi' := hI i hi; have hj' := hI j hj; have hi_lt := i.isLt
      by_cases h0 : i.val = 0
      · rw [h0, add_zero, Nat.mod_eq_of_lt (by omega)] at hval; omega
      · rw [show k - 1 + i.val = k + (i.val - 1) by omega, Nat.add_mod_left,
            Nat.mod_eq_of_lt (by omega)] at hval; omega
    · intro h
      have h1 : (1 : Fin k).val = 1 := fin_val_one_of_ge (by omega)
      have hval := congrArg Fin.val h
      simp only [Fin.val_add, h1] at hval
      have hi' := hI i hi; have hj' := hI j hj; have hi_lt := i.isLt
      by_cases hlast : i.val + 1 = k
      · rw [hlast, Nat.mod_self] at hval; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at hval; omega
  have hA_conv : ∀ i ∈ I, ConvexIndep (A i : Set ℝ²) := by
    intro i hi
    have hsub : (A i : Set ℝ²) ⊆ ((I.biUnion A : Finset ℝ²) : Set ℝ²) := by
      intro p hp; exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨i, hi, hp⟩)
    apply convexIndep_of_monotone_orient_neg (Set.Triplewise.mono hsub hnt)
      (raySlope (x (i - 1)) (x (i + 2)))
    · intro p hp q hq heq
      by_contra hne
      rcases hA_chain i hi p hp q hq hne with h | h
      · have hlt := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hA_spike i hi p hp))
          (inSpike_base_gt hk (hA_spike i hi q hq))).mp h.2
        linarith
      · have hlt := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hA_spike i hi q hq))
          (inSpike_base_gt hk (hA_spike i hi p hp))).mp h.2
        linarith
    · intro p hp q hq r hr hpq hqr
      have hpq' : hLt x i p q := by
        have hne : p ≠ q := fun h => by rw [h] at hpq; exact lt_irrefl _ hpq
        rcases hA_chain i hi p hp q hq hne with h | h
        · exact h
        · have := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hA_spike i hi q hq))
            (inSpike_base_gt hk (hA_spike i hi p hp))).mp h.2
          linarith
      have hqr' : hLt x i q r := by
        have hne : q ≠ r := fun h => by rw [h] at hqr; exact lt_irrefl _ hqr
        rcases hA_chain i hi q hq r hr hne with h | h
        · exact h
        · have := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hA_spike i hi r hr))
            (inSpike_base_gt hk (hA_spike i hi q hq))).mp h.2
          linarith
      exact hA_inner i hi p hp q hq r hr hpq' hqr'
  have hsep : ∀ i ∈ I, ∀ u ∈ A i, ∀ v ∈ A i, hLt x i u v →
      ∀ j ∈ I, j ≠ i → ∀ z ∈ A j, orient u v z < 0 := by
    intro i hi u hu v _ huv j hj hji z hz
    obtain ⟨h1, h2, h3⟩ := hfar i hi j hj hji.symm
    exact horizontal_sep hk hx h1 h2 h3 (hA_spike i hi u hu) huv (hA_spike j hj z hz)
  have hsep2 : ∀ i ∈ I, ∀ u ∈ A i, ∀ v ∈ A i, u ≠ v →
      ∀ j₁ ∈ I, j₁ ≠ i → ∀ w₁ ∈ A j₁, ∀ j₂ ∈ I, j₂ ≠ i → ∀ w₂ ∈ A j₂,
      0 < orient u v w₁ * orient u v w₂ := by
    intro i hi u hu v hv huv j₁ hj₁ hji₁ w₁ hw₁ j₂ hj₂ hji₂ w₂ hw₂
    rcases hA_chain i hi u hu v hv huv with h | h
    · have h1 := hsep i hi u hu v hv h j₁ hj₁ hji₁ w₁ hw₁
      have h2 := hsep i hi u hu v hv h j₂ hj₂ hji₂ w₂ hw₂
      nlinarith
    · have h1 := hsep i hi v hv u hu h j₁ hj₁ hji₁ w₁ hw₁
      have h2 := hsep i hi v hv u hu h j₂ hj₂ hji₂ w₂ hw₂
      have e1 : orient u v w₁ = -orient v u w₁ := by simp only [orient]; ring
      have e2 : orient u v w₂ = -orient v u w₂ := by simp only [orient]; ring
      rw [e1, e2]; nlinarith
  have h3in1 : ∀ i ∈ I, ∀ u v w : ℝ², u ∈ A i → v ∈ A i → w ∈ A i →
      ∀ j ∈ I, j ≠ i → ∀ z ∈ A j,
      u ≠ v → v ≠ w → u ≠ w → u ≠ z → v ≠ z → w ≠ z →
      NonTrilinear ({u, v, w, z} : Set ℝ²) → u ∉ convexHull ℝ ({v, w, z} : Set ℝ²) :=
    fun i hi u v w hu hv hw j hj hji z hz huv hvw huw huz hvz hwz hnt' =>
      not_mem_conv_three_chain (s := (-1 : ℝ)) hu hv hw huv huw huz hvw hvz hwz hnt' (hA_chain i hi)
        (fun p hp q hq r hr hpq hqr => by have := hA_inner i hi p hp q hq r hr hpq hqr; linarith)
        (fun p hp q hq hpq => by have := hsep i hi p hp q hq hpq j hj hji z hz; linarith)
  apply convexIndep_of_forall_triple hnt
  intro a b c d ha hb hc hd hda hdb hdc hab hbc hac
  have hnt4 : NonTrilinear ({a, b, c, d} : Set ℝ²) :=
    Set.Triplewise.mono (by intro z hz; simp at hz; rcases hz with rfl | rfl | rfl | rfl <;> assumption) hnt
  obtain ⟨ia, hia, haA⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp ha)
  obtain ⟨ib, hib, hbA⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hb)
  obtain ⟨ic, hic, hcA⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hc)
  obtain ⟨id_, hid, hdA⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hd)
  by_cases hda_eq : ia = id_
  · rw [hda_eq] at haA
    by_cases hdb_eq : ib = id_
    · rw [hdb_eq] at hbA
      by_cases hdc_eq : ic = id_
      · rw [hdc_eq] at hcA
        exact fun hm => hA_conv id_ hid d hdA (convexHull_mono (by
          intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl
          · exact ⟨haA, hda.symm⟩
          · exact ⟨hbA, hdb.symm⟩
          · exact ⟨hcA, hdc.symm⟩) hm)
      · exact h3in1 id_ hid d a b hdA haA hbA ic hic hdc_eq c hcA hda hab hdb hdc hac hbc
          (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4)
    · by_cases hdc_eq : ic = id_
      · rw [hdc_eq] at hcA
        rw [show ({a, b, c} : Set ℝ²) = {a, c, b} by ext z; simp; tauto]
        exact h3in1 id_ hid d a c hdA haA hcA ib hib hdb_eq b hbA hda hac hdc hdb hab hbc.symm
          (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4)
      · exact not_mem_convexHull_triple_of_same_side hnt4 hda hdb hdc hab hbc hac
          (hsep2 id_ hid a haA d hdA hda.symm ib hib hdb_eq b hbA ic hic hdc_eq c hcA)
  · by_cases hdb_eq : ib = id_
    · rw [hdb_eq] at hbA
      by_cases hdc_eq : ic = id_
      · rw [hdc_eq] at hcA
        rw [show ({a, b, c} : Set ℝ²) = {b, c, a} by ext z; simp; tauto]
        exact h3in1 id_ hid d b c hdA hbA hcA ia hia hda_eq a haA hdb hbc hdc hda hab.symm hac.symm
          (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4)
      · rw [show ({a, b, c} : Set ℝ²) = {b, a, c} by ext z; simp; tauto]
        exact not_mem_convexHull_triple_of_same_side
          (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4) hdb hda hdc hab.symm hac hbc
          (hsep2 id_ hid b hbA d hdA hdb.symm ia hia hda_eq a haA ic hic hdc_eq c hcA)
    · by_cases hdc_eq : ic = id_
      · rw [hdc_eq] at hcA
        rw [show ({a, b, c} : Set ℝ²) = {c, a, b} by ext z; simp; tauto]
        exact not_mem_convexHull_triple_of_same_side
          (Set.Triplewise.mono (by intro z hz; simp at hz ⊢; tauto) hnt4) hdc hda hdb hac.symm hab hbc.symm
          (hsep2 id_ hid c hcA d hdA hdc.symm ia hia hda_eq a haA ib hib hdb_eq b hbA)
      · apply not_mem_convexHull_of_orient_lt (inSpike_edge_lt (by omega) (hA_spike id_ hid d hdA))
        intro q hq; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl | rfl
        · exact (inSpike_other_edge_gt (by omega) (Ne.symm hda_eq) (hA_spike ia hia q haA)).le
        · exact (inSpike_other_edge_gt (by omega) (Ne.symm hdb_eq) (hA_spike ib hib q hbA)).le
        · exact (inSpike_other_edge_gt (by omega) (Ne.symm hdc_eq) (hA_spike ic hic q hcA)).le

/- ### Section 7: HMPT Main Bound (`ES(n) ≤ 2 ^ (n + O(√(n log n)))`) -/

/-- Core HMPT bound for a single even `k ≥ 4`: if `P` has no convex `n`-gon (`n ≥ 4`),
then `(P.card : ℝ) ^ k ≤ 2 ^ (8 * k ^ 2 + k * n) * (2 * n) ^ (2 * n)`. -/
theorem hmpt_power_bound {n k : ℕ} [NeZero k] (hn : 4 ≤ n) (hk : 4 ≤ k) (heven : k % 2 = 0)
    {P : Finset ℝ²} (hnt : NonTrilinear (P : Set ℝ²)) (hno : ¬ HasConvexNGon n (P : Set ℝ²))
    (hN : 2 ^ (4 * k) ≤ P.card) :
    (P.card : ℝ) ^ k ≤ (2 : ℝ) ^ (8 * k ^ 2 + k * n) * ((2 * n : ℕ) : ℝ) ^ (2 * n) := by
  obtain ⟨x, hx_ccw, hx_mem, hx_inj, hcluster⟩ := convex_clustering (by omega) hnt hN
  let Pi : Fin k → Finset ℝ² := fun i => P.filter (inSpike x i)
  -- For each i, define max vertical chain length v i, max horizontal chain length h i,
  -- and within a longest vertical/horizontal chain define max left/right (a i, b i)
  -- and max inner/outer (c i, d i) chain lengths!
  have hPi_sub : ∀ i, Pi i ⊆ P := fun i => Finset.filter_subset _ _
  have hPi_spike : ∀ i, ∀ p ∈ Pi i, inSpike x i p := fun i p hp => (Finset.mem_filter.mp hp).2
  -- Step 1: For each i, find a vertical chain Cv i and horizontal chain Ch i such that
  -- |Pi i| ≤ (Cv i).card * (Ch i).card (and every vertical/horizontal chain has size ≤ |Cv i|, |Ch i|)
  have hchains : ∀ i : Fin k,
      ∃ (Cv Ch : Finset ℝ²),
        Cv ⊆ Pi i ∧ Ch ⊆ Pi i ∧
        (∀ p ∈ Cv, ∀ q ∈ Cv, p ≠ q → vLt x i p q ∨ vLt x i q p) ∧
        (∀ p ∈ Ch, ∀ q ∈ Ch, p ≠ q → hLt x i p q ∨ hLt x i q p) ∧
        (Pi i).card ≤ Cv.card * Ch.card := by
    intro i
    let f : ℝ² → ℝ := raySlope (x (i + 2)) (x (i - 1))
    let g : ℝ² → ℝ := raySlope (x (i - 1)) (x (i + 2))
    have hPi_nt : NonTrilinear ((Pi i : Finset ℝ²) : Set ℝ²) := Set.Triplewise.mono (hPi_sub i) hnt
    have hA_not : ∀ p ∈ Pi i, x (i + 2) ≠ p := by
      intro p hp heq
      have h := inSpike_base_gt hk (hPi_spike i p hp)
      rw [← heq, orient_self₁₃] at h; linarith
    have hB_not : ∀ p ∈ Pi i, x (i - 1) ≠ p := by
      intro p hp heq
      have h := inSpike_base_gt hk (hPi_spike i p hp)
      rw [← heq, orient_self₂₃] at h; linarith
    have hf_inj : Set.InjOn f (Pi i : Set ℝ²) := by
      intro p hp q hq heq
      by_contra hne
      have hne0 := orient_ne_zero_of_not_collinear
        (hnt (hx_mem (i + 2)) (hPi_sub i hp) (hPi_sub i hq) (hA_not p hp) hne (hA_not q hq))
      rcases lt_or_gt_of_ne hne0 with hlt | hgt
      · have := (orient_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i p hp))
          (inSpike_base_gt hk (hPi_spike i q hq))).mp hlt
        linarith
      · have hlt : orient (x (i + 2)) q p < 0 := by rw [orient_swap₂₃]; linarith
        have := (orient_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i q hq))
          (inSpike_base_gt hk (hPi_spike i p hp))).mp hlt
        linarith
    have hg_inj : Set.InjOn g (Pi i : Set ℝ²) := by
      intro p hp q hq heq
      by_contra hne
      have hne0 := orient_ne_zero_of_not_collinear
        (hnt (hx_mem (i - 1)) (hPi_sub i hp) (hPi_sub i hq) (hB_not p hp) hne (hB_not q hq))
      rcases lt_or_gt_of_ne hne0 with hlt | hgt
      · have := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i p hp))
          (inSpike_base_gt hk (hPi_spike i q hq))).mp hlt
        linarith
      · have hlt : orient (x (i - 1)) q p < 0 := by rw [orient_swap₂₃]; linarith
        have := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i q hq))
          (inSpike_base_gt hk (hPi_spike i p hp))).mp hlt
        linarith
    let P_V : Finset ℝ² → Prop := fun C => ∀ a ∈ C, ∀ b ∈ C, g a < g b → f b < f a
    let P_H : Finset ℝ² → Prop := fun C => ∀ a ∈ C, ∀ b ∈ C, g a < g b → f a < f b
    let Vfam := (Pi i).powerset.filter P_V
    let Hfam := (Pi i).powerset.filter P_H
    have hVne : Vfam.Nonempty := ⟨∅, by simp [Vfam, P_V]⟩
    have hHne : Hfam.Nonempty := ⟨∅, by simp [Hfam, P_H]⟩
    obtain ⟨Cv, hCvF, hCvmax⟩ := Finset.exists_max_image Vfam Finset.card hVne
    obtain ⟨Ch, hChF, hChmax⟩ := Finset.exists_max_image Hfam Finset.card hHne
    obtain ⟨hCvSub, hCvOrd⟩ := Finset.mem_filter.mp hCvF
    obtain ⟨hChSub, hChOrd⟩ := Finset.mem_filter.mp hChF
    have hCvSub' : Cv ⊆ Pi i := Finset.mem_powerset.mp hCvSub
    have hChSub' : Ch ⊆ Pi i := Finset.mem_powerset.mp hChSub
    refine ⟨Cv, Ch, hCvSub', hChSub', ?_, ?_, ?_⟩
    · intro p hp q hq hne
      rcases lt_or_gt_of_ne (fun h => hne (hg_inj (hCvSub' hp) (hCvSub' hq) h)) with hgpq | hgqp
      · left
        have hfqp := hCvOrd p hp q hq hgpq
        have h1 : orient (x (i + 2)) q p < 0 :=
          (orient_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i q (hCvSub' hq)))
            (inSpike_base_gt hk (hPi_spike i p (hCvSub' hp)))).mpr hfqp
        have h2 : orient (x (i - 1)) p q < 0 :=
          (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i p (hCvSub' hp)))
            (inSpike_base_gt hk (hPi_spike i q (hCvSub' hq)))).mpr hgpq
        exact ⟨by rw [orient_swap₂₃] at h1; linarith, h2⟩
      · right
        have hfpq := hCvOrd q hq p hp hgqp
        have h1 : orient (x (i + 2)) p q < 0 :=
          (orient_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i p (hCvSub' hp)))
            (inSpike_base_gt hk (hPi_spike i q (hCvSub' hq)))).mpr hfpq
        have h2 : orient (x (i - 1)) q p < 0 :=
          (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i q (hCvSub' hq)))
            (inSpike_base_gt hk (hPi_spike i p (hCvSub' hp)))).mpr hgqp
        exact ⟨by rw [orient_swap₂₃] at h1; linarith, h2⟩
    · intro p hp q hq hne
      rcases lt_or_gt_of_ne (fun h => hne (hg_inj (hChSub' hp) (hChSub' hq) h)) with hgpq | hgqp
      · left
        have hfpq := hChOrd p hp q hq hgpq
        have h1 : orient (x (i + 2)) p q < 0 :=
          (orient_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i p (hChSub' hp)))
            (inSpike_base_gt hk (hPi_spike i q (hChSub' hq)))).mpr hfpq
        have h2 : orient (x (i - 1)) p q < 0 :=
          (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i p (hChSub' hp)))
            (inSpike_base_gt hk (hPi_spike i q (hChSub' hq)))).mpr hgpq
        exact ⟨h1, h2⟩
      · right
        have hfqp := hChOrd q hq p hp hgqp
        have h1 : orient (x (i + 2)) q p < 0 :=
          (orient_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i q (hChSub' hq)))
            (inSpike_base_gt hk (hPi_spike i p (hChSub' hp)))).mpr hfqp
        have h2 : orient (x (i - 1)) q p < 0 :=
          (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i q (hChSub' hq)))
            (inSpike_base_gt hk (hPi_spike i p (hChSub' hp)))).mpr hgqp
        exact ⟨h1, h2⟩
    · exact dilworth_two_functions (Pi i) f g hf_inj hg_inj Cv.card Ch.card
        (fun C hC hord => hCvmax C (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hC, hord⟩))
        (fun C hC hord => hChmax C (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hC, hord⟩))
  choose Cv Ch hCvSub hChSub hCvChain hChChain hDil using hchains
  -- Step 2: Apply transitive_cup_cap to Cv i (left/right) and Ch i (inner/outer)!
  -- Define a_i = max |L| (left convex chain in Cv i, orient < 0), b_i = max |R| (right convex chain in Cv i, orient > 0)
  -- Define c_i = max |I| (inner convex chain in Ch i, orient < 0), d_i = max |O| (outer convex chain in Ch i, orient > 0)
  -- Helper: given a chain C ⊆ Pi i ordered by g(p) = raySlope (x (i-1)) (x (i+2)) p,
  -- get max neg-triple subset L ⊆ C and max pos-triple subset R ⊆ C with
  -- C.card ≤ Nat.choose (max 2 (L.card + 1) + max 2 (R.card + 1) - 4) (max 2 (L.card + 1) - 2)!
  have hchain_split : ∀ (i : Fin k) (C : Finset ℝ²), C ⊆ Pi i →
      (∀ p ∈ C, ∀ q ∈ C, p ≠ q → orient (x (i - 1)) p q < 0 ∨ orient (x (i - 1)) q p < 0) →
      ∃ (A B : Finset ℝ²), A ⊆ C ∧ B ⊆ C ∧
        (∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, orient (x (i - 1)) p q < 0 → orient (x (i - 1)) q r < 0 → orient p q r < 0) ∧
        (∀ p ∈ B, ∀ q ∈ B, ∀ r ∈ B, orient (x (i - 1)) p q < 0 → orient (x (i - 1)) q r < 0 → 0 < orient p q r) ∧
        C.card ≤ Nat.choose (A.card + B.card) A.card := by
    intro i C hCPi hCtot
    let g : ℝ² → ℝ := raySlope (x (i - 1)) (x (i + 2))
    have hgt_iff : ∀ p ∈ C, ∀ q ∈ C, orient (x (i - 1)) p q < 0 ↔ g p < g q := fun p hp q hq =>
      orient_B_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i p (hCPi hp)))
        (inSpike_base_gt hk (hPi_spike i q (hCPi hq)))
    have hg_inj : Set.InjOn g (C : Set ℝ²) := by
      intro p hp q hq heq
      by_contra hne
      rcases hCtot p hp q hq hne with h | h
      · have := (hgt_iff p hp q hq).mp h; linarith
      · have := (hgt_iff q hq p hp).mp h; linarith
    let P_A : Finset ℝ² → Prop := fun A =>
      ∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, orient (x (i - 1)) p q < 0 → orient (x (i - 1)) q r < 0 → orient p q r < 0
    let P_B : Finset ℝ² → Prop := fun B =>
      ∀ p ∈ B, ∀ q ∈ B, ∀ r ∈ B, orient (x (i - 1)) p q < 0 → orient (x (i - 1)) q r < 0 → 0 < orient p q r
    let Afam := C.powerset.filter P_A
    let Bfam := C.powerset.filter P_B
    obtain ⟨A, hAF, hAmax⟩ := Finset.exists_max_image Afam Finset.card ⟨∅, by simp [Afam, P_A]⟩
    obtain ⟨B, hBF, hBmax⟩ := Finset.exists_max_image Bfam Finset.card ⟨∅, by simp [Bfam, P_B]⟩
    obtain ⟨hAC, hAord⟩ := Finset.mem_filter.mp hAF
    obtain ⟨hBC, hBord⟩ := Finset.mem_filter.mp hBF
    refine ⟨A, B, Finset.mem_powerset.mp hAC, Finset.mem_powerset.mp hBC, hAord, hBord, ?_⟩
    -- If C.card ≤ 1, then C.card ≤ 1 ≤ choose (A.card + B.card) A.card!
    by_cases hC1 : C.card ≤ 1
    · exact hC1.trans (Nat.choose_pos (Nat.le_add_right _ _))
    -- Otherwise C.card ≥ 2, so A.card ≥ 2 and B.card ≥ 2 (any 2-subset vacuously satisfies both!)
    have hA2 : 2 ≤ A.card := by
      obtain ⟨U, hUC, hU2⟩ := Finset.exists_subset_card_eq (show 2 ≤ C.card by omega)
      have hUmem : U ∈ Afam := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hUC, fun p hp q hq r hr hpq hqr => ?_⟩
        exfalso
        have hpq' : g p < g q := (hgt_iff p (hUC hp) q (hUC hq)).mp hpq
        have hqr' : g q < g r := (hgt_iff q (hUC hq) r (hUC hr)).mp hqr
        have hne1 : p ≠ q := fun h => by rw [h] at hpq'; exact lt_irrefl _ hpq'
        have hne2 : q ≠ r := fun h => by rw [h] at hqr'; exact lt_irrefl _ hqr'
        have hne3 : p ≠ r := fun h => by rw [h] at hpq'; linarith
        have h3 : ({p, q, r} : Finset ℝ²).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair hne2]; simp [hne1, hne3]
        have hsub : ({p, q, r} : Finset ℝ²) ⊆ U := by
          intro z hz; simp at hz; rcases hz with rfl | rfl | rfl <;> assumption
        have := Finset.card_le_card hsub; omega
      have := hAmax U hUmem; omega
    have hB2 : 2 ≤ B.card := by
      obtain ⟨U, hUC, hU2⟩ := Finset.exists_subset_card_eq (show 2 ≤ C.card by omega)
      have hUmem : U ∈ Bfam := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hUC, fun p hp q hq r hr hpq hqr => ?_⟩
        exfalso
        have hpq' : g p < g q := (hgt_iff p (hUC hp) q (hUC hq)).mp hpq
        have hqr' : g q < g r := (hgt_iff q (hUC hq) r (hUC hr)).mp hqr
        have hne1 : p ≠ q := fun h => by rw [h] at hpq'; exact lt_irrefl _ hpq'
        have hne2 : q ≠ r := fun h => by rw [h] at hqr'; exact lt_irrefl _ hqr'
        have hne3 : p ≠ r := fun h => by rw [h] at hpq'; linarith
        have h3 : ({p, q, r} : Finset ℝ²).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_pair hne2]; simp [hne1, hne3]
        have hsub : ({p, q, r} : Finset ℝ²) ⊆ U := by
          intro z hz; simp at hz; rcases hz with rfl | rfl | rfl <;> assumption
        have := Finset.card_le_card hsub; omega
      have := hBmax U hUmem; omega
    -- Apply transitive_cup_cap to S = C.image g with a = A.card + 1, b = B.card + 1!
    -- Wait: choose ((A.card + 1) + (B.card + 1) - 4) ((A.card + 1) - 2) = choose (A.card + B.card - 2) (A.card - 1) ≤ choose (A.card + B.card) A.card!
    by_contra! hbig
    have hch_le : Nat.choose ((A.card + 1) + (B.card + 1) - 4) ((A.card + 1) - 2) ≤
        Nat.choose (A.card + B.card) A.card := by
      have h1 : (A.card + 1) + (B.card + 1) - 4 = (A.card - 1) + (B.card - 1) := by omega
      have h2 : (A.card + 1) - 2 = A.card - 1 := by omega
      rw [h1, h2]
      calc Nat.choose ((A.card - 1) + (B.card - 1)) (A.card - 1)
          ≤ Nat.choose ((A.card - 1) + B.card) (A.card - 1) := Nat.choose_le_choose _ (by omega)
        _ ≤ Nat.choose (A.card + B.card) A.card := by
            set a' := A.card - 1
            have ha' : A.card = a' + 1 := by omega
            have hsum : A.card + B.card = (a' + B.card) + 1 := by omega
            rw [hsum, ha', Nat.choose_succ_succ]
            omega
    let S := C.image g
    have hScard : S.card = C.card := Finset.card_image_of_injOn hg_inj
    have hTcard : Nat.choose ((A.card + 1) + (B.card + 1) - 4) ((A.card + 1) - 2) < (Finset.univ : Finset {t // t ∈ S}).card := by
      rw [Finset.card_univ, Fintype.card_coe, hScard]; omega
    -- Pullback function from {t // t ∈ S} to C
    have hpull : ∀ t : {t // t ∈ S}, ∃ p ∈ C, g p = t.val := fun t => Finset.mem_image.mp t.property
    choose pt hptC hptg using hpull
    have hpt_inj : Function.Injective pt := fun t₁ t₂ h => Subtype.ext (by rw [← hptg t₁, ← hptg t₂, h])
    have hpt_B : ∀ ⦃t₁ t₂ : {t // t ∈ S}⦄, t₁ < t₂ → orient (x (i - 1)) (pt t₁) (pt t₂) < 0 := by
      intro t₁ t₂ hlt
      exact (hgt_iff (pt t₁) (hptC t₁) (pt t₂) (hptC t₂)).mpr (by rw [hptg t₁, hptg t₂]; exact hlt)
    let Col : {t // t ∈ S} → {t // t ∈ S} → {t // t ∈ S} → Prop :=
      fun u v w => orient (pt u) (pt v) (pt w) < 0
    have hT1 : ∀ ⦃u v w z : {t // t ∈ S}⦄, u < v → v < w → w < z → Col u v w → Col v w z → Col u v z ∧ Col u w z := by
      intro u v w z huv hvw hwz h1 h2
      exact orient_chain_transitive_neg (hpt_B huv) (hpt_B (huv.trans hvw)) (hpt_B hvw)
        (hpt_B (hvw.trans hwz)) (hpt_B hwz) h1 h2
    have hT2 : ∀ ⦃u v w z : {t // t ∈ S}⦄, u < v → v < w → w < z → ¬ Col u v w → ¬ Col v w z → ¬ Col u v z ∧ ¬ Col u w z := by
      intro u v w z huv hvw hwz h1 h2
      have hne : ∀ a b c : {t // t ∈ S}, a < b → b < c → orient (pt a) (pt b) (pt c) ≠ 0 := fun a b c hab hbc =>
        orient_ne_zero_of_not_collinear
          (hnt (hPi_sub i (hCPi (hptC a))) (hPi_sub i (hCPi (hptC b))) (hPi_sub i (hCPi (hptC c)))
            (hpt_inj.ne hab.ne) (hpt_inj.ne hbc.ne) (hpt_inj.ne (hab.trans hbc).ne))
      have h1' : 0 < orient (pt u) (pt v) (pt w) := lt_of_le_of_ne (le_of_not_gt h1) (hne u v w huv hvw).symm
      have h2' : 0 < orient (pt v) (pt w) (pt z) := lt_of_le_of_ne (le_of_not_gt h2) (hne v w z hvw hwz).symm
      have hres := orient_chain_transitive_pos (hpt_B huv) (hpt_B (huv.trans hvw)) (hpt_B hvw)
        (hpt_B (hvw.trans hwz)) (hpt_B hwz) h1' h2'
      exact ⟨not_lt.mpr hres.1.le, not_lt.mpr hres.2.le⟩
    rcases transitive_cup_cap Col hT1 hT2 ((A.card + 1) + (B.card + 1)) (A.card + 1) (B.card + 1)
        rfl (by omega) (by omega) Finset.univ hTcard with
      ⟨U, _, hUc, hUcol⟩ | ⟨V, _, hVc, hVcol⟩
    · let A' := U.image pt
      have hA'mem : A' ∈ Afam := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by
          intro p hp; obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hp; exact hptC u), ?_⟩
        intro p hp q hq r hr hpq hqr
        obtain ⟨u, huU, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨v, hvU, rfl⟩ := Finset.mem_image.mp hq
        obtain ⟨w, hwU, rfl⟩ := Finset.mem_image.mp hr
        have huv : u < v := by
          have := (hgt_iff _ (hptC u) _ (hptC v)).mp hpq
          rw [hptg u, hptg v] at this; exact this
        have hvw : v < w := by
          have := (hgt_iff _ (hptC v) _ (hptC w)).mp hqr
          rw [hptg v, hptg w] at this; exact this
        exact hUcol u huU v hvU w hwU huv hvw
      have hle := hAmax A' hA'mem
      rw [Finset.card_image_of_injective _ hpt_inj, hUc] at hle
      omega
    · let B' := V.image pt
      have hB'mem : B' ∈ Bfam := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by
          intro p hp; obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hp; exact hptC u), ?_⟩
        intro p hp q hq r hr hpq hqr
        obtain ⟨u, huV, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨v, hvV, rfl⟩ := Finset.mem_image.mp hq
        obtain ⟨w, hwV, rfl⟩ := Finset.mem_image.mp hr
        have huv : u < v := by
          have := (hgt_iff _ (hptC u) _ (hptC v)).mp hpq
          rw [hptg u, hptg v] at this; exact this
        have hvw : v < w := by
          have := (hgt_iff _ (hptC v) _ (hptC w)).mp hqr
          rw [hptg v, hptg w] at this; exact this
        have hnot := hVcol u huV v hvV w hwV huv hvw
        have hne := orient_ne_zero_of_not_collinear
          (hnt (hPi_sub i (hCPi (hptC u))) (hPi_sub i (hCPi (hptC v))) (hPi_sub i (hCPi (hptC w)))
            (hpt_inj.ne huv.ne) (hpt_inj.ne hvw.ne) (hpt_inj.ne (huv.trans hvw).ne))
        exact lt_of_le_of_ne (le_of_not_gt hnot) hne.symm
      have hle := hBmax B' hB'mem
      rw [Finset.card_image_of_injective _ hpt_inj, hVc] at hle
      omega
  -- Apply hchain_split to Cv i and Ch i for every i!
  have hv_split : ∀ i : Fin k, ∃ (Lv Rv : Finset ℝ²), Lv ⊆ Cv i ∧ Rv ⊆ Cv i ∧
      (∀ p ∈ Lv, ∀ q ∈ Lv, ∀ r ∈ Lv, vLt x i p q → vLt x i q r → orient p q r < 0) ∧
      (∀ p ∈ Rv, ∀ q ∈ Rv, ∀ r ∈ Rv, vLt x i p q → vLt x i q r → 0 < orient p q r) ∧
      (Cv i).card ≤ Nat.choose (Lv.card + Rv.card) Lv.card := by
    intro i
    obtain ⟨L, R, hL, hR, hLo, hRo, hcard⟩ := hchain_split i (Cv i) (hCvSub i)
      (fun p hp q hq hne => (hCvChain i p hp q hq hne).imp (·.2) (·.2))
    exact ⟨L, R, hL, hR, fun p hp q hq r hr hpq hqr => hLo p hp q hq r hr hpq.2 hqr.2,
      fun p hp q hq r hr hpq hqr => hRo p hp q hq r hr hpq.2 hqr.2, hcard⟩
  have hh_split : ∀ i : Fin k, ∃ (In Out : Finset ℝ²), In ⊆ Ch i ∧ Out ⊆ Ch i ∧
      (∀ p ∈ In, ∀ q ∈ In, ∀ r ∈ In, hLt x i p q → hLt x i q r → orient p q r < 0) ∧
      (∀ p ∈ Out, ∀ q ∈ Out, ∀ r ∈ Out, hLt x i p q → hLt x i q r → 0 < orient p q r) ∧
      (Ch i).card ≤ Nat.choose (In.card + Out.card) In.card := by
    intro i
    obtain ⟨L, R, hL, hR, hLo, hRo, hcard⟩ := hchain_split i (Ch i) (hChSub i)
      (fun p hp q hq hne => (hChChain i p hp q hq hne).imp (·.2) (·.2))
    exact ⟨L, R, hL, hR, fun p hp q hq r hr hpq hqr => hLo p hp q hq r hr hpq.2 hqr.2,
      fun p hp q hq r hr hpq hqr => hRo p hp q hq r hr hpq.2 hqr.2, hcard⟩
  choose Lv Rv hLvSub hRvSub hLvOrd hRvOrd hvChoose using hv_split
  choose In Out hInSub hOutSub hInOrd hOutOrd hhChoose using hh_split
  -- Step 3: Derive the 3 size bounds from `¬ HasConvexNGon n P`!
  -- Bound (A): (Rv i).card + (Lv (i + 1)).card ≤ n - 1
  have hba : ∀ i : Fin k, (Rv i).card + (Lv (i + 1)).card ≤ n := by
    intro i
    have hdisj : Disjoint (Rv i) (Lv (i + 1)) := by
      rw [Finset.disjoint_left]; intro p hpR hpL
      exact inSpike_disjoint (by omega) (fin_ne_add_one (by omega) i)
        (hPi_spike i p (hCvSub i (hRvSub i hpR)))
        (hPi_spike (i + 1) p (hCvSub (i + 1) (hLvSub (i + 1) hpL)))
    have hsubP : Rv i ∪ Lv (i + 1) ⊆ P := Finset.union_subset
      ((hRvSub i).trans ((hCvSub i).trans (hPi_sub i)))
      ((hLvSub (i + 1)).trans ((hCvSub (i + 1)).trans (hPi_sub (i + 1))))
    have hconv := joining_verticals hk hx_ccw (i := i) (R := Rv i) (L := Lv (i + 1))
      (Set.Triplewise.mono hsubP hnt)
      (fun p hp => hPi_spike i p (hCvSub i (hRvSub i hp)))
      (fun p hp => hPi_spike (i + 1) p (hCvSub (i + 1) (hLvSub (i + 1) hp)))
      (fun p hp q hq hne => hCvChain i p (hRvSub i hp) q (hRvSub i hq) hne)
      (fun p hp q hq hne => hCvChain (i + 1) p (hLvSub (i + 1) hp) q (hLvSub (i + 1) hq) hne)
      (hRvOrd i) (hLvOrd (i + 1))
    by_contra! hgt
    have hcard : n ≤ (Rv i ∪ Lv (i + 1)).card := by
      rw [Finset.card_union_of_disjoint hdisj]; omega
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
    apply hno
    refine ⟨S, hScard, (hSsub.trans hsubP : (S : Set ℝ²) ⊆ (P : Set ℝ²)), fun a ha hmem => ?_⟩
    exact hconv a (hSsub ha) (convexHull_mono (Set.sdiff_subset_sdiff_left (by exact_mod_cast hSsub)) hmem)
  -- Bound (B): (Out i).card ≤ n and (In i).card ≤ n
  have hd_le : ∀ i : Fin k, (Out i).card ≤ n := by
    intro i
    have hsubP : Out i ⊆ P := (hOutSub i).trans ((hChSub i).trans (hPi_sub i))
    have hconv : ConvexIndep (Out i : Set ℝ²) := by
      apply convexIndep_of_monotone_orient_pos (Set.Triplewise.mono hsubP hnt)
        (raySlope (x (i - 1)) (x (i + 2)))
      · intro p hp q hq heq
        by_contra hne
        rcases hChChain i p (hOutSub i hp) q (hOutSub i hq) hne with h | h
        · have := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i p (hChSub i (hOutSub i hp))))
            (inSpike_base_gt hk (hPi_spike i q (hChSub i (hOutSub i hq))))).mp h.2; linarith
        · have := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i q (hChSub i (hOutSub i hq))))
            (inSpike_base_gt hk (hPi_spike i p (hChSub i (hOutSub i hp))))).mp h.2; linarith
      · intro p hp q hq r hr hpq hqr
        have hpq' : hLt x i p q := by
          have hne : p ≠ q := fun h => by rw [h] at hpq; exact lt_irrefl _ hpq
          rcases hChChain i p (hOutSub i hp) q (hOutSub i hq) hne with h | h
          · exact h
          · have := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i q (hChSub i (hOutSub i hq))))
              (inSpike_base_gt hk (hPi_spike i p (hChSub i (hOutSub i hp))))).mp h.2; linarith
        have hqr' : hLt x i q r := by
          have hne : q ≠ r := fun h => by rw [h] at hqr; exact lt_irrefl _ hqr
          rcases hChChain i q (hOutSub i hq) r (hOutSub i hr) hne with h | h
          · exact h
          · have := (orient_B_eq_raySlope_diff (inSpike_base_gt hk (hPi_spike i r (hChSub i (hOutSub i hr))))
              (inSpike_base_gt hk (hPi_spike i q (hChSub i (hOutSub i hq))))).mp h.2; linarith
        exact hOutOrd i p hp q hq r hr hpq' hqr'
    by_contra! hgt
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (le_of_lt hgt)
    exact hno ⟨S, hScard, (hSsub.trans hsubP : (S : Set ℝ²) ⊆ (P : Set ℝ²)), fun a ha hmem =>
      hconv a (hSsub ha) (convexHull_mono (Set.sdiff_subset_sdiff_left (by exact_mod_cast hSsub)) hmem)⟩
  -- Bound (C): ∑ i (even), |In i| ≤ n and ∑ i (odd), |In i| ≤ n => ∑ i, |In i| ≤ 2 * n!
  have hc_parity : ∀ r : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val % 2 = r), (In i).card ≤ n := by
    intro r
    let I := Finset.univ.filter (fun i : Fin k => i.val % 2 = r)
    have hsubP : I.biUnion In ⊆ P := by
      intro p hp; obtain ⟨i, _, hpi⟩ := Finset.mem_biUnion.mp hp
      exact hPi_sub i (hChSub i (hInSub i hpi))
    have hpw : Set.PairwiseDisjoint (I : Set (Fin k)) In := by
      intro i _ j _ hij
      change Disjoint (In i) (In j)
      rw [Finset.disjoint_left]; intro p hpi hpj
      exact inSpike_disjoint (by omega) hij
        (hPi_spike i p (hChSub i (hInSub i hpi)))
        (hPi_spike j p (hChSub j (hInSub j hpj)))
    have hconv := joining_horizontals hk heven hx_ccw r In I (fun i hi => (Finset.mem_filter.mp hi).2)
      (Set.Triplewise.mono hsubP hnt)
      (fun i _ p hp => hPi_spike i p (hChSub i (hInSub i hp)))
      (fun i _ p hp q hq hne => hChChain i p (hInSub i hp) q (hInSub i hq) hne)
      (fun i _ => hInOrd i)
    by_contra! hgt
    have hcard : n ≤ (I.biUnion In).card := by
      rw [Finset.card_biUnion hpw]
      exact le_of_lt hgt
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
    exact hno ⟨S, hScard, (hSsub.trans hsubP : (S : Set ℝ²) ⊆ (P : Set ℝ²)), fun a ha hmem =>
      hconv a (hSsub ha) (convexHull_mono (Set.sdiff_subset_sdiff_left (by exact_mod_cast hSsub)) hmem)⟩
  have hc_sum : ∑ i : Fin k, (In i).card ≤ 2 * n := by
    have hsplit : (Finset.univ : Finset (Fin k)) =
        Finset.univ.filter (fun i : Fin k => i.val % 2 = 0) ∪
        Finset.univ.filter (fun i : Fin k => i.val % 2 = 1) := by
      ext i; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
      omega
    have hdisj : Disjoint (Finset.univ.filter (fun i : Fin k => i.val % 2 = 0))
        (Finset.univ.filter (fun i : Fin k => i.val % 2 = 1)) := by
      rw [Finset.disjoint_left]; intro i h0 h1
      simp only [Finset.mem_filter] at h0 h1; omega
    calc ∑ i : Fin k, (In i).card
        = ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val % 2 = 0), (In i).card +
          ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val % 2 = 1), (In i).card := by
            rw [← Finset.sum_union hdisj, ← hsplit]
      _ ≤ n + n := Nat.add_le_add (hc_parity 0) (hc_parity 1)
      _ = 2 * n := by omega
  have hc_le : ∀ i : Fin k, (In i).card ≤ n := by
    intro i
    have hmem : i ∈ Finset.univ.filter (fun j : Fin k => j.val % 2 = i.val % 2) := by simp
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem).trans (hc_parity (i.val % 2))
  -- Step 4: Multiply the bounds across all i : Fin k!
  have hab_sum : ∑ i : Fin k, ((Lv i).card + (Rv i).card) ≤ k * n := by
    have hshift : ∑ i : Fin k, (Lv i).card = ∑ i : Fin k, (Lv (i + 1)).card := by
      exact (Equiv.sum_comp (Equiv.addRight (1 : Fin k)) (fun i => (Lv i).card)).symm
    calc ∑ i : Fin k, ((Lv i).card + (Rv i).card)
        = ∑ i : Fin k, (Lv i).card + ∑ i : Fin k, (Rv i).card := Finset.sum_add_distrib
      _ = ∑ i : Fin k, (Lv (i + 1)).card + ∑ i : Fin k, (Rv i).card := by rw [hshift]
      _ = ∑ i : Fin k, ((Rv i).card + (Lv (i + 1)).card) := by
            rw [← Finset.sum_add_distrib]; congr 1; ext i; omega
      _ ≤ ∑ _i : Fin k, n := Finset.sum_le_sum (fun i _ => hba i)
      _ = k * n := by simp
  have hprod_le : (∏ i : Fin k, ((Pi i).card : ℝ)) ≤
      (2 : ℝ) ^ (k * n) * ((2 * n : ℕ) : ℝ) ^ (2 * n) := by
    have h1 : ∀ i : Fin k, ((Pi i).card : ℝ) ≤
        (2 : ℝ) ^ ((Lv i).card + (Rv i).card) * ((2 * n : ℕ) : ℝ) ^ (In i).card := by
      intro i
      have hnat : (Pi i).card ≤ 2 ^ ((Lv i).card + (Rv i).card) * (2 * n) ^ (In i).card := by
        have hv1 : (Cv i).card ≤ 2 ^ ((Lv i).card + (Rv i).card) :=
          (hvChoose i).trans (Nat.choose_le_two_pow _ _)
        have hh1 : (Ch i).card ≤ (2 * n) ^ (In i).card := by
          calc (Ch i).card
              ≤ Nat.choose ((In i).card + (Out i).card) (In i).card := hhChoose i
            _ ≤ ((In i).card + (Out i).card) ^ (In i).card := Nat.choose_le_pow _ _
            _ ≤ (2 * n) ^ (In i).card := Nat.pow_le_pow_left (by have := hc_le i; have := hd_le i; omega) _
        exact (hDil i).trans (Nat.mul_le_mul hv1 hh1)
      exact_mod_cast hnat
    calc ∏ i : Fin k, ((Pi i).card : ℝ)
        ≤ ∏ i : Fin k, ((2 : ℝ) ^ ((Lv i).card + (Rv i).card) * ((2 * n : ℕ) : ℝ) ^ (In i).card) :=
          Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => h1 i)
      _ = (∏ i : Fin k, (2 : ℝ) ^ ((Lv i).card + (Rv i).card)) *
          (∏ i : Fin k, ((2 * n : ℕ) : ℝ) ^ (In i).card) := Finset.prod_mul_distrib
      _ = (2 : ℝ) ^ (∑ i : Fin k, ((Lv i).card + (Rv i).card)) *
          ((2 * n : ℕ) : ℝ) ^ (∑ i : Fin k, (In i).card) := by
            rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
      _ ≤ (2 : ℝ) ^ (k * n) * ((2 * n : ℕ) : ℝ) ^ (2 * n) := by
            apply mul_le_mul
            · exact pow_le_pow_right₀ (by norm_num) hab_sum
            · exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 2 * n by omega)) hc_sum
            · positivity
            · positivity
  calc (P.card : ℝ) ^ k
      ≤ (2 : ℝ) ^ (8 * k ^ 2) * ∏ i : Fin k, ((Pi i).card : ℝ) := hcluster
    _ ≤ (2 : ℝ) ^ (8 * k ^ 2) * ((2 : ℝ) ^ (k * n) * ((2 * n : ℕ) : ℝ) ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left hprod_le (by positivity)
    _ = (2 : ℝ) ^ (8 * k ^ 2 + k * n) * ((2 * n : ℕ) : ℝ) ^ (2 * n) := by
        rw [pow_add]; ring

/-- Choosing `k` to be the smallest even integer ≥ `max 4 ⌈√(n * log n)⌉₊` gives
`f n ≤ 2 ^ (n + 24 * √(n * log n))` for all sufficiently large `n`. -/
theorem eventually_cardSet_hmpt :
    ∀ᶠ n : ℕ in atTop, ∃ N ∈ Erdos107.cardSet n,
      (N : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + 24 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) := by
  -- For all n ≥ 100, log n ≥ 4 > 1, 2*n ≤ n^2, log(2*n) / log 2 ≤ 4 * log n,
  -- and k = 2 * ⌈√(n * log n) / 2⌉₊ satisfies 4 ≤ k ≤ √(n * log n) + 2, 4*k ≤ n, etc.
  filter_upwards [Filter.eventually_ge_atTop (100 : ℕ)] with n hn
  have hn_real : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog_ge : (4 : ℝ) ≤ Real.log (n : ℝ) := by
    have h1 : Real.exp 4 ≤ (100 : ℝ) := by
      have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
      calc Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he 4
        _ ≤ 100 := by norm_num
    rw [← Real.log_exp 4]
    exact Real.log_le_log (Real.exp_pos 4) (h1.trans hn_real)
  have hsq_ge : (20 : ℝ) ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    rw [show (20 : ℝ) = Real.sqrt 400 by norm_num]
    exact Real.sqrt_le_sqrt (by nlinarith)
  let S : ℝ := Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
  let m : ℕ := Nat.ceil (S / 2)
  let k : ℕ := 2 * m
  have hm_ge : (10 : ℝ) ≤ (m : ℝ) := by
    have : S / 2 ≤ (m : ℝ) := Nat.le_ceil _
    linarith
  have hm_lt : (m : ℝ) < S / 2 + 1 := Nat.ceil_lt_add_one (by dsimp [S]; positivity)
  have hk_ge4 : 4 ≤ k := by
    have : (10 : ℕ) ≤ m := by exact_mod_cast hm_ge
    omega
  have hk_even : k % 2 = 0 := Nat.mul_mod_right 2 m
  have : NeZero k := ⟨by omega⟩
  have hk_lo : S ≤ (k : ℝ) := by
    have : S / 2 ≤ (m : ℝ) := Nat.le_ceil _
    have hk_cast : (k : ℝ) = 2 * (m : ℝ) := by exact_mod_cast rfl
    linarith
  have hk_hi : (k : ℝ) ≤ S + 2 := by
    have hk_cast : (k : ℝ) = 2 * (m : ℝ) := by exact_mod_cast rfl
    linarith
  have hk_hi_S : (k : ℝ) ≤ 1.1 * S := by linarith
  -- Choose N = ⌊2 ^ (n + 24 * S)⌋₊!
  let B : ℝ := (2 : ℝ) ^ ((n : ℝ) + 24 * S)
  let N : ℕ := Nat.floor B
  have hB_ge1 : 1 ≤ B := by
    dsimp [B]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hN_le : (N : ℝ) ≤ B := Nat.floor_le (by positivity)
  have hN_gt : B - 1 < (N : ℝ) := Nat.sub_one_lt_floor B
  have hN_ge_half : B / 2 ≤ (N : ℝ) := by
    have hB2 : 2 ≤ B := by
      dsimp [B]
      calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2 : ℝ) ^ ((n : ℝ) + 24 * S) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    linarith
  -- Show 2 ^ (4 * k) ≤ N (since 4 * k ≤ 4.4 * S < n + 24 * S - 1)
  have h4k_le : 2 ^ (4 * k) ≤ N := by
    have h4k_real : ((2 ^ (4 * k) : ℕ) : ℝ) ≤ (N : ℝ) := by
      calc ((2 ^ (4 * k) : ℕ) : ℝ)
          = (2 : ℝ) ^ ((4 * k : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_cast
        _ ≤ (2 : ℝ) ^ ((n : ℝ) + 24 * S - 1) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            have : ((4 * k : ℕ) : ℝ) = 4 * (k : ℝ) := by push_cast; ring
            linarith
        _ = B / 2 := by
            dsimp [B]; rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
        _ ≤ (N : ℝ) := hN_ge_half
    exact_mod_cast h4k_real
  -- Show N ∈ Erdos107.cardSet n!
  refine ⟨N, ?_, hN_le⟩
  intro P hPcard hnt
  by_contra hno
  have hpow := hmpt_power_bound (k := k) (by omega) hk_ge4 hk_even hnt hno (hPcard ▸ h4k_le)
  rw [hPcard] at hpow
  -- Compare logs / exponents:
  -- LHS ≥ (B / 2)^k = 2 ^ (k * (n + 24 * S - 1))
  -- RHS = 2 ^ (8 * k^2 + k * n) * (2 * n) ^ (2 * n)
  -- Since (2 * n) ≤ 2 ^ (3 * log n) (as log(2*n) / log 2 ≤ 3 * log n for n ≥ 100!):
  have h2n_le : ((2 * n : ℕ) : ℝ) ≤ (2 : ℝ) ^ (3 * Real.log (n : ℝ)) := by
    have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hlog2n : Real.log ((2 * n : ℕ) : ℝ) ≤ 3 * Real.log (n : ℝ) * Real.log 2 := by
      have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
      rw [hcast, Real.log_mul (by norm_num) hn_pos.ne']
      have hlog2_lt : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
      nlinarith
    calc ((2 * n : ℕ) : ℝ)
        = Real.exp (Real.log ((2 * n : ℕ) : ℝ)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (3 * Real.log (n : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hlog2n
      _ = (2 : ℝ) ^ (3 * Real.log (n : ℝ)) := by
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
  have hRHS_le : (2 : ℝ) ^ (8 * k ^ 2 + k * n) * ((2 * n : ℕ) : ℝ) ^ (2 * n) ≤
      (2 : ℝ) ^ ((8 * k ^ 2 + k * n : ℕ) + (2 * n : ℕ) * (3 * Real.log (n : ℝ))) := by
    have h1 : ((2 * n : ℕ) : ℝ) ^ (2 * n) ≤ ((2 : ℝ) ^ (3 * Real.log (n : ℝ))) ^ (2 * n) :=
      pow_le_pow_left₀ (by positivity) h2n_le (2 * n)
    have h2 : ((2 : ℝ) ^ (3 * Real.log (n : ℝ))) ^ (2 * n) =
        (2 : ℝ) ^ ((2 * n : ℕ) * (3 * Real.log (n : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
    rw [← Real.rpow_natCast (2 : ℝ) (8 * k ^ 2 + k * n),
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (h1.trans_eq h2) (by positivity)
  have hLHS_ge : (2 : ℝ) ^ ((k : ℝ) * ((n : ℝ) + 24 * S - 1)) ≤ (N : ℝ) ^ k := by
    calc (2 : ℝ) ^ ((k : ℝ) * ((n : ℝ) + 24 * S - 1))
        = ((2 : ℝ) ^ ((n : ℝ) + 24 * S - 1)) ^ k := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
      _ = (B / 2) ^ k := by
            dsimp [B]; rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      _ ≤ (N : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hN_ge_half k
  have hpow_cmp : (2 : ℝ) ^ ((k : ℝ) * ((n : ℝ) + 24 * S - 1)) ≤
      (2 : ℝ) ^ (((8 * k ^ 2 + k * n : ℕ) : ℝ) + ((2 * n : ℕ) : ℝ) * (3 * Real.log (n : ℝ))) :=
    hLHS_ge.trans (hpow.trans hRHS_le)
  have hexp_le : (k : ℝ) * ((n : ℝ) + 24 * S - 1) ≤
      ((8 * k ^ 2 + k * n : ℕ) : ℝ) + ((2 * n : ℕ) : ℝ) * (3 * Real.log (n : ℝ)) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hpow_cmp
  -- Simplify! 6 * n * log n = 6 * S^2, and 8 * k^2 ≤ 8 * (1.1 * S)^2 < 10 * S^2,
  -- while k * (24 * S - 1) ≥ S * (24 * S - 1) = 24 * S^2 - S > 16 * S^2!
  have hS_sq : S ^ 2 = (n : ℝ) * Real.log (n : ℝ) := Real.sq_sqrt (by positivity)
  have hcast1 : ((8 * k ^ 2 + k * n : ℕ) : ℝ) = 8 * (k : ℝ) ^ 2 + (k : ℝ) * (n : ℝ) := by
    push_cast; ring
  have hcast2 : ((2 * n : ℕ) : ℝ) * (3 * Real.log (n : ℝ)) = 6 * S ^ 2 := by
    push_cast; linarith
  rw [hcast1, hcast2] at hexp_le
  -- Now hexp_le says: k * (24 * S - 1) ≤ 8 * k^2 + 6 * S^2!
  -- Wait: k ≥ S and k ≤ 1.1 * S, so LHS ≥ 24 * S^2 - S and RHS ≤ 8 * 1.21 * S^2 + 6 * S^2 = 15.68 * S^2!
  have hk_sq : (k : ℝ) ^ 2 ≤ (1.1 * S) ^ 2 := by
    nlinarith
  nlinarith

/-- Monotonicity of `cardSet` and extension to all `n ≥ 3` (identical to the reduction helper). -/
lemma cardSet_mono {m n N : ℕ} (hmn : m ≤ n) (hN : N ∈ Erdos107.cardSet n) :
    N ∈ Erdos107.cardSet m := by
  intro X hX hgp
  obtain ⟨Y, hY, hYX, hconv⟩ := hN X hX hgp
  obtain ⟨Z, hZY, hZ⟩ := Finset.exists_subset_card_eq (hY ▸ hmn)
  refine ⟨Z, hZ, (hZY : (Z : Set ℝ²) ⊆ Y).trans hYX, fun z hz hmem => ?_⟩
  exact hconv z (hZY hz) (convexHull_mono (Set.sdiff_subset_sdiff_left (by exact_mod_cast hZY)) hmem)

end HMPT

theorem OMA.solution : type_of% @Erdos107.variants.hmpt_bound := by
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp HMPT.eventually_cardSet_hmpt
  obtain ⟨M, hM, _⟩ := hm m le_rfl
  let r : ℕ → ℝ := fun n => if m ≤ n then 24 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) else (M : ℝ)
  refine ⟨r, ?_, ?_⟩
  · rw [Asymptotics.isBigO_iff]
    refine ⟨24, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop m] with n hn
    simp only [r, if_pos hn, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (Real.sqrt_nonneg _)]
  · intro n _
    by_cases hn : m ≤ n
    · obtain ⟨N, hN, hNle⟩ := hm n hn
      have hf : (Erdos107.f n : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sInf_le hN
      simpa only [r, if_pos hn] using hf.trans hNle
    · have hf : (Erdos107.f n : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast Nat.sInf_le (HMPT.cardSet_mono (le_of_not_ge hn) hM)
      have hMpow : (M : ℝ) ≤ (2 : ℝ) ^ (M : ℝ) := by
        rw [Real.rpow_natCast]
        exact_mod_cast (Nat.lt_two_pow_self (n := M)).le
      have hpow : (2 : ℝ) ^ (M : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + (M : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg n))
      simpa only [r, if_neg hn] using hf.trans (hMpow.trans hpow)
