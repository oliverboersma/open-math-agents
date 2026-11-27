import OMAReductions.R_Green70_green_70_variants_empty_pentagon_R1
import Mathlib

/-! The Ramsey induction, generic projection and triple coloring are adapted from
@Genbox's merged proof of Erdos651.nonempty_cardSet, PR 932. We use supporting
closed half-planes so that collinear triples are allowed. -/
namespace Green70Weak
open Filter Finset Set
open scoped Topology

private lemma ramsey (α : Type*) [DecidableEq α] (r n : ℕ) :
    ∃ N : ℕ, ∀ (X : Finset α), N ≤ X.card → ∀ c : Finset α → Bool,
      ∃ Y ⊆ X, Y.card = n ∧ ∃ b : Bool, ∀ A ⊆ Y, A.card = r → c A = b := by
  induction r generalizing n with
  | zero =>
    refine ⟨n, fun X hX c => ?_⟩
    obtain ⟨Y, hYX, hcard⟩ := Finset.exists_subset_card_eq hX
    refine ⟨Y, hYX, hcard, c ∅, fun A _ hA => ?_⟩
    rw [Finset.card_eq_zero.mp hA]
  | succ r ih =>
    have stage (t : ℕ) : ∃ N : ℕ, ∀ (X : Finset α), N ≤ X.card → ∀ c : Finset α → Bool,
        ∃ Y ⊆ X, Y.card = t ∧ ∃ labels : α → Bool,
          ∀ A ⊆ Y, A.card = r + 1 → ∃ a ∈ A, c A = labels a := by
      induction t with
      | zero =>
        refine ⟨0, fun X _ _ => ⟨∅, Finset.empty_subset X, rfl, fun _ => false, ?_⟩⟩
        intro A hA hcard
        have hempty := Finset.subset_empty.mp hA
        simp [hempty] at hcard
      | succ t it =>
        obtain ⟨M, hM⟩ := it
        obtain ⟨N, hN⟩ := ih M
        refine ⟨N + 1, fun X hX c => ?_⟩
        obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
        have herase : N ≤ (X.erase x).card := by
          rw [Finset.card_erase_of_mem hx]
          omega
        obtain ⟨R, hR, hcardR, b, hb⟩ := hN (X.erase x) herase (fun A => c (insert x A))
        obtain ⟨Y, hY, hcard, labels, hlabels⟩ := hM R hcardR.ge c
        have hxY : x ∉ Y := fun h => (Finset.mem_erase.mp (hR (hY h))).1 rfl
        have hYX := hY.trans (hR.trans (Finset.erase_subset x X))
        refine ⟨insert x Y, Finset.insert_subset hx hYX, by simp [hxY, hcard],
          Function.update labels x b, ?_⟩
        intro A hA hcardA
        by_cases hxA : x ∈ A
        · have hAY : A.erase x ⊆ Y := by
            intro a ha
            obtain ⟨hne, haA⟩ := Finset.mem_erase.mp ha
            exact (Finset.mem_insert.mp (hA haA)).resolve_left hne
          have hac : (A.erase x).card = r := by rw [Finset.card_erase_of_mem hxA, hcardA]; simp
          refine ⟨x, hxA, ?_⟩
          simpa [Finset.insert_erase hxA] using hb _ (hAY.trans hY) hac
        · have hAY : A ⊆ Y := by
            intro a ha
            exact (Finset.mem_insert.mp (hA ha)).resolve_left (fun he => hxA (he ▸ ha))
          obtain ⟨a, ha, hc⟩ := hlabels A hAY hcardA
          have hax : a ≠ x := by
            rintro rfl
            exact hxA ha
          exact ⟨a, ha, by rwa [Function.update_of_ne hax]⟩
    obtain ⟨N, hN⟩ := stage (2 * n)
    refine ⟨N, fun X hX c => ?_⟩
    obtain ⟨Y, hYX, hcard, labels, hlabels⟩ := hN X hX c
    let U := Y.filter fun a => labels a = true
    let V := Y.filter fun a => labels a ≠ true
    have hsum : U.card + V.card = 2 * n :=
      (Finset.card_filter_add_card_filter_not (s := Y) _).trans hcard
    by_cases hU : n ≤ U.card
    · obtain ⟨Z, hZ, hcardZ⟩ := Finset.exists_subset_card_eq hU
      have hZY := hZ.trans (Finset.filter_subset _ _)
      refine ⟨Z, hZY.trans hYX, hcardZ, true, ?_⟩
      intro A hA hcardA
      obtain ⟨a, ha, he⟩ := hlabels A (hA.trans hZY) hcardA
      exact he.trans (Finset.mem_filter.mp (hZ (hA ha))).2
    · have hV : n ≤ V.card := by omega
      obtain ⟨Z, hZ, hcardZ⟩ := Finset.exists_subset_card_eq hV
      have hZY := hZ.trans (Finset.filter_subset _ _)
      refine ⟨Z, hZY.trans hYX, hcardZ, false, ?_⟩
      intro A hA hcardA
      obtain ⟨a, ha, he⟩ := hlabels A (hA.trans hZY) hcardA
      have ht := (Finset.mem_filter.mp (hZ (hA ha))).2
      exact he.trans (by cases h : labels a <;> simp_all)


private lemma coordinates (X : Finset (ℝ × ℝ)) :
    ∃ (x y : (ℝ × ℝ) →ₗ[ℝ] ℝ) (u v : ℝ × ℝ),
      Set.InjOn x (X : Set (ℝ × ℝ)) ∧ x u = 1 ∧ x v = 0 ∧ y v = 1 := by
  classical
  let bad := (X ×ˢ X).image fun uv : (ℝ × ℝ) × (ℝ × ℝ) =>
    (uv.2.1 - uv.1.1) / (uv.1.2 - uv.2.2)
  obtain ⟨t, ht⟩ := bad.exists_notMem
  let x : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ + t • LinearMap.snd ℝ ℝ ℝ
  let y := LinearMap.snd ℝ ℝ ℝ
  refine ⟨x,y,(1,0),(-t,1), ?_, by simp [x], by simp [x], by simp [y]⟩
  intro p hp q hq hx
  change p.1 + t * p.2 = q.1 + t * q.2 at hx
  by_cases hy : p.2 = q.2
  · exact Prod.ext (by linarith [show t*p.2 = t*q.2 by rw [hy]]) hy
  exfalso
  apply ht
  refine mem_image.mpr ⟨(p,q),mem_product.mpr ⟨hp,hq⟩,?_⟩
  apply (div_eq_iff (sub_ne_zero.mpr hy)).mpr
  nlinarith only [hx]

private noncomputable def slope (x y : (ℝ × ℝ) → ℝ) (p q : ℝ × ℝ) : ℝ :=
  (y q - y p) / (x q - x p)

private lemma boundary {S : Set (ℝ × ℝ)} {p : ℝ × ℝ} (hp : p ∈ S)
    (L : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hL : ∀ q ∈ S, L p ≤ L q)
    (w : ℝ × ℝ) (hw : L w < 0) : p ∈ frontier (convexHull ℝ S) := by
  refine ⟨subset_closure (subset_convexHull ℝ S hp), fun hi => ?_⟩
  have hsub : convexHull ℝ S ⊆ {q | L p ≤ L q} :=
    convexHull_min (fun q hq => hL q hq) (convex_halfSpace_ge L.isLinear _)
  have hc : Continuous (fun a : ℝ => p + a • w) := by fun_prop
  have ht : Tendsto (fun a : ℝ => p + a • w) (𝓝[>] 0) (𝓝 p) := by
    simpa [ContinuousWithinAt] using hc.continuousAt.continuousWithinAt (s := Ioi (0:ℝ)) (x := 0)
  have he : ∀ᶠ a : ℝ in 𝓝[>] 0, p + a • w ∈ convexHull ℝ S := ht (mem_interior_iff_mem_nhds.mp hi)
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a := self_mem_nhdsWithin
  obtain ⟨a,ha,ha'⟩ := (hpos.and he).exists
  have h := hsub ha'
  change L p ≤ L (p + a • w) at h
  rw [map_add, map_smul, smul_eq_mul] at h
  linarith [mul_neg_of_pos_of_neg ha hw]

private lemma supporting (Y : Finset (ℝ × ℝ)) (x y : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (u v : ℝ × ℝ) (hinj : Set.InjOn x (Y : Set (ℝ × ℝ)))
    (hu : x u = 1) (hv : x v = 0) (hy : y v = 1)
    (hslope : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, x a < x b → x b < x c →
      slope x y a b ≤ slope x y b c) :
    (Y : Set (ℝ × ℝ)) ⊆ frontier (convexHull ℝ (Y : Set (ℝ × ℝ))) := by
  classical
  intro p hp
  let A := Y.filter fun q => x q < x p
  let B := Y.filter fun q => x p < x q
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · obtain ⟨a,ha,hmax⟩ := exists_max_image A (fun a => slope x y a p) hA
      let s := slope x y a p
      obtain ⟨haY,hap⟩ := mem_filter.mp ha
      apply boundary hp (y - s • x) _ (-v)
      · simp [hv,hy]
      · intro q hq
        change y p - s * x p ≤ y q - s * x q
        rcases lt_trichotomy (x q) (x p) with hlt|he|hgt
        · have hh := (div_le_iff₀ (sub_pos.mpr hlt)).mp (hmax q (mem_filter.mpr ⟨hq,hlt⟩))
          change (y p - y q) ≤ s * (x p - x q) at hh
          linarith
        · have eq := hinj hq hp he
          simp [eq]
        · have hh := (le_div_iff₀ (sub_pos.mpr hgt)).mp (hslope a haY p hp q hq hap hgt)
          change s * (x q - x p) ≤ y q - y p at hh
          linarith
    · apply boundary hp (-x) _ u
      · simp [hu]
      · intro q hq
        have : ¬ x p < x q := fun h => hB ⟨q, mem_filter.mpr ⟨hq,h⟩⟩
        simpa using (neg_le_neg (le_of_not_gt this))
  · apply boundary hp x _ (-u)
    · simp [hu]
    · intro q hq
      exact le_of_not_gt fun h => hA ⟨q, mem_filter.mpr ⟨hq,h⟩⟩

end Green70Weak

open Green70Weak in
theorem OMA.solution : OMA.R_Green70_green_70_variants_empty_pentagon_R1.H1 := by
  classical
  intro m
  obtain ⟨N,hN⟩ := ramsey (ℝ × ℝ) 3 m
  refine ⟨N, fun X hNX => ?_⟩
  obtain ⟨x,y,u,v,hx,hu,hv,hy⟩ := coordinates X
  let color (A : Finset (ℝ × ℝ)) : Bool := decide
    (∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, x a < x b ∧ x b < x c ∧
      slope x y a b < slope x y b c)
  obtain ⟨Y, hYX, hcard, col, hcol⟩ := hN X hNX color
  refine ⟨Y, hYX, hcard.ge, ?_⟩
  have hY (a : ℝ × ℝ) (ha : a ∈ Y) (b : ℝ × ℝ) (hb : b ∈ Y) (c : ℝ × ℝ) (hc : c ∈ Y)
      (hab : x a < x b) (hbc : x b < x c) :
      (slope x y a b < slope x y b c) ↔ col = true := by
    let A : Finset (ℝ × ℝ) := {a, b, c}
    have hAY : A ⊆ Y := by
      intro p hp
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
    have hAcard : A.card = 3 := Finset.card_triple_eq_three_iff.mpr
      ⟨fun h => hab.ne (congrArg x h), fun h => (hab.trans hbc).ne (congrArg x h),
        fun h => hbc.ne (congrArg x h)⟩
    rw [← hcol A hAY hAcard]
    change _ ↔ decide _ = true
    rw [decide_eq_true_eq]
    constructor
    · exact fun hs => ⟨a, by simp [A], b, by simp [A], c, by simp [A], hab, hbc, hs⟩
    · rintro ⟨a', ha', b', hb', c', hc', hab', hbc', hs'⟩
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at ha' hb' hc'
      have heq : a' = a ∧ b' = b ∧ c' = c := by
        rcases ha' with rfl | rfl | rfl <;>
          rcases hb' with rfl | rfl | rfl <;>
          rcases hc' with rfl | rfl | rfl <;> grind
      rcases heq with ⟨rfl, rfl, rfl⟩
      exact hs'

  cases h : col with
  | true =>
    exact supporting Y x y u v (hx.mono hYX) hu hv hy
      (fun a ha b hb c hc hab hbc => ((hY a ha b hb c hc hab hbc).mpr h).le)
  | false =>
    apply supporting Y x (-y) u (-v) (hx.mono hYX) hu (by simp [hv]) (by simp [hy])
    intro a ha b hb c hc hab hbc
    have hn : ¬ slope x y a b < slope x y b c := by
      rw [hY a ha b hb c hc hab hbc, h]
      decide
    have hf (z w : ℝ × ℝ) : slope x ((-y : (ℝ × ℝ) →ₗ[ℝ] ℝ)) z w = -slope x y z w := by
      change (-y w - -y z) / (x w - x z) = -((y w - y z) / (x w - x z))
      ring
    rw [hf, hf]
    exact neg_le_neg (le_of_not_gt hn)
