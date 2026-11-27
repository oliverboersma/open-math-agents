import FormalConjectures.ErdosProblems.«107»
import Mathlib.Data.Nat.Choose.Sum

/-!
# Erdős Problem 107 — Suk's Bound `f(n) ≤ 2^((1 + o(1)) n)`

Self-contained proof of `Erdos107.variants.su_bound` (`f(n) ≤ 2^(n + o(n))`):
1. Coordinate reduction from `EuclideanSpace ℝ (Fin 2)` to `ℝ × ℝ` with distinct abscissas and
   strict linear separation characterization of convex position.
2. Classical Erdős–Szekeres cup–cap theorem (`card_le_binomial`).
3. Positive-fraction Erdős–Szekeres theorem (Pór–Valtr) via `Finset.powersetCard` double counting
   on alternating outer support triangles of a `(12k + 7)`-cap/cup, giving `k` separated sets
   in cap/cup position each containing at least `|X| / 2^(O(k))` points.
4. One-level block-chord decomposition (`k = M * B` parts into `M` blocks of size `B`):
   - In each block `r` with chord endpoints `a_r, b_r`, the triangle poset `p ≺ q` decomposes
     each interior part via Mirsky's theorem into antichains and chains.
   - Caps in antichains support `(a_r, b_r)` and concatenate across all `M` blocks, yielding a
     block `r*` whose interior antichains have size at most `((n + ⌈n/M⌉).choose ⌈n/M⌉)`.
   - Chains in `r*` map under an orientation-preserving projective map `Φ` (sending line `a b`
     to infinity) to `x`-sorted sets; every left-arc `L_i` and right-arc `R_j` (`i < j`) form a
     convex polygon `L_i ∪ R_j` via Plücker's identity, giving `a_i + b_j < n` and by telescoping
     some `i*` with `a_{i*} + b_{i*} ≤ n + n / (B - 4)`.
5. For any fixed `ε > 0`, choosing constants `B, M` (independent of `n`) yields
   `f(n) ≤ 2^((1 + ε) n)` for all sufficiently large `n`.
-/

open Filter Asymptotics Finset
open scoped Classical EuclideanGeometry BigOperators

namespace OMA.SuBound

/- ## Section 1: Asymptotic & Coordinate Reduction -/

private abbrev Point := ℝ × ℝ

private def orient (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1)

private def IsConvexPlanar (Y : Finset Point) : Prop :=
  ∀ p ∈ Y, ∃ u v : ℝ, ∀ q ∈ Y, q ≠ p → u * p.1 + v * p.2 < u * q.1 + v * q.2

private theorem from_eventual_epsilon {g : ℕ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, g n ≤ (2 : ℝ) ^ ((1 + ε) * n)) :
    ∃ r : ℕ → ℝ, r =o[atTop] (fun n => (n : ℝ)) ∧
      ∀ n : ℕ, g n ≤ (2 : ℝ) ^ ((n : ℝ) + r n) := by
  let r (n : ℕ) : ℝ := max (Real.logb 2 (max (g n) 1) - n) 0
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hpos (n : ℕ) : 0 < max (g n) 1 := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨r, ?_, fun n => ?_⟩
  · refine isLittleO_iff.mpr fun ε hε => ?_
    filter_upwards [h ε hε] with n hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h₁ : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) := by
      rw [← Real.rpow_zero 2]
      exact (Real.rpow_le_rpow_left_iff htwo).mpr (by positivity)
    have hm := max_le hn h₁
    have hl := (Real.logb_le_iff_le_rpow htwo (hpos n)).mpr hm
    rw [Real.norm_of_nonneg (le_max_right _ _), Real.norm_of_nonneg hn0]
    exact max_le (by linarith) (mul_nonneg hε.le hn0)
  · apply (le_max_left _ _).trans
    apply (Real.logb_le_iff_le_rpow htwo (hpos n)).mp
    have hr : Real.logb 2 (max (g n) 1) - n ≤ r n := le_max_left _ _
    linarith

private theorem cardSet_mono {n N M : ℕ} (hN : N ∈ Erdos107.cardSet n) (hNM : N ≤ M) :
    M ∈ Erdos107.cardSet n := by
  intro pts hcard hnt
  obtain ⟨Q, hQ, hQc⟩ := Finset.exists_subset_card_eq (s := pts) (n := N)
    (hNM.trans hcard.ge)
  have hQ' : (Q : Set (EuclideanSpace ℝ (Fin 2))) ⊆ (pts : Set (EuclideanSpace ℝ (Fin 2))) :=
    Finset.coe_subset.mpr hQ
  obtain ⟨S, hS, hSQ, hconv⟩ := hN Q hQc
    (fun a ha b hb c hc => hnt (hQ' ha) (hQ' hb) (hQ' hc))
  exact ⟨S, hS, hSQ.trans hQ', hconv⟩

private theorem from_epsilon_exists
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∃ N : ℕ, (N : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) ∧ N ∈ Erdos107.cardSet n) :
    ∃ r : ℕ → ℝ, r =o[atTop] (fun n => (n : ℝ)) ∧
      ∀ n ≥ 3, (Erdos107.f n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + r n) := by
  obtain ⟨r, hr, hrb⟩ := from_eventual_epsilon (g := fun n => (Erdos107.f n : ℝ)) (by
    intro ε hε
    filter_upwards [h ε hε] with n hn
    obtain ⟨N, hN, hmem⟩ := hn
    exact (Nat.cast_le.mpr (Nat.sInf_le (cardSet_mono hmem (Nat.le_floor hN)))).trans
      (Nat.floor_le (by positivity)))
  exact ⟨r, hr, fun n _ => hrb n⟩

private theorem finite_image_pullback {α β : Type*} [DecidableEq β] (L : α → β)
    (X : Finset α) (Z : Finset β) (hZ : Z ⊆ X.image L) (hL : Set.InjOn L (X : Set α)) :
    ∃ Y ⊆ X, Y.image L = Z ∧ Y.card = Z.card := by
  let Y := X.filter fun y => L y ∈ Z
  have hYX : Y ⊆ X := Finset.filter_subset _ _
  have hYZ : Y.image L = Z := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hy).2
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hZ hz)
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hz⟩, rfl⟩
  refine ⟨Y, hYX, hYZ, ?_⟩
  rw [← hYZ, Finset.card_image_of_injOn (hL.mono hYX)]

private theorem planar_coordinates (X : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ x y : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ,
      Set.InjOn x (X : Set (EuclideanSpace ℝ (Fin 2))) ∧
      ∀ p q, x p = x q → y p = y q → p = q := by
  let bad := (X ×ˢ X).image fun uv : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)) =>
    (uv.2 0 - uv.1 0) / (uv.1 1 - uv.2 1)
  obtain ⟨t, ht⟩ := bad.exists_notMem
  let x : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ :=
    EuclideanSpace.projₗ 0 + t • EuclideanSpace.projₗ 1
  let y : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 1
  have hjoint (p q : EuclideanSpace ℝ (Fin 2)) (hx : x p = x q) (hy : y p = y q) : p = q := by
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 = q 1 at hy
    apply PiLp.ext
    intro i
    fin_cases i
    · change p 0 = q 0
      rw [hy] at hx
      exact add_right_cancel hx
    · exact hy
  refine ⟨x, y, ?_, hjoint⟩
  intro p hp q hq hx
  by_cases hy : y p = y q
  · exact hjoint p q hx hy
  · exfalso
    apply ht
    refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 ≠ q 1 at hy
    apply (div_eq_iff (sub_ne_zero.mpr hy)).mpr
    nlinarith only [hx]

private theorem orient_ne_in_image (X : Finset (EuclideanSpace ℝ (Fin 2)))
    (hX : EuclideanGeometry.NonTrilinear (X : Set (EuclideanSpace ℝ (Fin 2))))
    (x y : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ)
    (hjoint : ∀ p q, x p = x q → y p = y q → p = q) :
    ∀ a ∈ X.image (x.prod y), ∀ b ∈ X.image (x.prod y), ∀ c ∈ X.image (x.prod y),
      a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0 := by
  intro u hu v hv w hw hab hbc he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hw
  change x a < x b at hab
  change x b < x c at hbc
  change (x b - x a) * (y c - y b) - (y b - y a) * (x c - x b) = 0 at he
  have hnab : a ≠ b := fun h => hab.ne (congrArg x h)
  have hnbc : b ≠ c := fun h => hbc.ne (congrArg x h)
  have hnac : a ≠ c := fun h => (hab.trans hbc).ne (congrArg x h)
  apply hX ha hb hc hnab hnbc hnac
  let r := (x b - x a) / (x c - x b)
  have hden := sub_ne_zero.mpr hbc.ne'
  have hxb : x b - x a = r * (x c - x b) := by
    dsimp [r]
    rw [div_mul_cancel₀ _ hden]
  have hyb : y b - y a = r * (y c - y b) := by
    dsimp [r]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hden).2
    linarith only [he]
  have hdiff : b - a = r • (c - b) := by
    apply hjoint
    · simpa only [map_sub, map_smul, smul_eq_mul] using hxb
    · simpa only [map_sub, map_smul, smul_eq_mul] using hyb
  apply (collinear_iff_of_mem (show b ∈ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))) by simp)).mpr
  refine ⟨c - b, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · refine ⟨-r, ?_⟩
    change _ = (-r) • (c - b) + b
    rw [neg_smul, ← hdiff]
    abel
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

private theorem cardSet_of_planar {n N : ℕ}
    (h : ∀ X : Finset Point, X.card = N →
        Set.InjOn Prod.fst (X : Set Point) →
        (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0) →
        ∃ Y ⊆ X, Y.card = n ∧ IsConvexPlanar Y) :
    N ∈ Erdos107.cardSet n := by
  intro pts hcard hnt
  obtain ⟨x, y, hx, hxy⟩ := planar_coordinates pts
  let L := x.prod y
  have hL : Function.Injective L := fun a b he =>
    hxy a b (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hinj : Set.InjOn Prod.fst (↑(pts.image L) : Set Point) := by
    intro u hu v hv he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
    exact congrArg L (hx ha hb he)
  obtain ⟨Y, hYX, hYc, hYconv⟩ := h (pts.image L)
    (by rw [Finset.card_image_of_injective _ hL, hcard])
    hinj (orient_ne_in_image pts hnt x y hxy)
  obtain ⟨Z, hZP, hZY, hZc⟩ := finite_image_pullback L pts Y hYX hL.injOn
  refine ⟨Z, hZc.trans hYc, Finset.coe_subset.mpr hZP, ?_⟩
  intro a ha hmem
  have haY : L a ∈ Y := by
    rw [← hZY]
    exact Finset.mem_image_of_mem L ha
  obtain ⟨u, v, huv⟩ := hYconv (L a) haY
  let Λ : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ := u • x + v • y
  have hsub : (Z : Set (EuclideanSpace ℝ (Fin 2))) \ {a} ⊆ {q | Λ a < Λ q} := by
    intro q hq
    have hqY : L q ∈ Y := by
      rw [← hZY]
      exact Finset.mem_image_of_mem L hq.1
    have hne : L q ≠ L a := fun he => hq.2 (hL he)
    exact huv (L q) hqY hne
  exact lt_irrefl (Λ a) ((convexHull_min hsub (convex_halfSpace_gt Λ.isLinear (Λ a))) hmem)

/- ## Section 2: Orientations, Cups/Caps, Erdős–Szekeres, and Convexity -/

private lemma orient_cyclic (a b c : Point) : orient a b c = orient b c a := by
  unfold orient; ring

private lemma orient_swap (a b c : Point) : orient a c b = - orient a b c := by
  unfold orient; ring

private lemma orient_swap_left (a b c : Point) : orient b a c = - orient a b c := by
  unfold orient; ring

private lemma orient_rev (a b c : Point) : orient c b a = - orient a b c := by
  unfold orient; ring

private lemma orient_self_left (a b : Point) : orient a a b = 0 := by
  unfold orient; ring

private lemma orient_self_right (a b : Point) : orient a b b = 0 := by
  unfold orient; ring

private lemma orient_self_outer (a b : Point) : orient a b a = 0 := by
  unfold orient; ring

private lemma orient_plucker (o a b p q : Point) :
    orient o a b * orient o p q = orient o a p * orient o b q - orient o a q * orient o b p := by
  unfold orient; ring

private lemma orient_ne_of_distinct {X : Finset Point}
    (hx : Set.InjOn Prod.fst (X : Set Point))
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
    {a b c : Point} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : orient a b c ≠ 0 := by
  have hab' : a.1 ≠ b.1 := fun h => hab (hx ha hb h)
  have hbc' : b.1 ≠ c.1 := fun h => hbc (hx hb hc h)
  have hac' : a.1 ≠ c.1 := fun h => hac (hx ha hc h)
  rcases lt_or_gt_of_ne hab' with h1 | h1 <;>
    rcases lt_or_gt_of_ne hbc' with h2 | h2 <;>
    rcases lt_or_gt_of_ne hac' with h3 | h3
  · exact hgen a ha b hb c hc h1 h2
  · linarith
  · rw [show orient a b c = - orient a c b by unfold orient; ring]
    exact neg_ne_zero.mpr (hgen a ha c hc b hb h3 h2)
  · rw [show orient a b c = orient c a b by unfold orient; ring]
    exact hgen c hc a ha b hb h3 h1
  · rw [show orient a b c = - orient b a c by unfold orient; ring]
    exact neg_ne_zero.mpr (hgen b hb a ha c hc h1 h3)
  · rw [show orient a b c = orient b c a by unfold orient; ring]
    exact hgen b hb c hc a ha h2 h3
  · linarith
  · rw [show orient a b c = - orient c b a by unfold orient; ring]
    exact neg_ne_zero.mpr (hgen c hc b hb a ha h2 h1)

private def turn (up : Bool) (a b c : Point) : Prop :=
  if up then 0 < orient a b c else orient a b c < 0

private def turns (up : Bool) : List Point → Prop
  | a :: b :: c :: l => turn up a b c ∧ turns up (b :: c :: l)
  | _ => True

private def IsSeq (up : Bool) (X : Finset Point) (l : List Point) : Prop :=
  (∀ p ∈ l, p ∈ X) ∧ l.Pairwise (fun p q => p.1 < q.1) ∧ turns up l

private def HasSeq (up : Bool) (X : Finset Point) (k : ℕ) : Prop :=
  ∃ l, IsSeq up X l ∧ l.length = k

private theorem isSeq_mono {up : Bool} {X Y : Finset Point} {l : List Point}
    (hl : IsSeq up X l) (hXY : X ⊆ Y) : IsSeq up Y l :=
  ⟨fun p hp => hXY (hl.1 p hp), hl.2⟩

private theorem isSeq_nodup {up : Bool} {X : Finset Point} {l : List Point}
    (hl : IsSeq up X l) : l.Nodup :=
  hl.2.1.imp fun {a b} (h : a.1 < b.1) (he : a = b) => (lt_irrefl a.1) (he ▸ h)

private theorem turns_append {up : Bool} {a b c : Point} (l : List Point)
    (hl : turns up (l ++ [a, b])) (hc : turn up a b c) :
    turns up (l ++ [a, b, c]) := by
  induction l with
  | nil => simpa [turns] using hc
  | cons x l ih =>
    cases l with
    | nil =>
      have h := (show turn up x a b ∧ turns up [a, b] from hl).1
      exact ⟨h, ih (by trivial)⟩
    | cons y l =>
      cases l with
      | nil =>
        exact ⟨(show turn up x y a ∧ turns up [y, a, b] from hl).1,
          ih (show turns up [y, a, b] from hl.2)⟩
      | cons z l =>
        exact ⟨(show turn up x y z ∧ turns up ((y :: z :: l) ++ [a, b]) from hl).1,
          ih (show turns up ((y :: z :: l) ++ [a, b]) from hl.2)⟩

private theorem isSeq_append {up : Bool} {X : Finset Point} {a b c : Point} {l : List Point}
    (hl : IsSeq up X (l ++ [a, b])) (hc : c ∈ X) (hbc : b.1 < c.1) (ht : turn up a b c) :
    IsSeq up X (l ++ [a, b, c]) := by
  rw [show l ++ [a, b, c] = (l ++ [a, b]) ++ [c] by simp]
  refine ⟨?_, List.pairwise_append.2 ⟨hl.2.1, by simp, ?_⟩, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hl.1 p hp
    · simpa using (List.mem_singleton.1 hp ▸ hc)
  · intro p hp q hq
    have hqc := List.mem_singleton.1 hq
    subst q
    rw [show l ++ [a, b] = (l ++ [a]) ++ [b] by simp] at hp
    rcases List.mem_append.1 hp with hp | hp
    · have hsort := hl.2.1
      rw [show l ++ [a, b] = (l ++ [a]) ++ [b] by simp] at hsort
      exact ((List.pairwise_append.1 hsort).2.2 _ hp _ (by simp)).trans hbc
    · simpa [List.mem_singleton.1 hp] using hbc
  · simpa using turns_append l hl.2.2 ht

private theorem exists_suffix_two {l : List Point} (h : 2 ≤ l.length) :
    ∃ pre a b, l = pre ++ [a, b] := by
  have hrevlen : 2 ≤ l.reverse.length := by simpa using h
  cases hr : l.reverse with
  | nil => simp [hr] at hrevlen
  | cons b r =>
    cases r with
    | nil => simp [hr] at hrevlen
    | cons a pre =>
      exact ⟨pre.reverse, a, b, by
        simpa [List.reverse_cons, List.append_assoc] using congrArg List.reverse hr⟩

private def IsEnd (s : ℕ) (X : Finset Point) (p : Point) : Prop :=
  ∃ pre a, IsSeq true X (pre ++ [a, p]) ∧ pre.length = s

private theorem no_shorter_cup_outside (s : ℕ) (X : Finset Point) :
    ¬ HasSeq true {p ∈ X | ¬ IsEnd s X p} (s + 2) := by
  rintro ⟨l, hl, hlen⟩
  obtain ⟨pre, a, p, rfl⟩ := exists_suffix_two (by omega : 2 ≤ l.length)
  have hp := Finset.mem_filter.1 (hl.1 p (by simp))
  have hpre : pre.length = s := by simpa using hlen
  exact hp.2 ⟨pre, a, isSeq_mono hl (Finset.filter_subset _ _), hpre⟩

private theorem no_shorter_cap_in_ends (s t : ℕ) (X : Finset Point)
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
    (hc : ¬ HasSeq true X (s + 3)) (hd : ¬ HasSeq false X (t + 3)) :
    ¬ HasSeq false {p ∈ X | IsEnd s X p} (t + 2) := by
  rintro ⟨l, hl, hlen⟩
  cases l with
  | nil => simp at hlen
  | cons p l =>
    cases l with
    | nil => simp at hlen
    | cons q tail =>
      obtain ⟨hp, pre, a, hcup, hpre⟩ := Finset.mem_filter.1 (hl.1 p (by simp))
      have hq := (Finset.mem_filter.1 (hl.1 q (by simp))).1
      have ha := hcup.1 a (by simp)
      have hap : a.1 < p.1 :=
        (List.pairwise_cons.1 (List.pairwise_append.1 hcup.2.1).2.1).1 p (by simp)
      have hpq : p.1 < q.1 := (List.pairwise_cons.1 hl.2.1).1 q (by simp)
      by_cases hturn : 0 < orient a p q
      · apply hc
        exact ⟨pre ++ [a, p, q],
          isSeq_append hcup hq hpq (by simpa [turn] using hturn), by simp [hpre]⟩
      · apply hd
        have hneg : orient a p q < 0 :=
          lt_of_le_of_ne (le_of_not_gt hturn) (hgen a ha p hp q hq hap hpq)
        have hlX := isSeq_mono hl (Finset.filter_subset _ _)
        refine ⟨a :: p :: q :: tail,
          ⟨?_, List.pairwise_cons.2 ⟨?_, hlX.2.1⟩, ?_⟩, ?_⟩
        · intro b hb
          rcases List.mem_cons.1 hb with rfl | hb
          · exact ha
          · exact hlX.1 b hb
        · intro b hb
          rcases List.mem_cons.1 hb with rfl | hb
          · exact hap
          · exact hap.trans ((List.pairwise_cons.1 hlX.2.1).1 _ hb)
        · change turn false a p q ∧ turns false (p :: q :: tail)
          exact ⟨by simpa [turn] using hneg, hlX.2.2⟩
        · simp only [List.length_cons] at hlen ⊢
          omega

private theorem hasSeq_two {X : Finset Point}
    (hx : Set.InjOn Prod.fst (X : Set Point)) (hX : 1 < X.card) (up : Bool) :
    HasSeq up X 2 := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hX
  have hne : a.1 ≠ b.1 := fun he => hab (hx ha hb he)
  have hseq {a b : Point} (ha : a ∈ X) (hb : b ∈ X) (hab : a.1 < b.1) :
      HasSeq up X 2 := by
    refine ⟨[a, b], ⟨?_, ?_, trivial⟩, rfl⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ha
      · exact hb
    · simp [hab]
  rcases lt_or_gt_of_ne hne with h | h
  · exact hseq ha hb h
  · exact hseq hb ha h

private theorem card_le_binomial (s t : ℕ) (X : Finset Point)
    (hx : Set.InjOn Prod.fst (X : Set Point))
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
    (hc : ¬ HasSeq true X (s + 2)) (hd : ¬ HasSeq false X (t + 2)) :
    X.card ≤ (s + t).choose s := by
  induction s generalizing t X with
  | zero =>
    simpa using (le_of_not_gt fun h => hc (hasSeq_two hx h true))
  | succ s ih =>
    induction t generalizing X with
    | zero =>
      simpa using (le_of_not_gt fun h => hd (hasSeq_two hx h false))
    | succ t jt =>
      let T := X.filter (IsEnd s X)
      let U := X.filter (fun p => ¬ IsEnd s X p)
      have hTX : T ⊆ X := Finset.filter_subset _ _
      have hUX : U ⊆ X := Finset.filter_subset _ _
      have hT : T.card ≤ (s + 1 + t).choose (s + 1) := by
        apply jt T (hx.mono hTX)
        · exact fun a ha b hb c hc hab hbc => hgen a (hTX ha) b (hTX hb) c (hTX hc) hab hbc
        · rintro ⟨l, hl, hlen⟩
          exact hc ⟨l, isSeq_mono hl hTX, hlen⟩
        · exact no_shorter_cap_in_ends s t X hgen hc hd
      have hU : U.card ≤ (s + (t + 1)).choose s := by
        apply ih (t + 1) U (hx.mono hUX)
        · exact fun a ha b hb c hc hab hbc => hgen a (hUX ha) b (hUX hb) c (hUX hc) hab hbc
        · exact no_shorter_cup_outside s X
        · rintro ⟨l, hl, hlen⟩
          exact hd ⟨l, isSeq_mono hl hUX, hlen⟩
      have hpart : T.card + U.card = X.card :=
        Finset.card_filter_add_card_filter_not (IsEnd s X)
      have hchoose :
          ((s + 1) + (t + 1)).choose (s + 1) =
            (s + (t + 1)).choose s + (s + 1 + t).choose (s + 1) := by
        rw [show (s + 1) + (t + 1) = (s + (t + 1)) + 1 by omega,
          Nat.choose_succ_succ', show s + (t + 1) = s + 1 + t by omega]
      rw [hchoose, ← hpart]
      exact (Nat.add_le_add hT hU).trans_eq (Nat.add_comm _ _)

private def signedOrient (up : Bool) (a b c : Point) : ℝ :=
  (if up then 1 else -1) * orient a b c

private theorem turn_iff_signed (up : Bool) (a b c : Point) :
    turn up a b c ↔ 0 < signedOrient up a b c := by
  cases up <;> simp [turn, signedOrient]

private theorem turn_quad {up : Bool} {a b c d : Point}
    (hab : a.1 < b.1) (hbc : b.1 < c.1) (hcd : c.1 < d.1)
    (h₁ : turn up a b c) (h₂ : turn up b c d) :
    turn up a b d ∧ turn up a c d := by
  rw [turn_iff_signed] at h₁ h₂
  simp only [turn_iff_signed]
  have hleft :
      (c.1 - b.1) * signedOrient up a b d =
        (d.1 - b.1) * signedOrient up a b c + (b.1 - a.1) * signedOrient up b c d := by
    unfold signedOrient orient; ring
  have hright :
      (c.1 - b.1) * signedOrient up a c d =
        (c.1 - a.1) * signedOrient up b c d + (d.1 - c.1) * signedOrient up a b c := by
    unfold signedOrient orient; ring
  constructor
  · apply (mul_pos_iff_of_pos_left (sub_pos.mpr hbc)).mp
    rw [hleft]
    exact add_pos (mul_pos (sub_pos.mpr (hbc.trans hcd)) h₁) (mul_pos (sub_pos.mpr hab) h₂)
  · apply (mul_pos_iff_of_pos_left (sub_pos.mpr hbc)).mp
    rw [hright]
    exact add_pos (mul_pos (sub_pos.mpr (hab.trans hbc)) h₂) (mul_pos (sub_pos.mpr hcd) h₁)

private theorem turns_tail {up : Bool} {a : Point} {l : List Point}
    (h : turns up (a :: l)) : turns up l := by
  rcases l with _ | ⟨b, _ | ⟨c, l⟩⟩ <;> [trivial; trivial; exact h.2]

private theorem x_lt_next {a b : Point} {l : List Point}
    (h : (a :: b :: l).Pairwise (fun p q => p.1 < q.1)) : a.1 < b.1 :=
  (List.pairwise_cons.1 h).1 b (by simp)

private theorem turns_delete {up : Bool} {p : Point} {l : List Point} (pre : List Point)
    (hs : (pre ++ p :: l).Pairwise (fun a b => a.1 < b.1))
    (ht : turns up (pre ++ p :: l)) : turns up (pre ++ l) := by
  induction pre with
  | nil => exact turns_tail ht
  | cons a pre ih =>
    cases pre with
    | nil =>
      rcases l with _ | ⟨b, _ | ⟨c, l⟩⟩
      · trivial
      · trivial
      · have hs' : (a :: p :: b :: c :: l).Pairwise (fun u v => u.1 < v.1) := hs
        have ht' : turns up (a :: p :: b :: c :: l) := ht
        have hp := turn_quad (x_lt_next hs') (x_lt_next hs'.tail)
          (x_lt_next hs'.tail.tail) ht'.1 ht'.2.1
        exact ⟨hp.2, ht'.2.2⟩
    | cons b pre =>
      cases pre with
      | nil =>
        cases l with
        | nil => trivial
        | cons c l =>
          have hs' : (a :: b :: p :: c :: l).Pairwise (fun u v => u.1 < v.1) := hs
          have ht' : turns up (a :: b :: p :: c :: l) := ht
          have hp := turn_quad (x_lt_next hs') (x_lt_next hs'.tail)
            (x_lt_next hs'.tail.tail) ht'.1 ht'.2.1
          exact ⟨hp.1, ih hs'.tail ht'.2⟩
      | cons c pre =>
        have ht' : turns up (a :: b :: c :: (pre ++ p :: l)) := ht
        exact ⟨ht'.1, ih hs.tail ht'.2⟩

private theorem turns_sublist_append {up : Bool} {l₁ l₂ : List Point} (h : List.Sublist l₁ l₂)
    (pre : List Point) (hs : (pre ++ l₂).Pairwise (fun a b => a.1 < b.1))
    (ht : turns up (pre ++ l₂)) : turns up (pre ++ l₁) := by
  induction h generalizing pre with
  | slnil => exact ht
  | cons a h ih =>
    apply ih pre
    · apply List.Pairwise.sublist _ hs
      exact (List.Sublist.refl _).append (List.Sublist.cons _ (List.Sublist.refl _))
    · exact turns_delete pre hs ht
  | cons_cons a h ih =>
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [a]) (by simpa only [List.append_assoc, List.singleton_append] using hs)
        (by simpa only [List.append_assoc, List.singleton_append] using ht)

private theorem turn_of_mem {up : Bool} {X : Finset Point} {l : List Point}
    (h : IsSeq up X l) {a b c : Point} (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) : turn up a b c := by
  let r : Point → Point → Prop := fun a b => a.1 < b.1
  let : Std.Antisymm r := ⟨fun _ _ h₁ h₂ => (lt_asymm h₁ h₂).elim⟩
  let : Std.Irrefl r := ⟨fun _ => lt_irrefl _⟩
  have htri : [a, b, c].Pairwise r := by simp [r, hab, hbc, hab.trans hbc]
  have hsub : [a, b, c] ⊆ l := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hsublist : List.Sublist [a, b, c] l :=
    List.sublist_of_subperm_of_pairwise (List.subperm_of_subset htri.nodup hsub) htri h.2.1
  exact (turns_sublist_append hsublist [] h.2.1 h.2.2).1

private theorem isSeq_getElem_lt {up : Bool} {X : Finset Point} {l : List Point}
    (h : IsSeq up X l) {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    l[i].1 < l[j].1 :=
  List.pairwise_iff_getElem.1 h.2.1 i j hi hj hij

private theorem isSeq_turn_getElem {up : Bool} {X : Finset Point} {l : List Point}
    (h : IsSeq up X l) {i j k : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hk : k < l.length)
    (hij : i < j) (hjk : j < k) : turn up l[i] l[j] l[k] :=
  turn_of_mem h (List.getElem_mem hi) (List.getElem_mem hj) (List.getElem_mem hk)
    (isSeq_getElem_lt h hi hj hij) (isSeq_getElem_lt h hj hk hjk)

/-- Unified convexity criterion: any nodup list whose ordered triples are strictly clockwise
forms a convex polygon in `ℝ × ℝ`. -/
private theorem isConvexPlanar_of_orient_neg {l : List Point}
    (hnodup : l.Nodup)
    (horient : ∀ (i j k : ℕ) (hi : i < l.length) (hj : j < l.length) (hk : k < l.length),
      i < j → j < k → orient l[i] l[j] l[k] < 0) :
    IsConvexPlanar l.toFinset := by
  intro p hp
  have hp' : p ∈ l := List.mem_toFinset.1 hp
  by_cases hlen : l.length ≤ 2
  · cases l with
    | nil => simp at hp'
    | cons a t =>
      cases t with
      | nil =>
        refine ⟨0, 0, fun q hq hqp => ?_⟩
        have ha : p = a := by simpa using hp'
        have hqa : q = a := by simpa using List.mem_toFinset.1 hq
        exact (hqp (hqa.trans ha.symm)).elim
      | cons b t =>
        cases t with
        | nil =>
          have hab : a ≠ b := (List.nodup_cons.1 hnodup).1 ∘ (by simpa using ·)
          have hsq : 0 < (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 := by
            by_contra hle
            have h1 : b.1 = a.1 := by nlinarith
            have h2 : b.2 = a.2 := by nlinarith
            exact hab (Prod.ext h1.symm h2.symm)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl
          · refine ⟨b.1 - p.1, b.2 - p.2, fun q hq hqp => ?_⟩
            have hq' := List.mem_toFinset.1 hq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
            rcases hq' with rfl | rfl
            · exact (hqp rfl).elim
            · nlinarith
          · refine ⟨-(p.1 - a.1), -(p.2 - a.2), fun q hq hqp => ?_⟩
            have hq' := List.mem_toFinset.1 hq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
            rcases hq' with rfl | rfl
            · nlinarith
            · exact (hqp rfl).elim
        | cons _ _ => simp at hlen
  · have h3 : 3 ≤ l.length := by omega
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hp'
    set N := l.length
    let prevIdx : ℕ := if r = 0 then N - 1 else r - 1
    let nextIdx : ℕ := if r + 1 = N then 0 else r + 1
    have hprevIdx : prevIdx < N := by dsimp [prevIdx]; split_ifs <;> omega
    have hnextIdx : nextIdx < N := by dsimp [nextIdx]; split_ifs <;> omega
    let prev := l[prevIdx]'hprevIdx
    let next := l[nextIdx]'hnextIdx
    refine ⟨next.2 - prev.2, -(next.1 - prev.1), fun q hq hqp => ?_⟩
    have hdiff : ∀ w : Point,
        (next.2 - prev.2) * w.1 + (-(next.1 - prev.1)) * w.2 -
          ((next.2 - prev.2) * l[r].1 + (-(next.1 - prev.1)) * l[r].2) =
          orient prev next l[r] - orient prev next w := by
      intro w; unfold orient; ring
    suffices hlt : orient prev next q < orient prev next l[r] by
      have := hdiff q; linarith
    have hpos : 0 < orient prev next l[r] := by
      by_cases hr0 : r = 0
      · subst hr0
        have hpv : prev = l[N - 1]'(by omega) := by simp [prev, prevIdx]
        have hnx : next = l[1]'(by omega) := by
          have : (0 : ℕ) + 1 ≠ N := by omega
          simp [next, nextIdx, this]
        rw [hpv, hnx, orient_rev]
        have := horient 0 1 (N - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
        linarith
      · by_cases hrN : r + 1 = N
        · have hpv : prev = l[r - 1]'(by omega) := by simp [prev, prevIdx, hr0]
          have hnx : next = l[0]'(by omega) := by simp [next, nextIdx, hrN]
          rw [hpv, hnx, orient_swap_left]
          have := horient 0 (r - 1) r (by omega) (by omega) hr (by omega) (by omega)
          linarith
        · have hpv : prev = l[r - 1]'(by omega) := by simp [prev, prevIdx, hr0]
          have hnx : next = l[r + 1]'(by omega) := by simp [next, nextIdx, hrN]
          rw [hpv, hnx, orient_swap]
          have := horient (r - 1) r (r + 1) (by omega) hr (by omega) (by omega) (by omega)
          linarith
    have hnonpos : orient prev next q ≤ 0 := by
      obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.1 hq)
      have hsr : s ≠ r := fun he => hqp (by subst he; rfl)
      by_cases hsp : s = prevIdx
      · subst hsp; change orient prev next prev ≤ 0; rw [orient_self_outer]
      · by_cases hsn : s = nextIdx
        · subst hsn; change orient prev next next ≤ 0; rw [orient_self_right]
        · apply le_of_lt
          by_cases hr0 : r = 0
          · subst hr0
            have h1s : 1 < s := by
              have : nextIdx = 1 := by simp [nextIdx]; omega
              omega
            have hsN : s < N - 1 := by
              have : prevIdx = N - 1 := by simp [prevIdx]
              omega
            have hpv : prev = l[N - 1]'(by omega) := by simp [prev, prevIdx]
            have hnx : next = l[1]'(by omega) := by
              have : (0 : ℕ) + 1 ≠ N := by omega
              simp [next, nextIdx, this]
            rw [hpv, hnx, orient_cyclic]
            exact horient 1 s (N - 1) (by omega) hs (by omega) h1s hsN
          · by_cases hrN : r + 1 = N
            · have h0s : 0 < s := by
                have : nextIdx = 0 := by simp [nextIdx, hrN]
                omega
              have hsN : s < r - 1 := by
                have : prevIdx = r - 1 := by simp [prevIdx, hr0]
                omega
              have hpv : prev = l[r - 1]'(by omega) := by simp [prev, prevIdx, hr0]
              have hnx : next = l[0]'(by omega) := by simp [next, nextIdx, hrN]
              rw [hpv, hnx, orient_cyclic]
              exact horient 0 s (r - 1) (by omega) hs (by omega) h0s hsN
            · have hpv : prev = l[r - 1]'(by omega) := by simp [prev, prevIdx, hr0]
              have hnx : next = l[r + 1]'(by omega) := by simp [next, nextIdx, hrN]
              have hne1 : s ≠ r - 1 := by
                have : prevIdx = r - 1 := by simp [prevIdx, hr0]
                omega
              have hne2 : s ≠ r + 1 := by
                have : nextIdx = r + 1 := by simp [nextIdx, hrN]
                omega
              rw [hpv, hnx]
              rcases lt_or_gt_of_ne hne1 with hlt' | hgt'
              · rw [← orient_cyclic]
                exact horient s (r - 1) (r + 1) hs (by omega) (by omega) hlt' (by omega)
              · exact horient (r - 1) (r + 1) s (by omega) (by omega) hs (by omega) (by omega)
    exact lt_of_le_of_lt hnonpos hpos

private theorem isConvexPlanar_subset {Y Z : Finset Point}
    (hY : IsConvexPlanar Y) (hZY : Z ⊆ Y) : IsConvexPlanar Z := by
  intro p hp
  obtain ⟨u, v, huv⟩ := hY p (hZY hp)
  exact ⟨u, v, fun q hq hqp => huv q (hZY hq) hqp⟩

private theorem isConvexPlanar_of_isSeq {up : Bool} {X : Finset Point} {l : List Point}
    (hl : IsSeq up X l) : IsConvexPlanar l.toFinset := by
  cases up with
  | false =>
    apply isConvexPlanar_of_orient_neg (isSeq_nodup hl)
    intro i j k hi hj hk hij hjk
    simpa [turn] using isSeq_turn_getElem hl hi hj hk hij hjk
  | true =>
    have hrev : l.reverse.toFinset = l.toFinset := by ext p; simp
    rw [← hrev]
    apply isConvexPlanar_of_orient_neg ((List.nodup_reverse).2 (isSeq_nodup hl))
    intro i j k hi hj hk hij hjk
    rw [List.length_reverse] at hi hj hk
    simp only [List.getElem_reverse]
    have h1 : l.length - 1 - k < l.length - 1 - j := by omega
    have h2 : l.length - 1 - j < l.length - 1 - i := by omega
    have ht := isSeq_turn_getElem hl (by omega) (by omega) (by omega) h1 h2
    simp only [turn, ↓reduceIte] at ht
    rw [orient_rev]
    linarith

private theorem exists_convex_of_hasSeq {up : Bool} {X : Finset Point} {k n : ℕ}
    (h : HasSeq up X k) (hnk : n ≤ k) :
    ∃ Y ⊆ X, Y.card = n ∧ IsConvexPlanar Y := by
  obtain ⟨l, hl, hlen⟩ := h
  have hsub : l.toFinset ⊆ X := fun p hp => hl.1 p (List.mem_toFinset.1 hp)
  have hcard : l.toFinset.card = k := (List.toFinset_card_of_nodup (isSeq_nodup hl)).trans hlen
  obtain ⟨Y, hYl, hYc⟩ := Finset.exists_subset_card_eq (hcard ▸ hnk)
  exact ⟨Y, hYl.trans hsub, hYc, isConvexPlanar_subset (isConvexPlanar_of_isSeq hl) hYl⟩

/- ## Section 3: Pór–Valtr Positive-Fraction Theorem via `powersetCard` Double Counting -/

private def OuterTri (up : Bool) (a b c d p : Point) : Prop :=
  b.1 < p.1 ∧ p.1 < c.1 ∧ turn up a b p ∧ turn up b p c ∧ turn up p c d

private theorem descFactorial_mul_choose_sub (N m r : ℕ) (hr : r ≤ m) (hm : m ≤ N) :
    N.descFactorial r * (N - r).choose (m - r) = m.descFactorial r * N.choose m := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 : N.descFactorial (r + 1) = (N - r) * N.descFactorial r := Nat.descFactorial_succ N r
    have h2 : m.descFactorial (r + 1) = (m - r) * m.descFactorial r := Nat.descFactorial_succ m r
    have h3 : (N - r) * (N - r - 1).choose (m - r - 1) = (m - r) * (N - r).choose (m - r) := by
      have hmr : 1 ≤ m - r := by omega
      have hnr : 1 ≤ N - r := by omega
      have hc := Nat.add_one_mul_choose_eq (N - r - 1) (m - r - 1)
      have hsub1 : N - r - 1 + 1 = N - r := by omega
      have hsub2 : m - r - 1 + 1 = m - r := by omega
      rw [hsub1, hsub2] at hc
      linarith
    have hnr' : N - (r + 1) = N - r - 1 := by omega
    have hmr' : m - (r + 1) = m - r - 1 := by omega
    rw [h1, h2, hnr', hmr']
    calc
      (N - r) * N.descFactorial r * (N - r - 1).choose (m - r - 1)
        = N.descFactorial r * ((N - r) * (N - r - 1).choose (m - r - 1)) := by ring
      _ = N.descFactorial r * ((m - r) * (N - r).choose (m - r)) := by rw [h3]
      _ = (m - r) * (N.descFactorial r * (N - r).choose (m - r)) := by ring
      _ = (m - r) * (m.descFactorial r * N.choose m) := by rw [ih (by omega)]
      _ = (m - r) * m.descFactorial r * N.choose m := by ring

private theorem two_pow_mul_descFactorial_ge (N r : ℕ) (hN : 2 * r ≤ N) :
    N ^ r ≤ 2 ^ r * N.descFactorial r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, pow_succ, Nat.descFactorial_succ]
    have h1 : N ^ r ≤ 2 ^ r * N.descFactorial r := ih (by omega)
    have h2 : N ≤ 2 * (N - r) := by omega
    calc
      N ^ r * N ≤ (2 ^ r * N.descFactorial r) * (2 * (N - r)) := Nat.mul_le_mul h1 h2
      _ = 2 ^ r * 2 * ((N - r) * N.descFactorial r) := by ring

private theorem descFactorial_le_pow (m r : ℕ) : m.descFactorial r ≤ m ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.descFactorial_succ, pow_succ, mul_comm (m ^ r) m]
    exact Nat.mul_le_mul (Nat.sub_le m r) ih

private theorem factorial_mul_choose_le_pow (t r : ℕ) :
    r.factorial * t.choose r ≤ t ^ r := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact descFactorial_le_pow t r

private theorem card_bad_samples_for_quad (X : Finset Point) (m : ℕ) (_hm : 9 ≤ m)
    (up : Bool) (a b c d : Point) (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X) (hd : d ∈ X)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) (hcd : c.1 < d.1) :
    ((X.powersetCard m).filter fun S =>
      a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧ 5 ≤ (S.filter (OuterTri up a b c d)).card).card ≤
      (X.filter (OuterTri up a b c d)).card.choose 5 * (X.card - 9).choose (m - 9) := by
  let Q : Finset Point := {a, b, c, d}
  let T : Finset Point := X.filter (OuterTri up a b c d)
  have hQcard : Q.card = 4 := by
    have h1 : a ≠ b := fun h => hab.ne (congrArg Prod.fst h)
    have h2 : a ≠ c := fun h => (hab.trans hbc).ne (congrArg Prod.fst h)
    have h3 : a ≠ d := fun h => (hab.trans (hbc.trans hcd)).ne (congrArg Prod.fst h)
    have h4 : b ≠ c := fun h => hbc.ne (congrArg Prod.fst h)
    have h5 : b ≠ d := fun h => (hbc.trans hcd).ne (congrArg Prod.fst h)
    have h6 : c ≠ d := fun h => hcd.ne (congrArg Prod.fst h)
    simp [Q, h1, h2, h3, h4, h5, h6]
  have hQX : Q ⊆ X := by
    intro p hp
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption
  have hQT : Disjoint Q T := by
    rw [Finset.disjoint_left]
    intro p hpQ hpT
    have htri := (Finset.mem_filter.1 hpT).2
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hpQ
    rcases hpQ with rfl | rfl | rfl | rfl
    · linarith [htri.1]
    · exact lt_irrefl _ htri.1
    · exact lt_irrefl _ htri.2.1
    · linarith [htri.2.1]
  let cover : Finset (Finset Point) :=
    (T.powersetCard 5).biUnion fun U =>
      ((X \ (Q ∪ U)).powersetCard (m - 9)).image fun R => (Q ∪ U) ∪ R
  have hsub : ((X.powersetCard m).filter fun S =>
      a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧ 5 ≤ (S.filter (OuterTri up a b c d)).card) ⊆ cover := by
    intro S hS
    obtain ⟨hSm, haS, hbS, hcS, hdS, h5⟩ := Finset.mem_filter.1 hS
    obtain ⟨hSX, hScard⟩ := Finset.mem_powersetCard.1 hSm
    obtain ⟨U, hUS, hUcard⟩ := Finset.exists_subset_card_eq h5
    have hUT : U ⊆ T := by
      intro p hp
      obtain ⟨hpS, htri⟩ := Finset.mem_filter.1 (hUS hp)
      exact Finset.mem_filter.2 ⟨hSX hpS, htri⟩
    have hQS : Q ⊆ S := by
      intro p hp
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> assumption
    have hUS' : U ⊆ S := fun p hp => (Finset.mem_filter.1 (hUS hp)).1
    have hQUS : Q ∪ U ⊆ S := Finset.union_subset hQS hUS'
    have hQUcard : (Q ∪ U).card = 9 := by
      rw [Finset.card_union_of_disjoint (hQT.mono_right hUT), hQcard, hUcard]
    refine Finset.mem_biUnion.2 ⟨U, Finset.mem_powersetCard.2 ⟨hUT, hUcard⟩, ?_⟩
    refine Finset.mem_image.2 ⟨S \ (Q ∪ U), Finset.mem_powersetCard.2 ⟨?_, ?_⟩, ?_⟩
    · intro p hp
      obtain ⟨hpS, hpQU⟩ := Finset.mem_sdiff.1 hp
      exact Finset.mem_sdiff.2 ⟨hSX hpS, hpQU⟩
    · rw [Finset.card_sdiff_of_subset hQUS, hScard, hQUcard]
    · exact Finset.union_sdiff_of_subset hQUS
  calc
    ((X.powersetCard m).filter fun S =>
        a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧ 5 ≤ (S.filter (OuterTri up a b c d)).card).card
      ≤ cover.card := Finset.card_le_card hsub
    _ ≤ ∑ U ∈ T.powersetCard 5,
          (((X \ (Q ∪ U)).powersetCard (m - 9)).image fun R => (Q ∪ U) ∪ R).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ U ∈ T.powersetCard 5, (X.card - 9).choose (m - 9) := by
        apply Finset.sum_le_sum
        intro U hU
        obtain ⟨hUT, hUcard⟩ := Finset.mem_powersetCard.1 hU
        have hQUX : Q ∪ U ⊆ X :=
          Finset.union_subset hQX (hUT.trans (Finset.filter_subset _ _))
        have hQUcard : (Q ∪ U).card = 9 := by
          rw [Finset.card_union_of_disjoint (hQT.mono_right hUT), hQcard, hUcard]
        calc
          (((X \ (Q ∪ U)).powersetCard (m - 9)).image fun R => (Q ∪ U) ∪ R).card
            ≤ ((X \ (Q ∪ U)).powersetCard (m - 9)).card := Finset.card_image_le
          _ = (X \ (Q ∪ U)).card.choose (m - 9) := Finset.card_powersetCard _ _
          _ = (X.card - 9).choose (m - 9) := by rw [Finset.card_sdiff_of_subset hQUX, hQUcard]
    _ = T.card.choose 5 * (X.card - 9).choose (m - 9) := by
        rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]

private theorem exists_good_sample (X : Finset Point) (m : ℕ) (hm : 9 ≤ m) (hN : 16 * m ≤ X.card) :
    ∃ S ∈ X.powersetCard m, ∀ (up : Bool) (a b c d : Point),
      a ∈ S → b ∈ S → c ∈ S → d ∈ S → a.1 < b.1 → b.1 < c.1 → c.1 < d.1 →
      5 ≤ (S.filter (OuterTri up a b c d)).card →
      X.card ≤ 2 * m ^ 2 * (X.filter (OuterTri up a b c d)).card := by
  let D : ℕ := 2 * m ^ 2
  let N : ℕ := X.card
  let Bad : Finset (Finset Point) :=
    (X.powersetCard m).filter fun S =>
      ∃ (up : Bool) (a b c d : Point),
        a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧ a.1 < b.1 ∧ b.1 < c.1 ∧ c.1 < d.1 ∧
        5 ≤ (S.filter (OuterTri up a b c d)).card ∧
        D * (X.filter (OuterTri up a b c d)).card < N
  have hBad_lt : Bad.card < (X.powersetCard m).card := by
    let Quads := (Finset.univ : Finset Bool) ×ˢ (X ×ˢ (X ×ˢ (X ×ˢ X)))
    let BadQuads := Quads.filter fun q =>
      q.2.1.1 < q.2.2.1.1 ∧ q.2.2.1.1 < q.2.2.2.1.1 ∧ q.2.2.2.1.1 < q.2.2.2.2.1 ∧
      D * (X.filter (OuterTri q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)).card < N
    have hBadSub : Bad ⊆ BadQuads.biUnion fun q =>
        (X.powersetCard m).filter fun S =>
          q.2.1 ∈ S ∧ q.2.2.1 ∈ S ∧ q.2.2.2.1 ∈ S ∧ q.2.2.2.2 ∈ S ∧
          5 ≤ (S.filter (OuterTri q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)).card := by
      intro S hS
      obtain ⟨hSm, up, a, b, c, d, ha, hb, hc, hd, hab, hbc, hcd, h5, hlt⟩ := Finset.mem_filter.1 hS
      have hSX := (Finset.mem_powersetCard.1 hSm).1
      refine Finset.mem_biUnion.2 ⟨(up, a, b, c, d), ?_, ?_⟩
      · refine Finset.mem_filter.2 ⟨?_, hab, hbc, hcd, hlt⟩
        exact Finset.mem_product.2 ⟨Finset.mem_univ _,
          Finset.mem_product.2 ⟨hSX ha, Finset.mem_product.2 ⟨hSX hb,
            Finset.mem_product.2 ⟨hSX hc, hSX hd⟩⟩⟩⟩
      · exact Finset.mem_filter.2 ⟨hSm, ha, hb, hc, hd, h5⟩
    have hmul : 120 * D ^ 5 * Bad.card ≤ 2 * N ^ 9 * (N - 9).choose (m - 9) := by
      have hstep1 : Bad.card ≤ ∑ q ∈ BadQuads,
          (X.filter (OuterTri q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)).card.choose 5 *
            (N - 9).choose (m - 9) := by
        calc
          Bad.card ≤ (BadQuads.biUnion _).card := Finset.card_le_card hBadSub
          _ ≤ ∑ q ∈ BadQuads, _ := Finset.card_biUnion_le
          _ ≤ ∑ q ∈ BadQuads, _ := by
            apply Finset.sum_le_sum
            intro q hq
            obtain ⟨hqQ, hab, hbc, hcd, _⟩ := Finset.mem_filter.1 hq
            have h1 := (Finset.mem_product.1 hqQ).2
            have ha := (Finset.mem_product.1 h1).1
            have h2 := (Finset.mem_product.1 h1).2
            have hb := (Finset.mem_product.1 h2).1
            have h3 := (Finset.mem_product.1 h2).2
            have hc := (Finset.mem_product.1 h3).1
            have hd := (Finset.mem_product.1 h3).2
            exact card_bad_samples_for_quad X m hm q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
              ha hb hc hd hab hbc hcd
      have hstep2 : 120 * D ^ 5 * Bad.card ≤
          ∑ q ∈ BadQuads, N ^ 5 * (N - 9).choose (m - 9) := by
        calc
          120 * D ^ 5 * Bad.card
            ≤ 120 * D ^ 5 * ∑ q ∈ BadQuads,
                (X.filter (OuterTri q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)).card.choose 5 *
                  (N - 9).choose (m - 9) := Nat.mul_le_mul_left _ hstep1
          _ = ∑ q ∈ BadQuads, (120 * D ^ 5 *
                (X.filter (OuterTri q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)).card.choose 5) *
                  (N - 9).choose (m - 9) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring
          _ ≤ ∑ q ∈ BadQuads, N ^ 5 * (N - 9).choose (m - 9) := by
            apply Finset.sum_le_sum
            intro q hq
            have hlt := (Finset.mem_filter.1 hq).2.2.2.2
            set t := (X.filter (OuterTri q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)).card
            have hfac : 120 * t.choose 5 ≤ t ^ 5 := by
              simpa [Nat.factorial] using factorial_mul_choose_le_pow t 5
            have hpow : 120 * D ^ 5 * t.choose 5 ≤ N ^ 5 := by
              calc
                120 * D ^ 5 * t.choose 5 = D ^ 5 * (120 * t.choose 5) := by ring
                _ ≤ D ^ 5 * t ^ 5 := Nat.mul_le_mul_left _ hfac
                _ = (D * t) ^ 5 := (mul_pow D t 5).symm
                _ ≤ N ^ 5 := Nat.pow_le_pow_left hlt.le 5
            exact Nat.mul_le_mul_right _ hpow
      have hBQcard : BadQuads.card ≤ 2 * N ^ 4 := by
        calc
          BadQuads.card ≤ Quads.card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = 2 * N ^ 4 := by
            simp only [Quads, Finset.card_product, Finset.card_univ, Fintype.card_bool, N]
            ring
      calc
        120 * D ^ 5 * Bad.card ≤ ∑ _q ∈ BadQuads, N ^ 5 * (N - 9).choose (m - 9) := hstep2
        _ = BadQuads.card * (N ^ 5 * (N - 9).choose (m - 9)) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (2 * N ^ 4) * (N ^ 5 * (N - 9).choose (m - 9)) := Nat.mul_le_mul_right _ hBQcard
        _ = 2 * N ^ 9 * (N - 9).choose (m - 9) := by ring
    have hdesc := descFactorial_mul_choose_sub N m 9 hm (by omega)
    have hN9 : N ^ 9 ≤ 2 ^ 9 * N.descFactorial 9 := two_pow_mul_descFactorial_ge N 9 (by omega)
    have hm9 : m.descFactorial 9 ≤ m ^ 9 := descFactorial_le_pow m 9
    have hstrict : 120 * D ^ 5 * Bad.card < 120 * D ^ 5 * (X.powersetCard m).card := by
      rw [Finset.card_powersetCard]
      have hchoose_pos : 0 < N.choose m := Nat.choose_pos (by omega)
      calc
        120 * D ^ 5 * Bad.card
          ≤ 2 * N ^ 9 * (N - 9).choose (m - 9) := hmul
        _ ≤ 2 * (2 ^ 9 * N.descFactorial 9) * (N - 9).choose (m - 9) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hN9)
        _ = 1024 * (N.descFactorial 9 * (N - 9).choose (m - 9)) := by ring
        _ = 1024 * (m.descFactorial 9 * N.choose m) := by rw [hdesc]
        _ ≤ 1024 * (m ^ 9 * N.choose m) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hm9)
        _ = 1024 * m ^ 9 * N.choose m := by ring
        _ < 120 * D ^ 5 * N.choose m := by
            apply Nat.mul_lt_mul_of_pos_right _ hchoose_pos
            have hD5 : 120 * D ^ 5 = 3840 * m ^ 10 := by dsimp [D]; ring
            rw [hD5, show m ^ 10 = m ^ 9 * m by ring]
            have hm9pos : 0 < m ^ 9 := Nat.pow_pos (by omega)
            nlinarith
    exact Nat.lt_of_mul_lt_mul_left hstrict
  have hne : ((X.powersetCard m) \ Bad).Nonempty := by
    have hBadSub' : Bad ⊆ X.powersetCard m := Finset.filter_subset _ _
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hBadSub']
    omega
  obtain ⟨S, hS⟩ := hne
  obtain ⟨hSm, hSnotBad⟩ := Finset.mem_sdiff.1 hS
  refine ⟨S, hSm, fun up a b c d ha hb hc hd hab hbc hcd h5 => ?_⟩
  by_contra hlt
  exact hSnotBad (Finset.mem_filter.2 ⟨hSm, up, a, b, c, d, ha, hb, hc, hd, hab, hbc, hcd, h5,
    Nat.lt_of_not_ge hlt⟩)

/-- Interleaving `k` points `p_0, ..., p_{k-1}` into the alternating outer triangles of a
`(2k + 2)`-cap/cup `y_0, ..., y_{2k+1}` produces a single `(3k + 2)`-cap/cup. -/
private theorem isSeq_interleave {up : Bool} {X : Finset Point} :
    ∀ (k : ℕ) (y : Fin (2 * k + 2) → Point) (p : Fin k → Point),
      (∀ j, y j ∈ X) →
      (∀ i, p i ∈ X) →
      (∀ j₁ j₂ : Fin (2 * k + 2), j₁ < j₂ → (y j₁).1 < (y j₂).1) →
      (∀ i : Fin k, OuterTri up
        (y ⟨2 * i.1, by omega⟩) (y ⟨2 * i.1 + 1, by omega⟩)
        (y ⟨2 * i.1 + 2, by omega⟩) (y ⟨2 * i.1 + 3, by omega⟩) (p i)) →
      ∃ l : List Point, IsSeq up X l ∧ (∀ i : Fin k, p i ∈ l) ∧
        (∀ j : Fin (2 * k + 2), y j ∈ l) ∧
        (∃ rest, l = y ⟨0, by omega⟩ :: y ⟨1, by omega⟩ :: rest) := by
  intro k
  induction k with
  | zero =>
    intro y p hy _ hsort _
    refine ⟨[y ⟨0, by omega⟩, y ⟨1, by omega⟩], ⟨?_, ?_, trivial⟩, ?_, ?_, ⟨[], rfl⟩⟩
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> exact hy _
    · exact List.pairwise_cons.2 ⟨by
        intro q hq
        rw [List.mem_singleton.1 hq]
        exact hsort ⟨0, by omega⟩ ⟨1, by omega⟩ (by show (0 : ℕ) < 1; omega), by simp⟩
    · intro i; exact Fin.elim0 i
    · intro j
      rcases j with ⟨j, hj⟩
      have hj' : j = 0 ∨ j = 1 := by omega
      rcases hj' with rfl | rfl <;> simp
  | succ k ih =>
    intro y p hy hp hsort htri
    let y' : Fin (2 * k + 2) → Point := fun j => y ⟨j.1 + 2, by omega⟩
    let p' : Fin k → Point := fun i => p ⟨i.1 + 1, by omega⟩
    have hy' : ∀ j, y' j ∈ X := fun j => hy _
    have hp' : ∀ i, p' i ∈ X := fun i => hp _
    have hsort' : ∀ j₁ j₂ : Fin (2 * k + 2), j₁ < j₂ → (y' j₁).1 < (y' j₂).1 :=
      fun j₁ j₂ h => hsort _ _ (by show j₁.1 + 2 < j₂.1 + 2; omega)
    have htri' : ∀ i : Fin k, OuterTri up
        (y' ⟨2 * i.1, by omega⟩) (y' ⟨2 * i.1 + 1, by omega⟩)
        (y' ⟨2 * i.1 + 2, by omega⟩) (y' ⟨2 * i.1 + 3, by omega⟩) (p' i) := by
      intro i
      simpa only [y', p', show 2 * (i.1 + 1) = 2 * i.1 + 2 by omega,
        show 2 * (i.1 + 1) + 1 = 2 * i.1 + 3 by omega,
        show 2 * (i.1 + 1) + 2 = 2 * i.1 + 4 by omega,
        show 2 * (i.1 + 1) + 3 = 2 * i.1 + 5 by omega] using htri ⟨i.1 + 1, by omega⟩
    obtain ⟨l', hl', hpl', hyl', rest, hreq⟩ := ih y' p' hy' hp' hsort' htri'
    have h0 := htri ⟨0, by omega⟩
    let y0 := y ⟨0, by omega⟩
    let y1 := y ⟨1, by omega⟩
    let p0 := p ⟨0, by omega⟩
    let y2 := y ⟨2, by omega⟩
    let y3 := y ⟨3, by omega⟩
    have hy01 : y0.1 < y1.1 := hsort ⟨0, by omega⟩ ⟨1, by omega⟩ (by show (0 : ℕ) < 1; omega)
    have hy1p0 : y1.1 < p0.1 := h0.1
    have hp0y2 : p0.1 < y2.1 := h0.2.1
    have hl'ge : ∀ q ∈ l', y2.1 ≤ q.1 := by
      intro q hq
      rw [hreq] at hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact le_rfl
      · exact le_of_lt ((List.pairwise_cons.1 (hreq ▸ hl'.2.1)).1 q hq)
    refine ⟨y0 :: y1 :: p0 :: l', ⟨?_, ?_, ?_⟩, ?_, ?_, ⟨p0 :: l', rfl⟩⟩
    · intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | rfl | rfl | hq
      · exact hy _
      · exact hy _
      · exact hp _
      · exact hl'.1 q hq
    · refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, hl'.2.1⟩⟩⟩
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | rfl | hq
        · exact hy01
        · exact hy01.trans hy1p0
        · exact hy01.trans (hy1p0.trans (hp0y2.trans_le (hl'ge q hq)))
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hy1p0
        · exact hy1p0.trans (hp0y2.trans_le (hl'ge q hq))
      · intro q hq
        exact hp0y2.trans_le (hl'ge q hq)
    · rw [hreq]
      change turn up y0 y1 p0 ∧ turn up y1 p0 y2 ∧ turn up p0 y2 y3 ∧ turns up (y2 :: y3 :: rest)
      exact ⟨h0.2.2.1, h0.2.2.2.1, h0.2.2.2.2, hreq ▸ hl'.2.2⟩
    · intro i
      rcases i with ⟨i, hi⟩
      cases i with
      | zero => simp [p0]
      | succ i =>
        have hm := hpl' ⟨i, by omega⟩
        simp only [List.mem_cons]; right; right; right; exact hm
    · intro j
      rcases j with ⟨j, hj⟩
      match j with
      | 0 => simp [y0]
      | 1 => simp [y1]
      | j + 2 =>
        have hm := hyl' ⟨j, by omega⟩
        simp only [List.mem_cons]; right; right; right; exact hm

/-- Pór–Valtr positive-fraction Erdős–Szekeres theorem (pure elementary version):
any general-position set `X` with at least `16 * m` points (where `K = 12k + 7` and
`m = (2K - 4).choose (K - 2) + 1`) contains `k` sets in cap or cup position, each of size
at least `|X| / (2 m^2)`. -/
private theorem por_valtr_cap_or_cup (k : ℕ) (hk : 1 ≤ k) (X : Finset Point)
    (hx : Set.InjOn Prod.fst (X : Set Point))
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
    (hX : 16 * ((2 * (12 * k + 7) - 4).choose (12 * k + 5) + 1) ≤ X.card) :
    ∃ (up : Bool) (P : Fin k → Finset Point),
      (∀ i, P i ⊆ X) ∧
      (∀ i, X.card ≤ 2 * (((2 * (12 * k + 7) - 4).choose (12 * k + 5) + 1) ^ 2) * (P i).card) ∧
      (∀ i j : Fin k, i < j → ∀ p ∈ P i, ∀ q ∈ P j, p.1 < q.1) ∧
      (∀ i j l : Fin k, i < j → j < l → ∀ p ∈ P i, ∀ q ∈ P j, ∀ r ∈ P l, turn up p q r) := by
  let K : ℕ := 12 * k + 7
  let m : ℕ := (2 * K - 4).choose (K - 2) + 1
  have hK19 : 19 ≤ K := by dsimp [K]; omega
  have hm9 : 9 ≤ m := by
    have hcentral : ∀ a : ℕ, a ≤ (2 * a).choose a := by
      intro a
      induction a with
      | zero => simp
      | succ a ih =>
        have h1 : (2 * (a + 1)).choose (a + 1) =
            (2 * a + 1).choose a + (2 * a + 1).choose (a + 1) := by
          rw [show 2 * (a + 1) = (2 * a + 1) + 1 by omega, Nat.choose_succ_succ']
        have h2 : (2 * a).choose a ≤ (2 * a + 1).choose a :=
          Nat.choose_le_choose a (by omega)
        have h3 : 1 ≤ (2 * a + 1).choose (a + 1) := Nat.choose_pos (by omega)
        omega
    have hch : K - 2 ≤ (2 * K - 4).choose (K - 2) := by
      simpa [show 2 * (K - 2) = 2 * K - 4 by omega] using hcentral (K - 2)
    dsimp [m]; omega
  have hm_eq : m = (2 * (12 * k + 7) - 4).choose (12 * k + 5) + 1 := by
    dsimp [m, K]; rw [show 12 * k + 7 - 2 = 12 * k + 5 by omega]
  obtain ⟨S, hSm, hgood⟩ := exists_good_sample X m hm9 (hm_eq ▸ hX)
  obtain ⟨hSX, hScard⟩ := Finset.mem_powersetCard.1 hSm
  have hseq : HasSeq true S K ∨ HasSeq false S K := by
    by_contra! h
    have hs : (K - 2) + 2 = K := by omega
    have hs' : (K - 2) + (K - 2) = 2 * K - 4 := by omega
    have hle := card_le_binomial (K - 2) (K - 2) S (hx.mono hSX)
      (fun a ha b hb c hc hab hbc => hgen a (hSX ha) b (hSX hb) c (hSX hc) hab hbc)
      (by simpa only [hs] using h.1) (by simpa only [hs] using h.2)
    rw [hScard, hs'] at hle
    exact (Nat.not_succ_le_self _) hle
  have hbuild : ∀ up : Bool, HasSeq up S K →
      ∃ P : Fin k → Finset Point,
        (∀ i, P i ⊆ X) ∧
        (∀ i, X.card ≤ 2 * m ^ 2 * (P i).card) ∧
        (∀ i j : Fin k, i < j → ∀ p ∈ P i, ∀ q ∈ P j, p.1 < q.1) ∧
        (∀ i j l : Fin k, i < j → j < l → ∀ p ∈ P i, ∀ q ∈ P j, ∀ r ∈ P l, turn up p q r) := by
    rintro up ⟨C, hC, hClen⟩
    have hClen' : C.length = 12 * k + 7 := hClen
    let y : Fin (2 * k + 2) → Point := fun j => C[6 * j.1]'(by omega)
    let P : Fin k → Finset Point := fun i =>
      X.filter (OuterTri up
        (y ⟨2 * i.1, by omega⟩) (y ⟨2 * i.1 + 1, by omega⟩)
        (y ⟨2 * i.1 + 2, by omega⟩) (y ⟨2 * i.1 + 3, by omega⟩))
    have hyS : ∀ j, y j ∈ S := fun j => hC.1 _ (List.getElem_mem _)
    have hysort : ∀ j₁ j₂ : Fin (2 * k + 2), j₁ < j₂ → (y j₁).1 < (y j₂).1 :=
      fun j₁ j₂ hj => isSeq_getElem_lt hC (by omega) (by omega) (by show 6 * j₁.1 < 6 * j₂.1; omega)
    have h5_of : ∀ i : Fin k, 5 ≤ (S.filter (OuterTri up
        (y ⟨2 * i.1, by omega⟩) (y ⟨2 * i.1 + 1, by omega⟩)
        (y ⟨2 * i.1 + 2, by omega⟩) (y ⟨2 * i.1 + 3, by omega⟩))).card := by
      intro i
      let idx : Fin 5 → Point := fun r => C[6 * (2 * i.1 + 1) + r.1 + 1]'(by omega)
      have hinj : Function.Injective idx := by
        intro r₁ r₂ he
        have hlt : ∀ {u v : Fin 5}, u < v → (idx u).1 < (idx v).1 := fun {u v} huv =>
          isSeq_getElem_lt hC (by omega) (by omega)
            (by show 6 * (2 * i.1 + 1) + u.1 + 1 < 6 * (2 * i.1 + 1) + v.1 + 1; omega)
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt' | hlt'
        · exact (hlt hlt').ne (congrArg Prod.fst he)
        · exact (hlt hlt').ne (congrArg Prod.fst he.symm)
      have himg : Finset.univ.image idx ⊆ S.filter (OuterTri up
          (y ⟨2 * i.1, by omega⟩) (y ⟨2 * i.1 + 1, by omega⟩)
          (y ⟨2 * i.1 + 2, by omega⟩) (y ⟨2 * i.1 + 3, by omega⟩)) := by
        intro q hq
        obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hq
        refine Finset.mem_filter.2 ⟨hC.1 _ (List.getElem_mem _), ?_, ?_, ?_, ?_, ?_⟩
        · dsimp only [y, idx]; exact isSeq_getElem_lt hC (by omega) (by omega) (by omega)
        · dsimp only [y, idx]; exact isSeq_getElem_lt hC (by omega) (by omega) (by omega)
        · dsimp only [y, idx]; exact isSeq_turn_getElem hC (by omega) (by omega) (by omega) (by omega) (by omega)
        · dsimp only [y, idx]; exact isSeq_turn_getElem hC (by omega) (by omega) (by omega) (by omega) (by omega)
        · dsimp only [y, idx]; exact isSeq_turn_getElem hC (by omega) (by omega) (by omega) (by omega) (by omega)
      have hcard : (Finset.univ.image idx).card = 5 := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      exact hcard ▸ Finset.card_le_card himg
    have hPcard_of : ∀ i : Fin k, X.card ≤ 2 * m ^ 2 * (P i).card := fun i =>
      hgood up
        (y ⟨2 * i.1, by omega⟩) (y ⟨2 * i.1 + 1, by omega⟩)
        (y ⟨2 * i.1 + 2, by omega⟩) (y ⟨2 * i.1 + 3, by omega⟩)
        (hyS _) (hyS _) (hyS _) (hyS _)
        (hysort _ _ (by show 2 * i.1 < 2 * i.1 + 1; omega))
        (hysort _ _ (by show 2 * i.1 + 1 < 2 * i.1 + 2; omega))
        (hysort _ _ (by show 2 * i.1 + 2 < 2 * i.1 + 3; omega))
        (h5_of i)
    refine ⟨P, fun i => Finset.filter_subset _ _, hPcard_of, ?_, ?_⟩
    · intro i j hij p hp q hq
      have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_filter.1 hq).2
      have hmid : (y ⟨2 * i.1 + 2, by omega⟩).1 < (y ⟨2 * j.1 + 1, by omega⟩).1 :=
        hysort _ _ (by show 2 * i.1 + 2 < 2 * j.1 + 1; omega)
      exact hp'.2.1.trans (hmid.trans hq'.1)
    · intro i j l hij hjl p hp q hq r hr
      have hPne : ∀ t : Fin k, (P t).Nonempty := by
        intro t
        have hpos : 0 < X.card := by omega
        have hle := hPcard_of t
        exact Finset.card_pos.1 (by
          by_contra h0
          have hz : (P t).card = 0 := by omega
          rw [hz, mul_zero] at hle
          omega)
      let f : Fin k → Point := fun t =>
        if t = i then p else if t = j then q else if t = l then r else (hPne t).choose
      have hfP : ∀ t, f t ∈ P t := by
        intro t
        by_cases hti : t = i
        · subst hti; simpa [f] using hp
        · by_cases htj : t = j
          · subst htj; simpa [f, hti] using hq
          · by_cases htl : t = l
            · subst htl; simpa [f, hti, htj] using hr
            · simpa [f, hti, htj, htl] using (hPne t).choose_spec
      obtain ⟨L, hL, hfL, -, -⟩ := isSeq_interleave k y f
        (fun j => hSX (hyS j)) (fun t => (Finset.mem_filter.1 (hfP t)).1) hysort
        (fun t => (Finset.mem_filter.1 (hfP t)).2)
      have hfi : f i = p := by simp [f]
      have hfj : f j = q := by simp [f, hij.ne']
      have hfl : f l = r := by simp [f, (hij.trans hjl).ne', hjl.ne']
      have hpq : p.1 < q.1 :=
        (Finset.mem_filter.1 hp).2.2.1.trans
          ((hysort _ _ (by show 2 * i.1 + 2 < 2 * j.1 + 1; omega)).trans
            (Finset.mem_filter.1 hq).2.1)
      have hqr : q.1 < r.1 :=
        (Finset.mem_filter.1 hq).2.2.1.trans
          ((hysort _ _ (by show 2 * j.1 + 2 < 2 * l.1 + 1; omega)).trans
            (Finset.mem_filter.1 hr).2.1)
      exact turn_of_mem hL (hfi ▸ hfL i) (hfj ▸ hfL j) (hfl ▸ hfL l) hpq hqr
  rcases hseq with h | h
  · obtain ⟨P, h1, h2, h3, h4⟩ := hbuild true h
    exact ⟨true, P, h1, hm_eq ▸ h2, h3, h4⟩
  · obtain ⟨P, h1, h2, h3, h4⟩ := hbuild false h
    exact ⟨false, P, h1, hm_eq ▸ h2, h3, h4⟩

/- ## Section 4: Mirsky's Theorem & Block-Chord Poset / Projective Chains -/

private lemma finset_chain_exists_max {α : Type*} (lt : α → α → Prop)
    (hirr : ∀ x, ¬ lt x x) (htrans : ∀ x y z, lt x y → lt y z → lt x z)
    (C : Finset α) (hCne : C.Nonempty)
    (hchain : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → lt x y ∨ lt y x) :
    ∃ x ∈ C, ∀ y ∈ C, ¬ lt x y := by
  induction C using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hCne).elim
  | insert a s ha ihs =>
    by_cases hs : s.Nonempty
    · obtain ⟨m, hm, hmax⟩ := ihs hs
        (fun x hx y hy hxy => hchain x (Finset.mem_insert_of_mem hx) y
          (Finset.mem_insert_of_mem hy) hxy)
      have ham : a ≠ m := fun h => ha (h ▸ hm)
      rcases hchain a (Finset.mem_insert_self _ _) m (Finset.mem_insert_of_mem hm) ham with hlt | hlt
      · refine ⟨m, Finset.mem_insert_of_mem hm, fun y hy hmy => ?_⟩
        rcases Finset.mem_insert.1 hy with hya | hys
        · rw [hya] at hmy; exact hirr a (htrans a m a hlt hmy)
        · exact hmax y hys hmy
      · refine ⟨a, Finset.mem_insert_self _ _, fun y hy hay => ?_⟩
        rcases Finset.mem_insert.1 hy with hya | hys
        · rw [hya] at hay; exact hirr a hay
        · exact hmax y hys (htrans m a y hlt hay)
    · rw [Finset.not_nonempty_iff_eq_empty.1 hs]
      exact ⟨a, Finset.mem_singleton_self a, fun y hy => by
        rw [Finset.mem_singleton.1 hy]; exact hirr a⟩

/-- Mirsky's theorem in pure Finset form: if every antichain has size ≤ W and every chain has
size ≤ H in a finite strict partial order, then `P.card ≤ W * H`. -/
private theorem mirsky {α : Type*} (lt : α → α → Prop)
    (hirr : ∀ x, ¬ lt x x) (htrans : ∀ x y z, lt x y → lt y z → lt x z)
    (P : Finset α) (W H : ℕ)
    (hW : ∀ A ⊆ P, (∀ x ∈ A, ∀ y ∈ A, ¬ lt x y) → A.card ≤ W)
    (hH : ∀ C ⊆ P, (∀ x ∈ C, ∀ y ∈ C, x ≠ y → lt x y ∨ lt y x) → C.card ≤ H) :
    P.card ≤ W * H := by
  induction H generalizing P with
  | zero =>
    suffices h0 : P = ∅ by simp [h0]
    by_contra hne
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have h1 := hH {x} (Finset.singleton_subset_iff.2 hx) (by simp)
    simp at h1
  | succ H ih =>
    let M := P.filter fun x => ∀ y ∈ P, ¬ lt x y
    have hMP : M ⊆ P := Finset.filter_subset _ _
    have hMcard : M.card ≤ W := hW M hMP (fun x hx y hy => (Finset.mem_filter.1 hx).2 y (hMP hy))
    have hRest : (P \ M).card ≤ W * H := by
      apply ih (P \ M)
      · exact fun A hA => hW A (hA.trans Finset.sdiff_subset)
      · intro C hC hchain
        by_cases hCe : C = ∅
        · simp [hCe]
        · have hCne : C.Nonempty := Finset.nonempty_iff_ne_empty.2 hCe
          obtain ⟨x, hxC, hxmax⟩ := finset_chain_exists_max lt hirr htrans C hCne hchain
          have hxPM := hC hxC
          have hxP : x ∈ P := (Finset.mem_sdiff.1 hxPM).1
          have hxnotM : x ∉ M := (Finset.mem_sdiff.1 hxPM).2
          have hexq : ∃ q ∈ P, lt x q := by
            by_contra hall
            push Not at hall
            exact hxnotM (Finset.mem_filter.2 ⟨hxP, hall⟩)
          obtain ⟨q, hqP, hxq⟩ := hexq
          have hqnotC : q ∉ C := fun hqC => hxmax q hqC hxq
          have hCq_chain : ∀ u ∈ insert q C, ∀ v ∈ insert q C, u ≠ v → lt u v ∨ lt v u := by
            intro u hu v hv huv
            rcases Finset.mem_insert.1 hu with huq | huC <;>
              rcases Finset.mem_insert.1 hv with hvq | hvC
            · exact (huv (huq.trans hvq.symm)).elim
            · right
              rw [huq]
              by_cases hvx : v = x
              · exact hvx ▸ hxq
              · rcases hchain v hvC x hxC hvx with hvx' | hxv'
                · exact htrans v x q hvx' hxq
                · exact (hxmax v hvC hxv').elim
            · left
              rw [hvq]
              by_cases hux : u = x
              · exact hux ▸ hxq
              · rcases hchain u huC x hxC hux with hux' | hxu'
                · exact htrans u x q hux' hxq
                · exact (hxmax u huC hxu').elim
            · exact hchain u huC v hvC huv
          have hle := hH (insert q C)
            (Finset.insert_subset_iff.2 ⟨hqP, hC.trans Finset.sdiff_subset⟩) hCq_chain
          rw [Finset.card_insert_of_notMem hqnotC] at hle
          omega
    have hsplit : P.card = M.card + (P \ M).card := by
      rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_right, Finset.union_sdiff_of_subset hMP]
    calc
      P.card = M.card + (P \ M).card := hsplit
      _ ≤ W + W * H := Nat.add_le_add hMcard hRest
      _ = W * (H + 1) := by ring

/-- Chord height `h(p) = - orient a p b > 0` for points strictly above segment `a b`. -/
private def chordH (a b p : Point) : ℝ := - orient a p b

/-- Chord partial order `p ≺ q` (`p ∈ int(△(a, q, b))`):
equivalent to `0 < orient a p q ∧ orient p q b < 0`. -/
private def chordLt (a b p q : Point) : Prop :=
  0 < orient a p q ∧ orient p q b < 0

private noncomputable def slopeFrom (a p : Point) : ℝ := (p.2 - a.2) / (p.1 - a.1)

private noncomputable def slopeTo (b p : Point) : ℝ := (p.2 - b.2) / (b.1 - p.1)

private lemma orient_eq_slopeFrom {a p q : Point} (hp : a.1 < p.1) (hq : a.1 < q.1) :
    orient a p q = (p.1 - a.1) * (q.1 - a.1) * (slopeFrom a q - slopeFrom a p) := by
  have hp' : p.1 - a.1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  have hq' : q.1 - a.1 ≠ 0 := sub_ne_zero.mpr hq.ne'
  unfold orient slopeFrom
  field_simp [hp', hq']
  ring

private lemma orient_eq_slopeTo {b p q : Point} (hp : p.1 < b.1) (hq : q.1 < b.1) :
    orient p q b = (b.1 - p.1) * (b.1 - q.1) * (slopeTo b p - slopeTo b q) := by
  have hp' : b.1 - p.1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  have hq' : b.1 - q.1 ≠ 0 := sub_ne_zero.mpr hq.ne'
  unfold orient slopeTo
  field_simp [hp', hq']
  ring

private lemma chordLt_iff_slopes {a b p q : Point}
    (hap : a.1 < p.1) (haq : a.1 < q.1) (hpb : p.1 < b.1) (hqb : q.1 < b.1) :
    chordLt a b p q ↔ slopeFrom a p < slopeFrom a q ∧ slopeTo b p < slopeTo b q := by
  unfold chordLt
  rw [orient_eq_slopeFrom hap haq, orient_eq_slopeTo hpb hqb]
  have h1 : 0 < (p.1 - a.1) * (q.1 - a.1) := mul_pos (sub_pos.2 hap) (sub_pos.2 haq)
  have h2 : 0 < (b.1 - p.1) * (b.1 - q.1) := mul_pos (sub_pos.2 hpb) (sub_pos.2 hqb)
  constructor
  · rintro ⟨hα, hβ⟩
    refine ⟨sub_pos.1 ((mul_pos_iff_of_pos_left h1).1 hα), ?_⟩
    have hlt : slopeTo b p - slopeTo b q < 0 := by nlinarith
    linarith
  · rintro ⟨hα, hβ⟩
    exact ⟨mul_pos h1 (sub_pos.2 hα), by nlinarith [mul_pos h2 (sub_pos.2 hβ)]⟩

private lemma chordLt_irrefl (a b p : Point) : ¬ chordLt a b p p := by
  rintro ⟨h, _⟩
  rw [orient_self_right] at h
  exact lt_irrefl 0 h

private lemma chordLt_trans {a b p q r : Point}
    (hap : a.1 < p.1) (haq : a.1 < q.1) (har : a.1 < r.1)
    (hpb : p.1 < b.1) (hqb : q.1 < b.1) (hrb : r.1 < b.1)
    (hpq : chordLt a b p q) (hqr : chordLt a b q r) : chordLt a b p r := by
  rw [chordLt_iff_slopes hap haq hpb hqb] at hpq
  rw [chordLt_iff_slopes haq har hqb hrb] at hqr
  rw [chordLt_iff_slopes hap har hpb hrb]
  exact ⟨hpq.1.trans hqr.1, hpq.2.trans hqr.2⟩

private lemma incomp_orient_neg {a b p q : Point}
    (hap : a.1 < p.1) (hpq : p.1 < q.1) (hqb : q.1 < b.1)
    (hqcap : orient a q b < 0)
    (hne1 : orient a p q ≠ 0) (hne2 : orient p q b ≠ 0)
    (h1 : ¬ chordLt a b p q) (h2 : ¬ chordLt a b q p) :
    orient a p q < 0 ∧ orient p q b < 0 := by
  rcases lt_or_gt_of_ne hne1 with hα | hα
  · rcases lt_or_gt_of_ne hne2 with hβ | hβ
    · exact ⟨hα, hβ⟩
    · exfalso
      apply h2
      constructor
      · rw [orient_swap]; linarith
      · rw [orient_swap_left]; linarith
  · rcases lt_or_gt_of_ne hne2 with hβ | hβ
    · exact (h1 ⟨hα, hβ⟩).elim
    · exfalso
      have hquad := (turn_quad hap hpq hqb
        (show turn true a p q by simpa [turn] using hα)
        (show turn true p q b by simpa [turn] using hβ)).2
      simp only [turn, ↓reduceIte] at hquad
      linarith

private lemma antichain_cap_supporting {a b : Point} {A : Finset Point} {l : List Point}
    (hA : ∀ p ∈ A, a.1 < p.1 ∧ p.1 < b.1 ∧ orient a p b < 0)
    (hgen1 : ∀ p ∈ A, ∀ q ∈ A, p.1 < q.1 → orient a p q ≠ 0)
    (hgen2 : ∀ p ∈ A, ∀ q ∈ A, p.1 < q.1 → orient p q b ≠ 0)
    (hanti : ∀ p ∈ A, ∀ q ∈ A, ¬ chordLt a b p q)
    (hl : IsSeq false A l) (hne : l ≠ []) :
    IsSeq false (insert a (insert b A)) (a :: l ++ [b]) := by
  have hlA : ∀ p ∈ l, p ∈ A := hl.1
  have hab : a.1 < b.1 := by
    obtain ⟨p, t, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hp := hA p (hlA p (by simp))
    linarith
  have hmem : ∀ p ∈ a :: l ++ [b], p ∈ insert a (insert b A) := by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · simp
    · rcases List.mem_append.1 hp with hp | hp
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hlA p hp))
      · simp [List.mem_singleton.1 hp]
  have hsort : (a :: l ++ [b]).Pairwise (fun p q => p.1 < q.1) := by
    refine List.pairwise_cons.2 ⟨?_, List.pairwise_append.2 ⟨hl.2.1, by simp, ?_⟩⟩
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact (hA q (hlA q hq)).1
      · simpa [List.mem_singleton.1 hq] using hab
    · intro p hp q hq
      simpa [List.mem_singleton.1 hq] using (hA p (hlA p hp)).2.1
  have hturns : turns false (a :: l ++ [b]) := by
    cases l with
    | nil => exact (hne rfl).elim
    | cons u t =>
      cases t with
      | nil =>
        have hu := hA u (hlA u (by simp))
        exact ⟨by simpa [turn] using hu.2.2, trivial⟩
      | cons v t =>
        have huA := hlA u (by simp)
        have hvA := hlA v (by simp)
        have huv : u.1 < v.1 := (List.pairwise_cons.1 hl.2.1).1 v (by simp)
        have hfirst := (incomp_orient_neg (hA u huA).1 huv (hA v hvA).2.1 (hA v hvA).2.2
          (hgen1 u huA v hvA huv) (hgen2 u huA v hvA huv)
          (hanti u huA v hvA) (hanti v hvA u huA)).1
        obtain ⟨pre, x, y, hxy⟩ := exists_suffix_two (show 2 ≤ (u :: v :: t).length by simp)
        have hxA : x ∈ A := hlA x (by rw [hxy]; simp)
        have hyA : y ∈ A := hlA y (by rw [hxy]; simp)
        have hxy_lt : x.1 < y.1 := by
          have hs := hl.2.1
          rw [hxy] at hs
          exact (List.pairwise_cons.1 (List.pairwise_append.1 hs).2.1).1 y (by simp)
        have hlast := (incomp_orient_neg (hA x hxA).1 hxy_lt (hA y hyA).2.1 (hA y hyA).2.2
          (hgen1 x hxA y hyA hxy_lt) (hgen2 x hxA y hyA hxy_lt)
          (hanti x hxA y hyA) (hanti y hyA x hxA)).2
        have ht_app : turns false ((u :: v :: t) ++ [b]) := by
          rw [hxy]
          have := turns_append (up := false) pre (hxy ▸ hl.2.2) (by simpa [turn] using hlast)
          simpa [List.append_assoc] using this
        change turn false a u v ∧ turns false (u :: v :: (t ++ [b]))
        exact ⟨by simpa [turn] using hfirst, by simpa using ht_app⟩
  exact ⟨hmem, hsort, hturns⟩

/-- Projective coordinate map sending line `a b` to infinity while preserving orientation signs
and mapping `chordLt a b`-chains to strictly `x`-increasing sequences. -/
private noncomputable def projMap (a b p : Point) : Point :=
  (-(1 / chordH a b p), -(p.1 / chordH a b p))

private lemma orient_projMap {a b p q r : Point}
    (hp : 0 < chordH a b p) (hq : 0 < chordH a b q) (hr : 0 < chordH a b r) :
    orient (projMap a b p) (projMap a b q) (projMap a b r) =
      ((b.1 - a.1) / (chordH a b p * chordH a b q * chordH a b r)) * orient p q r := by
  have hp' : chordH a b p ≠ 0 := hp.ne'
  have hq' : chordH a b q ≠ 0 := hq.ne'
  have hr' : chordH a b r ≠ 0 := hr.ne'
  unfold projMap
  simp only [orient]
  field_simp [hp', hq', hr']
  unfold chordH orient
  ring

private lemma chordH_lt_of_chordLt {a b p q : Point}
    (hap : a.1 < p.1) (haq : a.1 < q.1) (hpb : p.1 < b.1) (hqb : q.1 < b.1)
    (hp : 0 < chordH a b p) (hpq : chordLt a b p q) :
    chordH a b p < chordH a b q := by
  have hab : a.1 < b.1 := hap.trans hpb
  have hab' : 0 < b.1 - a.1 := sub_pos.2 hab
  have h1 : chordH a b p = (b.1 - a.1) * (p.1 - a.1) *
      (slopeFrom a p - (b.2 - a.2) / (b.1 - a.1)) := by
    have hpa' : p.1 - a.1 ≠ 0 := sub_ne_zero.mpr hap.ne'
    unfold chordH orient slopeFrom; field_simp [hpa', hab'.ne']; ring
  have h1q : chordH a b q = (b.1 - a.1) * (q.1 - a.1) *
      (slopeFrom a q - (b.2 - a.2) / (b.1 - a.1)) := by
    have hqa' : q.1 - a.1 ≠ 0 := sub_ne_zero.mpr haq.ne'
    unfold chordH orient slopeFrom; field_simp [hqa', hab'.ne']; ring
  have h2 : chordH a b p = (b.1 - a.1) * (b.1 - p.1) *
      (slopeTo b p + (b.2 - a.2) / (b.1 - a.1)) := by
    have hbp' : b.1 - p.1 ≠ 0 := sub_ne_zero.mpr hpb.ne'
    unfold chordH orient slopeTo; field_simp [hbp', hab'.ne']; ring
  have h2q : chordH a b q = (b.1 - a.1) * (b.1 - q.1) *
      (slopeTo b q + (b.2 - a.2) / (b.1 - a.1)) := by
    have hbq' : b.1 - q.1 ≠ 0 := sub_ne_zero.mpr hqb.ne'
    unfold chordH orient slopeTo; field_simp [hbq', hab'.ne']; ring
  obtain ⟨hα, hβ⟩ := (chordLt_iff_slopes hap haq hpb hqb).1 hpq
  rcases le_total p.1 q.1 with hle | hle
  · have hpos : 0 < slopeFrom a p - (b.2 - a.2) / (b.1 - a.1) := by
      rw [h1] at hp
      exact (mul_pos_iff_of_pos_left (mul_pos hab' (sub_pos.2 hap))).1 hp
    rw [h1, h1q]
    have hmul : (b.1 - a.1) * (p.1 - a.1) ≤ (b.1 - a.1) * (q.1 - a.1) :=
      mul_le_mul_of_nonneg_left (by linarith) hab'.le
    have hmul_pos : 0 < (b.1 - a.1) * (p.1 - a.1) := mul_pos hab' (sub_pos.2 hap)
    nlinarith
  · have hpos : 0 < slopeTo b p + (b.2 - a.2) / (b.1 - a.1) := by
      rw [h2] at hp
      exact (mul_pos_iff_of_pos_left (mul_pos hab' (sub_pos.2 hpb))).1 hp
    rw [h2, h2q]
    have hmul : (b.1 - a.1) * (b.1 - p.1) ≤ (b.1 - a.1) * (b.1 - q.1) :=
      mul_le_mul_of_nonneg_left (by linarith) hab'.le
    have hmul_pos : 0 < (b.1 - a.1) * (b.1 - p.1) := mul_pos hab' (sub_pos.2 hpb)
    nlinarith

private lemma projMap_fst_lt {a b p q : Point}
    (hap : a.1 < p.1) (haq : a.1 < q.1) (hpb : p.1 < b.1) (hqb : q.1 < b.1)
    (hp : 0 < chordH a b p) (hpq : chordLt a b p q) :
    (projMap a b p).1 < (projMap a b q).1 := by
  have hlt := chordH_lt_of_chordLt hap haq hpb hqb hp hpq
  have hq : 0 < chordH a b q := hp.trans hlt
  unfold projMap
  dsimp only
  have : 1 / chordH a b q < 1 / chordH a b p := one_div_lt_one_div_of_lt hp hlt
  linarith

/-- Plücker lemma for chain pairs on the left: if `p₁ ≺ p₂` in `P_i` and `q ∈ P_j` (`i < j`),
then `orient p₁ p₂ q < 0`. -/
private lemma orient_chain_left_right {a b p₁ p₂ q : Point}
    (hp₂cap : orient a p₂ b < 0)
    (h12 : chordLt a b p₁ p₂)
    (hcap1 : orient a p₂ q < 0) (hcap2 : orient p₂ q b < 0) :
    orient p₁ p₂ q < 0 := by
  have hpl := orient_plucker p₂ a b p₁ q
  have h_oab : 0 < orient p₂ a b := by rw [orient_swap_left]; linarith
  have h_oap : 0 < orient p₂ a p₁ := by rw [orient_cyclic]; exact h12.1
  have h_obq : 0 < orient p₂ b q := by rw [orient_swap]; linarith
  have h_oaq : 0 < orient p₂ a q := by rw [orient_swap_left]; linarith
  have h_obp : orient p₂ b p₁ < 0 := by rw [← orient_cyclic]; exact h12.2
  have hpos : 0 < orient p₂ p₁ q := by
    apply (mul_pos_iff_of_pos_left h_oab).1
    rw [hpl]
    nlinarith
  rw [orient_swap_left] at hpos
  linarith

/-- Plücker lemma for chain pairs on the right: if `q₁ ≺ q₂` in `P_j` and `p ∈ P_i` (`i < j`),
then `orient q₁ q₂ p > 0`. -/
private lemma orient_chain_right_left {a b q₁ q₂ p : Point}
    (hq₂cap : orient a q₂ b < 0)
    (h12 : chordLt a b q₁ q₂)
    (hcap1 : orient a p q₂ < 0) (hcap2 : orient p q₂ b < 0) :
    0 < orient q₁ q₂ p := by
  have hpl := orient_plucker q₂ a b q₁ p
  have h_oab : 0 < orient q₂ a b := by rw [orient_swap_left]; linarith
  have h_oaq : 0 < orient q₂ a q₁ := by rw [orient_cyclic]; exact h12.1
  have h_obp : orient q₂ b p < 0 := by rw [← orient_cyclic]; exact hcap2
  have h_oap : orient q₂ a p < 0 := by rw [orient_cyclic]; exact hcap1
  have h_obq : orient q₂ b q₁ < 0 := by rw [← orient_cyclic]; exact h12.2
  have hneg : orient q₂ q₁ p < 0 := by
    have hmul : orient q₂ a b * orient q₂ q₁ p < 0 := by rw [hpl]; nlinarith
    nlinarith
  rw [orient_swap_left] at hneg
  linarith

/-- Pullback of a `projMap`-sequence in a `chordLt`-chain back to original points. -/
private lemma pullback_proj_seq {a b : Point} {Q : Finset Point} {up : Bool} {l' : List Point}
    (hQ : ∀ p ∈ Q, a.1 < p.1 ∧ p.1 < b.1 ∧ orient a p b < 0)
    (hchain : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → chordLt a b p q ∨ chordLt a b q p)
    (hl' : IsSeq up (Q.image (projMap a b)) l') :
    ∃ l : List Point, l.length = l'.length ∧ (∀ p ∈ l, p ∈ Q) ∧ l.Nodup ∧
      (∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i < j → chordLt a b l[i] l[j]) ∧
      (∀ (i j k : ℕ) (hi : i < l.length) (hj : j < l.length) (hk : k < l.length),
        i < j → j < k → turn up l[i] l[j] l[k]) := by
  have hab : ∀ p ∈ Q, a.1 < b.1 := fun p hp => (hQ p hp).1.trans (hQ p hp).2.1
  have hHpos : ∀ p ∈ Q, 0 < chordH a b p := fun p hp => neg_pos.2 (hQ p hp).2.2
  have hproj_inj : Set.InjOn (fun p => (projMap a b p).1) (Q : Set Point) := by
    intro p hp q hq he
    by_contra hne
    rcases hchain p hp q hq hne with hlt | hlt
    · exact (projMap_fst_lt (hQ p hp).1 (hQ q hq).1 (hQ p hp).2.1 (hQ q hq).2.1
        (hHpos p hp) hlt).ne he
    · exact (projMap_fst_lt (hQ q hq).1 (hQ p hp).1 (hQ q hq).2.1 (hQ p hp).2.1
        (hHpos q hq) hlt).ne he.symm
  have hpick : ∀ w ∈ l', ∃ p ∈ Q, projMap a b p = w :=
    fun w hw => Finset.mem_image.1 (hl'.1 w hw)
  let l : List Point := l'.attach.map fun ⟨w, hw⟩ => (hpick w hw).choose
  have hlen : l.length = l'.length := by simp [l]
  have hlQ : ∀ p ∈ l, p ∈ Q := by
    intro p hp
    obtain ⟨⟨w, hw⟩, -, rfl⟩ := List.mem_map.1 hp
    exact (hpick w hw).choose_spec.1
  have hmap : ∀ (i : ℕ) (hi : i < l.length),
      projMap a b l[i] = l'[i]'(hlen ▸ hi) := by
    intro i hi
    simp only [l, List.getElem_map, List.getElem_attach]
    exact (hpick l'[i] (List.getElem_mem (hlen ▸ hi))).choose_spec.2
  have hlt_ord : ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i < j →
      chordLt a b l[i] l[j] := by
    intro i j hi hj hij
    have hfst : (projMap a b l[i]).1 < (projMap a b l[j]).1 := by
      rw [hmap i hi, hmap j hj]
      exact isSeq_getElem_lt hl' (hlen ▸ hi) (hlen ▸ hj) hij
    have hne : l[i] ≠ l[j] := fun he => hfst.ne (congrArg (fun p => (projMap a b p).1) he)
    have hiQ := hlQ _ (List.getElem_mem hi)
    have hjQ := hlQ _ (List.getElem_mem hj)
    rcases hchain _ hiQ _ hjQ hne with h1 | h2
    · exact h1
    · exfalso
      have hrev := projMap_fst_lt (hQ _ hjQ).1 (hQ _ hiQ).1 (hQ _ hjQ).2.1 (hQ _ hiQ).2.1
        (hHpos _ hjQ) h2
      linarith
  have hnodup : l.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro ⟨i, hi⟩ ⟨j, hj⟩ he
    have he' : l[i] = l[j] := he
    by_contra hne
    have hne' : i ≠ j := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with h1 | h1
    · have hlt := hlt_ord i j hi hj h1
      rw [← he'] at hlt
      exact chordLt_irrefl a b l[i] hlt
    · have hlt := hlt_ord j i hj hi h1
      rw [he'] at hlt
      exact chordLt_irrefl a b l[j] hlt
  have hturn : ∀ (i j k : ℕ) (hi : i < l.length) (hj : j < l.length) (hk : k < l.length),
      i < j → j < k → turn up l[i] l[j] l[k] := by
    intro i j k hi hj hk hij hjk
    have ht' := isSeq_turn_getElem hl' (hlen ▸ hi) (hlen ▸ hj) (hlen ▸ hk) hij hjk
    rw [← hmap i hi, ← hmap j hj, ← hmap k hk] at ht'
    have hiQ := hlQ _ (List.getElem_mem hi)
    have hjQ := hlQ _ (List.getElem_mem hj)
    have hkQ := hlQ _ (List.getElem_mem hk)
    have hfac : 0 < (b.1 - a.1) / (chordH a b l[i] * chordH a b l[j] * chordH a b l[k]) :=
      div_pos (sub_pos.2 (hab _ hiQ))
        (mul_pos (mul_pos (hHpos _ hiQ) (hHpos _ hjQ)) (hHpos _ hkQ))
    rw [turn_iff_signed] at ht' ⊢
    unfold signedOrient at ht' ⊢
    rw [orient_projMap (hHpos _ hiQ) (hHpos _ hjQ) (hHpos _ hkQ)] at ht'
    have heq : (if up then (1 : ℝ) else -1) *
        ((b.1 - a.1) / (chordH a b l[i] * chordH a b l[j] * chordH a b l[k]) *
          orient l[i] l[j] l[k]) =
        ((b.1 - a.1) / (chordH a b l[i] * chordH a b l[j] * chordH a b l[k])) *
          ((if up then (1 : ℝ) else -1) * orient l[i] l[j] l[k]) := by ring
    rw [heq] at ht'
    exact (mul_pos_iff_of_pos_left hfac).1 ht'
  exact ⟨l, hlen, hlQ, hnodup, hlt_ord, hturn⟩

/-- Convexity of the union `L_i ∪ R_j` of a left-arc in `Q_i` and a right-arc in `Q_j` (`i < j`). -/
private theorem chain_oval_convex {a b : Point} {Q₁ Q₂ : Finset Point}
    {L R : List Point}
    (hQ₁ : ∀ p ∈ Q₁, a.1 < p.1 ∧ p.1 < b.1 ∧ orient a p b < 0)
    (hQ₂ : ∀ q ∈ Q₂, a.1 < q.1 ∧ q.1 < b.1 ∧ orient a q b < 0)
    (hsep : ∀ p ∈ Q₁, ∀ q ∈ Q₂, p.1 < q.1)
    (hcap1 : ∀ p ∈ Q₁, ∀ q ∈ Q₂, orient a p q < 0)
    (hcap2 : ∀ p ∈ Q₁, ∀ q ∈ Q₂, orient p q b < 0)
    (hLQ : ∀ p ∈ L, p ∈ Q₁) (hLnd : L.Nodup)
    (hLlt : ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length), i < j → chordLt a b L[i] L[j])
    (hLturn : ∀ (i j k : ℕ) (hi : i < L.length) (hj : j < L.length) (hk : k < L.length),
      i < j → j < k → orient L[i] L[j] L[k] < 0)
    (hRQ : ∀ q ∈ R, q ∈ Q₂) (hRnd : R.Nodup)
    (hRlt : ∀ (i j : ℕ) (hi : i < R.length) (hj : j < R.length), i < j → chordLt a b R[i] R[j])
    (hRturn : ∀ (i j k : ℕ) (hi : i < R.length) (hj : j < R.length) (hk : k < R.length),
      i < j → j < k → 0 < orient R[i] R[j] R[k]) :
    IsConvexPlanar (L ++ R.reverse).toFinset ∧
      (L ++ R.reverse).toFinset.card = L.length + R.length := by
  have hdisj : List.Disjoint L R.reverse := by
    intro p hpL hpR
    have hp1 := hLQ p hpL
    have hp2 := hRQ p (List.mem_reverse.1 hpR)
    exact (lt_irrefl p.1) (hsep p hp1 p hp2)
  have hnd : (L ++ R.reverse).Nodup :=
    List.nodup_append.2 ⟨hLnd, List.nodup_reverse.2 hRnd, fun p hpL q hqR hpq => hdisj hpL (hpq ▸ hqR)⟩
  have hcard : (L ++ R.reverse).toFinset.card = L.length + R.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_append, List.length_reverse]
  refine ⟨isConvexPlanar_of_orient_neg hnd ?_, hcard⟩
  intro i j k hi hj hk hij hjk
  rw [List.length_append, List.length_reverse] at hi hj hk
  by_cases hiL : i < L.length
  · by_cases hjL : j < L.length
    · by_cases hkL : k < L.length
      · simp only [List.getElem_append_left hiL, List.getElem_append_left hjL,
          List.getElem_append_left hkL]
        exact hLturn i j k hiL hjL hkL hij hjk
      · simp only [List.getElem_append_left hiL, List.getElem_append_left hjL,
          List.getElem_append_right (Nat.le_of_not_lt hkL), List.getElem_reverse]
        have hq := hRQ _ (List.getElem_mem (show R.length - 1 - (k - L.length) < R.length by omega))
        have hp2 := hLQ _ (List.getElem_mem hjL)
        exact orient_chain_left_right (hQ₁ _ hp2).2.2 (hLlt i j hiL hjL hij)
          (hcap1 _ hp2 _ hq) (hcap2 _ hp2 _ hq)
    · have hkR : L.length ≤ k := by omega
      simp only [List.getElem_append_left hiL,
        List.getElem_append_right (Nat.le_of_not_lt hjL),
        List.getElem_append_right hkR, List.getElem_reverse]
      have hp := hLQ _ (List.getElem_mem hiL)
      have hq2 := hRQ _ (List.getElem_mem (show R.length - 1 - (j - L.length) < R.length by omega))
      have h12 := hRlt (R.length - 1 - (k - L.length)) (R.length - 1 - (j - L.length))
        (by omega) (by omega) (by omega)
      have hpos := orient_chain_right_left (hQ₂ _ hq2).2.2 h12
        (hcap1 _ hp _ hq2) (hcap2 _ hp _ hq2)
      rw [orient_rev]
      linarith
  · have hjR : L.length ≤ j := by omega
    have hkR : L.length ≤ k := by omega
    simp only [List.getElem_append_right (Nat.le_of_not_lt hiL),
      List.getElem_append_right hjR, List.getElem_append_right hkR, List.getElem_reverse]
    have hpos := hRturn (R.length - 1 - (k - L.length)) (R.length - 1 - (j - L.length))
      (R.length - 1 - (i - L.length)) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [orient_rev]
    linarith

/- ## Section 5: Block Assembly, Binomial Estimate, and Final Theorem -/

private lemma block_start_lt {M B r : ℕ} (hr : r < M) (hB : 0 < B) : r * B < M * B := by
  have : r + 1 ≤ M := hr
  nlinarith

private lemma block_idx_lt {M B r j : ℕ} (hr : r < M) (hj : j < B) : r * B + j < M * B := by
  have : r + 1 ≤ M := hr
  nlinarith

private lemma block_idx_lt_of_le {M B r i : ℕ} (hr : r < M) (hi : i < r * B + B) : i < M * B := by
  have : r + 1 ≤ M := hr
  nlinarith

private lemma prev_block_lt {t B : ℕ} (ht : 0 < t) (hB : 1 ≤ B) : (t - 1) * B + (B - 1) < t * B := by
  have : (t - 1) * B + B = t * B := by
    rw [← Nat.succ_mul]
    congr 1
    omega
  omega

/-- Concatenating `M` supporting caps `a_r :: C_r ++ [b_r]` across blocks produces one big cap. -/
private theorem concat_block_caps {X : Finset Point} {M B : ℕ} (hB : 3 ≤ B)
    (P : Fin (M * B) → Finset Point)
    (_hPX : ∀ i, P i ⊆ X)
    (hsep : ∀ i j : Fin (M * B), i < j → ∀ p ∈ P i, ∀ q ∈ P j, p.1 < q.1)
    (hcap : ∀ i j l : Fin (M * B), i < j → j < l →
      ∀ p ∈ P i, ∀ q ∈ P j, ∀ r ∈ P l, orient p q r < 0)
    (a b : Fin M → Point)
    (ha : ∀ r : Fin M, a r ∈ P ⟨r.1 * B, block_start_lt r.2 (by omega)⟩)
    (hb : ∀ r : Fin M, b r ∈ P ⟨r.1 * B + (B - 1), block_idx_lt r.2 (by omega)⟩)
    (C : Fin M → List Point)
    (hCidx : ∀ r : Fin M, ∃ (i : ℕ) (_ : r.1 * B < i) (_ : i < r.1 * B + (B - 1)),
      ∀ p ∈ C r, p ∈ P ⟨i, block_idx_lt_of_le r.2 (by omega)⟩)
    (hCne : ∀ r : Fin M, C r ≠ [])
    (hCseq : ∀ r : Fin M, IsSeq false X (a r :: C r ++ [b r])) :
    ∃ L : List Point, IsSeq false X L ∧ ∑ r : Fin M, (C r).length ≤ L.length := by
  have hgen : ∀ (t : ℕ) (ht : t ≤ M),
      ∃ L : List Point, IsSeq false X L ∧
        (∑ r : Fin t, (C ⟨r.1, by omega⟩).length) ≤ L.length ∧
        (∀ p ∈ L, ∀ r : Fin M, t ≤ r.1 → ∀ q ∈ P ⟨r.1 * B, block_start_lt r.2 (by omega)⟩, p.1 < q.1) ∧
        ((t = 0 ∧ L = []) ∨ ∃ (pre : List Point) (u : Point) (ht0 : 0 < t),
          L = pre ++ [u, b ⟨t - 1, by omega⟩] ∧
          ∃ (idx : ℕ) (_ : idx < (t - 1) * B + (B - 1)),
            u ∈ P ⟨idx, block_idx_lt_of_le (show t - 1 < M by omega) (by omega)⟩) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨[], ⟨by simp, by simp, trivial⟩, by simp, by simp, Or.inl ⟨rfl, rfl⟩⟩
    | succ t ih =>
      intro ht
      obtain ⟨L₀, hL₀, hlen₀, hleft₀, htail₀⟩ := ih (by omega)
      set r0 : Fin M := ⟨t, by omega⟩
      obtain ⟨i0, hi0l, hi0r, hCi0⟩ := hCidx r0
      have hCr0 := hCseq r0
      obtain ⟨u0, tail0, hCeq⟩ := List.exists_cons_of_ne_nil (hCne r0)
      have hu0P : u0 ∈ P ⟨i0, block_idx_lt_of_le r0.2 (by omega)⟩ := hCi0 u0 (by rw [hCeq]; simp)
      obtain ⟨pre1, x1, y1, hxy1⟩ := exists_suffix_two (show 2 ≤ (a r0 :: C r0 ++ [b r0]).length by
        simp [hCeq])
      have hy1_eq : y1 = b r0 := by
        have hlast := congrArg List.getLast? hxy1
        rw [List.getLast?_append_of_ne_nil _ (by simp),
          List.getLast?_append_of_ne_nil _ (by simp)] at hlast
        simp at hlast
        exact hlast.symm
      subst hy1_eq
      have hx1_in : x1 ∈ a r0 :: C r0 := by
        have hmem : x1 ∈ a r0 :: C r0 ++ [b r0] := by rw [hxy1]; simp
        have hlt : x1.1 < (b r0).1 := by
          have hs := hCr0.2.1; rw [hxy1] at hs
          exact (List.pairwise_cons.1 (List.pairwise_append.1 hs).2.1).1 (b r0) (by simp)
        rcases List.mem_cons.1 hmem with rfl | hmem
        · simp
        · rcases List.mem_append.1 hmem with hmem | hmem
          · exact List.mem_cons_of_mem _ hmem
          · exact (hlt.ne (congrArg Prod.fst (List.mem_singleton.1 hmem))).elim
      have hx1P : ∃ (idx : ℕ) (_ : idx < t * B + (B - 1)),
          x1 ∈ P ⟨idx, block_idx_lt_of_le (show t < M by omega) (by omega)⟩ := by
        rcases List.mem_cons.1 hx1_in with rfl | hxC
        · exact ⟨t * B, by omega, ha r0⟩
        · exact ⟨i0, hi0r, hCi0 x1 hxC⟩
      have hnew_left : ∀ p ∈ L₀ ++ (a r0 :: C r0 ++ [b r0]), ∀ r : Fin M, t + 1 ≤ r.1 →
          ∀ q ∈ P ⟨r.1 * B, block_start_lt r.2 (by omega)⟩, p.1 < q.1 := by
        intro p hp r hr q hq
        have htr : t * B + (B - 1) < r.1 * B := by
          have h1 : (t + 1) * B ≤ r.1 * B := Nat.mul_le_mul_right B hr
          have h2 : t * B + B = (t + 1) * B := by ring
          omega
        rcases List.mem_append.1 hp with hp | hp
        · exact hleft₀ p hp r (by omega) q hq
        · rcases List.mem_cons.1 hp with rfl | hp
          · exact hsep _ _ (by show t * B < r.1 * B; omega) _ (ha r0) _ hq
          · rcases List.mem_append.1 hp with hp | hp
            · exact hsep _ _ (by show i0 < r.1 * B; dsimp [r0] at hi0r; omega) _ (hCi0 p hp) _ hq
            · rw [List.mem_singleton.1 hp]
              exact hsep _ _ (by show t * B + (B - 1) < r.1 * B; exact htr) _ (hb r0) _ hq
      have hsum_step : ∑ r : Fin (t + 1), (C ⟨r.1, by omega⟩).length ≤
          (L₀ ++ (a r0 :: C r0 ++ [b r0])).length := by
        rw [Fin.sum_univ_castSucc, List.length_append]
        have hlen1 : (C r0).length ≤ (a r0 :: C r0 ++ [b r0]).length := by simp; omega
        exact Nat.add_le_add hlen₀ hlen1
      have hnew_tail : (t + 1 = 0 ∧ L₀ ++ (a r0 :: C r0 ++ [b r0]) = []) ∨
          ∃ (pre : List Point) (u : Point) (_ : 0 < t + 1),
          L₀ ++ (a r0 :: C r0 ++ [b r0]) = pre ++ [u, b ⟨t + 1 - 1, by omega⟩] ∧
          ∃ (idx : ℕ) (_ : idx < (t + 1 - 1) * B + (B - 1)),
            u ∈ P ⟨idx, block_idx_lt_of_le (show t + 1 - 1 < M by omega) (by omega)⟩ := by
        right
        refine ⟨L₀ ++ pre1, x1, by omega, ?_, ?_⟩
        · rw [hxy1, List.append_assoc]; rfl
        · simpa using hx1P
      have hseq_comb : IsSeq false X (L₀ ++ (a r0 :: C r0 ++ [b r0])) := by
        rcases htail₀ with ⟨ht0, hL0nil⟩ | ⟨pre0, u_prev, ht0, hL₀eq, idx_prev, hidx_prev, hu_prev⟩
        · subst hL0nil; simpa using hCr0
        · refine ⟨?_, ?_, ?_⟩
          · intro p hp
            rcases List.mem_append.1 hp with hp | hp
            · exact hL₀.1 p hp
            · exact hCr0.1 p hp
          · refine List.pairwise_append.2 ⟨hL₀.2.1, hCr0.2.1, ?_⟩
            intro p hp q hq
            have hpa : p.1 < (a r0).1 := hleft₀ p hp r0 (le_refl t) (a r0) (ha r0)
            rcases List.mem_cons.1 hq with rfl | hq
            · exact hpa
            · exact hpa.trans ((List.pairwise_cons.1 hCr0.2.1).1 q hq)
          · have hprev_lt : (t - 1) * B + (B - 1) < t * B := prev_block_lt ht0 (by omega)
            have ht1 : turn false u_prev (b ⟨t - 1, by omega⟩) (a r0) := by
              change orient u_prev (b ⟨t - 1, by omega⟩) (a r0) < 0
              exact hcap ⟨idx_prev, block_idx_lt_of_le (show t - 1 < M by omega) (by omega)⟩
                ⟨(t - 1) * B + (B - 1), block_idx_lt (show t - 1 < M by omega) (by omega)⟩
                ⟨t * B, block_start_lt r0.2 (by omega)⟩
                (by show idx_prev < (t - 1) * B + (B - 1); omega)
                (by show (t - 1) * B + (B - 1) < t * B; exact hprev_lt)
                _ hu_prev _ (hb _) _ (ha r0)
            have ht2 : turn false (b ⟨t - 1, by omega⟩) (a r0) u0 := by
              change orient (b ⟨t - 1, by omega⟩) (a r0) u0 < 0
              exact hcap ⟨(t - 1) * B + (B - 1), block_idx_lt (show t - 1 < M by omega) (by omega)⟩
                ⟨t * B, block_start_lt r0.2 (by omega)⟩
                ⟨i0, block_idx_lt_of_le r0.2 (by omega)⟩
                (by show (t - 1) * B + (B - 1) < t * B; exact hprev_lt)
                (by show t * B < i0; exact hi0l)
                _ (hb _) _ (ha r0) _ hu0P
            have hturns_join : ∀ (l₁ : List Point) (x y z w : Point) (l₂ : List Point),
                turns false (l₁ ++ [x, y]) → turns false (z :: w :: l₂) →
                turn false x y z → turn false y z w →
                turns false ((l₁ ++ [x, y]) ++ z :: w :: l₂) := by
              intro l₁ x y z w l₂ h1 h2 hxyz hyzw
              induction l₁ with
              | nil => exact ⟨hxyz, hyzw, h2⟩
              | cons v l₁ ihl =>
                obtain ⟨a1, rest1, h1eq⟩ := List.exists_cons_of_ne_nil (by simp : l₁ ++ [x, y] ≠ [])
                obtain ⟨a2, rest2, h2eq⟩ : ∃ a2 rest2, rest1 = a2 :: rest2 := by
                  apply List.exists_cons_of_ne_nil
                  intro hnil
                  have hlen := congrArg List.length h1eq
                  simp [hnil] at hlen
                have h12 : l₁ ++ [x, y] = a1 :: a2 :: rest2 := by rw [h1eq, h2eq]
                have h1' : turn false v a1 a2 ∧ turns false (a1 :: a2 :: rest2) := by
                  rw [List.cons_append, h12] at h1
                  exact h1
                have htail : turns false ((l₁ ++ [x, y]) ++ z :: w :: l₂) :=
                  ihl (by rw [h12]; exact h1'.2)
                rw [List.cons_append, List.cons_append, h12, List.cons_append, List.cons_append]
                exact ⟨h1'.1, by rw [h12, List.cons_append, List.cons_append] at htail; exact htail⟩
            rw [hL₀eq, hCeq]
            exact hturns_join pre0 u_prev (b ⟨t - 1, by omega⟩) (a r0) u0 (tail0 ++ [b r0])
              (hL₀eq ▸ hL₀.2.2) (by simpa [hCeq] using hCr0.2.2) ht1 ht2
      exact ⟨L₀ ++ (a r0 :: C r0 ++ [b r0]), hseq_comb, hsum_step, hnew_left, hnew_tail⟩
  obtain ⟨L, hL, hlen, -, -⟩ := hgen M le_rfl
  exact ⟨L, hL, hlen⟩

/-- Elementary binomial bound: `(a + b).choose b ≤ M^b * (1 + 1/M)^(a + b)` for `M ≥ 1`. -/
private lemma choose_le_pow_mul_one_add (a b M : ℕ) (hM : 1 ≤ M) :
    ((a + b).choose b : ℝ) ≤ (M : ℝ) ^ b * (1 + 1 / (M : ℝ)) ^ (a + b) := by
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 (by omega)
  have hxpos : (0 : ℝ) < 1 / (M : ℝ) := one_div_pos.2 hMpos
  have hpow : ((a + b).choose b : ℝ) * (1 / (M : ℝ)) ^ b ≤ (1 + 1 / (M : ℝ)) ^ (a + b) := by
    rw [add_comm (1 : ℝ), add_pow]
    have hmem : b ∈ Finset.range (a + b + 1) := Finset.mem_range.2 (by omega)
    have hle := Finset.single_le_sum
      (f := fun k => (1 / (M : ℝ)) ^ k * (1 : ℝ) ^ (a + b - k) * ((a + b).choose k : ℝ))
      (fun k _ => by positivity) hmem
    simpa [mul_comm] using hle
  have hinv : (M : ℝ) ^ b * (1 / (M : ℝ)) ^ b = 1 := by
    rw [← mul_pow, mul_one_div_cancel hMpos.ne', one_pow]
  calc
    ((a + b).choose b : ℝ) = ((a + b).choose b : ℝ) * ((M : ℝ) ^ b * (1 / (M : ℝ)) ^ b) := by
      rw [hinv, mul_one]
    _ = (M : ℝ) ^ b * (((a + b).choose b : ℝ) * (1 / (M : ℝ)) ^ b) := by ring
    _ ≤ (M : ℝ) ^ b * (1 + 1 / (M : ℝ)) ^ (a + b) := mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Core block-chord upper bound: if `M * B` sets in cap position each have size ≥ `L`
and `X` contains no convex `n`-gon (`n ≥ 2 * M`, `B ≥ 5`), then
`L ≤ (n + m).choose m * 2^(n + n / (B - 4))` where `m = (n + M - 1) / M`. -/
private theorem block_chord_bound {X : Finset Point} {M B n L : ℕ}
    (hM : 1 ≤ M) (hB : 5 ≤ B) (hn : 2 * M ≤ n)
    (hx : Set.InjOn Prod.fst (X : Set Point))
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
    (hno : ¬ ∃ Y ⊆ X, Y.card = n ∧ IsConvexPlanar Y)
    (P : Fin (M * B) → Finset Point)
    (hPX : ∀ i, P i ⊆ X)
    (hPL : ∀ i, L ≤ (P i).card)
    (hsep : ∀ i j : Fin (M * B), i < j → ∀ p ∈ P i, ∀ q ∈ P j, p.1 < q.1)
    (hcap : ∀ i j l : Fin (M * B), i < j → j < l →
      ∀ p ∈ P i, ∀ q ∈ P j, ∀ r ∈ P l, orient p q r < 0) :
    (L : ℝ) ≤ (((n + (n + M - 1) / M).choose ((n + M - 1) / M) : ℕ) : ℝ) *
      (2 : ℝ) ^ ((n : ℝ) + (n : ℝ) / ((B - 4 : ℕ) : ℝ)) := by
  by_cases hL0 : L = 0
  · subst hL0; simp only [Nat.cast_zero]; positivity
  have hPne : ∀ i : Fin (M * B), (P i).Nonempty := fun i =>
    Finset.card_pos.1 (lt_of_lt_of_le (Nat.pos_of_ne_zero hL0) (hPL i))
  let a : Fin M → Point := fun r => (hPne ⟨r.1 * B, block_start_lt r.2 (by omega)⟩).choose
  let b : Fin M → Point := fun r => (hPne ⟨r.1 * B + (B - 1), block_idx_lt r.2 (by omega)⟩).choose
  have ha : ∀ r : Fin M, a r ∈ P ⟨r.1 * B, block_start_lt r.2 (by omega)⟩ := fun r => (hPne _).choose_spec
  have hb : ∀ r : Fin M, b r ∈ P ⟨r.1 * B + (B - 1), block_idx_lt r.2 (by omega)⟩ := fun r => (hPne _).choose_spec
  let m : ℕ := (n + M - 1) / M
  have hm2 : 2 ≤ m := by
    dsimp [m]
    exact Nat.le_div_iff_mul_le (by omega) |>.2 (by omega)
  have hMm : n ≤ M * m := by
    dsimp [m]
    have hdiv := Nat.div_add_mod (n + M - 1) M
    have hmod := Nat.mod_lt (n + M - 1) (show 0 < M by omega)
    omega
  -- Step 1: Some block `r*` has no supporting `m`-cap in any interior part's antichain
  have hgood_block : ∃ r : Fin M, ∀ (j : ℕ) (hj1 : r.1 * B < j) (hj2 : j < r.1 * B + (B - 1)),
      ∀ A ⊆ P ⟨j, block_idx_lt_of_le r.2 (by omega)⟩,
        (∀ x ∈ A, ∀ y ∈ A, ¬ chordLt (a r) (b r) x y) → ¬ HasSeq false A m := by
    by_contra hall
    push Not at hall
    choose idx hidx1 hidx2 A hAP hAanti C hC hClen using hall
    have hCne : ∀ r : Fin M, C r ≠ [] := fun r h => by
      have := hClen r; rw [h] at this; simp at this; omega
    have hCsupp : ∀ r : Fin M, IsSeq false X (a r :: C r ++ [b r]) := by
      intro r
      have hAr : ∀ p ∈ A r, (a r).1 < p.1 ∧ p.1 < (b r).1 ∧ orient (a r) p (b r) < 0 := by
        intro p hp
        have hpP := hAP r hp
        exact ⟨hsep _ _ (by show r.1 * B < idx r; exact hidx1 r) _ (ha r) _ hpP,
          hsep _ _ (by show idx r < r.1 * B + (B - 1); exact hidx2 r) _ hpP _ (hb r),
          hcap _ _ _ (by show r.1 * B < idx r; exact hidx1 r)
            (by show idx r < r.1 * B + (B - 1); exact hidx2 r) _ (ha r) _ hpP _ (hb r)⟩
      have hsub := antichain_cap_supporting hAr
        (fun p hp q hq hpq => hgen _ (hPX _ (ha r)) _ (hPX _ (hAP r hp)) _ (hPX _ (hAP r hq))
          (hAr p hp).1 hpq)
        (fun p hp q hq hpq => hgen _ (hPX _ (hAP r hp)) _ (hPX _ (hAP r hq)) _ (hPX _ (hb r))
          hpq (hAr q hq).2.1)
        (hAanti r) (hC r) (hCne r)
      refine isSeq_mono hsub ?_
      exact Finset.insert_subset_iff.2 ⟨hPX _ (ha r),
        Finset.insert_subset_iff.2 ⟨hPX _ (hb r), (hAP r).trans (hPX _)⟩⟩
    obtain ⟨BigCap, hBigCap, hBigLen⟩ := concat_block_caps (by omega : 3 ≤ B) P hPX hsep hcap
      a b ha hb C
      (fun r => ⟨idx r, hidx1 r, hidx2 r, fun p hp => hAP r ((hC r).1 p hp)⟩)
      hCne hCsupp
    have hlen_ge : n ≤ BigCap.length := by
      have hsum : ∑ r : Fin M, (C r).length = M * m := by
        simp [hClen]
      exact hMm.trans (hsum ▸ hBigLen)
    exact hno (exists_convex_of_hasSeq ⟨BigCap, hBigCap, rfl⟩ hlen_ge)
  obtain ⟨rstar, hrstar⟩ := hgood_block
  set a0 := a rstar
  set b0 := b rstar
  let W : ℕ := (n + m).choose m
  -- Step 2: Every interior part `P_j` of block `rstar` has every antichain of size ≤ W,
  -- hence by Mirsky contains a `chordLt`-chain `Q_j` with `L ≤ W * Q_j.card`.
  have hQexists : ∀ t : Fin (B - 2),
      ∃ Q ⊆ P ⟨rstar.1 * B + 1 + t.1, block_idx_lt_of_le rstar.2 (by omega)⟩,
      (∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → chordLt a0 b0 p q ∨ chordLt a0 b0 q p) ∧
      L ≤ W * Q.card := by
    intro t
    set j : Fin (M * B) := ⟨rstar.1 * B + 1 + t.1, block_idx_lt_of_le rstar.2 (by omega)⟩
    have hj1 : rstar.1 * B < j.1 := by dsimp [j]; omega
    have hj2 : j.1 < rstar.1 * B + (B - 1) := by dsimp [j]; omega
    have hPgeom : ∀ p ∈ P j, a0.1 < p.1 ∧ p.1 < b0.1 ∧ orient a0 p b0 < 0 := fun p hp =>
      ⟨hsep _ _ hj1 _ (ha rstar) _ hp, hsep _ _ hj2 _ hp _ (hb rstar),
        hcap _ _ _ hj1 hj2 _ (ha rstar) _ hp _ (hb rstar)⟩
    have hantiW : ∀ A ⊆ P j, (∀ p ∈ A, ∀ q ∈ A, ¬ chordLt a0 b0 p q) → A.card ≤ W := by
      intro A hAP hanti
      have hnocap : ¬ HasSeq false A m := hrstar j.1 hj1 hj2 A hAP hanti
      have hnocup : ¬ HasSeq true A n := fun hcup =>
        hno (exists_convex_of_hasSeq
          (by obtain ⟨l, hl, hlen⟩ := hcup; exact ⟨l, isSeq_mono hl (hAP.trans (hPX j)), hlen⟩)
          le_rfl)
      have hle := card_le_binomial (n - 2) (m - 2) A (hx.mono (hAP.trans (hPX j)))
        (fun x hxA y hyA z hzA hxy hyz =>
          hgen x (hPX j (hAP hxA)) y (hPX j (hAP hyA)) z (hPX j (hAP hzA)) hxy hyz)
        (by rwa [show n - 2 + 2 = n by omega])
        (by rwa [show m - 2 + 2 = m by omega])
      have hch : (n - 2 + (m - 2)).choose (n - 2) ≤ W := by
        dsimp [W]
        rw [← Nat.choose_symm (by omega : n - 2 ≤ n - 2 + (m - 2)),
          show n - 2 + (m - 2) - (n - 2) = m - 2 by omega]
        calc
          (n - 2 + (m - 2)).choose (m - 2) ≤ (n + m - 2).choose (m - 2) :=
            Nat.choose_le_choose (m - 2) (by omega)
          _ ≤ (n + m).choose m := by
            have h1 : (n + m - 2).choose (m - 2) ≤ (n + m - 1).choose (m - 1) := by
              have := Nat.choose_succ_succ (n + m - 2) (m - 2)
              simp only [Nat.succ_eq_add_one] at this
              rw [show n + m - 2 + 1 = n + m - 1 by omega, show m - 2 + 1 = m - 1 by omega] at this
              omega
            have h2 : (n + m - 1).choose (m - 1) ≤ (n + m).choose m := by
              have := Nat.choose_succ_succ (n + m - 1) (m - 1)
              simp only [Nat.succ_eq_add_one] at this
              rw [show n + m - 1 + 1 = n + m by omega, show m - 1 + 1 = m by omega] at this
              omega
            exact h1.trans h2
      exact hle.trans hch
    by_contra hnoQ
    push Not at hnoQ
    let Hmax : ℕ := (L - 1) / W
    have hHbound : ∀ C ⊆ P j,
        (∀ p ∈ C, ∀ q ∈ C, p ≠ q → chordLt a0 b0 p q ∨ chordLt a0 b0 q p) → C.card ≤ Hmax := by
      intro C hCP hCchain
      have hlt : W * C.card < L := hnoQ C hCP hCchain
      have hWpos : 0 < W := Nat.choose_pos (by omega)
      have hle1 : W * C.card ≤ L - 1 := by omega
      exact (Nat.le_div_iff_mul_le hWpos).2 (by rw [mul_comm]; exact hle1)
    have hmir := mirsky (fun p q : {p // p ∈ P j} => chordLt a0 b0 p.1 q.1)
      (fun x => chordLt_irrefl a0 b0 x.1)
      (fun x y z => chordLt_trans (hPgeom x.1 x.2).1 (hPgeom y.1 y.2).1 (hPgeom z.1 z.2).1
        (hPgeom x.1 x.2).2.1 (hPgeom y.1 y.2).2.1 (hPgeom z.1 z.2).2.1)
      Finset.univ W Hmax
      (fun A _ hA => by
        have hcard : (A.image Subtype.val).card = A.card :=
          Finset.card_image_of_injective _ Subtype.val_injective
        rw [← hcard]
        apply hantiW (A.image Subtype.val)
        · intro p hp; obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hp; exact x.2
        · intro p hp q hq
          obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.1 hp
          obtain ⟨y, hyA, rfl⟩ := Finset.mem_image.1 hq
          exact hA x hxA y hyA)
      (fun C _ hC => by
        have hcard : (C.image Subtype.val).card = C.card :=
          Finset.card_image_of_injective _ Subtype.val_injective
        rw [← hcard]
        apply hHbound (C.image Subtype.val)
        · intro p hp; obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hp; exact x.2
        · intro p hp q hq hpq
          obtain ⟨x, hxC, rfl⟩ := Finset.mem_image.1 hp
          obtain ⟨y, hyC, rfl⟩ := Finset.mem_image.1 hq
          exact hC x hxC y hyC (fun h => hpq (congrArg Subtype.val h)))
    rw [Finset.card_univ, Fintype.card_coe] at hmir
    have hWpos : 0 < W := Nat.choose_pos (by omega)
    have hWH : W * Hmax < L := by
      have hL1 : 1 ≤ L := Nat.pos_of_ne_zero hL0
      have := Nat.mul_div_le (L - 1) W
      dsimp [Hmax]
      omega
    exact (not_lt_of_ge ((hPL j).trans hmir)) hWH
  choose Q hQP hQchain hQL using hQexists
  -- Step 3: For each interior chain `Q t`, measure max left-arc `la t` and max right-arc `rb t`
  -- in `projMap a0 b0 (Q t)`
  have hmax_arc : ∀ (up : Bool) (t : Fin (B - 2)),
      ∃ c : ℕ, 1 ≤ c ∧ c < n ∧
        HasSeq up ((Q t).image (projMap a0 b0)) c ∧
        ¬ HasSeq up ((Q t).image (projMap a0 b0)) (c + 1) := by
    intro up t
    set j : Fin (M * B) := ⟨rstar.1 * B + 1 + t.1, block_idx_lt_of_le rstar.2 (by omega)⟩
    have hj1 : rstar.1 * B < j.1 := by dsimp [j]; omega
    have hj2 : j.1 < rstar.1 * B + (B - 1) := by dsimp [j]; omega
    have hQgeom : ∀ p ∈ Q t, a0.1 < p.1 ∧ p.1 < b0.1 ∧ orient a0 p b0 < 0 := fun p hp =>
      ⟨hsep _ _ hj1 _ (ha rstar) _ (hQP t hp), hsep _ _ hj2 _ (hQP t hp) _ (hb rstar),
        hcap _ _ _ hj1 hj2 _ (ha rstar) _ (hQP t hp) _ (hb rstar)⟩
    have hno_n : ¬ HasSeq up ((Q t).image (projMap a0 b0)) n := by
      rintro ⟨l', hl', hlen'⟩
      obtain ⟨l, hlen, hlQ, hnd, -, hturn⟩ := pullback_proj_seq hQgeom (hQchain t) hl'
      apply hno
      cases up with
      | false =>
        refine ⟨l.toFinset, fun p hp => hPX j (hQP t (hlQ p (List.mem_toFinset.1 hp))),
          (List.toFinset_card_of_nodup hnd).trans (hlen.trans hlen'),
          isConvexPlanar_of_orient_neg hnd fun i₁ i₂ i₃ hi₁ hi₂ hi₃ h12 h23 =>
            by simpa [turn] using hturn i₁ i₂ i₃ hi₁ hi₂ hi₃ h12 h23⟩
      | true =>
        refine ⟨l.reverse.toFinset,
          fun p hp => hPX j (hQP t (hlQ p (List.mem_reverse.1 (List.mem_toFinset.1 hp)))),
          (List.toFinset_card_of_nodup (List.nodup_reverse.2 hnd)).trans
            (by rw [List.length_reverse, hlen, hlen']),
          isConvexPlanar_of_orient_neg (List.nodup_reverse.2 hnd)
            fun i₁ i₂ i₃ hi₁ hi₂ hi₃ h12 h23 => by
              rw [List.length_reverse] at hi₁ hi₂ hi₃
              simp only [List.getElem_reverse]
              have ht := hturn (l.length - 1 - i₃) (l.length - 1 - i₂) (l.length - 1 - i₁)
                (by omega) (by omega) (by omega) (by omega) (by omega)
              simp only [turn, ↓reduceIte] at ht
              rw [orient_rev]; linarith⟩
    have h1 : HasSeq up ((Q t).image (projMap a0 b0)) 1 := by
      have hQne : (Q t).Nonempty := Finset.card_pos.1 (by
        by_contra h0
        have hz : (Q t).card = 0 := by omega
        have := hQL t; rw [hz, mul_zero] at this; omega)
      obtain ⟨p, hp⟩ := hQne
      exact ⟨[projMap a0 b0 p], ⟨fun q hq => by
        rw [List.mem_singleton.1 hq]; exact Finset.mem_image_of_mem _ hp, by simp, trivial⟩, rfl⟩
    let S := (Finset.range n).filter fun c => HasSeq up ((Q t).image (projMap a0 b0)) c
    have hSne : S.Nonempty := ⟨1, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), h1⟩⟩
    obtain ⟨c, hcS, hcmax⟩ := Finset.exists_max_image S id hSne
    obtain ⟨hcrange, hcseq⟩ := Finset.mem_filter.1 hcS
    have hc1 : 1 ≤ c := hcmax 1 (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), h1⟩)
    have hcn : c < n := Finset.mem_range.1 hcrange
    refine ⟨c, hc1, hcn, hcseq, fun hc1seq => ?_⟩
    by_cases hcn1 : c + 1 < n
    · have := hcmax (c + 1) (Finset.mem_filter.2 ⟨Finset.mem_range.2 hcn1, hc1seq⟩)
      dsimp at this; omega
    · have heq : c + 1 = n := by omega
      exact hno_n (heq ▸ hc1seq)
  choose la hla1 _ hla_has hla_no using hmax_arc false
  choose rb hrb1 _ hrb_has hrb_no using hmax_arc true
  -- Step 4: Cross-oval bound `la t₁ + rb t₂ < n` for all `t₁ < t₂`
  have hcross : ∀ t₁ t₂ : Fin (B - 2), t₁ < t₂ → la t₁ + rb t₂ < n := by
    intro t₁ t₂ ht12
    by_contra hge
    have hge' : n ≤ la t₁ + rb t₂ := Nat.le_of_not_lt hge
    set j₁ : Fin (M * B) := ⟨rstar.1 * B + 1 + t₁.1, block_idx_lt_of_le rstar.2 (by omega)⟩
    set j₂ : Fin (M * B) := ⟨rstar.1 * B + 1 + t₂.1, block_idx_lt_of_le rstar.2 (by omega)⟩
    have hj12 : j₁ < j₂ := by show rstar.1 * B + 1 + t₁.1 < rstar.1 * B + 1 + t₂.1; omega
    have hQ₁ : ∀ p ∈ Q t₁, a0.1 < p.1 ∧ p.1 < b0.1 ∧ orient a0 p b0 < 0 := fun p hp =>
      ⟨hsep _ _ (by show rstar.1 * B < j₁.1; dsimp [j₁]; omega) _ (ha rstar) _ (hQP t₁ hp),
        hsep _ _ (by show j₁.1 < rstar.1 * B + (B - 1); dsimp [j₁]; omega) _ (hQP t₁ hp) _ (hb rstar),
        hcap _ _ _ (by show rstar.1 * B < j₁.1; dsimp [j₁]; omega)
          (by show j₁.1 < rstar.1 * B + (B - 1); dsimp [j₁]; omega)
          _ (ha rstar) _ (hQP t₁ hp) _ (hb rstar)⟩
    have hQ₂ : ∀ q ∈ Q t₂, a0.1 < q.1 ∧ q.1 < b0.1 ∧ orient a0 q b0 < 0 := fun q hq =>
      ⟨hsep _ _ (by show rstar.1 * B < j₂.1; dsimp [j₂]; omega) _ (ha rstar) _ (hQP t₂ hq),
        hsep _ _ (by show j₂.1 < rstar.1 * B + (B - 1); dsimp [j₂]; omega) _ (hQP t₂ hq) _ (hb rstar),
        hcap _ _ _ (by show rstar.1 * B < j₂.1; dsimp [j₂]; omega)
          (by show j₂.1 < rstar.1 * B + (B - 1); dsimp [j₂]; omega)
          _ (ha rstar) _ (hQP t₂ hq) _ (hb rstar)⟩
    obtain ⟨L', hL', hL'len⟩ := hla_has t₁
    obtain ⟨R', hR', hR'len⟩ := hrb_has t₂
    obtain ⟨L, hLlen, hLQ, hLnd, hLlt, hLturn⟩ := pullback_proj_seq hQ₁ (hQchain t₁) hL'
    obtain ⟨R, hRlen, hRQ, hRnd, hRlt, hRturn⟩ := pullback_proj_seq hQ₂ (hQchain t₂) hR'
    obtain ⟨hconv, hcard⟩ := chain_oval_convex hQ₁ hQ₂
      (fun p hp q hq => hsep j₁ j₂ hj12 p (hQP t₁ hp) q (hQP t₂ hq))
      (fun p hp q hq => hcap _ j₁ j₂ (by show rstar.1 * B < j₁.1; dsimp [j₁]; omega) hj12
        _ (ha rstar) p (hQP t₁ hp) q (hQP t₂ hq))
      (fun p hp q hq => hcap j₁ j₂ _ hj12
        (by show j₂.1 < rstar.1 * B + (B - 1); dsimp [j₂]; omega)
        p (hQP t₁ hp) q (hQP t₂ hq) _ (hb rstar))
      hLQ hLnd hLlt (fun i₁ i₂ i₃ hi₁ hi₂ hi₃ h12 h23 =>
        by simpa [turn] using hLturn i₁ i₂ i₃ hi₁ hi₂ hi₃ h12 h23)
      hRQ hRnd hRlt (fun i₁ i₂ i₃ hi₁ hi₂ hi₃ h12 h23 =>
        by simpa [turn] using hRturn i₁ i₂ i₃ hi₁ hi₂ hi₃ h12 h23)
    have hsubX : (L ++ R.reverse).toFinset ⊆ X := by
      intro p hp
      rcases List.mem_append.1 (List.mem_toFinset.1 hp) with hpL | hpR
      · exact hPX j₁ (hQP t₁ (hLQ p hpL))
      · exact hPX j₂ (hQP t₂ (hRQ p (List.mem_reverse.1 hpR)))
    have hcard_ge : n ≤ (L ++ R.reverse).toFinset.card := by
      rw [hcard, hLlen, hRlen, hL'len, hR'len]; exact hge'
    obtain ⟨Y, hYsub, hYc⟩ := Finset.exists_subset_card_eq hcard_ge
    exact hno ⟨Y, hYsub.trans hsubX, hYc, isConvexPlanar_subset hconv hYsub⟩
  -- Step 5: Telescoping sum over `B - 4 ≥ 1` middle indices gives `t*` with
  -- `(B - 4) * (la t* + rb t*) ≤ (B - 3) * n`
  have hteles : ∃ tstar : Fin (B - 2), (B - 4) * (la tstar + rb tstar) ≤ (B - 3) * n := by
    have hsum_le : ∑ s : Fin (B - 3), (la ⟨s.1, by omega⟩ + rb ⟨s.1 + 1, by omega⟩) ≤
        (B - 3) * n := by
      calc
        ∑ s : Fin (B - 3), (la ⟨s.1, by omega⟩ + rb ⟨s.1 + 1, by omega⟩)
          ≤ ∑ _s : Fin (B - 3), n := by
            apply Finset.sum_le_sum
            intro s _
            exact (hcross ⟨s.1, by omega⟩ ⟨s.1 + 1, by omega⟩ (by show s.1 < s.1 + 1; omega)).le
        _ = (B - 3) * n := by simp
    have hmid_le : ∑ s : Fin (B - 4), (la ⟨s.1 + 1, by omega⟩ + rb ⟨s.1 + 1, by omega⟩) ≤
        ∑ s : Fin (B - 3), (la ⟨s.1, by omega⟩ + rb ⟨s.1 + 1, by omega⟩) := by
      have hsplit1 : ∑ s : Fin (B - 3), la ⟨s.1, by omega⟩ =
          la ⟨0, by omega⟩ + ∑ s : Fin (B - 4), la ⟨s.1 + 1, by omega⟩ := by
        have hB3 : B - 3 = (B - 4) + 1 := by omega
        have := Fin.sum_univ_succ (n := B - 4) (fun s : Fin ((B - 4) + 1) => la ⟨s.1, by omega⟩)
        convert this using 1
        · refine Finset.sum_bij (fun s _ => ⟨s.1, by omega⟩) (fun _ _ => Finset.mem_univ _)
            (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
            (fun b _ => ⟨⟨b.1, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩) (fun _ _ => rfl)
        · simp [Fin.val_succ]
      have hsplit2 : ∑ s : Fin (B - 3), rb ⟨s.1 + 1, by omega⟩ =
          (∑ s : Fin (B - 4), rb ⟨s.1 + 1, by omega⟩) + rb ⟨B - 3, by omega⟩ := by
        have hB3 : B - 3 = (B - 4) + 1 := by omega
        have := Fin.sum_univ_castSucc (n := B - 4)
          (fun s : Fin ((B - 4) + 1) => rb ⟨s.1 + 1, by omega⟩)
        convert this using 1
        · refine Finset.sum_bij (fun s _ => ⟨s.1, by omega⟩) (fun _ _ => Finset.mem_univ _)
            (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
            (fun b _ => ⟨⟨b.1, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩) (fun _ _ => rfl)
        · congr 2; ext; simp; omega
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsplit1, hsplit2]
      omega
    have htot := hmid_le.trans hsum_le
    by_contra hall
    push Not at hall
    have hgt : (B - 4) * ((B - 3) * n) < (B - 4) * ∑ s : Fin (B - 4),
        (la ⟨s.1 + 1, by omega⟩ + rb ⟨s.1 + 1, by omega⟩) := by
      have hne : (Finset.univ : Finset (Fin (B - 4))).Nonempty :=
        ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      calc
        (B - 4) * ((B - 3) * n) = ∑ _s : Fin (B - 4), (B - 3) * n := by simp
        _ < ∑ s : Fin (B - 4), (B - 4) * (la ⟨s.1 + 1, by omega⟩ + rb ⟨s.1 + 1, by omega⟩) :=
            Finset.sum_lt_sum_of_nonempty hne (fun s _ => hall ⟨s.1 + 1, by omega⟩)
        _ = (B - 4) * ∑ s : Fin (B - 4), (la ⟨s.1 + 1, by omega⟩ + rb ⟨s.1 + 1, by omega⟩) := by
            rw [Finset.mul_sum]
    exact not_lt_of_ge (Nat.mul_le_mul_left (B - 4) htot) hgt
  obtain ⟨tstar, htstar⟩ := hteles
  -- Step 6: Apply `card_le_binomial` to `projMap a0 b0 (Q tstar)`
  set jstar : Fin (M * B) := ⟨rstar.1 * B + 1 + tstar.1, block_idx_lt_of_le rstar.2 (by omega)⟩
  have hQgeom : ∀ p ∈ Q tstar, a0.1 < p.1 ∧ p.1 < b0.1 ∧ orient a0 p b0 < 0 := fun p hp =>
    ⟨hsep _ _ (by show rstar.1 * B < jstar.1; dsimp [jstar]; omega) _ (ha rstar) _ (hQP tstar hp),
      hsep _ _ (by show jstar.1 < rstar.1 * B + (B - 1); dsimp [jstar]; omega) _ (hQP tstar hp) _ (hb rstar),
      hcap _ _ _ (by show rstar.1 * B < jstar.1; dsimp [jstar]; omega)
        (by show jstar.1 < rstar.1 * B + (B - 1); dsimp [jstar]; omega)
        _ (ha rstar) _ (hQP tstar hp) _ (hb rstar)⟩
  have hHpos : ∀ p ∈ Q tstar, 0 < chordH a0 b0 p := fun p hp => neg_pos.2 (hQgeom p hp).2.2
  have hproj_inj_fst : Set.InjOn (fun p => (projMap a0 b0 p).1) (Q tstar : Set Point) := by
    intro p hp q hq he
    by_contra hne
    rcases hQchain tstar p hp q hq hne with h1 | h1
    · exact (projMap_fst_lt (hQgeom p hp).1 (hQgeom q hq).1 (hQgeom p hp).2.1 (hQgeom q hq).2.1
        (hHpos p hp) h1).ne he
    · exact (projMap_fst_lt (hQgeom q hq).1 (hQgeom p hp).1 (hQgeom q hq).2.1 (hQgeom p hp).2.1
        (hHpos q hq) h1).ne he.symm
  have hproj_inj : Set.InjOn (projMap a0 b0) (Q tstar : Set Point) :=
    fun p hp q hq he => hproj_inj_fst hp hq (congrArg Prod.fst he)
  have hfst_img : Set.InjOn Prod.fst (↑((Q tstar).image (projMap a0 b0)) : Set Point) := by
    intro u hu v hv he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hv
    exact congrArg (projMap a0 b0) (hproj_inj_fst hp hq he)
  have hgen_img : ∀ u ∈ (Q tstar).image (projMap a0 b0), ∀ v ∈ (Q tstar).image (projMap a0 b0),
      ∀ w ∈ (Q tstar).image (projMap a0 b0), u.1 < v.1 → v.1 < w.1 → orient u v w ≠ 0 := by
    intro u hu v hv w hw huv hvw
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hw
    rw [orient_projMap (hHpos p hp) (hHpos q hq) (hHpos r hr)]
    have hab0 : a0.1 < b0.1 := (hQgeom p hp).1.trans (hQgeom p hp).2.1
    have hfac : (b0.1 - a0.1) / (chordH a0 b0 p * chordH a0 b0 q * chordH a0 b0 r) ≠ 0 :=
      (div_pos (sub_pos.2 hab0) (mul_pos (mul_pos (hHpos p hp) (hHpos q hq)) (hHpos r hr))).ne'
    have hpq : p ≠ q := fun h => huv.ne (congrArg (fun z => (projMap a0 b0 z).1) h)
    have hqr : q ≠ r := fun h => hvw.ne (congrArg (fun z => (projMap a0 b0 z).1) h)
    have hpr : p ≠ r := fun h => (huv.trans hvw).ne (congrArg (fun z => (projMap a0 b0 z).1) h)
    exact mul_ne_zero hfac (orient_ne_of_distinct hx hgen
      (hPX jstar (hQP tstar hp)) (hPX jstar (hQP tstar hq)) (hPX jstar (hQP tstar hr)) hpq hqr hpr)
  have hQcard_le : (Q tstar).card ≤ 2 ^ (la tstar + rb tstar) := by
    have hbi := card_le_binomial (rb tstar - 1) (la tstar - 1) ((Q tstar).image (projMap a0 b0))
      hfst_img hgen_img
      (by rw [show rb tstar - 1 + 2 = rb tstar + 1 by have := hrb1 tstar; omega]; exact hrb_no tstar)
      (by rw [show la tstar - 1 + 2 = la tstar + 1 by have := hla1 tstar; omega]; exact hla_no tstar)
    rw [Finset.card_image_of_injOn hproj_inj] at hbi
    calc
      (Q tstar).card ≤ (rb tstar - 1 + (la tstar - 1)).choose (rb tstar - 1) := hbi
      _ ≤ 2 ^ (rb tstar - 1 + (la tstar - 1)) := Nat.choose_le_two_pow _ _
      _ ≤ 2 ^ (la tstar + rb tstar) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLle : L ≤ W * 2 ^ (la tstar + rb tstar) := (hQL tstar).trans (Nat.mul_le_mul_left W hQcard_le)
  have hexp : ((la tstar + rb tstar : ℕ) : ℝ) ≤ (n : ℝ) + (n : ℝ) / ((B - 4 : ℕ) : ℝ) := by
    have hB4pos : (0 : ℝ) < ((B - 4 : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
    have hcast : ((B - 4 : ℕ) : ℝ) * ((la tstar + rb tstar : ℕ) : ℝ) ≤
        ((B - 3 : ℕ) : ℝ) * (n : ℝ) := by exact_mod_cast htstar
    have hB3 : ((B - 3 : ℕ) : ℝ) = ((B - 4 : ℕ) : ℝ) + 1 := by
      have : B - 3 = (B - 4) + 1 := by omega
      exact_mod_cast this
    rw [hB3] at hcast
    have hmul : ((B - 4 : ℕ) : ℝ) * ((la tstar + rb tstar : ℕ) : ℝ) ≤
        ((B - 4 : ℕ) : ℝ) * ((n : ℝ) + (n : ℝ) / ((B - 4 : ℕ) : ℝ)) := by
      rw [mul_add, mul_div_cancel₀ _ hB4pos.ne']
      linarith
    exact le_of_mul_le_mul_left hmul hB4pos
  have hLreal : (L : ℝ) ≤ (W : ℝ) * (2 : ℝ) ^ ((la tstar + rb tstar : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hLle
  calc
    (L : ℝ) ≤ (W : ℝ) * (2 : ℝ) ^ ((la tstar + rb tstar : ℕ) : ℝ) := hLreal
    _ ≤ (W : ℝ) * (2 : ℝ) ^ ((n : ℝ) + (n : ℝ) / ((B - 4 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left
          ((Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 hexp) (Nat.cast_nonneg W)

/-- Vertical reflection `(x, y) ↦ (x, -y)` reduces the cup case to the cap case. -/
private theorem reflect_y_cap_reduction {X : Finset Point} {M B n L : ℕ}
    (hM : 1 ≤ M) (hB : 5 ≤ B) (hn : 2 * M ≤ n)
    (hx : Set.InjOn Prod.fst (X : Set Point))
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
    (hno : ¬ ∃ Y ⊆ X, Y.card = n ∧ IsConvexPlanar Y)
    (up : Bool) (P : Fin (M * B) → Finset Point)
    (hPX : ∀ i, P i ⊆ X)
    (hPL : ∀ i, L ≤ (P i).card)
    (hsep : ∀ i j : Fin (M * B), i < j → ∀ p ∈ P i, ∀ q ∈ P j, p.1 < q.1)
    (hturn : ∀ i j l : Fin (M * B), i < j → j < l →
      ∀ p ∈ P i, ∀ q ∈ P j, ∀ r ∈ P l, turn up p q r) :
    (L : ℝ) ≤ (((n + (n + M - 1) / M).choose ((n + M - 1) / M) : ℕ) : ℝ) *
      (2 : ℝ) ^ ((n : ℝ) + (n : ℝ) / ((B - 4 : ℕ) : ℝ)) := by
  cases up with
  | false =>
    exact block_chord_bound hM hB hn hx hgen hno P hPX hPL hsep
      (fun i j l hij hjl p hp q hq r hr => by simpa [turn] using hturn i j l hij hjl p hp q hq r hr)
  | true =>
    let refl : Point → Point := fun p => (p.1, -p.2)
    have hrefl_inj : Function.Injective refl := by
      intro p q h
      exact Prod.ext (by simpa [refl] using congrArg Prod.fst h)
        (neg_inj.1 (by simpa [refl] using congrArg Prod.snd h))
    have hrefl_orient : ∀ p q r, orient (refl p) (refl q) (refl r) = - orient p q r := by
      intro p q r; unfold orient refl; dsimp only; ring
    have hno' : ¬ ∃ Y ⊆ X.image refl, Y.card = n ∧ IsConvexPlanar Y := by
      rintro ⟨Y, hYX, hYc, hYconv⟩
      obtain ⟨Z, hZX, hZY, hZc⟩ := finite_image_pullback refl X Y hYX hrefl_inj.injOn
      apply hno
      refine ⟨Z, hZX, hZc.trans hYc, fun p hp => ?_⟩
      obtain ⟨u, v, huv⟩ := hYconv (refl p) (hZY ▸ Finset.mem_image_of_mem refl hp)
      refine ⟨u, -v, fun q hq hqp => ?_⟩
      have hlt := huv (refl q) (hZY ▸ Finset.mem_image_of_mem refl hq) (fun h => hqp (hrefl_inj h))
      dsimp only [refl] at hlt
      linarith
    apply block_chord_bound (X := X.image refl) (P := fun i => (P i).image refl) hM hB hn
    · intro u hu v hv he
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hv
      exact congrArg refl (hx hp hq he)
    · intro u hu v hv w hw huv hvw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hv
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hw
      rw [hrefl_orient]
      exact neg_ne_zero.2 (hgen p hp q hq r hr huv hvw)
    · exact hno'
    · exact fun i => Finset.image_subset_image (hPX i)
    · exact fun i => by rw [Finset.card_image_of_injective _ hrefl_inj]; exact hPL i
    · intro i j hij u hu v hv
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hv
      exact hsep i j hij p hp q hq
    · intro i j l hij hjl u hu v hv w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hv
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hw
      rw [hrefl_orient]
      have ht := hturn i j l hij hjl p hp q hq r hr
      simp only [turn, ↓reduceIte] at ht
      linarith

/-- For any `δ > 0`, there exists `M ≥ 2` such that `(M : ℝ) + 1 ≤ 2^(δ * M)` and `2 / M ≤ δ`. -/
private lemma exists_good_M (δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℕ, 2 ≤ M ∧ ((M : ℝ) + 1) ≤ (2 : ℝ) ^ (δ * (M : ℝ)) ∧ 2 / (M : ℝ) ≤ δ := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  set c : ℝ := δ * Real.log 2
  have hc : 0 < c := mul_pos hδ (by linarith)
  let M : ℕ := max 2 (max (Nat.ceil (2 / δ)) (Nat.ceil (16 / c ^ 2) + 4))
  have hM2 : 2 ≤ M := le_max_left _ _
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 (by omega)
  have hMdiv : 2 / (M : ℝ) ≤ δ := by
    rw [div_le_iff₀ hMpos]
    have h1 : (2 / δ : ℝ) ≤ (M : ℝ) :=
      (Nat.le_ceil (2 / δ)).trans (by exact_mod_cast (le_max_left _ _).trans (le_max_right _ _))
    have := (div_le_iff₀ hδ).1 h1
    linarith
  have hMpow : ((M : ℝ) + 1) ≤ (2 : ℝ) ^ (δ * (M : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hexp_eq : Real.log 2 * (δ * (M : ℝ)) = 2 * (c * (M : ℝ) / 2) := by
      dsimp [c]; ring
    rw [hexp_eq, show Real.exp (2 * (c * (M : ℝ) / 2)) = (Real.exp (c * (M : ℝ) / 2)) ^ 2 by
      rw [sq, ← Real.exp_add]; congr 1; ring]
    have hlin : 1 + c * (M : ℝ) / 2 ≤ Real.exp (c * (M : ℝ) / 2) := by
      linarith [Real.add_one_le_exp (c * (M : ℝ) / 2)]
    have hsq : (1 + c * (M : ℝ) / 2) ^ 2 ≤ (Real.exp (c * (M : ℝ) / 2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlin 2
    have hMbig : 16 / c ^ 2 + 4 ≤ (M : ℝ) := by
      have h1 : (Nat.ceil (16 / c ^ 2) + 4 : ℕ) ≤ M :=
        (le_max_right _ _).trans (le_max_right _ _)
      have h2 : 16 / c ^ 2 ≤ (Nat.ceil (16 / c ^ 2) : ℝ) := Nat.le_ceil _
      have h3 : ((Nat.ceil (16 / c ^ 2) + 4 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast h1
      push_cast at h3; linarith
    have hcM : 16 ≤ c ^ 2 * (M : ℝ) := by
      have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
      have := (div_le_iff₀ hc2).1 (by linarith : 16 / c ^ 2 ≤ (M : ℝ))
      linarith
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
    have hquad : (M : ℝ) + 1 ≤ (1 + c * (M : ℝ) / 2) ^ 2 := by
      have hge : 4 * (M : ℝ) ≤ c ^ 2 * (M : ℝ) ^ 2 / 4 := by
        have : 16 * (M : ℝ) ≤ (c ^ 2 * (M : ℝ)) * (M : ℝ) :=
          mul_le_mul_of_nonneg_right hcM hMpos.le
        nlinarith
      nlinarith [mul_nonneg hc.le hMpos.le]
    exact hquad.trans hsq
  exact ⟨M, hM2, hMpow, hMdiv⟩

/-- Exponential bound on `(n + m).choose m` where `m = (n + M - 1) / M`. -/
private lemma choose_exp_bound (ε : ℝ) (hε : 0 < ε) (M n : ℕ) (hM2 : 2 ≤ M)
    (hMpow : ((M : ℝ) + 1) ≤ (2 : ℝ) ^ (ε / 8 * (M : ℝ)))
    (hMdiv : 2 / (M : ℝ) ≤ ε / 8) :
    (((n + (n + M - 1) / M).choose ((n + M - 1) / M) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (ε / 4 * (n : ℝ) + ε / 8 * (M : ℝ)) := by
  set m : ℕ := (n + M - 1) / M
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 (by omega)
  have hMm : (M : ℝ) * (m : ℝ) ≤ (n : ℝ) + (M : ℝ) := by
    have hdiv : M * m ≤ n + M - 1 := Nat.mul_div_le (n + M - 1) M
    have : M * m ≤ n + M := by omega
    exact_mod_cast this
  have h1 := choose_le_pow_mul_one_add n m M (by omega)
  have h2 : (M : ℝ) ^ m * (1 + 1 / (M : ℝ)) ^ (n + m) =
      ((M : ℝ) + 1) ^ m * (1 + 1 / (M : ℝ)) ^ n := by
    rw [pow_add, mul_left_comm, ← mul_pow]
    have : (M : ℝ) * (1 + 1 / (M : ℝ)) = (M : ℝ) + 1 := by field_simp [hMpos.ne']
    rw [this, mul_comm]
  rw [h2] at h1
  have hterm1 : ((M : ℝ) + 1) ^ m ≤ (2 : ℝ) ^ (ε / 8 * (n : ℝ) + ε / 8 * (M : ℝ)) := by
    calc
      ((M : ℝ) + 1) ^ m ≤ ((2 : ℝ) ^ (ε / 8 * (M : ℝ))) ^ m :=
        pow_le_pow_left₀ (by positivity) hMpow m
      _ = (2 : ℝ) ^ (ε / 8 * (M : ℝ) * (m : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ (2 : ℝ) ^ (ε / 8 * (n : ℝ) + ε / 8 * (M : ℝ)) := by
        apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2
        have := mul_le_mul_of_nonneg_left hMm (show (0 : ℝ) ≤ ε / 8 by linarith)
        linarith
  have hterm2 : (1 + 1 / (M : ℝ)) ^ n ≤ (2 : ℝ) ^ (ε / 8 * (n : ℝ)) := by
    have he2 : (1 + 1 / (M : ℝ)) ≤ (2 : ℝ) ^ (2 / (M : ℝ)) := by
      have hexp : 1 + 1 / (M : ℝ) ≤ Real.exp (1 / (M : ℝ)) := by
        linarith [Real.add_one_le_exp (1 / (M : ℝ))]
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
      have hexp2 : Real.exp (1 / (M : ℝ)) ≤ (2 : ℝ) ^ (2 / (M : ℝ)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        apply Real.exp_le_exp.2
        have : 1 / (M : ℝ) = (1 / 2) * (2 / (M : ℝ)) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hlog2 (by positivity)
      exact hexp.trans hexp2
    calc
      (1 + 1 / (M : ℝ)) ^ n ≤ ((2 : ℝ) ^ (2 / (M : ℝ))) ^ n :=
        pow_le_pow_left₀ (by positivity) he2 n
      _ = (2 : ℝ) ^ (2 / (M : ℝ) * (n : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ (2 : ℝ) ^ (ε / 8 * (n : ℝ)) := by
        apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2
        exact mul_le_mul_of_nonneg_right hMdiv (Nat.cast_nonneg n)
  calc
    (((n + m).choose m : ℕ) : ℝ) ≤ ((M : ℝ) + 1) ^ m * (1 + 1 / (M : ℝ)) ^ n := h1
    _ ≤ (2 : ℝ) ^ (ε / 8 * (n : ℝ) + ε / 8 * (M : ℝ)) * (2 : ℝ) ^ (ε / 8 * (n : ℝ)) :=
        mul_le_mul hterm1 hterm2 (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (ε / 4 * (n : ℝ) + ε / 8 * (M : ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring

/-- Main Suk theorem in `OMA.SuBound`. -/
private theorem su_bound_proof : type_of% @Erdos107.variants.su_bound := by
  apply from_epsilon_exists
  intro ε hε
  obtain ⟨M, hM2, hMpow, hMdiv⟩ := exists_good_M (ε / 8) (by linarith)
  let B : ℕ := Nat.ceil (4 / ε) + 5
  have hB5 : 5 ≤ B := by dsimp [B]; omega
  have hBdiv : 1 / ((B - 4 : ℕ) : ℝ) ≤ ε / 4 := by
    have hB4pos : (0 : ℝ) < ((B - 4 : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
    rw [div_le_iff₀ hB4pos]
    have hceil : 4 / ε ≤ (Nat.ceil (4 / ε) : ℝ) := Nat.le_ceil _
    have hle : (Nat.ceil (4 / ε) : ℝ) ≤ ((B - 4 : ℕ) : ℝ) := by
      have : Nat.ceil (4 / ε) ≤ B - 4 := by dsimp [B]; omega
      exact_mod_cast this
    have h4 : 4 / ε ≤ ((B - 4 : ℕ) : ℝ) := hceil.trans hle
    have := (div_le_iff₀ hε).1 h4
    linarith
  let k : ℕ := M * B
  have hk1 : 1 ≤ k := Nat.mul_pos (by omega) (by omega)
  obtain ⟨m0, hm0_def⟩ : ∃ m0 : ℕ, m0 = (2 * (12 * k + 7) - 4).choose (12 * k + 5) + 1 := ⟨_, rfl⟩
  obtain ⟨D, hD_def⟩ : ∃ D : ℕ, D = 2 * m0 ^ 2 := ⟨_, rfl⟩
  have hm0_pos : 0 < m0 := by rw [hm0_def]; exact Nat.succ_pos _
  have hDpos_nat : 0 < D := by rw [hD_def]; exact Nat.mul_pos (by norm_num) (pow_pos hm0_pos 2)
  have hDpos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.2 hDpos_nat
  -- Pick `n0` large enough that `2^(ε/2 * n) ≥ 2 * D * 2^(ε/8 * M) + 16 * m0 + 2`
  obtain ⟨Cconst, hC_def⟩ : ∃ Cconst : ℝ,
      Cconst = 2 * (D : ℝ) * (2 : ℝ) ^ (ε / 8 * (M : ℝ)) + 16 * (m0 : ℝ) + 2 := ⟨_, rfl⟩
  have hD_term_nonneg : (0 : ℝ) ≤ 2 * (D : ℝ) * (2 : ℝ) ^ (ε / 8 * (M : ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg D)) (Real.rpow_nonneg (by norm_num) _)
  have hm0_term_nonneg : (0 : ℝ) ≤ 16 * (m0 : ℝ) :=
    mul_nonneg (by norm_num) (Nat.cast_nonneg m0)
  have hCpos : 0 < Cconst := by linarith
  obtain ⟨n0_pow, hn0_pow⟩ := exists_nat_gt (Real.logb 2 Cconst / (ε / 2))
  let n0 : ℕ := max (2 * M) (max n0_pow 4)
  refine Filter.eventually_atTop.2 ⟨n0, fun n hn => ?_⟩
  have hn2M : 2 * M ≤ n := (le_max_left _ _).trans hn
  have hnpow : n0_pow ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn4 : 4 ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  let N : ℕ := ⌊(2 : ℝ) ^ ((1 + ε) * (n : ℝ))⌋₊
  refine ⟨N, Nat.floor_le (by positivity), ?_⟩
  apply cardSet_of_planar
  intro X hXcard hx hgen
  by_contra hno
  -- First check `16 * m0 ≤ X.card`
  have h2eps : Cconst < (2 : ℝ) ^ (ε / 2 * (n : ℝ)) := by
    have hlt1 : Real.logb 2 Cconst / (ε / 2) < (n : ℝ) :=
      hn0_pow.trans_le (by exact_mod_cast hnpow)
    have hlt2 : Real.logb 2 Cconst < ε / 2 * (n : ℝ) := by
      have := (div_lt_iff₀ (show 0 < ε / 2 by linarith)).1 hlt1
      linarith
    exact (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) hCpos).1 hlt2
  have h2big : (2 : ℝ) ^ ((1 + ε) * (n : ℝ)) - 1 < (X.card : ℝ) := by
    rw [hXcard]
    have := Nat.lt_floor_add_one ((2 : ℝ) ^ ((1 + ε) * (n : ℝ)))
    linarith
  have h16m0 : 16 * m0 ≤ X.card := by
    have h1 : (16 * (m0 : ℝ)) ≤ Cconst - 2 := by linarith
    have h2 : (2 : ℝ) ^ (ε / 2 * (n : ℝ)) ≤ (2 : ℝ) ^ ((1 + ε) * (n : ℝ)) :=
      (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2
        (mul_le_mul_of_nonneg_right (by linarith : ε / 2 ≤ 1 + ε) (Nat.cast_nonneg n))
    have h3 : (16 * (m0 : ℝ)) < (X.card : ℝ) := by linarith
    exact_mod_cast h3.le
  -- Apply Pór–Valtr
  have h16m0' : 16 * ((2 * (12 * k + 7) - 4).choose (12 * k + 5) + 1) ≤ X.card := by
    rwa [← hm0_def]
  obtain ⟨up, P, hPX, hPcard, hsep, hturn⟩ := por_valtr_cap_or_cup k hk1 X hx hgen h16m0'
  have hD_eq : 2 * (((2 * (12 * k + 7) - 4).choose (12 * k + 5) + 1) ^ 2) = D := by
    rw [← hm0_def, ← hD_def]
  let L : ℕ := X.card / D
  have hPL : ∀ i, L ≤ (P i).card := by
    intro i
    have hle : X.card ≤ D * (P i).card := by
      have hp := hPcard i
      rwa [hD_eq] at hp
    calc
      L = X.card / D := rfl
      _ ≤ (D * (P i).card) / D := Nat.div_le_div_right hle
      _ = (P i).card := Nat.mul_div_right (P i).card hDpos_nat
  -- Apply block-chord bound
  have hLbound := reflect_y_cap_reduction (M := M) (B := B) (n := n) (L := L)
    (by omega) hB5 hn2M hx hgen hno up P hPX hPL hsep hturn
  -- Bound the binomial factor `(n + m).choose m ≤ 2^(ε/4 * n + ε/8 * M)`
  set m : ℕ := (n + M - 1) / M
  have hbin : (((n + m).choose m : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ε / 4 * (n : ℝ) + ε / 8 * (M : ℝ)) :=
    choose_exp_bound ε hε M n hM2 hMpow hMdiv
  -- Combine `X.card < D * (L + 1)` with `hLbound` and `hbin`
  have hXleD : (X.card : ℝ) ≤ (D : ℝ) * ((L : ℝ) + 1) := by
    have hnat : X.card ≤ D * (L + 1) := by
      have hmod := Nat.div_add_mod X.card D
      have hlt := Nat.mod_lt X.card hDpos_nat
      calc
        X.card = D * L + X.card % D := hmod.symm
        _ ≤ D * L + D := Nat.add_le_add_left hlt.le _
        _ = D * (L + 1) := by rw [mul_add, mul_one]
    exact_mod_cast hnat
  have hchain_exp : (n : ℝ) + (n : ℝ) / ((B - 4 : ℕ) : ℝ) ≤ (1 + ε / 4) * (n : ℝ) := by
    have : (n : ℝ) / ((B - 4 : ℕ) : ℝ) = (1 / ((B - 4 : ℕ) : ℝ)) * (n : ℝ) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hBdiv (Nat.cast_nonneg n)
    linarith
  have hLtot : (L : ℝ) ≤ (2 : ℝ) ^ (ε / 8 * (M : ℝ)) * (2 : ℝ) ^ ((1 + ε / 2) * (n : ℝ)) := by
    calc
      (L : ℝ) ≤ (((n + m).choose m : ℕ) : ℝ) *
          (2 : ℝ) ^ ((n : ℝ) + (n : ℝ) / ((B - 4 : ℕ) : ℝ)) := hLbound
      _ ≤ (2 : ℝ) ^ (ε / 4 * (n : ℝ) + ε / 8 * (M : ℝ)) *
          (2 : ℝ) ^ ((1 + ε / 4) * (n : ℝ)) :=
          mul_le_mul hbin
            ((Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 hchain_exp)
            (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (ε / 8 * (M : ℝ)) * (2 : ℝ) ^ ((1 + ε / 2) * (n : ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1; ring
  have hXupper : (X.card : ℝ) ≤ Cconst * (2 : ℝ) ^ ((1 + ε / 2) * (n : ℝ)) - 1 := by
    have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 + ε / 2) * (n : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hMle : (1 : ℝ) ≤ (2 : ℝ) ^ (ε / 8 * (M : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hL1 : (L : ℝ) + 1 ≤
        2 * (2 : ℝ) ^ (ε / 8 * (M : ℝ)) * (2 : ℝ) ^ ((1 + ε / 2) * (n : ℝ)) := by
      have hprod : (1 : ℝ) ≤ (2 : ℝ) ^ (ε / 8 * (M : ℝ)) * (2 : ℝ) ^ ((1 + ε / 2) * (n : ℝ)) :=
        one_le_mul_of_one_le_of_one_le hMle h1le
      linarith
    have hCge : 2 * (D : ℝ) * (2 : ℝ) ^ (ε / 8 * (M : ℝ)) ≤ Cconst - 1 := by linarith
    calc
      (X.card : ℝ) ≤ (D : ℝ) * ((L : ℝ) + 1) := hXleD
      _ ≤ (D : ℝ) * (2 * (2 : ℝ) ^ (ε / 8 * (M : ℝ)) * (2 : ℝ) ^ ((1 + ε / 2) * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hL1 hDpos.le
      _ = (2 * (D : ℝ) * (2 : ℝ) ^ (ε / 8 * (M : ℝ))) * (2 : ℝ) ^ ((1 + ε / 2) * (n : ℝ)) := by ring
      _ ≤ (Cconst - 1) * (2 : ℝ) ^ ((1 + ε / 2) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hCge (by positivity)
      _ = Cconst * (2 : ℝ) ^ ((1 + ε / 2) * (n : ℝ)) - (2 : ℝ) ^ ((1 + ε / 2) * (n : ℝ)) := by ring
      _ ≤ Cconst * (2 : ℝ) ^ ((1 + ε / 2) * (n : ℝ)) - 1 := by linarith
  have hXstrict : (X.card : ℝ) < (2 : ℝ) ^ ((1 + ε) * (n : ℝ)) - 1 := by
    have hmul : Cconst * (2 : ℝ) ^ ((1 + ε / 2) * (n : ℝ)) <
        (2 : ℝ) ^ (ε / 2 * (n : ℝ)) * (2 : ℝ) ^ ((1 + ε / 2) * (n : ℝ)) :=
      mul_lt_mul_of_pos_right h2eps (Real.rpow_pos_of_pos (by norm_num) _)
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show ε / 2 * (n : ℝ) + (1 + ε / 2) * (n : ℝ) = (1 + ε) * (n : ℝ) by ring] at hmul
    linarith
  linarith

end OMA.SuBound

theorem OMA.solution : type_of% @Erdos107.variants.su_bound :=
  OMA.SuBound.su_bound_proof
