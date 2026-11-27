import OMAReductions.R_Erdos107_erdos_107_R1
import Mathlib.Data.Nat.Choose.Sum

/-!
The formalization below is by @Genbox (open-math-agents #1086).
This submission applies its lower bound to @ihateSAS’s reduction.

The upper bound is the cup and cap recurrence from Erdős and Szekeres (1935).
https://www.numdam.org/item/CM_1935__2__463_0/

The lower bound uses their binomial blocks (1960, Section 2).
https://users.renyi.hu/~p_erdos/1960-09.pdf
-/

open Finset
open scoped Classical EuclideanGeometry

theorem OMA.finite_image_pullback {α β : Type*} [DecidableEq β] (L : α → β) (X : Finset α) (Z : Finset β)
    (hZ : Z ⊆ X.image L) (hL : Set.InjOn L (X : Set α)) :
    ∃ Y ⊆ X, Y.image L = Z ∧ Y.card = Z.card := by
  classical
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

theorem OMA.planar_coordinates (X : Finset (ℝ^2)) :
    ∃ x y : (ℝ^2) →ₗ[ℝ] ℝ, Set.InjOn x (X : Set (ℝ^2)) ∧
      ∀ p q, x p = x q → y p = y q → p = q := by
  classical
  let bad := (X ×ˢ X).image fun uv : (ℝ^2) × (ℝ^2) =>
    (uv.2 0 - uv.1 0) / (uv.1 1 - uv.2 1)
  obtain ⟨t, ht⟩ := bad.exists_notMem
  let x : (ℝ^2) →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 0 + t • EuclideanSpace.projₗ 1
  let y : (ℝ^2) →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 1
  have hjoint (p q : ℝ^2) (hx : x p = x q) (hy : y p = y q) : p = q := by
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

noncomputable def OMA.planar_slope (x y : (ℝ^2) → ℝ) (p q : ℝ^2) : ℝ :=
  (y q - y p) / (x q - x p)

theorem OMA.planar_convex_of_increasing_slopes (Y : Finset (ℝ^2))
    (x y : (ℝ^2) →ₗ[ℝ] ℝ) (hinj : Set.InjOn x (Y : Set (ℝ^2)))
    (hslope : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, x a < x b → x b < x c →
      OMA.planar_slope x y a b < OMA.planar_slope x y b c) :
    ConvexIndependent ℝ (Subtype.val : ↥(Y : Set (ℝ^2)) → ℝ^2) := by
  classical
  have hsupport (p : ℝ^2) (hp : p ∈ Y) : ∃ L : (ℝ^2) →ₗ[ℝ] ℝ,
      ∀ q ∈ Y, q ≠ p → L p < L q := by
    let A := Y.filter fun q => x q < x p
    let B := Y.filter fun q => x p < x q
    by_cases hA : A.Nonempty
    · by_cases hB : B.Nonempty
      · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image A (fun a => OMA.planar_slope x y a p) hA
        obtain ⟨b, hb, hmin⟩ := Finset.exists_min_image B (OMA.planar_slope x y p) hB
        obtain ⟨haY, hap⟩ := Finset.mem_filter.mp ha
        obtain ⟨hbY, hpb⟩ := Finset.mem_filter.mp hb
        obtain ⟨s, h₁, h₂⟩ := exists_between (hslope a haY p hp b hbY hap hpb)
        refine ⟨y - s • x, fun q hq hqp => ?_⟩
        change y p - s * x p < y q - s * x q
        have hne : x q ≠ x p := fun h => hqp (hinj hq hp h)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hs := (hmax q (Finset.mem_filter.mpr ⟨hq, hlt⟩)).trans_lt h₁
          have hs' := (div_lt_iff₀ (sub_pos.mpr hlt)).mp hs
          linarith
        · have hs := h₂.trans_le (hmin q (Finset.mem_filter.mpr ⟨hq, hgt⟩))
          have hs' := (lt_div_iff₀ (sub_pos.mpr hgt)).mp hs
          linarith
      · refine ⟨-x, fun q hq hqp => ?_⟩
        change -x p < -x q
        have hne : x q ≠ x p := fun h => hqp (hinj hq hp h)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact neg_lt_neg hlt
        · exact (hB ⟨q, Finset.mem_filter.mpr ⟨hq, hgt⟩⟩).elim
    · refine ⟨x, fun q hq hqp => ?_⟩
      have hne : x q ≠ x p := fun h => hqp (hinj hq hp h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (hA ⟨q, Finset.mem_filter.mpr ⟨hq, hlt⟩⟩).elim
      · exact hgt
  rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
  intro p hp h
  obtain ⟨L, hL⟩ := hsupport p hp
  have hsub : (Y : Set (ℝ^2)) \ {p} ⊆ {q | L p < L q} :=
    fun q hq => hL q hq.1 hq.2
  have he := (convexHull_min hsub (convex_halfSpace_gt L.isLinear (L p))) h
  exact (lt_irrefl (L p)) he

namespace ErdosSzekeresUpper

private abbrev Point := ℝ × ℝ

private def orient (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1)

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
      rw [show l ++ [a,b] = (l ++ [a]) ++ [b] by simp] at hsort
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
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X,
      a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
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
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X,
      a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
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
    unfold signedOrient orient
    ring
  have hright :
      (c.1 - b.1) * signedOrient up a c d =
        (c.1 - a.1) * signedOrient up b c d + (d.1 - c.1) * signedOrient up a b c := by
    unfold signedOrient orient
    ring
  constructor
  · apply (mul_pos_iff_of_pos_left (sub_pos.mpr hbc)).mp
    rw [hleft]
    exact add_pos (mul_pos (sub_pos.mpr (hbc.trans hcd)) h₁) (mul_pos (sub_pos.mpr hab) h₂)
  · apply (mul_pos_iff_of_pos_left (sub_pos.mpr hbc)).mp
    rw [hright]
    exact add_pos (mul_pos (sub_pos.mpr (hab.trans hbc)) h₂) (mul_pos (sub_pos.mpr hcd) h₁)

private theorem turns_tail {up : Bool} {a : Point} {l : List Point}
    (h : turns up (a :: l)) : turns up l := by
  rcases l with _ | ⟨b, _ | ⟨c, l⟩⟩
  · trivial
  · trivial
  · exact h.2

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
  have hh := turns_sublist_append hsublist [] h.2.1 h.2.2
  exact hh.1

private theorem orient_ne_in_image (X : Finset ℝ²)
    (hX : EuclideanGeometry.NonTrilinear (X : Set ℝ²))
    (x y : ℝ² →ₗ[ℝ] ℝ) (hjoint : ∀ p q, x p = x q → y p = y q → p = q) :
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
  apply (collinear_iff_of_mem (show b ∈ ({a, b, c} : Set ℝ²) by simp)).mpr
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

private theorem convex_from_seq {up : Bool} {X : Finset ℝ²} {n : ℕ}
    (x y : ℝ² →ₗ[ℝ] ℝ) (hx : Set.InjOn x (X : Set ℝ²))
    (hxy : ∀ p q, x p = x q → y p = y q → p = q)
    (h : HasSeq up (X.image (x.prod y)) n) :
    EuclideanGeometry.HasConvexNGon n (X : Set ℝ²) := by
  obtain ⟨l, hl, hlen⟩ := h
  let L := x.prod y
  have hL : Function.Injective L := by
    intro a b he
    exact hxy a b (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hsub : l.toFinset ⊆ X.image L := by
    intro p hp
    exact hl.1 p (List.mem_toFinset.1 hp)
  obtain ⟨Y, hYX, hY, hYcard⟩ := OMA.finite_image_pullback L X l.toFinset hsub hL.injOn
  have hnodup : l.Nodup := by
    apply hl.2.1.imp
    intro a b hab he
    subst b
    exact (lt_irrefl _) hab
  have hmem : ∀ a ∈ Y, L a ∈ l := by
    intro a ha
    apply List.mem_toFinset.1
    rw [← hY]
    exact Finset.mem_image.2 ⟨a, ha, rfl⟩
  refine ⟨Y, hYcard.trans ((List.toFinset_card_of_nodup hnodup).trans hlen), hYX, ?_⟩
  have hYC : ConvexIndependent ℝ (Subtype.val : ↥(Y : Set ℝ²) → ℝ²) := by
    cases up with
    | true =>
      apply OMA.planar_convex_of_increasing_slopes Y x y (hx.mono hYX)
      intro a ha b hb c hc hab hbc
      have ht := turn_of_mem hl (hmem a ha) (hmem b hb) (hmem c hc) hab hbc
      change 0 < (x b - x a) * (y c - y b) - (y b - y a) * (x c - x b) at ht
      unfold OMA.planar_slope
      apply (div_lt_div_iff₀ (sub_pos.2 hab) (sub_pos.2 hbc)).2
      linarith only [ht]
    | false =>
      apply OMA.planar_convex_of_increasing_slopes Y x (-y) (hx.mono hYX)
      intro a ha b hb c hc hab hbc
      have ht := turn_of_mem hl (hmem a ha) (hmem b hb) (hmem c hc) hab hbc
      change (x b - x a) * (y c - y b) - (y b - y a) * (x c - x b) < 0 at ht
      change (-y b - -y a) / (x b - x a) < (-y c - -y b) / (x c - x b)
      apply (div_lt_div_iff₀ (sub_pos.2 hab) (sub_pos.2 hbc)).2
      linarith only [ht]
  exact convexIndependent_set_iff_notMem_convexHull_sdiff.1 hYC

theorem upper_mem (n : ℕ) (hn : 3 ≤ n) :
    (2 * n - 4).choose (n - 2) + 1 ∈ Erdos107.cardSet n := by
  intro X hXcard hX
  obtain ⟨x, y, hx, hxy⟩ := OMA.planar_coordinates X
  let L := x.prod y
  have hL : Function.Injective L := by
    intro a b h
    exact hxy a b (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hinj : Set.InjOn Prod.fst (↑(X.image L) : Set Point) := by
    intro u hu v hv he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
    exact congrArg L (hx ha hb he)
  have hg := orient_ne_in_image X hX x y hxy
  have hseq : HasSeq true (X.image L) n ∨ HasSeq false (X.image L) n := by
    by_contra! h
    let s := n - 2
    have hs : s + 2 = n := by dsimp [s]; omega
    have hs' : s + s = 2 * n - 4 := by dsimp [s]; omega
    have hle := card_le_binomial s s (X.image L) hinj hg
      (by simpa only [hs] using h.1) (by simpa only [hs] using h.2)
    rw [Finset.card_image_of_injective _ hL, hXcard, hs'] at hle
    exact (Nat.not_succ_le_self _) hle
  rcases hseq with h | h
  · exact convex_from_seq x y hx hxy h
  · exact convex_from_seq x y hx hxy h

end ErdosSzekeresUpper

open Finset EuclideanGeometry
open scoped BigOperators

namespace ErdosSzekeresLower

private abbrev Point := ℝ × ℝ

private def orient (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1)

private def Chain (up : Bool) (S : Finset Point) : Prop :=
  ∀ ⦃a b c : Point⦄, a ∈ S → b ∈ S → c ∈ S → a.1 < b.1 → b.1 < c.1 →
    if up then 0 < orient a b c else orient a b c < 0

private lemma chain_mono {up : Bool} {T S : Finset Point} (h : Chain up S) (hT : T ⊆ S) :
    Chain up T := by
  intro a b c ha hb hc hab hbc
  exact h (hT ha) (hT hb) (hT hc) hab hbc

private def Box (W : ℕ) (B : ℝ) (S : Finset Point) : Prop :=
  ∀ p ∈ S, ∃ i : ℕ, i < W ∧ p.1 = (i : ℝ) ∧ 0 ≤ p.2 ∧ p.2 ≤ B

private structure Config (r s : ℕ) (B : ℝ) (S : Finset Point) : Prop where
  card : S.card = (r + s).choose r
  box : Box ((r + s).choose r) B S
  inj : Set.InjOn Prod.fst (S : Set Point)
  nonzero : ∀ ⦃a b c : Point⦄, a ∈ S → b ∈ S → c ∈ S → a.1 < b.1 → b.1 < c.1 →
    orient a b c ≠ 0
  chain_card : ∀ (up : Bool) (T : Finset Point), T ⊆ S → Chain up T →
    T.card ≤ if up then s + 1 else r + 1

private def rise (W U : ℕ) (B : ℝ) : ℝ := ((W : ℝ) + (U : ℝ) + 2) * (B + 1)

private def shift (W U : ℕ) (B : ℝ) (p : Point) : Point := (p.1 + W, p.2 + rise W U B)

private lemma shift_injective (W U : ℕ) (B : ℝ) : Function.Injective (shift W U B) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (add_right_cancel h1) (add_right_cancel h2)

private lemma orient_shift (W U : ℕ) (B : ℝ) (a b c : Point) :
    orient (shift W U B a) (shift W U B b) (shift W U B c) = orient a b c := by
  unfold orient shift
  dsimp only
  ring

private lemma shift_lt_iff {W U : ℕ} {B : ℝ} {a b : Point} :
    (shift W U B a).1 < (shift W U B b).1 ↔ a.1 < b.1 := by
  simp [shift]

private lemma box_bounds {W : ℕ} {B : ℝ} {S : Finset Point} (hbox : Box W B S)
    {p : Point} (hp : p ∈ S) :
    0 ≤ p.1 ∧ p.1 < (W : ℝ) ∧ 0 ≤ p.2 ∧ p.2 ≤ B := by
  obtain ⟨i, hi, he, hy₀, hy₁⟩ := hbox p hp
  exact ⟨he ▸ Nat.cast_nonneg i, he ▸ (by exact_mod_cast hi), hy₀, hy₁⟩

private lemma internal_gap {W : ℕ} {B : ℝ} {S : Finset Point} (hbox : Box W B S)
    {a b : Point} (ha : a ∈ S) (hb : b ∈ S) (hab : a.1 < b.1) :
    1 ≤ b.1 - a.1 ∧ b.2 - a.2 ≤ B := by
  obtain ⟨i, _, hi, ha₀, _⟩ := hbox a ha
  obtain ⟨j, _, hj, _, hb₁⟩ := hbox b hb
  have hij : i < j := by
    rw [hi, hj] at hab
    exact_mod_cast hab
  have h : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (by omega : i + 1 ≤ j)
  constructor <;> linarith

private lemma box_mono {W : ℕ} {B C : ℝ} {S : Finset Point} (hbox : Box W B S) (h : B ≤ C) :
    Box W C S := by
  intro p hp
  obtain ⟨i, hi, hx, hy, hB⟩ := hbox p hp
  exact ⟨i, hi, hx, hy, hB.trans h⟩

private lemma cross_gap {W U : ℕ} {B : ℝ} {L R : Finset Point}
    (hL : Box W B L) (hR : Box U B R) {a b : Point} (ha : a ∈ L) (hb : b ∈ R) :
    a.1 < (shift W U B b).1 ∧ (shift W U B b).1 - a.1 ≤ (W : ℝ) + (U : ℝ) ∧
      rise W U B - B ≤ (shift W U B b).2 - a.2 := by
  obtain ⟨ha₀, ha₁, -, ha₂⟩ := box_bounds hL ha
  obtain ⟨hb₀, hb₁, hb₂, -⟩ := box_bounds hR hb
  unfold shift
  dsimp only
  exact ⟨by linarith, by linarith, by linarith⟩

private lemma tilt_gap (W U : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    B * ((W : ℝ) + (U : ℝ)) < rise W U B - B := by
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hU : (0 : ℝ) ≤ U := Nat.cast_nonneg U
  dsimp [rise]
  linarith

private lemma cross_orient_positive {W U : ℕ} {B : ℝ} {L R : Finset Point}
    (hL : Box W B L) (hR : Box U B R) (hB : 0 ≤ B) {a b c : Point}
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ R) (hab : a.1 < b.1) :
    0 < orient a b (shift W U B c) := by
  obtain ⟨hx, hy⟩ := internal_gap hL ha hb hab
  obtain ⟨hsep, hdx, hdy⟩ := cross_gap hL hR hb hc
  have hgap := tilt_gap W U hB
  have hprod : 0 ≤ B * ((W : ℝ) + (U : ℝ)) := mul_nonneg hB (by positivity)
  have hl := mul_le_mul hx hdy (hprod.trans hgap.le) (by linarith)
  have hr := mul_le_mul hy hdx (by linarith) hB
  unfold orient
  linarith

private lemma cross_orient_negative {W U : ℕ} {B : ℝ} {L R : Finset Point}
    (hL : Box W B L) (hR : Box U B R) (hB : 0 ≤ B) {a b c : Point}
    (ha : a ∈ L) (hb : b ∈ R) (hc : c ∈ R) (hbc : b.1 < c.1) :
    orient a (shift W U B b) (shift W U B c) < 0 := by
  obtain ⟨hx, hy⟩ := internal_gap hR hb hc hbc
  obtain ⟨hsep, hdx, hdy⟩ := cross_gap hL hR ha hb
  have hgap := tilt_gap W U hB
  have hprod : 0 ≤ B * ((W : ℝ) + (U : ℝ)) := mul_nonneg hB (by positivity)
  have hl := mul_le_mul hdy hx (by norm_num) (by linarith)
  have hr := mul_le_mul hy hdx (by linarith) hB
  change ((shift W U B b).1 - a.1) * ((shift W U B c).2 - (shift W U B b).2) -
    ((shift W U B b).2 - a.2) * ((shift W U B c).1 - (shift W U B b).1) < 0
  have hyShift : (shift W U B c).2 - (shift W U B b).2 = c.2 - b.2 := by unfold shift; simp
  have hxShift : (shift W U B c).1 - (shift W U B b).1 = c.1 - b.1 := by unfold shift; simp
  rw [hyShift, hxShift]
  linarith

private lemma image_invariant_chain {T S : Finset Point} {f : Point → Point}
    (hf : Function.Injective f) (hx : ∀ a b, (f a).1 < (f b).1 ↔ a.1 < b.1)
    (up : Bool) (ho : ∀ a b c, (if up then 0 < orient (f a) (f b) (f c) else orient (f a) (f b) (f c) < 0) →
      (if up then 0 < orient a b c else orient a b c < 0))
    (hT : T ⊆ S.image f) (ht : Chain up T) :
    ∃ A ⊆ S, A.card = T.card ∧ Chain up A := by
  classical
  let A := S.filter fun p => f p ∈ T
  have hA : A ⊆ S := Finset.filter_subset _ _
  have him : A.image f = T := by
    ext p
    constructor
    · intro hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
      exact (Finset.mem_filter.1 ha).2
    · intro hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (hT hp)
      exact Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, hp⟩, rfl⟩
  refine ⟨A, hA, ?_, ?_⟩
  · rw [← him, Finset.card_image_of_injective _ hf]
  · intro a b c ha hb hc hab hbc
    have hh := ht (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2 (Finset.mem_filter.1 hc).2
      ((hx _ _).2 hab) ((hx _ _).2 hbc)
    exact ho _ _ _ hh

private lemma card_succ_choose (r s : ℕ) :
    ((r + 1) + s).choose (r + 1) + (r + (s + 1)).choose r =
      ((r + 1) + (s + 1)).choose (r + 1) := by
  rw [show (r + 1) + (s + 1) = (r + s + 1) + 1 by omega,
    Nat.choose_succ_succ, show r + 1 + s = r + s + 1 by omega,
    show r + (s + 1) = r + s + 1 by omega, add_comm]

private lemma join_configs {r s : ℕ} {A B : ℝ} {L R : Finset Point}
    (hA : 0 ≤ A) (hL : Config (r + 1) s A L) (hR : Config r (s + 1) B R) :
    ∃ M ≥ (0 : ℝ), ∃ S, Config (r + 1) (s + 1) M S := by
  classical
  let W := ((r + 1) + s).choose (r + 1)
  let U := (r + (s + 1)).choose r
  let C := max A B
  let f := shift W U C
  let Q := L ∪ R.image f
  have hC : 0 ≤ C := hA.trans (le_max_left _ _)
  have hRnonneg : 0 ≤ rise W U C := by unfold rise; positivity
  have hlbox : Box W C L := box_mono hL.box (le_max_left _ _)
  have hrbox : Box U C R := box_mono hR.box (le_max_right _ _)
  have hsep {x y : Point} (hx : x ∈ L) (hy : y ∈ R) : x.1 < (f y).1 :=
    (cross_gap hlbox hrbox hx hy).1
  have hMem {x : Point} (hx : x ∈ Q) : x ∈ L ∨ ∃ y ∈ R, f y = x :=
    (Finset.mem_union.1 hx).imp_right Finset.mem_image.1
  have hdisj : Disjoint L (R.image f) := by
    refine Finset.disjoint_left.2 fun a ha hb => ?_
    obtain ⟨b, hbR, rfl⟩ := Finset.mem_image.1 hb
    exact (lt_irrefl _) (hsep ha hbR)
  have hW : W + U = ((r + 1) + (s + 1)).choose (r + 1) := card_succ_choose r s
  refine ⟨C + rise W U C, add_nonneg hC hRnonneg, Q, ?_, ?_, ?_, ?_, ?_⟩
  · change (L ∪ R.image f).card = _
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (shift_injective _ _ _),
      hL.card, hR.card]
    exact hW
  · intro a ha
    rw [← hW]
    rcases hMem ha with haL | ⟨b, hbR, rfl⟩
    · obtain ⟨i, hi, hx, h₀, h₁⟩ := hlbox a haL
      exact ⟨i, by omega, hx, h₀, by linarith⟩
    · obtain ⟨i, hi, hx, h₀, h₁⟩ := hrbox b hbR
      exact ⟨i + W, by omega, by simp [f, shift, hx], add_nonneg h₀ hRnonneg,
        by change b.2 + rise W U C ≤ C + rise W U C; linarith⟩
  · intro a ha b hb hab
    rcases hMem ha with haL | ⟨a', haR, rfl⟩ <;> rcases hMem hb with hbL | ⟨b', hbR, rfl⟩
    · exact hL.inj haL hbL hab
    · exact ((hsep haL hbR).ne hab).elim
    · exact ((hsep hbL haR).ne hab.symm).elim
    · exact congrArg f (hR.inj haR hbR (add_right_cancel hab))
  · intro a b c ha hb hc hab hbc
    rcases hMem ha with haL | ⟨a', haR, rfl⟩ <;>
      rcases hMem hb with hbL | ⟨b', hbR, rfl⟩ <;>
      rcases hMem hc with hcL | ⟨c', hcR, rfl⟩
    · exact hL.nonzero haL hbL hcL hab hbc
    · exact (cross_orient_positive hlbox hrbox hC haL hbL hcR hab).ne'
    · exact ((hsep hcL hbR).not_gt hbc).elim
    · exact (cross_orient_negative hlbox hrbox hC haL hbR hcR (shift_lt_iff.1 hbc)).ne
    · exact ((hsep hbL haR).not_gt hab).elim
    · exact ((hsep hbL haR).not_gt hab).elim
    · exact ((hsep hcL hbR).not_gt hbc).elim
    · change orient (shift W U C a') (shift W U C b') (shift W U C c') ≠ 0
      rw [orient_shift]
      exact hR.nonzero haR hbR hcR (shift_lt_iff.1 hab) (shift_lt_iff.1 hbc)
  · intro up T hT ht
    let L' := T ∩ L
    let R' := T ∩ R.image f
    have hleft (p : Point) (hp : p ∈ L') : p ∈ T ∧ p ∈ L := Finset.mem_inter.1 hp
    have hright (p : Point) (hp : p ∈ R') : p ∈ T ∧ ∃ q ∈ R, f q = p :=
      ⟨(Finset.mem_inter.1 hp).1, Finset.mem_image.1 (Finset.mem_inter.1 hp).2⟩
    have hboth : T.card ≤ L'.card + R'.card := by
      have hh : T ⊆ L' ∪ R' := by
        intro x hx
        rcases Finset.mem_union.1 (hT hx) with h | h
        · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hx, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hx, h⟩)
      exact (Finset.card_le_card hh).trans (Finset.card_union_le _ _)
    have hlc : L'.card ≤ if up then s + 1 else r + 2 :=
      hL.chain_card up L' Finset.inter_subset_right (chain_mono ht Finset.inter_subset_left)
    obtain ⟨Z, hZ, hcZ, hChainZ⟩ :=
      image_invariant_chain (shift_injective W U C) (fun _ _ => shift_lt_iff)
        up (by simp only [orient_shift]; exact fun _ _ _ h => h)
        (show R' ⊆ R.image f from Finset.inter_subset_right)
        (chain_mono ht (show R' ⊆ T from Finset.inter_subset_left))
    have hrc : R'.card ≤ if up then s + 2 else r + 1 :=
      hcZ ▸ hR.chain_card up Z hZ hChainZ
    have hcup (hu : up = true) (hne : L'.Nonempty) : R'.card ≤ 1 := by
      obtain ⟨a, ha⟩ := hne
      obtain ⟨haT, haL⟩ := hleft a ha
      refine Finset.card_le_one_iff.2 fun {b c} hb hc => ?_
      obtain ⟨hbT, b', hbR, rfl⟩ := hright b hb
      obtain ⟨hcT, c', hcR, rfl⟩ := hright c hc
      by_contra hne'
      have hn : b'.1 ≠ c'.1 := fun he => hne' (congrArg f (hR.inj hbR hcR he))
      have hbad {p q : Point} (hp : p ∈ R) (hq : q ∈ R) (hpT : f p ∈ T)
          (hqT : f q ∈ T) (hpq : p.1 < q.1) : False := by
        have hlt := ht haT hpT hqT (hsep haL hp) (shift_lt_iff.2 hpq)
        rw [hu, if_pos rfl] at hlt
        exact (cross_orient_negative hlbox hrbox hC haL hp hq hpq).not_gt hlt
      exact (lt_or_gt_of_ne hn).elim (hbad hbR hcR hbT hcT) (hbad hcR hbR hcT hbT)
    have hcap (hu : up = false) (hne : R'.Nonempty) : L'.card ≤ 1 := by
      obtain ⟨c, hc⟩ := hne
      obtain ⟨hcT, c', hcR, rfl⟩ := hright c hc
      refine Finset.card_le_one_iff.2 fun {a b} ha hb => ?_
      obtain ⟨haT, haL⟩ := hleft a ha
      obtain ⟨hbT, hbL⟩ := hleft b hb
      by_contra hne'
      have hn : a.1 ≠ b.1 := fun h => hne' (hL.inj haL hbL h)
      have hbad {p q : Point} (hp : p ∈ L) (hq : q ∈ L) (hpT : p ∈ T)
          (hqT : q ∈ T) (hpq : p.1 < q.1) : False := by
        have hlt := ht hpT hqT hcT hpq (hsep hq hcR)
        simp only [hu, Bool.false_eq_true, if_false] at hlt
        exact (cross_orient_positive hlbox hrbox hC hp hq hcR hpq).not_gt hlt
      exact (lt_or_gt_of_ne hn).elim (hbad haL hbL haT hbT) (hbad hbL haL hbT haT)
    cases up
    · rcases R'.eq_empty_or_nonempty with he | hn
      · simp only [he, Finset.card_empty, add_zero] at hboth
        simp only [Bool.false_eq_true, if_false] at hlc ⊢
        omega
      · have := hcap rfl hn
        simp only [Bool.false_eq_true, if_false] at hrc ⊢
        omega
    · rcases L'.eq_empty_or_nonempty with he | hn
      · simp only [he, Finset.card_empty, zero_add] at hboth
        simp only [if_true] at hrc ⊢
        omega
      · have := hcup rfl hn
        simp only [if_true] at hlc ⊢
        omega

private lemma singleton_config (r s : ℕ) (hcard : (r + s).choose r = 1) :
    Config r s 0 ({0} : Finset Point) := by
  refine ⟨by simp [hcard], ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain rfl := Finset.mem_singleton.1 ha
    exact ⟨0, by simp [hcard], by norm_num, le_rfl, le_rfl⟩
  · intro a ha b hb _
    exact (Finset.mem_singleton.1 ha).trans (Finset.mem_singleton.1 hb).symm
  · intro a b c ha hb _ hab _
    obtain rfl := Finset.mem_singleton.1 ha
    obtain rfl := Finset.mem_singleton.1 hb
    exact False.elim ((lt_irrefl _) hab)
  · intro up T hT _
    have h : T.card ≤ 1 := by simpa using Finset.card_le_card hT
    split <;> omega

private lemma configurations (r s : ℕ) : ∃ B ≥ (0 : ℝ), ∃ S, Config r s B S := by
  induction r generalizing s with
  | zero => exact ⟨0, le_rfl, {0}, singleton_config 0 s (by simp)⟩
  | succ r ihr =>
    induction s with
    | zero => exact ⟨0, le_rfl, {0}, singleton_config (r + 1) 0 (by simp)⟩
    | succ s ihs =>
      obtain ⟨A, hA, L, hL⟩ := ihs
      obtain ⟨B, _, R, hR⟩ := ihr (s + 1)
      exact join_configs hA hL hR

/-- The point on the chord with the same abscissa as b records the orientation of a,b,c. -/
private lemma chord {K : Set Point} (hK : Convex ℝ K) {a b c : Point} (ha : a ∈ K) (hc : c ∈ K)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) :
    ∃ p ∈ K, p.1 = b.1 ∧ orient a b c = (c.1 - a.1) * (p.2 - b.2) := by
  have hden : 0 < c.1 - a.1 := by linarith
  let t := (b.1 - a.1) / (c.1 - a.1)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.2 hab.le) hden.le
  have ht1 : t ≤ 1 := (div_le_iff₀ hden).2 (by linarith)
  have he : t * (c.1 - a.1) = b.1 - a.1 := div_mul_cancel₀ _ hden.ne'
  let p := (1 - t) • a + t • c
  refine ⟨p, hK ha hc (sub_nonneg.2 ht1) ht0 (by ring), ?_, ?_⟩
  · change (1 - t) * a.1 + t * c.1 = b.1
    linarith only [he]
  · change orient a b c = (c.1 - a.1) * ((1 - t) * a.2 + t * c.2 - b.2)
    unfold orient
    linear_combination -(c.2 - a.2) * he

private lemma between_vertical {K : Set Point} (hK : Convex ℝ K) {p b q : Point}
    (hp : p ∈ K) (hq : q ∈ K) (hpx : p.1 = b.1) (hqx : q.1 = b.1)
    (hpy : p.2 < b.2) (hqy : b.2 < q.2) : b ∈ K := by
  have hden : 0 < q.2 - p.2 := by linarith
  let t := (b.2 - p.2) / (q.2 - p.2)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.2 hpy.le) hden.le
  have ht1 : t ≤ 1 := (div_le_iff₀ hden).2 (by linarith)
  have he : t * (q.2 - p.2) = b.2 - p.2 := div_mul_cancel₀ _ hden.ne'
  have hm : (1 - t) • p + t • q ∈ K := hK hp hq (sub_nonneg.2 ht1) ht0 (by ring)
  have heq : (1 - t) • p + t • q = b := by
    apply Prod.ext
    · change (1 - t) * p.1 + t * q.1 = b.1
      rw [hpx, hqx]
      ring
    · change (1 - t) * p.2 + t * q.2 = b.2
      linarith only [he]
  exact heq ▸ hm

private lemma no_opposite_chords {T : Finset Point}
    (hconv : ConvexIndependent ℝ ((↑) : ↥(T : Set Point) → Point))
    {a b c d e : Point} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hd : d ∈ T) (he : e ∈ T)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) (hdb : d.1 < b.1) (hbe : b.1 < e.1)
    (hneg : orient a b c < 0) (hpos : 0 < orient d b e) : False := by
  let K := convexHull ℝ ((T : Set Point) \ {b})
  have hK : Convex ℝ K := convex_convexHull _ _
  have hmem (u : Point) (hu : u ∈ T) (hne : u.1 ≠ b.1) : u ∈ K :=
    subset_convexHull _ _ ⟨hu, fun heq => hne (congrArg Prod.fst heq)⟩
  obtain ⟨p, hp, hpx, hpo⟩ := chord hK (hmem a ha hab.ne) (hmem c hc hbc.ne') hab hbc
  obtain ⟨q, hq, hqx, hqo⟩ := chord hK (hmem d hd hdb.ne) (hmem e he hbe.ne') hdb hbe
  have hpy : p.2 < b.2 := by
    have hneg' : (c.1 - a.1) * (p.2 - b.2) < 0 := hpo ▸ hneg
    have hden : 0 < c.1 - a.1 := by linarith
    exact sub_neg.1 (neg_of_mul_neg_right hneg' hden.le)
  have hqy : b.2 < q.2 := by
    have hpos' : 0 < (e.1 - d.1) * (q.2 - b.2) := hqo ▸ hpos
    have hden : 0 < e.1 - d.1 := by linarith
    exact sub_pos.1 (pos_of_mul_pos_right hpos' hden.le)
  exact (convexIndependent_set_iff_notMem_convexHull_sdiff.1 hconv) b hb
    (between_vertical hK hp hq hpx hqx hpy hqy)

private def LowerAt (T : Finset Point) (b : Point) : Prop :=
  ∀ ⦃a c : Point⦄, a ∈ T → c ∈ T → a.1 < b.1 → b.1 < c.1 → 0 < orient a b c

private lemma collinear_orient {K : Set Point} (h : Collinear ℝ K) {a b c : Point}
    (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) : orient a b c = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem ha).1 h
  obtain ⟨s, hs⟩ := hv b hb
  obtain ⟨t, ht⟩ := hv c hc
  change b = s • v + a at hs
  change c = t • v + a at ht
  rw [hs, ht]
  unfold orient
  change (s * v.1 + a.1 - a.1) * (t * v.2 + a.2 - (s * v.2 + a.2)) -
    (s * v.2 + a.2 - a.2) * (t * v.1 + a.1 - (s * v.1 + a.1)) = 0
  ring


private noncomputable def margin (m : ℕ) : ℝ := 1 / (10 * (2 * (m : ℝ) + 1))

private lemma margin_pos (m : ℕ) : 0 < margin m := by unfold margin; positivity

private lemma margin_le (m : ℕ) : margin m ≤ 1 / 10 := by
  unfold margin
  apply (div_le_iff₀ (by positivity)).2
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

private noncomputable def factor (m W : ℕ) (B : ℝ) : ℝ :=
  margin m / ((B + 2) * ((W : ℝ) + 2))

private lemma factor_pos (m W : ℕ) {B : ℝ} (hB : 0 ≤ B) : 0 < factor m W B :=
  div_pos (margin_pos m) (by positivity)

private noncomputable def place (m i W : ℕ) (B : ℝ) (p : Point) : Point :=
  ((i : ℝ) + factor m W B * p.1, -(i : ℝ)^2 + factor m W B * (p.2 + (B + 1) * p.1))

private lemma place_x_iff (m i W : ℕ) {B : ℝ} (hB : 0 ≤ B) (a b : Point) :
    (place m i W B a).1 < (place m i W B b).1 ↔ a.1 < b.1 := by
  change (i : ℝ) + factor m W B * a.1 < (i : ℝ) + factor m W B * b.1 ↔ a.1 < b.1
  rw [add_lt_add_iff_left, mul_lt_mul_iff_of_pos_left (factor_pos m W hB)]

private lemma place_x_eq (m i W : ℕ) {B : ℝ} (hB : 0 ≤ B) {a b : Point}
    (h : (place m i W B a).1 = (place m i W B b).1) : a.1 = b.1 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ((place_x_iff m i W hB a b).2 hlt).ne h
  · exact ((place_x_iff m i W hB b a).2 hlt).ne h.symm

private lemma place_injective (m i W : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    Function.Injective (place m i W B) := by
  intro a b he
  have hx := place_x_eq m i W hB (congrArg Prod.fst he)
  have hy := congrArg Prod.snd he
  change -(i : ℝ)^2 + factor m W B * (a.2 + (B + 1) * a.1) =
    -(i : ℝ)^2 + factor m W B * (b.2 + (B + 1) * b.1) at hy
  rw [add_right_inj, mul_right_inj' (factor_pos m W hB).ne', hx, add_left_inj] at hy
  exact Prod.ext hx hy

private lemma orient_place (m i W : ℕ) (B : ℝ) (a b c : Point) :
    orient (place m i W B a) (place m i W B b) (place m i W B c) =
      (factor m W B)^2 * orient a b c := by
  unfold orient place
  dsimp only
  ring

private def Near (m i : ℕ) (p : Point) : Prop :=
  (i : ℝ) ≤ p.1 ∧ p.1 ≤ (i : ℝ) + margin m ∧
    -(i : ℝ)^2 ≤ p.2 ∧ p.2 ≤ -(i : ℝ)^2 + margin m

private lemma place_near (m i : ℕ) {W : ℕ} {B : ℝ} (hB : 0 ≤ B)
    {S : Finset Point} (hbox : Box W B S) {a : Point} (ha : a ∈ S) :
    Near m i (place m i W B a) := by
  obtain ⟨hx₀, hx, hy₀, hy⟩ := box_bounds hbox ha
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  let t := factor m W B
  let d := (B + 2) * ((W : ℝ) + 2)
  have ht : 0 < t := factor_pos m W hB
  have hd : 0 < d := by dsimp [d]; positivity
  have htd : t * d = margin m := div_mul_cancel₀ _ hd.ne'
  have hxd : a.1 ≤ d := by
    dsimp [d]
    nlinarith only [hx, hW, hB, mul_nonneg hB hW]
  have hyd : a.2 + (B + 1) * a.1 ≤ d := by
    have h := mul_le_mul_of_nonneg_left hx.le (show 0 ≤ B + 1 by positivity)
    dsimp [d]
    linarith only [h, hy, hB, hW]
  have hx₁ := mul_le_mul_of_nonneg_left hxd ht.le
  have hy₁ := mul_le_mul_of_nonneg_left hyd ht.le
  rw [htd] at hx₁ hy₁
  have hx₂ : 0 ≤ t * a.1 := mul_nonneg ht.le hx₀
  have hy₂ : 0 ≤ t * (a.2 + (B + 1) * a.1) := by positivity
  change (i : ℝ) ≤ (i : ℝ) + t * a.1 ∧
    (i : ℝ) + t * a.1 ≤ (i : ℝ) + margin m ∧
    -(i : ℝ)^2 ≤ -(i : ℝ)^2 + t * (a.2 + (B + 1) * a.1) ∧
    -(i : ℝ)^2 + t * (a.2 + (B + 1) * a.1) ≤ -(i : ℝ)^2 + margin m
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private noncomputable def slope (a b : Point) : ℝ := (b.2 - a.2) / (b.1 - a.1)

private lemma orient_as_slope {a b c : Point} (hab : a.1 < b.1) (hbc : b.1 < c.1) :
    orient a b c = (b.1 - a.1) * (c.1 - b.1) * (slope b c - slope a b) := by
  unfold orient slope
  field_simp [sub_ne_zero.mpr hab.ne', sub_ne_zero.mpr hbc.ne']

private lemma orient_pos_of_slope {a b c : Point} (hab : a.1 < b.1) (hbc : b.1 < c.1)
    (hs : slope a b < slope b c) : 0 < orient a b c := by
  rw [orient_as_slope hab hbc]
  exact mul_pos (mul_pos (sub_pos.2 hab) (sub_pos.2 hbc)) (sub_pos.2 hs)

private lemma orient_neg_of_slope {a b c : Point} (hab : a.1 < b.1) (hbc : b.1 < c.1)
    (hs : slope b c < slope a b) : orient a b c < 0 := by
  rw [orient_as_slope hab hbc]
  exact mul_neg_of_pos_of_neg (mul_pos (sub_pos.2 hab) (sub_pos.2 hbc)) (sub_neg.2 hs)

private lemma placed_slope_pos (m i : ℕ) {W : ℕ} {B : ℝ} (hB : 0 ≤ B)
    {S : Finset Point} (hbox : Box W B S) {a b : Point} (ha : a ∈ S) (hb : b ∈ S)
    (hab : (place m i W B a).1 < (place m i W B b).1) :
    0 < slope (place m i W B a) (place m i W B b) := by
  have hd := (internal_gap hbox ha hb ((place_x_iff m i W hB a b).1 hab)).1
  obtain ⟨-, -, -, ha'⟩ := box_bounds hbox ha
  obtain ⟨-, -, hb', -⟩ := box_bounds hbox hb
  have hy : 0 < b.2 - a.2 + (B + 1) * (b.1 - a.1) := by
    have h := mul_le_mul_of_nonneg_left hd (show 0 ≤ B + 1 by positivity)
    linarith
  have h := mul_pos (factor_pos m W hB) hy
  unfold slope
  refine div_pos ?_ (sub_pos.2 hab)
  change -(i : ℝ)^2 + factor m W B * (b.2 + (B + 1) * b.1) -
    (-(i : ℝ)^2 + factor m W B * (a.2 + (B + 1) * a.1)) > 0
  linarith only [h]

private lemma cross_slope {m i j : ℕ} {a b : Point}
    (hij : i < j) (hjm : j ≤ m) (ha : Near m i a) (hb : Near m j b) :
    a.1 < b.1 ∧ -(i : ℝ) - (j : ℝ) - 1 / 4 < slope a b ∧
      slope a b < -(i : ℝ) - (j : ℝ) + 1 / 4 := by
  obtain ⟨hax₀, hax₁, hay₀, hay₁⟩ := ha
  obtain ⟨hbx₀, hbx₁, hby₀, hby₁⟩ := hb
  let d := margin m
  let τ := (i : ℝ) + (j : ℝ)
  have hd := margin_le m
  have hd0 := (margin_pos m).le
  have hgap : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
  have hix : (i : ℝ) ≤ m := by exact_mod_cast (hij.le.trans hjm)
  have hjx : (j : ℝ) ≤ m := by exact_mod_cast hjm
  have ht₀ : 0 ≤ τ := by dsimp [τ]; positivity
  have ht₁ : τ ≤ 2 * (m : ℝ) := by dsimp [τ]; linarith
  have hdx : (9 : ℝ) / 10 ≤ b.1 - a.1 := by linarith
  have hdx0 : 0 < b.1 - a.1 := by linarith
  let ex := b.1 - (j : ℝ) - (a.1 - (i : ℝ))
  let ey := b.2 + (j : ℝ)^2 - (a.2 + (i : ℝ)^2)
  have hex : -d ≤ ex ∧ ex ≤ d := by dsimp [ex, d]; constructor <;> linarith
  have hey : -d ≤ ey ∧ ey ≤ d := by dsimp [ey, d]; constructor <;> linarith
  have heql : b.2 - a.2 + τ * (b.1 - a.1) = ey + τ * ex := by dsimp [τ, ey, ex]; ring
  have htd : τ * d ≤ (2 * (m : ℝ)) * d := mul_le_mul_of_nonneg_right ht₁ hd0
  have htExL := mul_le_mul_of_nonneg_left hex.1 ht₀
  have htExR := mul_le_mul_of_nonneg_left hex.2 ht₀
  have hdelta : d * (10 * (2 * (m : ℝ) + 1)) = 1 := by
    dsimp [d, margin]
    exact div_mul_cancel₀ _ (by positivity)
  have hErrL : -(1 : ℝ) / 10 ≤ b.2 - a.2 + τ * (b.1 - a.1) := by
    rw [heql]
    linarith only [hdelta, htd, hey.1, htExL]
  have hErrR : b.2 - a.2 + τ * (b.1 - a.1) ≤ (1 : ℝ) / 10 := by
    rw [heql]
    linarith only [hdelta, htd, hey.2, htExR]
  refine ⟨sub_pos.1 hdx0, ?_, ?_⟩
  · unfold slope
    apply (lt_div_iff₀ hdx0).2
    dsimp [τ] at hErrL
    linarith only [hErrL, hdx]
  · unfold slope
    apply (div_lt_iff₀ hdx0).2
    dsimp [τ] at hErrR
    linarith only [hErrR, hdx]

private lemma cross_slope_neg {m i j : ℕ} {a b : Point}
    (hij : i < j) (hjm : j ≤ m) (ha : Near m i a) (hb : Near m j b) :
    slope a b < 0 := by
  have h := (cross_slope hij hjm ha hb).2.2
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  linarith

private lemma cross_three_neg {m i j k : ℕ} {a b c : Point}
    (hij : i < j) (hjk : j < k) (hkm : k ≤ m)
    (ha : Near m i a) (hb : Near m j b) (hc : Near m k c) :
    orient a b c < 0 := by
  obtain ⟨hab, hl, -⟩ := cross_slope hij (hjk.le.trans hkm) ha hb
  obtain ⟨hbc, -, hh⟩ := cross_slope hjk hkm hb hc
  have hi : (i : ℝ) + 1 ≤ k := by exact_mod_cast (hij.trans hjk)
  exact orient_neg_of_slope hab hbc (by linarith)


private structure Blocks (m : ℕ) (Q : Fin (m + 1) → Finset Point) : Prop where
  card : ∀ i, (Q i).card = m.choose i.val
  near : ∀ i, ∀ p ∈ Q i, Near m i.val p
  inj : ∀ i, Set.InjOn Prod.fst (Q i : Set Point)
  nonzero : ∀ i, ∀ ⦃a b c : Point⦄, a ∈ Q i → b ∈ Q i → c ∈ Q i → a.1 < b.1 → b.1 < c.1 →
    orient a b c ≠ 0
  pos : ∀ i, ∀ ⦃a b : Point⦄, a ∈ Q i → b ∈ Q i → a.1 < b.1 → 0 < slope a b
  chain : ∀ i (up : Bool) (T : Finset Point), T ⊆ Q i → Chain up T →
    T.card ≤ if up then m - i.val + 1 else i.val + 1

private lemma blocks_exist (m : ℕ) : ∃ Q, Blocks m Q := by
  classical
  have hex (i : Fin (m + 1)) := configurations i.val (m - i.val)
  choose B hB S hS using hex
  let W (i : Fin (m + 1)) := (i.val + (m - i.val)).choose i.val
  let f (i : Fin (m + 1)) := place m i.val (W i) (B i)
  let Q (i : Fin (m + 1)) := (S i).image (f i)
  have hf (i : Fin (m + 1)) : Function.Injective (f i) := place_injective m _ _ (hB i)
  have hmem {i : Fin (m + 1)} {a : Point} (ha : a ∈ Q i) :
      ∃ b ∈ S i, f i b = a := Finset.mem_image.1 ha
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change ((S i).image (f i)).card = _
    have hi : i.val + (m - i.val) = m := by have := i.isLt; omega
    rw [Finset.card_image_of_injective _ (hf i), (hS i).card, hi]
  · intro i a ha
    obtain ⟨b, hb, rfl⟩ := hmem ha
    exact place_near m _ (hB i) (hS i).box hb
  · intro i a ha b hb he
    obtain ⟨a', ha', rfl⟩ := hmem ha
    obtain ⟨b', hb', rfl⟩ := hmem hb
    exact congrArg (f i) ((hS i).inj ha' hb' (place_x_eq m _ _ (hB i) he))
  · intro i a b c ha hb hc hab hbc
    obtain ⟨a', ha', rfl⟩ := hmem ha
    obtain ⟨b', hb', rfl⟩ := hmem hb
    obtain ⟨c', hc', rfl⟩ := hmem hc
    change orient (place m i.val (W i) (B i) a') (place m i.val (W i) (B i) b')
      (place m i.val (W i) (B i) c') ≠ 0
    rw [orient_place]
    exact mul_ne_zero (pow_ne_zero _ (factor_pos m _ (hB i)).ne')
      ((hS i).nonzero ha' hb' hc' ((place_x_iff m _ _ (hB i) _ _).1 hab)
        ((place_x_iff m _ _ (hB i) _ _).1 hbc))
  · intro i a b ha hb hab
    obtain ⟨a', ha', rfl⟩ := hmem ha
    obtain ⟨b', hb', rfl⟩ := hmem hb
    exact placed_slope_pos m _ (hB i) (hS i).box ha' hb' hab
  · intro i up T hT ht
    obtain ⟨Z, hZ, hcZ, hchain⟩ := image_invariant_chain (hf i) (place_x_iff m _ _ (hB i))
      up (fun a b c h => by
        change (if up then 0 < orient (place m i.val (W i) (B i) a) (place m i.val (W i) (B i) b)
          (place m i.val (W i) (B i) c) else orient (place m i.val (W i) (B i) a)
          (place m i.val (W i) (B i) b) (place m i.val (W i) (B i) c) < 0) at h
        rw [orient_place] at h
        have hk : 0 < (factor m (W i) (B i)) ^ 2 := pow_pos (factor_pos m _ (hB i)) _
        cases up
        · exact neg_of_mul_neg_right h hk.le
        · exact (mul_pos_iff_of_pos_left hk).1 h) hT ht
    rw [← hcZ]
    exact (hS i).chain_card up Z hZ hchain

private lemma across_x {m : ℕ} {Q : Fin (m + 1) → Finset Point} (hQ : Blocks m Q)
    {i j : Fin (m + 1)} {a b : Point} (hi : i < j) (ha : a ∈ Q i) (hb : b ∈ Q j) :
    a.1 < b.1 :=
  (cross_slope hi (by have := j.isLt; omega) (hQ.near i a ha) (hQ.near j b hb)).1

private lemma across_slope {m : ℕ} {Q : Fin (m + 1) → Finset Point} (hQ : Blocks m Q)
    {i j : Fin (m + 1)} {a b : Point} (hi : i < j) (ha : a ∈ Q i) (hb : b ∈ Q j) :
    slope a b < 0 :=
  cross_slope_neg hi (by have := j.isLt; omega) (hQ.near i a ha) (hQ.near j b hb)

private lemma across_three {m : ℕ} {Q : Fin (m + 1) → Finset Point} (hQ : Blocks m Q)
    {i j k : Fin (m + 1)} {a b c : Point}
    (hij : i < j) (hjk : j < k) (ha : a ∈ Q i) (hb : b ∈ Q j) (hc : c ∈ Q k) :
    orient a b c < 0 :=
  cross_three_neg hij hjk (by have := k.isLt; omega) (hQ.near i a ha) (hQ.near j b hb) (hQ.near k c hc)

private lemma across_pos {m : ℕ} {Q : Fin (m + 1) → Finset Point} (hQ : Blocks m Q)
    {i j : Fin (m + 1)} {a b c : Point}
    (hij : i < j) (ha : a ∈ Q i) (hb : b ∈ Q j) (hc : c ∈ Q j) (hbc : b.1 < c.1) :
    0 < orient a b c :=
  orient_pos_of_slope (across_x hQ hij ha hb) hbc
    ((across_slope hQ hij ha hb).trans (hQ.pos j hb hc hbc))

private lemma across_neg {m : ℕ} {Q : Fin (m + 1) → Finset Point} (hQ : Blocks m Q)
    {i j : Fin (m + 1)} {a b c : Point}
    (hij : i < j) (ha : a ∈ Q i) (hb : b ∈ Q i) (hc : c ∈ Q j) (hab : a.1 < b.1) :
    orient a b c < 0 :=
  orient_neg_of_slope hab (across_x hQ hij hb hc)
    ((across_slope hQ hij hb hc).trans (hQ.pos i ha hb hab))

private lemma one_block_convex {m : ℕ} {Q : Fin (m + 1) → Finset Point} (hQ : Blocks m Q)
    {i : Fin (m + 1)} {T : Finset Point} (hT : T ⊆ Q i) (hne : T.Nonempty)
    (hc : ConvexIndependent ℝ ((↑) : ↥(T : Set Point) → Point)) : T.card ≤ m + 1 := by
  classical
  obtain ⟨z, hz, hzmin⟩ := Finset.exists_min_image T Prod.fst hne
  let A := T.filter (LowerAt T)
  let D := T.filter fun p => ¬ LowerAt T p
  let D' := insert z D
  have hA : A ⊆ T := Finset.filter_subset _ _
  have hD : D ⊆ T := Finset.filter_subset _ _
  have hD' : D' ⊆ T := Finset.insert_subset_iff.2 ⟨hz, hD⟩
  have hzlow : LowerAt T z := by
    intro a c ha _ hab _
    exact ((hzmin a ha).not_gt hab).elim
  have hzD : z ∉ D := fun h => (Finset.mem_filter.1 h).2 hzlow
  have ha : Chain true A := by
    intro a b c ha hb hc hab hbc
    exact (Finset.mem_filter.1 hb).2 (hA ha) (hA hc) hab hbc
  have hd : Chain false D' := by
    intro a b c ha hb hcc hab hbc
    have hn : ¬ LowerAt T b := by
      rcases Finset.mem_insert.1 hb with he | he
      · subst b
        exact ((hzmin a (hD' ha)).not_gt hab).elim
      · exact (Finset.mem_filter.1 he).2
    unfold LowerAt at hn
    push Not at hn
    obtain ⟨x, y, hx, hy, hxb, hby, hxy⟩ := hn
    have hneg : orient x b y < 0 :=
      lt_of_le_of_ne hxy (hQ.nonzero i (hT hx) (hT (hD' hb)) (hT hy) hxb hby)
    change orient a b c < 0
    by_contra! hp
    have hp' := lt_of_le_of_ne hp (hQ.nonzero i (hT (hD' ha)) (hT (hD' hb)) (hT (hD' hcc)) hab hbc).symm
    exact no_opposite_chords hc hx (hD' hb) hy (hD' ha) (hD' hcc) hxb hby hab hbc hneg hp'
  have hcA : A.card ≤ m - i.val + 1 := hQ.chain i true A (hA.trans hT) ha
  have hcD : D'.card ≤ i.val + 1 := hQ.chain i false D' (hD'.trans hT) hd
  have hsum : A.card + D.card = T.card := Finset.card_filter_add_card_filter_not (LowerAt T)
  rw [show D'.card = D.card + 1 from Finset.card_insert_of_notMem hzD] at hcD
  have hi := i.isLt
  omega


private noncomputable def assembled {m : ℕ} (Q : Fin (m + 1) → Finset Point) : Finset Point :=
  by classical exact univ.biUnion Q

private lemma mem_assembled {m : ℕ} {Q : Fin (m + 1) → Finset Point} {p : Point} :
    p ∈ assembled Q ↔ ∃ i, p ∈ Q i := by
  classical
  simp [assembled, Finset.mem_biUnion]

private lemma assembled_card {m : ℕ} {Q : Fin (m + 1) → Finset Point} (hQ : Blocks m Q) :
    (assembled Q).card = 2 ^ m := by
  classical
  have hdis : (↑(univ : Finset (Fin (m + 1))) : Set (Fin (m + 1))).PairwiseDisjoint Q := by
    intro i _ j _ hij
    apply Finset.disjoint_left.2
    intro p hp hq
    rcases lt_or_gt_of_ne hij with h | h
    · exact (lt_irrefl _) (across_x hQ h hp hq)
    · exact (lt_irrefl _) (across_x hQ h hq hp)
  unfold assembled
  rw [Finset.card_biUnion hdis]
  simp only [hQ.card]
  rw [Fin.sum_univ_eq_sum_range, Nat.sum_range_choose]

private lemma assembled_inj {m : ℕ} {Q : Fin (m + 1) → Finset Point} (hQ : Blocks m Q) :
    Set.InjOn Prod.fst (assembled Q : Set Point) := by
  intro a ha b hb he
  obtain ⟨i, hi⟩ := mem_assembled.1 ha
  obtain ⟨j, hj⟩ := mem_assembled.1 hb
  rcases lt_trichotomy i j with h | rfl | h
  · exact ((across_x hQ h hi hj).ne he).elim
  · exact hQ.inj i hi hj he
  · exact ((across_x hQ h hj hi).ne he.symm).elim

private lemma assembled_nonzero {m : ℕ} {Q : Fin (m + 1) → Finset Point} (hQ : Blocks m Q)
    {a b c : Point} (ha : a ∈ assembled Q) (hb : b ∈ assembled Q) (hc : c ∈ assembled Q)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) : orient a b c ≠ 0 := by
  obtain ⟨i, hi⟩ := mem_assembled.1 ha
  obtain ⟨j, hj⟩ := mem_assembled.1 hb
  obtain ⟨k, hk⟩ := mem_assembled.1 hc
  have hij : i ≤ j := le_of_not_gt fun h => (across_x hQ h hj hi).not_gt hab
  have hjk : j ≤ k := le_of_not_gt fun h => (across_x hQ h hk hj).not_gt hbc
  rcases eq_or_lt_of_le hij with rfl | h
  · rcases eq_or_lt_of_le hjk with rfl | h'
    · exact hQ.nonzero i hi hj hk hab hbc
    · exact (across_neg hQ h' hi hj hk hab).ne
  · rcases eq_or_lt_of_le hjk with rfl | h'
    · exact (across_pos hQ h hi hj hk hbc).ne'
    · exact (across_three hQ h h' hi hj hk).ne

/-- Earlier and later occupied blocks force the end chains and allow one point per middle block. -/
private lemma assembled_convex_card {m : ℕ} {Q : Fin (m + 1) → Finset Point} (hQ : Blocks m Q)
    {T : Finset Point} (hT : T ⊆ assembled Q)
    (hconv : ConvexIndependent ℝ ((↑) : ↥(T : Set Point) → Point)) : T.card ≤ m + 1 := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
  let B (i : Fin (m + 1)) := T ∩ Q i
  let I : Finset (Fin (m + 1)) := univ.filter fun i => (B i).Nonempty
  have hIn {i : Fin (m + 1)} (h : (B i).Nonempty) : i ∈ I :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
  have hProp {i : Fin (m + 1)} (h : i ∈ I) : (B i).Nonempty := (Finset.mem_filter.1 h).2
  have hLoc {p : Point} (hp : p ∈ T) : ∃ i ∈ I, p ∈ B i := by
    obtain ⟨i, hi⟩ := mem_assembled.1 (hT hp)
    have hh : p ∈ B i := Finset.mem_inter.2 ⟨hp, hi⟩
    exact ⟨i, hIn ⟨p, hh⟩, hh⟩
  have hTne := hne
  obtain ⟨p, hp⟩ := hTne
  obtain ⟨i, hi, _⟩ := hLoc hp
  let hI : I.Nonempty := ⟨i, hi⟩
  let a := I.min' hI
  let b := I.max' hI
  have ha : a ∈ I := Finset.min'_mem I hI
  have hb : b ∈ I := Finset.max'_mem I hI
  have hlo {i : Fin (m + 1)} (hi : i ∈ I) : a ≤ i := Finset.min'_le I i hi
  have hhi {i : Fin (m + 1)} (hi : i ∈ I) : i ≤ b := Finset.le_max' I i hi
  rcases eq_or_lt_of_le (hlo hb) with he | hlt
  · have hs : T ⊆ Q a := by
      intro x hx
      obtain ⟨j, hj, hmem⟩ := hLoc hx
      have heq : j = a := le_antisymm ((hhi hj).trans he.ge) (hlo hj)
      subst j
      exact (Finset.mem_inter.1 hmem).2
    exact one_block_convex hQ hs hne hconv
  obtain ⟨p, hp⟩ := hProp ha
  obtain ⟨q, hq⟩ := hProp hb
  obtain ⟨hpT, hpQ⟩ := Finset.mem_inter.1 hp
  obtain ⟨hqT, hqQ⟩ := Finset.mem_inter.1 hq
  have hA : Chain false (B a) := by
    intro x y z hx hy hz hxy hyz
    obtain ⟨hxT, hxQ⟩ := Finset.mem_inter.1 hx
    obtain ⟨hyT, hyQ⟩ := Finset.mem_inter.1 hy
    obtain ⟨hzT, hzQ⟩ := Finset.mem_inter.1 hz
    change orient x y z < 0
    by_contra! h
    have hpos := lt_of_le_of_ne h (hQ.nonzero a hxQ hyQ hzQ hxy hyz).symm
    exact no_opposite_chords hconv hxT hyT hqT hxT hzT hxy (across_x hQ hlt hyQ hqQ)
      hxy hyz (across_neg hQ hlt hxQ hyQ hqQ hxy) hpos
  have hB : Chain true (B b) := by
    intro x y z hx hy hz hxy hyz
    obtain ⟨hxT, hxQ⟩ := Finset.mem_inter.1 hx
    obtain ⟨hyT, hyQ⟩ := Finset.mem_inter.1 hy
    obtain ⟨hzT, hzQ⟩ := Finset.mem_inter.1 hz
    change 0 < orient x y z
    by_contra! h
    have hneg := lt_of_le_of_ne h (hQ.nonzero b hxQ hyQ hzQ hxy hyz)
    exact no_opposite_chords hconv hxT hyT hzT hpT hzT hxy hyz (across_x hQ hlt hpQ hyQ)
      hyz hneg (across_pos hQ hlt hpQ hyQ hzQ hyz)
  have hab {i : Fin (m + 1)} (hai : a < i) (hib : i < b) : (B i).card ≤ 1 := by
    refine Finset.card_le_one_iff.2 fun {x y} hx hy => ?_
    obtain ⟨hxT, hxQ⟩ := Finset.mem_inter.1 hx
    obtain ⟨hyT, hyQ⟩ := Finset.mem_inter.1 hy
    by_contra hne'
    have hneq : x.1 ≠ y.1 := fun he => hne' (hQ.inj i hxQ hyQ he)
    have hbad {x y : Point} (hxT : x ∈ T) (hyT : y ∈ T) (hxQ : x ∈ Q i) (hyQ : y ∈ Q i)
        (hxy : x.1 < y.1) : False :=
      no_opposite_chords hconv hpT hxT hqT hpT hyT (across_x hQ hai hpQ hxQ)
        (across_x hQ hib hxQ hqQ) (across_x hQ hai hpQ hxQ) hxy
        (across_three hQ hai hib hpQ hxQ hqQ) (across_pos hQ hai hpQ hxQ hyQ hxy)
    exact (lt_or_gt_of_ne hneq).elim (hbad hxT hyT hxQ hyQ) (hbad hyT hxT hyQ hxQ)
  let M := Finset.Ioo a b
  have hsub : T ⊆ (B a ∪ B b) ∪ M.biUnion B := by
    intro x hx
    obtain ⟨i, hi, hBi⟩ := hLoc hx
    rcases eq_or_lt_of_le (hlo hi) with rfl | hai
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hBi)
    rcases eq_or_lt_of_le (hhi hi) with rfl | hib
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hBi)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_Ioo.2 ⟨hai, hib⟩, hBi⟩)
  have hmid : (M.biUnion B).card ≤ M.card := by
    have h := Finset.card_biUnion_le_card_mul M B 1 (fun i hi =>
      hab (Finset.mem_Ioo.1 hi).1 (Finset.mem_Ioo.1 hi).2)
    simpa using h
  have hM : M.card = b.val - a.val - 1 := Fin.card_Ioo a b
  have hAc : (B a).card ≤ a.val + 1 := hQ.chain a false (B a) Finset.inter_subset_right hA
  have hBc : (B b).card ≤ m - b.val + 1 := hQ.chain b true (B b) Finset.inter_subset_right hB
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hh := Finset.card_union_le (B a) (B b)
  have hbval := b.isLt
  have habval : a.val < b.val := hlt
  omega

private lemma not_collinear_of_sorted {S : Finset Point}
    (hex : Set.InjOn Prod.fst (S : Set Point))
    (hdet : ∀ ⦃a b c⦄, a ∈ S → b ∈ S → c ∈ S → a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
    {a b c : Point} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : ¬ Collinear ℝ ({a, b, c} : Set Point) := by
  have habx : a.1 ≠ b.1 := fun h => hab (hex ha hb h)
  have hacx : a.1 ≠ c.1 := fun h => hac (hex ha hc h)
  have hbcx : b.1 ≠ c.1 := fun h => hbc (hex hb hc h)
  intro h
  have hbad {x y z : Point} (hx : x ∈ ({a, b, c} : Set Point))
      (hy : y ∈ ({a, b, c} : Set Point)) (hz : z ∈ ({a, b, c} : Set Point))
      (hxy : x.1 < y.1) (hyz : y.1 < z.1) : False := by
    have hsub : ({a, b, c} : Set Point) ⊆ (S : Set Point) := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    exact (hdet (hsub hx) (hsub hy) (hsub hz) hxy hyz) (collinear_orient h hx hy hz)
  rcases lt_or_gt_of_ne habx with h1 | h1
  · rcases lt_or_gt_of_ne hbcx with h2 | h2
    · exact hbad (by simp) (by simp) (by simp) h1 h2
    rcases lt_or_gt_of_ne hacx with h3 | h3
    · exact hbad (by simp) (by simp) (by simp) h3 h2
    · exact hbad (by simp) (by simp) (by simp) h3 h1
  · rcases lt_or_gt_of_ne hacx with h3 | h3
    · exact hbad (by simp) (by simp) (by simp) h1 h3
    rcases lt_or_gt_of_ne hbcx with h2 | h2
    · exact hbad (by simp) (by simp) (by simp) h2 h3
    · exact hbad (by simp) (by simp) (by simp) h2 h1

private noncomputable def coords : ℝ² ≃ₗ[ℝ] Point :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv.trans (LinearEquiv.piFinTwo ℝ (fun _ => ℝ))

theorem witness (m : ℕ) :
    ∃ X : Finset ℝ², X.card = 2 ^ m ∧ NonTrilinear (X : Set ℝ²) ∧
      ∀ Y ⊆ X, ConvexIndep (Y : Set ℝ²) → Y.card ≤ m + 1 := by
  classical
  obtain ⟨Q, hQ⟩ := blocks_exist m
  let S := assembled Q
  let e := coords
  let X := S.image e.symm
  have hXcard : X.card = 2 ^ m := by
    rw [Finset.card_image_of_injective _ e.symm.injective, assembled_card hQ]
  have hInv {x : ℝ²} (hx : x ∈ X) : e x ∈ S := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    simpa using hp
  refine ⟨X, hXcard, ?_, ?_⟩
  · intro a ha b hb c hc hab hbc hac
    have htri := not_collinear_of_sorted (assembled_inj hQ)
      (fun {x y z} hx hy hz hxy hyz => assembled_nonzero hQ hx hy hz hxy hyz)
      (hInv ha) (hInv hb) (hInv hc)
      (fun he => hab (e.injective he)) (fun he => hac (e.injective he)) (fun he => hbc (e.injective he))
    apply affineIndependent_iff_not_collinear_set.1
    apply AffineIndependent.of_comp e.toAffineMap
    have hvec : (e : ℝ² → Point) ∘ ![a, b, c] = ![e a, e b, e c] := by
      funext i
      fin_cases i <;> rfl
    change AffineIndependent ℝ ((e : ℝ² → Point) ∘ ![a, b, c])
    rw [hvec]
    exact affineIndependent_iff_not_collinear_set.2 htri
  · intro Y hY hc
    let T := Y.image e
    have hT : T ⊆ S := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
      exact hInv (hY hq)
    have hTc : ConvexIndependent ℝ ((↑) : ↥(T : Set Point) → Point) := by
      rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
      intro p hp hpHull
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
      apply hc q hq
      have himage : e.symm '' ((T : Set Point) \ {e q}) ⊆ (Y : Set ℝ²) \ {q} := by
        rintro _ ⟨u, hu, rfl⟩
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hu.1
        refine ⟨by simpa using hv, ?_⟩
        simpa using show e v ≠ e q from hu.2
      apply convexHull_mono himage
      change q ∈ convexHull ℝ (e.symm.toLinearMap '' ((T : Set Point) \ {e q}))
      rw [← e.symm.toLinearMap.image_convexHull]
      exact ⟨e q, hpHull, e.symm_apply_apply q⟩
    have h := assembled_convex_card hQ hT hTc
    change (Y.image e).card ≤ _ at h
    rwa [Finset.card_image_of_injective _ e.injective] at h


theorem lower {n : ℕ} (hn : 3 ≤ n) (hne : (Erdos107.cardSet n).Nonempty) :
    2 ^ (n - 2) + 1 ≤ Erdos107.f n := by
  have hf : Erdos107.f n ∈ Erdos107.cardSet n := Nat.sInf_mem hne
  by_contra! h
  obtain ⟨X, hXcard, hX, hXconv⟩ := witness (n - 2)
  have hsmall : Erdos107.f n ≤ X.card := by omega
  obtain ⟨X', hSub, hCard⟩ := Finset.exists_subset_card_eq hsmall
  have hX' : NonTrilinear (X' : Set ℝ²) := Set.Triplewise.mono hSub hX
  obtain ⟨Y, hYn, hY, hconv⟩ := hf X' hCard hX'
  have hYS : Y ⊆ X := fun _ hy => hSub (hY hy)
  have hh := hXconv Y hYS hconv
  omega

end ErdosSzekeresLower

theorem OMA.solution : OMA.R_Erdos107_erdos_107_R1.H2 := by
  intro n hn
  exact ErdosSzekeresLower.lower hn ⟨_, ErdosSzekeresUpper.upper_mem n hn⟩
