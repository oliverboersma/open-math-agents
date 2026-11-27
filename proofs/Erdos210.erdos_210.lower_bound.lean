import FormalConjectures.ErdosProblems.«210»
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
Kelly and Moser, On the number of ordinary lines determined by n points (1958).
Credit: @LDJAI. The existing four-attachment and two-line bounds are credited in place.
-/
-- KellyMoserLocal

/-!
Local geometry in the affine dual of a projective point configuration.
Use an affine coordinate in which all the finitely many lines are graphs,
and the vertex being tested uniquely maximizes the horizontal coordinate.
Translating the vertex to the origin makes its incident lines precisely
the graphs with zero intercept.
-/
namespace KellyMoser
namespace Dual

/-- The graph of `y = slope * x + intercept`. -/
structure Line where
  slope : ℝ
  intercept : ℝ

theorem Line.ext {l k : Line} (ha : l.slope = k.slope) (hb : l.intercept = k.intercept) : l = k := by
  cases l
  cases k
  simp_all

def val (l : Line) (x : ℝ) := l.slope * x + l.intercept

/-- Every intersection of distinct-slope lines occurs at or left of the origin. -/
def Rightmost (S : Finset Line) : Prop :=
  ∀ l ∈ S, ∀ k ∈ S, l.slope ≠ k.slope → ∀ x, val l x = val k x → x ≤ 0

/-- A singleton slope class represents an ordinary intersection with the line at infinity. -/
def SingletonSlope (S : Finset Line) (l : Line) : Prop :=
  ∀ k ∈ S, k.slope = l.slope → k = l

theorem crossing_sign {S : Finset Line} (hr : Rightmost S)
    {l k : Line} (hl : l ∈ S) (hk : k ∈ S) (h0 : l.intercept = 0) :
    0 ≤ k.intercept * (k.slope - l.slope) := by
  by_cases he : l.slope = k.slope
  · simp [he]
  let x := k.intercept / (l.slope - k.slope)
  have hd : l.slope - k.slope ≠ 0 := sub_ne_zero.mpr he
  have hx : x * (l.slope - k.slope) = k.intercept := div_mul_cancel₀ _ hd
  have hv : val l x = val k x := by
    unfold val
    rw [h0]
    linarith only [hx]
  have hxr := hr l hl k hk he x hv
  have hs := mul_nonpos_of_nonpos_of_nonneg hxr (sq_nonneg (l.slope - k.slope))
  calc
    0 ≤ -(x * (l.slope - k.slope)^2) := neg_nonneg.mpr hs
    _ = k.intercept * (k.slope - l.slope) := by rw [← hx]; ring

/-- All lines strictly between two incident slopes are singletons, if they
pass through the exposed vertex. -/
theorem middle_singleton {S : Finset Line} (hr : Rightmost S)
    {l m u : Line} (hl : l ∈ S) (hu : u ∈ S)
    (hl0 : l.intercept = 0) (hm0 : m.intercept = 0) (hu0 : u.intercept = 0)
    (hlm : l.slope < m.slope) (hmu : m.slope < u.slope) :
    SingletonSlope S m := by
  intro k hk he
  have hlo := crossing_sign hr hl hk hl0
  have hhi := crossing_sign hr hu hk hu0
  rw [he] at hlo hhi
  have hi : k.intercept ≤ 0 := by
    by_contra! h
    exact (not_lt_of_ge hhi) (mul_neg_of_pos_of_neg h (sub_neg.mpr hmu))
  have lo : 0 ≤ k.intercept := by
    by_contra! h
    exact (not_lt_of_ge hlo) (mul_neg_of_neg_of_pos h (sub_pos.mpr hlm))
  exact Line.ext he ((le_antisymm hi lo).trans hm0.symm)

/-- Signs of the barycentric coordinates of an off-vertex line relative to
two incident lines. This is the affine content of triangular attachment. -/
theorem sector {S : Finset Line} (hr : Rightmost S) {l u k : Line}
    (hl : l ∈ S) (hu : u ∈ S) (hk : k ∈ S)
    (hl0 : l.intercept = 0) (hu0 : u.intercept = 0)
    (h : k.intercept ≠ 0) :
    (0 < k.intercept ∧ l.slope ≤ k.slope ∧ u.slope ≤ k.slope) ∨
    (k.intercept < 0 ∧ k.slope ≤ l.slope ∧ k.slope ≤ u.slope) := by
  have ha := crossing_sign hr hl hk hl0
  have hb := crossing_sign hr hu hk hu0
  rcases lt_or_gt_of_ne h with hn | hp
  · right
    exact ⟨hn, sub_nonpos.mp (nonpos_of_mul_nonneg_right ha hn),
      sub_nonpos.mp (nonpos_of_mul_nonneg_right hb hn)⟩
  · left
    exact ⟨hp, sub_nonneg.mp (nonneg_of_mul_nonneg_right ha hp),
      sub_nonneg.mp (nonneg_of_mul_nonneg_right hb hp)⟩

/-- With non-singleton slopes on either side of an interior incident slope,
finite arrangement vertices occur strictly on both sides of the middle line. -/
theorem straddling {S : Finset Line} (hr : Rightmost S)
    {l m u : Line} (hl : l ∈ S) (hu : u ∈ S)
    (hl0 : l.intercept = 0) (hm0 : m.intercept = 0) (hu0 : u.intercept = 0)
    (hlm : l.slope < m.slope) (hmu : m.slope < u.slope)
    (hls : ¬ SingletonSlope S l) (hus : ¬ SingletonSlope S u) :
    (∃ a ∈ S, ∃ b ∈ S, a.slope ≠ b.slope ∧
      ∃ x, val a x = val b x ∧ val m x < val a x) ∧
    (∃ a ∈ S, ∃ b ∈ S, a.slope ≠ b.slope ∧
      ∃ x, val a x = val b x ∧ val a x < val m x) := by
  classical
  unfold SingletonSlope at hls hus
  push Not at hls hus
  obtain ⟨l', hl', hel, hnl⟩ := hls
  obtain ⟨u', hu', heu, hnu⟩ := hus
  have crossAt {a b : Line} (ha : a ∈ S) (hb : b ∈ S)
      (hne : a.slope ≠ b.slope) (ha0 : a.intercept = 0) (hb0 : b.intercept ≠ 0) :
      ∃ x < 0, val a x = val b x := by
    let x := b.intercept / (a.slope - b.slope)
    have he : x * (a.slope - b.slope) = b.intercept := div_mul_cancel₀ _ (sub_ne_zero.mpr hne)
    have hv : val a x = val b x := by unfold val; rw [ha0]; linarith only [he]
    have hne0 : x ≠ 0 := by intro h; rw [h, zero_mul] at he; exact hb0 he.symm
    exact ⟨x, lt_of_le_of_ne (hr a ha b hb hne x hv) hne0, hv⟩
  have hn₁ : l.slope ≠ u'.slope := by rw [heu]; exact (hlm.trans hmu).ne
  have hn₂ : u.slope ≠ l'.slope := by rw [hel]; exact (hlm.trans hmu).ne'
  obtain ⟨x, hx, ex⟩ := crossAt hl hu' hn₁ hl0
    (fun h => hnu (Line.ext heu (h.trans hu0.symm)))
  obtain ⟨y, hy, ey⟩ := crossAt hu hl' hn₂ hu0
    (fun h => hnl (Line.ext hel (h.trans hl0.symm)))
  have high : val m x < val l x := by
    simpa [val, hm0, hl0] using (mul_lt_mul_of_neg_right hlm hx)
  have low : val u y < val m y := by
    simpa [val, hm0, hu0] using (mul_lt_mul_of_neg_right hmu hy)
  exact ⟨⟨l, hl, u', hu', hn₁, x, ex, high⟩, ⟨u, hu, l', hl', hn₂, y, ey, low⟩⟩

end Dual
end KellyMoser
-- KellyMoserVertex
namespace KellyMoser.Dual
open scoped Classical

def OrdinaryAt (S : Finset Line) (x y : ℝ) : Prop :=
  (S.filter (fun l => val l x = y)).card = 2

/-- Choose the outermost two slopes and a strictly interior slope
at a vertex incident with at least three distinct lines. -/
theorem incident_three {S : Finset Line}
    (h : 3 ≤ (S.filter (fun l => l.intercept = 0)).card) :
    ∃ l ∈ S, ∃ m ∈ S, ∃ u ∈ S, l.intercept = 0 ∧ m.intercept = 0 ∧ u.intercept = 0 ∧
      l.slope < m.slope ∧ m.slope < u.slope := by
  classical
  let I := S.filter (fun l => l.intercept = 0)
  have hn : I.Nonempty := Finset.card_pos.mp (by change 0 < (S.filter _).card; omega)
  obtain ⟨l, hl, hmin⟩ := I.exists_min_image Line.slope hn
  obtain ⟨u, hu, hmax⟩ := I.exists_max_image Line.slope hn
  have hnot : ¬ I ⊆ ({l,u} : Finset Line) := by
    intro hi
    have := Finset.card_le_card hi
    have htwo : ({l,u} : Finset Line).card ≤ 2 := Finset.card_le_two
    change 3 ≤ I.card at h
    omega
  obtain ⟨m, hm, hmu⟩ := Finset.not_subset.mp hnot
  have hmne : m ≠ l ∧ m ≠ u := by simpa using hmu
  have member (z : Line) (hz : z ∈ I) : z ∈ S ∧ z.intercept = 0 := Finset.mem_filter.mp hz
  have ne_slope (z : Line) (hz : z ∈ I) (hne : m ≠ z) : m.slope ≠ z.slope :=
    fun e => hne (Line.ext e ((member _ hm).2.trans (member _ hz).2.symm))
  exact ⟨l,(member _ hl).1,m,(member _ hm).1,u,(member _ hu).1,(member _ hl).2,
    (member _ hm).2,(member _ hu).2,lt_of_le_of_ne (hmin m hm) (ne_slope l hl hmne.1).symm,
    lt_of_le_of_ne (hmax m hm) (ne_slope u hu hmne.2)⟩

theorem ordinary_of_no_singleton {S : Finset Line} (hr : Rightmost S)
    (atLeastTwo : 2 ≤ (S.filter (fun l => l.intercept = 0)).card)
    (hno : ∀ m ∈ S, ¬ SingletonSlope S m) : OrdinaryAt S 0 0 := by
  classical
  have hle : (S.filter (fun l => l.intercept = 0)).card ≤ 2 := by
    by_contra! hgt
    obtain ⟨l,hl,m,hm,u,hu,hl0,hm0,hu0,hlm,hmu⟩ := incident_three hgt
    exact hno m hm (middle_singleton hr hl hu hl0 hm0 hu0 hlm hmu)
  simpa [OrdinaryAt, val] using le_antisymm hle atLeastTwo

/-- A nonordinary extreme vertex when there is only one singleton direction
lies on its line, and actual vertices of the arrangement lie on both sides. -/
theorem one_singleton_bad_vertex {S : Finset Line} (hr : Rightmost S)
    (atLeastTwo : 2 ≤ (S.filter (fun l => l.intercept = 0)).card)
    (bad : ¬ OrdinaryAt S 0 0) {s : Line}
    (unique : ∀ m ∈ S, SingletonSlope S m → m = s) :
    s.intercept = 0 ∧
    (∃ a ∈ S, ∃ b ∈ S, a.slope ≠ b.slope ∧
      ∃ x, val a x = val b x ∧ val s x < val a x) ∧
    (∃ a ∈ S, ∃ b ∈ S, a.slope ≠ b.slope ∧
      ∃ x, val a x = val b x ∧ val a x < val s x) := by
  classical
  have hne : (S.filter (fun l => l.intercept = 0)).card ≠ 2 := by
    simpa [OrdinaryAt, val] using bad
  have hgt : 3 ≤ (S.filter (fun l => l.intercept = 0)).card := by omega
  obtain ⟨l,hl,m,hm,u,hu,hl0,hm0,hu0,hlm,hmu⟩ := incident_three hgt
  obtain rfl := unique m hm (middle_singleton hr hl hu hl0 hm0 hu0 hlm hmu)
  have hls : ¬ SingletonSlope S l := fun H => hlm.ne (congrArg Line.slope (unique l hl H))
  have hus : ¬ SingletonSlope S u := fun H => hmu.ne' (congrArg Line.slope (unique u hu H))
  exact ⟨hm0,straddling hr hl hu hl0 hm0 hu0 hlm hmu hls hus⟩

end KellyMoser.Dual
-- KellyMoserSector
namespace KellyMoser.Dual

def SameSign (a b c : ℝ) := (0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)

/-- Homogeneous-coordinate certificate for the triangular face incident
to an ordinary rightmost vertex and the line at infinity. The signed
boundary vectors are −(l.slope,1,0), (u.slope,1,0), and (0,0,1). -/
theorem signed_coordinates {S : Finset Line} {l u : Line} (hr : Rightmost S)
    (hl : l ∈ S) (hu : u ∈ S) (hlu : l.slope < u.slope)
    (hl0 : l.intercept = 0) (hu0 : u.intercept = 0)
    (two : ∀ k ∈ S, k.intercept = 0 → k = l ∨ k = u) :
    ∀ k ∈ S, ∃ a b c : ℝ, k.slope = -a*l.slope+b*u.slope ∧
      1 = -a+b ∧ k.intercept = c ∧ SameSign a b c := by
  intro k hk
  by_cases hz : k.intercept = 0
  · rcases two k hk hz with rfl | rfl
    · exact ⟨-1, 0, 0, by ring, by ring, hz, Or.inr ⟨by norm_num, le_rfl, le_rfl⟩⟩
    · exact ⟨0, 1, 0, by ring, by ring, hz, Or.inl ⟨le_rfl, zero_le_one, le_rfl⟩⟩
  let a := (k.slope-u.slope)/(u.slope-l.slope)
  let b := (k.slope-l.slope)/(u.slope-l.slope)
  have hd := sub_pos.mpr hlu
  refine ⟨a,b,k.intercept,?_,?_,rfl,?_⟩
  · dsimp [a,b]
    field_simp [hd.ne']
    ring
  · dsimp [a,b]
    field_simp [hd.ne']
    ring
  · rcases sector hr hl hu hk hl0 hu0 hz with h | h
    · exact Or.inl ⟨div_nonneg (sub_nonneg.mpr h.2.2) hd.le,
        div_nonneg (sub_nonneg.mpr h.2.1) hd.le, h.1.le⟩
    · exact Or.inr ⟨div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h.2.2) hd.le,
        div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h.2.1) hd.le, h.1.le⟩

end KellyMoser.Dual
-- KellyMoserChart
namespace KellyMoser.Dual
open scoped Classical

/-- Affine coordinates at (x₀,y₀) with new horizontal coordinate
A(x−x₀)+B(y−y₀) and new vertical coordinate y−y₀. -/
noncomputable def change (A B x₀ y₀ : ℝ) (l : Line) : Line :=
  ⟨l.slope / (A + B*l.slope), A * (val l x₀ - y₀) / (A + B*l.slope)⟩

theorem change_val {A B x₀ y₀ : ℝ} (l : Line) (hd : A + B*l.slope ≠ 0) (x : ℝ) :
    val (change A B x₀ y₀ l) (A*(x-x₀) + B*(val l x-y₀)) = val l x-y₀ := by
  dsimp [change, val]
  apply (mul_left_cancel₀ hd)
  have h₁ := div_mul_cancel₀ l.slope hd
  have h₂ := div_mul_cancel₀ (A * (l.slope*x₀+l.intercept-y₀)) hd
  linear_combination (A*(x-x₀)+B*(l.slope*x+l.intercept-y₀))*h₁ + h₂

theorem change_slope_eq {A B x₀ y₀ : ℝ} {l k : Line} (ha : A ≠ 0)
    (hl : A+B*l.slope ≠ 0) (hk : A+B*k.slope ≠ 0) :
    (change A B x₀ y₀ l).slope = (change A B x₀ y₀ k).slope ↔ l.slope = k.slope := by
  change l.slope / _ = k.slope / _ ↔ _
  rw [div_eq_div_iff hl hk]
  constructor
  · intro he
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show A * (l.slope - k.slope) = 0 by
      linear_combination he)).resolve_left ha
  · intro h
    rw [h]

theorem change_intercept_zero {A B x₀ y₀ : ℝ} (l : Line) (ha : A ≠ 0)
    (hl : A+B*l.slope ≠ 0) :
    (change A B x₀ y₀ l).intercept = 0 ↔ val l x₀ = y₀ := by
  simp [change, div_eq_zero_iff, hl, ha, sub_eq_zero]

theorem change_injective_on {S : Finset Line} {A B x₀ y₀ : ℝ} (ha : A ≠ 0)
    (hden : ∀ l ∈ S, A+B*l.slope ≠ 0) :
    (S : Set Line).InjOn (change A B x₀ y₀) := by
  intro l hl k hk e
  have hs := (change_slope_eq ha (hden l hl) (hden k hk)).mp (congrArg Line.slope e)
  apply Line.ext hs
  have hb := congrArg Line.intercept e
  change A * (val l x₀ - y₀) / _ = A * (val k x₀ - y₀) / _ at hb
  rw [hs] at hb
  have hz := (div_left_inj' (hden k hk)).mp hb
  have hv := mul_left_cancel₀ ha hz
  unfold val at hv
  rw [hs] at hv
  linarith only [hv]

/-- A maximizing vertex becomes a rightmost vertex in its supporting chart. -/
theorem supporting_chart {S : Finset Line} {A B x₀ y₀ : ℝ} (ha : A ≠ 0)
    (hden : ∀ l ∈ S, A+B*l.slope ≠ 0)
    (hsupport : ∀ l ∈ S, ∀ k ∈ S, l.slope ≠ k.slope → ∀ x,
      val l x = val k x → A*x+B*val l x ≤ A*x₀+B*y₀) :
    Rightmost (S.image (change A B x₀ y₀)) := by
  classical
  rintro _ hm₁ _ hm₂ hn X he
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hm₁
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm₂
  have hne : l.slope ≠ k.slope := fun e =>
    hn ((change_slope_eq ha (hden l hl) (hden k hk)).mpr e)
  let x := (k.intercept-l.intercept)/(l.slope-k.slope)
  have hmul : x*(l.slope-k.slope) = k.intercept-l.intercept :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr hne)
  have hx : val l x = val k x := by unfold val; linarith only [hmul]
  let X' := A*(x-x₀) + B*(val l x-y₀)
  have he' : val (change A B x₀ y₀ l) X' = val (change A B x₀ y₀ k) X' := by
    calc
      _ = val l x - y₀ := change_val l (hden l hl) x
      _ = val k x - y₀ := by rw [hx]
      _ = _ := by simpa [X', hx] using (change_val (x₀ := x₀) (y₀ := y₀) k (hden k hk) x).symm
  have hXX : X = X' := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show ((change A B x₀ y₀ l).slope -
      (change A B x₀ y₀ k).slope) * (X-X') = 0 by
      unfold val at he he'
      linear_combination he - he')).resolve_left (sub_ne_zero.mpr hn)
  rw [hXX]
  have hs := hsupport l hl k hk hne x hx
  dsimp [X']
  linarith only [hs]

end KellyMoser.Dual
-- KellyMoserExposure
namespace KellyMoser
abbrev XY := ℝ × ℝ
def score (A B : ℝ) (z : XY) := A*z.1+B*z.2

/-- The first coefficient and the directional derivative along each of the
input graph lines are nonzero. These conditions make the supporting chart invertible. -/
def admissible (slopes : Finset ℝ) (A B : ℝ) : Prop :=
  A ≠ 0 ∧ ∀ a ∈ slopes, A+B*a ≠ 0

open scoped Classical in
noncomputable def exposed (V : Finset XY) (slopes : Finset ℝ) : Finset XY :=
  V.filter (fun v => ∃ A B, admissible slopes A B ∧ ∀ u ∈ V, score A B u ≤ score A B v)

/-- Every open half-plane that contains a member of a finite vertex set
also contains a maximizer with a permissible supporting direction. -/
theorem exposed_half_plane {V : Finset XY} (slopes : Finset ℝ) {v : XY} (hv : v ∈ V)
    (A B c : ℝ) (hgood : c < score A B v) :
    ∃ w ∈ exposed V slopes, c < score A B w := by
  classical
  obtain ⟨u, _, hu⟩ := V.exists_max_image (fun u => |u.1-v.1|) ⟨v,hv⟩
  let K := |u.1-v.1|+1
  have hK : 0 < K := by dsimp [K]; positivity
  let forbidden := insert (-A) (slopes.image fun a => -(A+B*a))
  obtain ⟨t, ⟨ht, ht'⟩, hout⟩ :=
    (Set.Ioo_infinite (div_pos (sub_pos.mpr hgood) hK)).exists_notMem_finset forbidden
  have hA : admissible slopes (A+t) B := by
    constructor
    · intro h
      exact hout (Finset.mem_insert.mpr (Or.inl (by linarith only [h])))
    · intro a ha h
      exact hout (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, ha, by linarith only [h]⟩))
  obtain ⟨w, hw, hmax⟩ := V.exists_max_image (score (A+t) B) ⟨v,hv⟩
  refine ⟨w, Finset.mem_filter.mpr ⟨hw, A+t, B, hA, hmax⟩, ?_⟩
  have hdist : w.1-v.1 ≤ K := (le_abs_self _).trans ((hu w hw).trans (by dsimp [K]; linarith))
  have htw := mul_le_mul_of_nonneg_left hdist ht.le
  have hlim := (lt_div_iff₀ hK).mp ht'
  have hvw := hmax v hv
  unfold score at hvw hlim ⊢
  linarith only [hvw, htw, hlim]

theorem exposed_both_sides {V : Finset XY} (slopes : Finset ℝ) (A B c : ℝ)
    {u v : XY} (hu : u ∈ V) (hv : v ∈ V) (hu' : score A B u < c) (hv' : c < score A B v) :
    (∃ p ∈ exposed V slopes, score A B p < c) ∧ (∃ q ∈ exposed V slopes, c < score A B q) := by
  have hneg (z : XY) : score (-A) (-B) z = - score A B z := by unfold score; ring
  obtain ⟨p, hp, h⟩ := exposed_half_plane slopes hu (-A) (-B) (-c) (by rw [hneg]; linarith)
  exact ⟨⟨p, hp, by rw [hneg] at h; linarith⟩, exposed_half_plane slopes hv A B c hv'⟩

/-- Three noncollinear vertices force three distinct exposed vertices.
Here noncollinearity means that no affine line contains the entire set. -/
theorem three_exposed {V : Finset XY} (slopes : Finset ℝ)
    (nc : ∀ A B c : ℝ, A ≠ 0 ∨ B ≠ 0 → ∃ v ∈ V, score A B v ≠ c) :
    3 ≤ (exposed V slopes).card := by
  classical
  let E := exposed V slopes
  have E_nc (A B c : ℝ) (hAB : A ≠ 0 ∨ B ≠ 0) : ∃ v ∈ E, score A B v ≠ c := by
    obtain ⟨v, hv, hne⟩ := nc A B c hAB
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hneg (z : XY) : score (-A) (-B) z = -score A B z := by unfold score; ring
      obtain ⟨p, hp, h⟩ := exposed_half_plane slopes hv (-A) (-B) (-c)
        (by rw [hneg]; linarith)
      exact ⟨p, hp, by rw [hneg] at h; linarith⟩
    · obtain ⟨p, hp, h⟩ := exposed_half_plane slopes hv A B c hgt
      exact ⟨p, hp, h.ne'⟩
  obtain ⟨p, hp, _⟩ := E_nc 1 0 0 (Or.inl one_ne_zero)
  obtain ⟨q, hq, hqp⟩ := E_nc 1 0 (score 1 0 p) (Or.inl one_ne_zero)
  have hdiff : q.1 ≠ p.1 := by simpa [score] using hqp
  let A := q.2-p.2
  let B := p.1-q.1
  obtain ⟨r, hr, hrne⟩ := E_nc A B (score A B p) (Or.inr (sub_ne_zero.mpr hdiff.symm))
  have hpq : p ≠ q := fun h => hqp (congrArg (score 1 0) h.symm)
  have he : score A B q = score A B p := by dsimp [score, A, B]; ring
  have hrp : r ≠ p := fun h => hrne (congrArg _ h)
  have hrq : r ≠ q := fun h => hrne ((congrArg _ h).trans he)
  have hsub : ({p,q,r} : Finset XY) ⊆ E := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have hcard := Finset.card_le_card hsub
  simpa [hpq, hrp.symm, hrq.symm, E] using hcard
end KellyMoser
-- KellyMoserDual
namespace KellyMoser.Dual
open scoped Classical

noncomputable def crossX (l k : Line) := (k.intercept-l.intercept)/(l.slope-k.slope)
noncomputable def crossPt (p : Line × Line) : XY :=
  (crossX p.1 p.2, val p.1 (crossX p.1 p.2))

noncomputable def vertices (S : Finset Line) : Finset XY :=
  ((S ×ˢ S).filter (fun p => p.1.slope ≠ p.2.slope)).image crossPt

theorem cross_iff {l k : Line} (h : l.slope ≠ k.slope) (x : ℝ) :
    val l x = val k x ↔ x = crossX l k := by
  unfold val crossX
  rw [eq_div_iff (sub_ne_zero.mpr h)]
  constructor <;> intro e <;> linarith only [e]

theorem mem_vertices {S : Finset Line} {v : XY} :
    v ∈ vertices S ↔ ∃ l ∈ S, ∃ k ∈ S, l.slope ≠ k.slope ∧ val l v.1 = v.2 ∧ val k v.1 = v.2 := by
  constructor
  · rintro hv
    obtain ⟨⟨l,k⟩, h, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hmem,hne⟩ := Finset.mem_filter.mp h
    have hpair := Finset.mem_product.mp hmem
    exact ⟨l,hpair.1,k,hpair.2,hne,rfl,((cross_iff hne _).mpr rfl).symm⟩
  · rintro ⟨l,hl,k,hk,hne,hlv,hkv⟩
    have hx := (cross_iff hne _).mp (hlv.trans hkv.symm)
    exact Finset.mem_image.mpr ⟨(l,k),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hl,hk⟩,hne⟩,
      Prod.ext hx.symm (by simpa [crossPt, ← hx] using hlv)⟩

theorem changed_singleton {S : Finset Line} {A B x₀ y₀ : ℝ} (ha : A ≠ 0)
    (hden : ∀ l ∈ S, A+B*l.slope ≠ 0) {l : Line} (hl : l ∈ S) :
    SingletonSlope (S.image (change A B x₀ y₀)) (change A B x₀ y₀ l) ↔ SingletonSlope S l := by
  constructor
  · intro h k hk hslope
    exact change_injective_on ha hden hk hl
      (h _ (Finset.mem_image_of_mem _ hk) ((change_slope_eq ha (hden _ hk) (hden _ hl)).mpr hslope))
  · rintro h _ hmem hslope
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hmem
    exact congrArg _ (h _ hk ((change_slope_eq ha (hden _ hk) (hden _ hl)).mp hslope))

theorem change_inc_card {S : Finset Line} {A B x₀ y₀ : ℝ} (ha : A ≠ 0)
    (hden : ∀ l ∈ S, A+B*l.slope ≠ 0) :
    ((S.image (change A B x₀ y₀)).filter (fun l => l.intercept = 0)).card =
      (S.filter (fun l => val l x₀ = y₀)).card := by
  classical
  rw [Finset.filter_image]
  have eq : S.filter (fun a => (change A B x₀ y₀ a).intercept = 0) =
      S.filter (fun a => val a x₀ = y₀) := by
    apply Finset.filter_congr
    intro l hl
    exact change_intercept_zero l ha (hden _ hl)
  rw [eq]
  exact Finset.card_image_of_injOn (fun _ hl _ hk =>
    change_injective_on ha hden (Finset.mem_filter.mp hl).1 (Finset.mem_filter.mp hk).1)

theorem two_at_vertex {S : Finset Line} {v : XY} (hv : v ∈ vertices S) :
    2 ≤ (S.filter (fun l => val l v.1 = v.2)).card := by
  obtain ⟨l,hl,k,hk,hn,hlv,hkv⟩ := mem_vertices.mp hv
  have hne : l ≠ k := fun e => hn (congrArg Line.slope e)
  have hsub : ({l,k} : Finset Line) ⊆ S.filter (fun l => val l v.1 = v.2) := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | he
    · exact Finset.mem_filter.mpr ⟨hl,hlv⟩
    · rw [Finset.mem_singleton.mp he]
      exact Finset.mem_filter.mpr ⟨hk,hkv⟩
  simpa [hne] using Finset.card_le_card hsub

noncomputable def slopes (S : Finset Line) := S.image Line.slope

/-- Every admissibly exposed vertex is rightmost in its supporting chart. -/
theorem exists_chart {S : Finset Line} {v : XY} (hv : v ∈ exposed (vertices S) (slopes S)) :
    ∃ A B : ℝ, A ≠ 0 ∧ (∀ l ∈ S, A+B*l.slope ≠ 0) ∧
      Rightmost (S.image (change A B v.1 v.2)) := by
  obtain ⟨_,A,B,⟨ha,hd⟩,hmax⟩ := Finset.mem_filter.mp hv
  have hden (l : Line) (hl : l ∈ S) := hd l.slope (Finset.mem_image_of_mem _ hl)
  refine ⟨A,B,ha,hden,supporting_chart ha hden ?_⟩
  intro l hl k hk hne x e
  have hV : (x,val l x) ∈ vertices S := mem_vertices.mpr ⟨l,hl,k,hk,hne,rfl,e.symm⟩
  exact hmax _ hV

theorem ordinary_of_exposed_no_singleton {S : Finset Line} {v : XY}
    (hv : v ∈ exposed (vertices S) (slopes S))
    (hno : ∀ l ∈ S, ¬ SingletonSlope S l) : OrdinaryAt S v.1 v.2 := by
  obtain ⟨A,B,ha,hd,hr⟩ := exists_chart hv
  have eq := change_inc_card (x₀ := v.1) (y₀ := v.2) ha hd
  have hh := two_at_vertex (Finset.mem_filter.mp hv).1
  have no' : ∀ m ∈ S.image (change A B v.1 v.2), ¬ SingletonSlope (S.image (change A B v.1 v.2)) m := by
    rintro _ hm' H
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hm'
    exact hno _ hm ((changed_singleton ha hd hm).mp H)
  have h := ordinary_of_no_singleton hr (by omega) no'
  unfold OrdinaryAt at *
  simp only [val, mul_zero, zero_add] at h
  exact eq.symm.trans h

/-- The inverse chart sends actual intersections back to actual intersections,
and rescales signed vertical distance to a line by a nonzero constant. -/
theorem unchange_side {S : Finset Line} {A B x₀ y₀ : ℝ} (ha : A ≠ 0)
    (hd : ∀ l ∈ S, A+B*l.slope ≠ 0) {m : Line} (hm : m ∈ S) {X Y : ℝ}
    (hv : (X,Y) ∈ vertices (S.image (change A B x₀ y₀))) :
    ∃ v ∈ vertices S, (Y-val (change A B x₀ y₀ m) X)*(A+B*m.slope) =
      A*(v.2-val m v.1) := by
  obtain ⟨_,hl',_,hk',hne,h₁,h₂⟩ := mem_vertices.mp hv
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hl'
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hk'
  let x := x₀ + (X-B*Y)/A
  let y := y₀ + Y
  have hX : A*(x-x₀)+B*(y-y₀) = X := by
    dsimp [x,y]
    field_simp [ha]
    ring
  have ident (j : Line) (hj : j ∈ S) :
      (Y-val (change A B x₀ y₀ j) X)*(A+B*j.slope) = A*(y-val j x) := by
    have e := change_val (x₀ := x₀) (y₀ := y₀) j (hd _ hj) x
    have hs := div_mul_cancel₀ j.slope (hd j hj)
    have hh := div_mul_cancel₀ (A * (val j x₀-y₀)) (hd j hj)
    have he : A*(x-x₀)+B*Y = X := by simpa [y] using hX
    dsimp [change, val, y] at hs hh ⊢
    linear_combination -X*hs - hh + j.slope * he
  refine ⟨(x,y),mem_vertices.mpr ⟨l,hl,k,hk,?_,?_,?_⟩,ident m hm⟩
  · exact fun e => hne ((change_slope_eq ha (hd l hl) (hd k hk)).mpr e)
  · have he := ident l hl
    change val (change A B x₀ y₀ l) X = Y at h₁
    rw [h₁,sub_self,zero_mul] at he
    exact (sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_left ha)).symm
  · have he := ident k hk
    change val (change A B x₀ y₀ k) X = Y at h₂
    rw [h₂,sub_self,zero_mul] at he
    exact (sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_left ha)).symm

theorem one_singleton_exposed {S : Finset Line} {s : Line} (hs : s ∈ S)
    (unique : ∀ m ∈ S, SingletonSlope S m → m = s) {v : XY}
    (hv : v ∈ exposed (vertices S) (slopes S)) (hbad : ¬ OrdinaryAt S v.1 v.2) :
    val s v.1 = v.2 ∧ ∃ u ∈ vertices S, ∃ w ∈ vertices S,
      (u.2-val s u.1)*(w.2-val s w.1) < 0 := by
  classical
  obtain ⟨A,B,ha,hd,hr⟩ := exists_chart hv
  let f := change A B v.1 v.2
  have eq := change_inc_card (x₀ := v.1) (y₀ := v.2) ha hd
  have hh := two_at_vertex (Finset.mem_filter.mp hv).1
  have bad : ¬ OrdinaryAt (S.image f) 0 0 := by
    unfold OrdinaryAt at *
    simpa [val, f, eq] using hbad
  have unique' : ∀ m ∈ S.image f, SingletonSlope (S.image f) m → m = f s := by
    rintro _ hm' H
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hm'
    exact congrArg f (unique m hm ((changed_singleton ha hd hm).mp H))
  obtain ⟨hzero,⟨a,ha',b,hb',hab,x,hex,hx⟩,⟨c,hc,d,hd',hcd,y,hey,hy⟩⟩ :=
    one_singleton_bad_vertex hr (by omega) bad unique'
  refine ⟨(change_intercept_zero s ha (hd s hs)).mp hzero, ?_⟩
  have vert (l k : Line) (hl : l ∈ S.image f) (hk : k ∈ S.image f)
      (hne : l.slope ≠ k.slope) (z : ℝ) (he : val l z = val k z) :
      (z,val l z) ∈ vertices (S.image f) := mem_vertices.mpr ⟨l,hl,k,hk,hne,rfl,he.symm⟩
  obtain ⟨u,hu,eu⟩ := unchange_side ha hd hs (vert a b ha' hb' hab x hex)
  obtain ⟨w,hw,ew⟩ := unchange_side ha hd hs (vert c d hc hd' hcd y hey)
  refine ⟨u,hu,w,hw,?_⟩
  have hn := mul_neg_of_pos_of_neg (sub_pos.mpr hx) (sub_neg.mpr hy)
  have hm := mul_neg_of_neg_of_pos hn (sq_pos_of_ne_zero (hd s hs))
  have hp : ((val a x - val (f s) x)*(val c y-val (f s) y)) * (A+B*s.slope)^2 =
      ((u.2-val s u.1)*(w.2-val s w.1))*A^2 := by
    calc
      _ = ((val a x-val (f s) x)*(A+B*s.slope))*((val c y-val (f s) y)*(A+B*s.slope)) := by ring
      _ = _ := by rw [eu,ew]; ring
  rw [hp] at hm
  exact neg_of_mul_neg_left hm (sq_nonneg A)

/-- Among the exposed vertices, three are ordinary with no singleton slopes,
and at least two are ordinary with a single singleton slope. -/
theorem local_counts (S : Finset Line)
    (nc : ∀ A B c : ℝ, A ≠ 0 ∨ B ≠ 0 → ∃ v ∈ vertices S, score A B v ≠ c) :
    let O := (exposed (vertices S) (slopes S)).filter (fun v => OrdinaryAt S v.1 v.2)
    ((∀ m ∈ S, ¬ SingletonSlope S m) → 3 ≤ O.card) ∧
    (∀ s ∈ S, (∀ m ∈ S, SingletonSlope S m → m = s) → 2 ≤ O.card) := by
  classical
  let E := exposed (vertices S) (slopes S)
  have large : 3 ≤ E.card := three_exposed _ nc
  have all (ho : ∀ v ∈ E, OrdinaryAt S v.1 v.2) :
      E.filter (fun v => OrdinaryAt S v.1 v.2) = E := Finset.filter_true_of_mem ho
  constructor
  · intro h
    exact (all (fun _ hv => ordinary_of_exposed_no_singleton hv h)).symm ▸ large
  · intro s hs hu
    by_cases good : ∀ v ∈ E, OrdinaryAt S v.1 v.2
    · change 2 ≤ (E.filter _).card
      rw [all good]
      omega
    push Not at good
    obtain ⟨v,hv,hb⟩ := good
    obtain ⟨_,u,hu',w,hw',hop⟩ := one_singleton_exposed hs hu hv hb
    have hsides (z : XY) : score (-s.slope) 1 z - s.intercept = z.2-val s z.1 := by
      dsimp [score,val]; ring
    rw [← hsides, ← hsides] at hop
    have sides : (∃ p ∈ E, score (-s.slope) 1 p < s.intercept) ∧
        (∃ q ∈ E, s.intercept < score (-s.slope) 1 q) := by
      rcases mul_neg_iff.mp hop with h | h
      · exact exposed_both_sides _ _ _ _ hw' hu' (sub_neg.mp h.2) (sub_pos.mp h.1)
      · exact exposed_both_sides _ _ _ _ hu' hw' (sub_neg.mp h.1) (sub_pos.mp h.2)
    obtain ⟨⟨p,hp,hn⟩,⟨q,hq,hpos⟩⟩ := sides
    have off (z : XY) (hz : z ∈ E) (hne : score (-s.slope) 1 z ≠ s.intercept) :
        z ∈ E.filter (fun z => OrdinaryAt S z.1 z.2) := by
      apply Finset.mem_filter.mpr
      refine ⟨hz,?_⟩
      by_contra bad
      have he := (one_singleton_exposed hs hu hz bad).1
      exact hne (sub_eq_zero.mp ((hsides z).trans (sub_eq_zero.mpr he.symm)))
    exact Finset.one_lt_card.mpr ⟨p, off p hp hn.ne, q, off q hq hpos.ne',
      fun e => (hn.trans hpos).ne (congrArg (score (-s.slope) 1) e)⟩

end KellyMoser.Dual
-- KellyMoserGrid
namespace KellyMoser.Dual
open scoped Classical

theorem grid_noncollinear {S : Finset Line} {l l' k k' : Line}
    (hl : l ∈ S) (hl' : l' ∈ S) (hk : k ∈ S) (hk' : k' ∈ S)
    (hll : l.slope = l'.slope) (hkk : k.slope = k'.slope)
    (hnl : l ≠ l') (hnk : k ≠ k') (hsep : l.slope ≠ k.slope) :
    ∀ A B c : ℝ, A ≠ 0 ∨ B ≠ 0 → ∃ v ∈ vertices S, score A B v ≠ c := by
  intro A B c nonzero
  by_contra! h
  have onCross (a b : Line) (ha : a ∈ S) (hb : b ∈ S) (hne : a.slope ≠ b.slope) :
      score A B (crossPt (a,b)) = c :=
    h _ (Finset.mem_image.mpr ⟨(a,b),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hne⟩,rfl⟩)
  have constrain (a b d : Line) (ha : a ∈ S) (hb : b ∈ S) (hd : d ∈ S)
      (hab : a.slope ≠ b.slope) (hbd : b.slope = d.slope) (hnd : b ≠ d) :
      A+B*a.slope = 0 := by
    have had : a.slope ≠ d.slope := hbd ▸ hab
    have xne : crossX a b ≠ crossX a d := by
      intro he
      have e₁ := (cross_iff hab _).mpr rfl
      have e₂ := (cross_iff had _).mpr rfl
      rw [← he] at e₂
      apply hnd (Line.ext hbd ?_)
      have hx := e₁.symm.trans e₂
      dsimp [val] at hx
      rw [hbd] at hx
      linarith
    have h₁ := onCross a b ha hb hab
    have h₂ := onCross a d ha hd had
    dsimp only [crossPt,score,val] at h₁ h₂
    apply (mul_eq_zero.mp (show (A+B*a.slope)*(crossX a b-crossX a d) = 0 by
      linear_combination h₁-h₂)).resolve_right (sub_ne_zero.mpr xne)
  have ha := constrain l k k' hl hk hk' hsep hkk hnk
  have hb := constrain k l l' hk hl hl' hsep.symm hll hnl
  have hz : B = 0 := (mul_eq_zero.mp (show B*(l.slope-k.slope) = 0 by
    linear_combination ha-hb)).resolve_right (sub_ne_zero.mpr hsep)
  rw [hz,zero_mul,add_zero] at ha
  exact nonzero.elim (fun H => H ha) (fun H => H hz)

/-- If three distinct slopes occur and at most one line is the sole line
of its slope, there are two nonsingleton slope classes. -/
theorem grid_of_three {S : Finset Line} (three : 3 ≤ (slopes S).card)
    (one : ∀ l ∈ S, ∀ k ∈ S, SingletonSlope S l → SingletonSlope S k → l = k) :
    ∀ A B c : ℝ, A ≠ 0 ∨ B ≠ 0 → ∃ v ∈ vertices S, score A B v ≠ c := by
  classical
  let N := S.filter (fun l => ¬ SingletonSlope S l)
  let U := S.filter (SingletonSlope S)
  have hU : U.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro l hl k hk
    exact one _ (Finset.mem_filter.mp hl).1 _ (Finset.mem_filter.mp hk).1
      (Finset.mem_filter.mp hl).2 (Finset.mem_filter.mp hk).2
  have sub : slopes S ⊆ slopes N ∪ slopes U := by
    rintro a ha
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ha
    by_cases h : SingletonSlope S l
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hl,h⟩))
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hl,h⟩))
  have two : 1 < (slopes N).card := by
    have hu' : (slopes U).card ≤ U.card := Finset.card_image_le
    have hsub := Finset.card_le_card sub
    have hun := Finset.card_union_le (slopes N) (slopes U)
    omega
  obtain ⟨a,ha,b,hb,hn⟩ := Finset.one_lt_card.mp two
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hls,hl'⟩ := Finset.mem_filter.mp hl
  obtain ⟨hks,hk'⟩ := Finset.mem_filter.mp hk
  unfold SingletonSlope at hl' hk'
  push Not at hl' hk'
  obtain ⟨l',hl',hs₁,hn₁⟩ := hl'
  obtain ⟨k',hk',hs₂,hn₂⟩ := hk'
  exact grid_noncollinear hls hl' hks hk' hs₁.symm hs₂.symm hn₁.symm hn₂.symm hn

end KellyMoser.Dual
-- KellyMoserCounting
namespace KellyMoser

open Finset
open scoped BigOperators Classical

/-- The sum of the row counts and the sum of the column counts count the same flags. -/
theorem countFlags {P L : Type*} (s : Finset P) (t : Finset L) (I : P → L → Prop) :
    ∑ p ∈ s, (t.filter (I p)).card = ∑ l ∈ t, (s.filter (fun p => I p l)).card := by
  classical
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- The counting argument for Kelly–Moser. The two relations are ordinary
incidences and attachments. Exactly two points are incident with each
ordinary line. Each line can be attached to at most four points. -/
theorem countOrdinary {P L : Type*} (s : Finset P) (t : Finset L)
    (inc att : P → L → Prop)
    (incTwo : ∀ l ∈ t, (s.filter (fun p => inc p l)).card = 2)
    (attFour : ∀ l ∈ t, (s.filter (fun p => att p l)).card ≤ 4)
    (zero : ∀ p ∈ s, (t.filter (inc p)).card = 0 → 3 ≤ (t.filter (att p)).card)
    (one : ∀ p ∈ s, (t.filter (inc p)).card = 1 → 2 ≤ (t.filter (att p)).card) :
    3 * s.card ≤ 7 * t.card := by
  classical
  let d (p : P) := (t.filter (inc p)).card
  let a (p : P) := (t.filter (att p)).card
  have hd : ∑ p ∈ s, d p = 2 * t.card := by
    rw [show (∑ p ∈ s, d p) = _ from countFlags s t inc]
    simpa [Nat.mul_comm] using Finset.sum_congr (s₁ := t) (s₂ := t) rfl incTwo
  have ha : ∑ p ∈ s, a p ≤ 4 * t.card := by
    rw [show (∑ p ∈ s, a p) = _ from countFlags s t att]
    simpa [Nat.mul_comm] using Finset.sum_le_sum attFour
  -- Pointwise weighting absorbs the order-two exception without a separate count.
  have point (p : P) (hp : p ∈ s) : 6 ≤ 3 * d p + 2 * a p := by
    by_cases h0 : d p = 0
    · have h : 3 ≤ a p := zero p hp h0
      omega
    by_cases h1 : d p = 1
    · have h : 2 ≤ a p := one p hp h1
      omega
    omega
  have h := Finset.sum_le_sum point
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hd] at h
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  simp at h
  omega

end KellyMoser
-- PrimalBasic
namespace KellyMoser.Primal
open KellyMoser.Dual
open EuclideanGeometry
open scoped Classical

abbrev P := EuclideanSpace ℝ (Fin 2)
abbrev H := Fin 3 → ℝ
def lift (p : P) : H := ![p 0,p 1,1]

theorem point_eq {p q : P} (h₀ : p 0 = q 0) (h₁ : p 1 = q 1) : p=q := by
  ext i
  fin_cases i
  · exact h₀
  · exact h₁

/-- A nonconstant affine equation through two distinct points defines their joining line. -/
theorem on_join {p q : P} (hne : p ≠ q) (A B C : ℝ) (hn : A ≠ 0 ∨ B ≠ 0)
    (hp : A*p 0+B*p 1=C) (hq : A*q 0+B*q 1=C) (z : P) :
    z ∈ line[ℝ,p,q] ↔ A*z 0+B*z 1=C := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨t,rfl⟩
    rw [AffineMap.lineMap_apply_module']
    change A*(t*(q 0-p 0)+p 0)+B*(t*(q 1-p 1)+p 1)=C
    linear_combination (1-t)*hp+t*hq
  · intro hz
    by_cases he : p 0=q 0
    · have h1 : q 1-p 1 ≠ 0 := sub_ne_zero.mpr (fun h => hne (point_eq he h.symm))
      have hB : B=0 := (mul_eq_zero.mp (show B*(q 1-p 1)=0 by
        linear_combination hq-hp+A*he)).resolve_right h1
      have hA := hn.resolve_right (not_not.mpr hB)
      have hx : z 0=p 0 := sub_eq_zero.mp ((mul_eq_zero.mp (show A*(z 0-p 0)=0 by
        rw [hB] at hp hz; linarith only [hp,hz])).resolve_left hA)
      refine ⟨(z 1-p 1)/(q 1-p 1),point_eq ?_ ?_⟩
      · rw [AffineMap.lineMap_apply_module']
        change _*(q 0-p 0)+p 0=z 0
        rw [he,sub_self,mul_zero,zero_add,← he,hx]
      · rw [AffineMap.lineMap_apply_module']
        change (z 1-p 1)/(q 1-p 1)*(q 1-p 1)+p 1=z 1
        rw [div_mul_cancel₀ _ h1,sub_add_cancel]
    · have hd := sub_ne_zero.mpr (Ne.symm he)
      have hB : B ≠ 0 := by
        intro e
        have hA := hn.resolve_right (not_not.mpr e)
        have h := (mul_eq_zero.mp (show A*(q 0-p 0)=0 by rw [e] at hp hq; linarith only [hp,hq])).resolve_left hA
        exact hd h
      let t := (z 0-p 0)/(q 0-p 0)
      have htx : t*(q 0-p 0)=z 0-p 0 := div_mul_cancel₀ _ hd
      refine ⟨t,point_eq ?_ ?_⟩
      · rw [AffineMap.lineMap_apply_module']
        change t*(q 0-p 0)+p 0=z 0
        linarith only [htx]
      · rw [AffineMap.lineMap_apply_module']
        change t*(q 1-p 1)+p 1=z 1
        apply (mul_left_cancel₀ hB)
        linear_combination t*hq+(1-t)*hp-hz-A*htx

def dx (w z : P) := z 0 - w 0
def den (t : ℝ) (w z : P) := z 1-w 1+t*dx w z
def valid (s : Finset P) (w : P) (t : ℝ) : Prop :=
  ∀ z ∈ s.erase w, den t w z ≠ 0

theorem exists_valid (s : Finset P) (w : P) : ∃ t, valid s w t := by
  classical
  let F := (s.erase w).image (fun z => (w 1-z 1)/dx w z)
  obtain ⟨t,_,ht⟩ := (Set.infinite_univ : (Set.univ : Set ℝ).Infinite).exists_notMem_finset F
  refine ⟨t,?_⟩
  intro z hz h
  by_cases hd : dx w z = 0
  · have h0 : z 0 = w 0 := sub_eq_zero.mp hd
    have h1 : z 1 = w 1 := by simpa [den,hd,sub_eq_zero] using h
    exact (Finset.mem_erase.mp hz).1 (point_eq h0 h1)
  · apply ht (Finset.mem_image.mpr ⟨z,hz,?_⟩)
    apply Eq.symm
    rw [eq_div_iff hd]
    dsimp only [den] at h
    linarith

noncomputable def graph (t : ℝ) (w z : P) : Line :=
  ⟨-dx w z / den t w z, 1 / den t w z⟩
noncomputable def graphs (s : Finset P) (w : P) (t : ℝ) := (s.erase w).image (graph t w)

theorem graph_inj {s : Finset P} {w : P} {t : ℝ} (h : valid s w t) :
    ((s.erase w : Finset P) : Set P).InjOn (graph t w) := by
  intro p hp q hq H
  have hi := congrArg Line.intercept H
  change 1/den t w p = 1/den t w q at hi
  have hd : den t w p = den t w q := by simpa only [one_div,inv_inj] using hi
  have hs := congrArg Line.slope H
  change -dx w p/den t w p = -dx w q/den t w q at hs
  rw [hd] at hs
  have hx := (div_left_inj' (h q hq)).mp hs
  dsimp [dx,den] at hx hd
  exact point_eq (by linarith only [hx]) (by linear_combination hd+t*hx)

theorem slope_iff_join {s : Finset P} {w : P} {t : ℝ} (h : valid s w t)
    {p z : P} (hp : p ∈ s.erase w) (hz : z ∈ s.erase w) :
    (graph t w z).slope = (graph t w p).slope ↔ z ∈ line[ℝ,w,p] := by
  let A := den t w p-t*dx w p
  let B := -dx w p
  let C := A*w 0+B*w 1
  have hn : A ≠ 0 ∨ B ≠ 0 := by
    by_contra! hf
    apply h p hp
    dsimp [A,B] at hf
    linear_combination hf.1 - t*hf.2
  have heq := on_join (Finset.mem_erase.mp hp).1.symm A B C hn rfl
    (by dsimp [A,B,C,den,dx]; ring) z
  rw [heq]
  change -dx w z/den t w z = -dx w p/den t w p ↔ _
  rw [div_eq_div_iff (h z hz) (h p hp)]
  dsimp [A,B,C,dx,den]
  constructor <;> intro e <;> linarith only [e]

def evalForm (w : P) (t : ℝ) (v : XY) (z : P) := dx w z*v.1+den t w z*v.2

theorem graph_pass {s : Finset P} {w : P} {t : ℝ} (h : valid s w t)
    {z : P} (hz : z ∈ s.erase w) (v : XY) :
    val (graph t w z) v.1 = v.2 ↔ evalForm w t v z = 1 := by
  dsimp [val,graph,evalForm]
  have hd := h z hz
  constructor
  · intro he
    have h' := congrArg (fun a : ℝ => a * den t w z) he
    dsimp at h'
    linear_combination -h' + v.1*(div_mul_cancel₀ (-dx w z) hd) + (div_mul_cancel₀ 1 hd)
  · intro he
    apply (mul_right_cancel₀ hd)
    linear_combination -he + v.1*(div_mul_cancel₀ (-dx w z) hd) + (div_mul_cancel₀ 1 hd)

end KellyMoser.Primal
-- PrimalIncidence
namespace KellyMoser.Primal
open KellyMoser.Dual EuclideanGeometry
open scoped Classical

noncomputable def cut (w : P) (t : ℝ) (v : XY) : AffineSubspace ℝ P where
  carrier := {z | evalForm w t v z = 1}
  smul_vsub_vadd_mem' c p q z hp hq hz := by
    change evalForm w t v p = 1 at hp
    change evalForm w t v q = 1 at hq
    change evalForm w t v z = 1 at hz
    change ((c*(p 0-q 0)+z 0)-w 0)*v.1 +
      (((c*(p 1-q 1)+z 1)-w 1)+t*((c*(p 0-q 0)+z 0)-w 0))*v.2 = 1
    dsimp only [evalForm,den,dx] at hp hq hz
    linear_combination c*hp-c*hq+hz

theorem not_mem_cut (w : P) (t : ℝ) (v : XY) : w ∉ cut w t v := by
  change ¬ evalForm w t v w = 1
  simp [evalForm,dx,den]

theorem join_eq_cut {w p q : P} {t : ℝ} {v : XY} (hne : p ≠ q)
    (hp : p ∈ cut w t v) (hq : q ∈ cut w t v) : line[ℝ,p,q] = cut w t v := by
  change evalForm w t v p = 1 at hp
  change evalForm w t v q = 1 at hq
  let A := v.1+t*v.2
  let B := v.2
  let C := 1 + A*w 0+B*w 1
  have eqn (z : P) : A*z 0+B*z 1=C ↔ evalForm w t v z=1 := by
    dsimp [A,B,C,evalForm,den,dx]
    constructor <;> intro h <;> linarith only [h]
  have hn : A ≠ 0 ∨ B ≠ 0 := by
    by_contra! h
    have e := (eqn p).mpr hp
    dsimp only [C] at e
    rw [h.1,h.2] at e
    norm_num at e
  ext z
  exact (on_join hne A B C hn ((eqn p).mpr hp) ((eqn q).mpr hq) z).trans (eqn z)

theorem card_cut {s : Finset P} {w : P} {t : ℝ} (h : valid s w t) (v : XY) :
    (s.filter (fun z => z ∈ cut w t v)).card =
      ((graphs s w t).filter (fun l => val l v.1 = v.2)).card := by
  unfold graphs
  rw [Finset.filter_image, Finset.card_image_of_injOn]
  · congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hz,hv⟩
      have hzw : z ≠ w := fun e => not_mem_cut w t v (e ▸ hv)
      exact ⟨⟨hzw,hz⟩,(graph_pass h (Finset.mem_erase.mpr ⟨hzw,hz⟩) v).mpr hv⟩
    · rintro ⟨⟨hne,hz⟩,hv⟩
      exact ⟨hz,(graph_pass h (Finset.mem_erase.mpr ⟨hne,hz⟩) v).mp hv⟩
  · intro a ha b hb he
    exact graph_inj h (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 he

theorem cut_of_vertex {s : Finset P} {w : P} {t : ℝ} (h : valid s w t)
    {v : XY} (hv : v ∈ vertices (graphs s w t)) :
    ∃ p ∈ s.erase w, ∃ q ∈ s.erase w, (graph t w p).slope ≠ (graph t w q).slope ∧
      p ∈ cut w t v ∧ q ∈ cut w t v := by
  obtain ⟨l,hl,k,hk,hn,hlv,hkv⟩ := mem_vertices.mp hv
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hk
  exact ⟨p,hp,q,hq,hn,(graph_pass h hp v).mp hlv,(graph_pass h hq v).mp hkv⟩

theorem ordinary_cut {s : Finset P} {w : P} {t : ℝ} (h : valid s w t)
    {v : XY} (hv : v ∈ vertices (graphs s w t)) (ho : OrdinaryAt (graphs s w t) v.1 v.2) :
    cut w t v ∈ ordinaryLines s := by
  obtain ⟨p,hp,q,hq,hn,hlv,hkv⟩ := cut_of_vertex h hv
  have hne : p ≠ q := fun e => hn (e ▸ rfl)
  exact mem_ordinaryLines.mpr ⟨⟨p,(Finset.mem_erase.mp hp).2,q,(Finset.mem_erase.mp hq).2,
    hne,join_eq_cut hne hlv hkv⟩,(card_cut h v).trans ho⟩

theorem cut_injective {s : Finset P} {w : P} {t : ℝ} (h : valid s w t) :
    ((vertices (graphs s w t) : Finset XY) : Set XY).InjOn (cut w t) := by
  intro v hv v' _ he
  obtain ⟨p,hp,q,hq,hn,hl,hk⟩ := cut_of_vertex h hv
  have h₁ := (graph_pass h hp v).mpr hl
  have h₂ := (graph_pass h hq v).mpr hk
  have h₃ := (graph_pass h hp v').mpr (show p ∈ cut w t v' from he ▸ hl)
  have h₄ := (graph_pass h hq v').mpr (show q ∈ cut w t v' from he ▸ hk)
  have hx := ((cross_iff hn _).mp (h₁.trans h₂.symm)).trans
    ((cross_iff hn _).mp (h₃.trans h₄.symm)).symm
  exact Prod.ext hx (h₁.symm.trans ((congrArg _ hx).trans h₃))

/-- A singleton slope gives an ordinary original line through w. -/
theorem singleton_line {s : Finset P} {w : P} {t : ℝ} (h : valid s w t)
    (hw : w ∈ s) {p : P} (hp : p ∈ s.erase w)
    (single : SingletonSlope (graphs s w t) (graph t w p)) :
    line[ℝ,w,p] ∈ (ordinaryLines s).filter (fun L => w ∈ L) := by
  have hn := (Finset.mem_erase.mp hp).1
  have eq : s.filter (fun z => z ∈ line[ℝ,w,p]) = {w,p} := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨hz,hl⟩
      by_cases H : z=w
      · exact Or.inl H
      · have he := Finset.mem_erase.mpr ⟨H,hz⟩
        exact Or.inr (graph_inj h he hp (single _ (Finset.mem_image_of_mem _ he)
          ((slope_iff_join h hp he).mpr hl)))
    · rintro (rfl | rfl)
      · exact ⟨hw,left_mem_affineSpan_pair ..⟩
      · exact ⟨(Finset.mem_erase.mp hp).2,right_mem_affineSpan_pair ..⟩
  exact Finset.mem_filter.mpr ⟨mem_ordinaryLines.mpr ⟨⟨w,hw,p,(Finset.mem_erase.mp hp).2,hn.symm,rfl⟩,
    by rw [eq]; simp [hn.symm]⟩,left_mem_affineSpan_pair ..⟩

theorem singleton_inj {s : Finset P} {w : P} {t : ℝ} (h : valid s w t)
    {p q : P} (hp : p ∈ s.erase w) (hq : q ∈ s.erase w)
    (si : SingletonSlope (graphs s w t) (graph t w p)) (e : line[ℝ,w,p]=line[ℝ,w,q]) :
    graph t w q = graph t w p :=
  si _ (Finset.mem_image_of_mem _ hq) ((slope_iff_join h hp hq).mpr
    (e.symm ▸ right_mem_affineSpan_pair ℝ w q))

end KellyMoser.Primal
-- Components
/-! The four-attachment bound and two-line covering bound below are from dk8827's
merged LeftToSolve Csima–Sawyer proof and reduction. -/
open EuclideanGeometry Finset
open scoped BigOperators Classical Pointwise
namespace OMA.OrdinaryAttachment

abbrev HVec := Fin 3 → ℝ

def homogeneous (p : KellyMoser.Primal.P) : HVec := ![p 0, p 1, 1]

private def height (p q : KellyMoser.Primal.P) : HVec →ₗ[ℝ] ℝ where
  toFun v := (q 0 - p 0) * (v 1 - p 1 * v 2) - (q 1 - p 1) * (v 0 - p 0 * v 2)
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' a x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private theorem hp_height (p q : KellyMoser.Primal.P) : height p q (homogeneous p) = 0 := by
  simp [height, homogeneous]

private theorem hq_height (p q : KellyMoser.Primal.P) : height p q (homogeneous q) = 0 := by
  simp [height, homogeneous]
  ring

private theorem point_eq {p q : KellyMoser.Primal.P} (h₀ : p 0 = q 0) (h₁ : p 1 = q 1) : p = q := by
  ext i
  fin_cases i
  · exact h₀
  · exact h₁

private theorem height_ne_zero {p q w : KellyMoser.Primal.P} (hpq : p ≠ q)
    (hw : w ∉ line[ℝ, p, q]) : height p q (homogeneous w) ≠ 0 := by
  intro h
  apply hw
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.2
  have hh : (q 0 - p 0) * (w 1 - p 1) = (q 1 - p 1) * (w 0 - p 0) := by
    simpa [height, homogeneous, sub_eq_zero] using h
  by_cases h₀ : p 0 = q 0
  · have h₁ : q 1 - p 1 ≠ 0 := fun hz => hpq (point_eq h₀ (sub_eq_zero.1 hz).symm)
    have hw₀ : w 0 = p 0 := by
      have he : (q 1 - p 1) * (w 0 - p 0) = 0 := by simpa [h₀] using hh.symm
      exact sub_eq_zero.1 ((mul_eq_zero.1 he).resolve_left h₁)
    let t := (w 1 - p 1) / (q 1 - p 1)
    refine ⟨t, point_eq ?_ ?_⟩
    · rw [AffineMap.lineMap_apply_module']
      change t * (q 0 - p 0) + p 0 = w 0
      simp [h₀, hw₀]
    · rw [AffineMap.lineMap_apply_module']
      change ((w 1 - p 1) / (q 1 - p 1)) * (q 1 - p 1) + p 1 = w 1
      rw [div_mul_cancel₀ _ h₁, sub_add_cancel]
  · have h₀' : q 0 - p 0 ≠ 0 := sub_ne_zero.2 (Ne.symm h₀)
    let t := (w 0 - p 0) / (q 0 - p 0)
    refine ⟨t, point_eq ?_ ?_⟩
    · rw [AffineMap.lineMap_apply_module']
      change ((w 0 - p 0) / (q 0 - p 0)) * (q 0 - p 0) + p 0 = w 0
      rw [div_mul_cancel₀ _ h₀', sub_add_cancel]
    · rw [AffineMap.lineMap_apply_module']
      change ((w 0 - p 0) / (q 0 - p 0)) * (q 1 - p 1) + p 1 = w 1
      have hw₁ : ((w 0 - p 0) / (q 0 - p 0)) * (q 1 - p 1) = w 1 - p 1 := by
        apply (mul_right_cancel₀ h₀')
        calc
          _ = (q 1 - p 1) * (w 0 - p 0) := by
            rw [mul_right_comm, div_mul_cancel₀ _ h₀', mul_comm]
          _ = _ := by rw [← hh, mul_comm]
      rw [hw₁, sub_add_cancel]

private theorem pair_coeff {p q : KellyMoser.Primal.P} (hpq : p ≠ q) {a b : ℝ}
    (h : a • homogeneous p + b • homogeneous q = 0) : a = 0 ∧ b = 0 := by
  have h2 : a + b = 0 := by simpa [homogeneous] using congrFun h 2
  have key (i : Fin 2) : b * (q i - p i) = 0 := by
    have hi : a * p i + b * q i = 0 := by
      fin_cases i
      · simpa [homogeneous] using congrFun h 0
      · simpa [homogeneous] using congrFun h 1
    linear_combination hi - (p i) * h2
  have hb : b = 0 := by
    by_contra hb
    exact hpq (point_eq ((sub_eq_zero.1 ((mul_eq_zero.1 (key 0)).resolve_left hb)).symm)
      ((sub_eq_zero.1 ((mul_eq_zero.1 (key 1)).resolve_left hb)).symm))
  exact ⟨by simpa [hb] using h2, hb⟩

private theorem sign_cases {a : ℝ} (ha : a ^ 2 = 1) : a = 1 ∨ a = -1 := by
  have hz : (a - 1) * (a + 1) = 0 := by nlinarith only [ha]
  rcases mul_eq_zero.1 hz with h | h
  · exact Or.inl (by linarith only [h])
  · exact Or.inr (by linarith only [h])

private theorem orient_nonneg {p q w z : KellyMoser.Primal.P} {ε δ δ' : ℝ}
    (hδ' : δ' ^ 2 = 1)
    (hsign : (δ' * height p q (homogeneous z)) * (δ * height p q (homogeneous w)) > 0)
    (hex : ∃ a b c : ℝ,
      homogeneous z = a • homogeneous p + b • (ε • homogeneous q) + c • (δ • homogeneous w) ∧
      ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))) :
    ∃ a b c : ℝ, δ' • homogeneous z =
      a • homogeneous p + b • (ε • homogeneous q) + c • (δ • homogeneous w) ∧
      0 ≤ a ∧ 0 ≤ b ∧ 0 < c := by
  obtain ⟨a, b, c, hz, hcone⟩ := hex
  have hheight : height p q (homogeneous z) = c * (δ * height p q (homogeneous w)) := by
    conv_lhs => rw [hz]
    simp [hp_height, hq_height]
  have hcc : 0 < δ' * c := by
    have hs : 0 < (δ' * c) * (δ * height p q (homogeneous w)) ^ 2 := by
      calc
        _ < (δ' * height p q (homogeneous z)) * (δ * height p q (homogeneous w)) := hsign
        _ = _ := by rw [hheight]; ring
    exact pos_of_mul_pos_left hs (sq_nonneg _)
  have hab : 0 ≤ δ' * a ∧ 0 ≤ δ' * b := by
    rcases sign_cases hδ' with rfl | rfl
    · rw [one_mul, one_mul]
      rw [one_mul] at hcc
      rcases hcone with h | h
      · exact ⟨h.1, h.2.1⟩
      · exact (hcc.not_ge h.2.2).elim
    · simp only [neg_mul, one_mul] at hcc ⊢
      rcases hcone with h | h
      · exfalso
        linarith only [hcc, h.2.2]
      · exact ⟨by linarith only [h.1], by linarith only [h.2.1]⟩
  refine ⟨δ' * a, δ' * b, δ' * c, ?_, hab.1, hab.2, hcc⟩
  conv_lhs => rw [hz]
  module


private theorem cones_unique {p q w z : KellyMoser.Primal.P} (hpq : p ≠ q)
    {ε δ δ' : ℝ} (hε : ε ≠ 0) (hδ' : δ' ≠ 0)
    (hw : δ * height p q (homogeneous w) ≠ 0)
    (hf : ∃ a b c : ℝ, δ' • homogeneous z =
      a • homogeneous p + b • (ε • homogeneous q) + c • (δ • homogeneous w) ∧
      0 ≤ a ∧ 0 ≤ b ∧ 0 < c)
    (hg : ∃ a b c : ℝ, δ • homogeneous w =
      a • homogeneous p + b • (ε • homogeneous q) + c • (δ' • homogeneous z) ∧
      0 ≤ a ∧ 0 ≤ b ∧ 0 < c) :
    w = z := by
  obtain ⟨a, b, c, hf, ha, hb, hc⟩ := hf
  obtain ⟨a', b', c', hg, ha', hb', hc'⟩ := hg
  have hzw : δ' * height p q (homogeneous z) = c * (δ * height p q (homogeneous w)) := by
    simpa [hp_height, hq_height] using congrArg (height p q) hf
  have hwz : δ * height p q (homogeneous w) = c' * (δ' * height p q (homogeneous z)) := by
    simpa [hp_height, hq_height] using congrArg (height p q) hg
  rw [hzw] at hwz
  have hcc : c' * c = 1 := by
    apply mul_right_cancel₀ hw
    simpa only [one_mul, mul_assoc] using hwz.symm
  have hsum : δ • homogeneous w =
      (a' + c' * a) • homogeneous p + (b' + c' * b) • (ε • homogeneous q) +
      (c' * c) • (δ • homogeneous w) := by
    calc
      _ = _ := hg
      _ = _ := by
        conv_lhs => rw [hf]
        module
  rw [hcc, one_smul] at hsum
  have hs0 : (a' + c' * a) • homogeneous p + (b' + c' * b) • (ε • homogeneous q) = 0 := by
    simpa using congrArg (fun v : HVec => v - δ • homogeneous w) hsum.symm
  obtain ⟨hsa, hsb⟩ := pair_coeff hpq (by simpa only [smul_smul] using hs0)
  have ha0 : a = 0 := by
    have hz : c' * a = 0 := le_antisymm (by linarith only [hsa, ha']) (mul_nonneg hc'.le ha)
    exact (mul_eq_zero.1 hz).resolve_left hc'.ne'
  have hb0 : b = 0 := by
    have hsb' := (mul_eq_zero.1 hsb).resolve_right hε
    have hz : c' * b = 0 := le_antisymm (by linarith only [hsb', hb']) (mul_nonneg hc'.le hb)
    exact (mul_eq_zero.1 hz).resolve_left hc'.ne'
  simp only [ha0, hb0, zero_smul, zero_add] at hf
  have he : δ' = c * δ := by
    simpa [homogeneous] using congrFun hf 2
  have hcoord (i : Fin 2) : δ' * z i = (c * δ) * w i := by
    fin_cases i
    · simpa [homogeneous, mul_assoc] using congrFun hf 0
    · simpa [homogeneous, mul_assoc] using congrFun hf 1
  have hwz (i : Fin 2) : w i = z i := by
    apply mul_left_cancel₀ hδ'
    rw [hcoord, he]
  exact point_eq (hwz 0) (hwz 1)

private theorem swap_order {s : Finset KellyMoser.Primal.P} {p q w : KellyMoser.Primal.P} {ε δ : ℝ}
    (hε : ε ^ 2 = 1)
    (h : ∀ z ∈ s, ∃ a b c : ℝ,
      homogeneous z = a • homogeneous q + b • (ε • homogeneous p) + c • (δ • homogeneous w) ∧
      ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))) :
    ∀ z ∈ s, ∃ a b c : ℝ,
      homogeneous z = a • homogeneous p + b • (ε • homogeneous q) + c • ((ε * δ) • homogeneous w) ∧
      ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)) := by
  intro z hz
  obtain ⟨a, b, c, he, hs⟩ := h z hz
  rcases sign_cases hε with rfl | rfl
  · exact ⟨b, a, c, by simpa [add_comm] using he, hs.imp
      (fun h => ⟨h.2.1, h.1, h.2.2⟩) (fun h => ⟨h.2.1, h.1, h.2.2⟩)⟩
  · refine ⟨-b, -a, -c, ?_, ?_⟩
    · rw [he]
      module
    · rcases hs with h₀ | h₀
      · exact Or.inr ⟨neg_nonpos.2 h₀.2.1, neg_nonpos.2 h₀.1, neg_nonpos.2 h₀.2.2⟩
      · exact Or.inl ⟨neg_nonneg.2 h₀.2.1, neg_nonneg.2 h₀.1, neg_nonneg.2 h₀.2.2⟩


set_option maxHeartbeats 1600000 in
theorem four_attachments (s : Finset KellyMoser.Primal.P) (L : AffineSubspace ℝ KellyMoser.Primal.P)
    (hL : L ∈ ordinaryLines s) :
    (s.filter (fun w =>
      ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
        ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
          ∀ z ∈ s, ∃ a b c : ℝ,
            homogeneous z = a • homogeneous p + b • (ε • homogeneous q) +
              c • (δ • homogeneous w) ∧
            ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)))).card ≤ 4 := by
  classical
  obtain ⟨p, q, hpq, hpqL⟩ := card_eq_two.1 ((mem_ordinaryLines.1 hL).2)
  let W := s.filter (fun w =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          homogeneous z = a • homogeneous p + b • (ε • homogeneous q) +
            c • (δ • homogeneous w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)))
  have hmem (x : KellyMoser.Primal.P) : x ∈ s ∧ x ∈ L ↔ x = p ∨ x = q := by
    rw [← mem_filter, hpqL]
    simp
  have hpL : p ∈ L := ((hmem p).2 (Or.inl rfl)).2
  have hqL : q ∈ L := ((hmem q).2 (Or.inr rfl)).2
  have hchoice (w : W) : ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧ (w : KellyMoser.Primal.P) ∉ L ∧
      ∀ z ∈ s, ∃ a b c : ℝ,
        homogeneous z = a • homogeneous p + b • (ε • homogeneous q) +
          c • (δ • homogeneous w) ∧
        ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)) := by
    obtain ⟨p', hp', q', hq', hn, hp'L, hq'L, hw, ε, δ, hε, hδ, hcone⟩ := (mem_filter.1 w.2).2
    rcases (hmem p').1 ⟨hp', hp'L⟩ with rfl | rfl
    · rcases (hmem q').1 ⟨hq', hq'L⟩ with rfl | rfl
      · exact (hn rfl).elim
      · exact ⟨ε, δ, hε, hδ, hw, hcone⟩
    · rcases (hmem q').1 ⟨hq', hq'L⟩ with rfl | rfl
      · exact ⟨ε, ε * δ, hε, by rw [mul_pow, hε, hδ, one_mul], hw, swap_order hε hcone⟩
      · exact (hn rfl).elim
  choose ε δ hε hδ houtside hcone using hchoice
  let depth (w : W) := δ w * height p q (homogeneous w)
  have depth_ne (w : W) : depth w ≠ 0 := by
    have hd0 : δ w ≠ 0 := by
      intro hd
      simpa [hd] using hδ w
    exact mul_ne_zero hd0
      (height_ne_zero hpq (fun h => houtside w (affineSpan_pair_le_of_mem_of_mem hpL hqL h)))
  let label (w : W) : Bool × Bool := (decide (ε w = 1), decide (0 < depth w))
  have inj : Function.Injective label := by
    intro w z he
    have h₁ : decide (ε w = 1) = decide (ε z = 1) := congrArg Prod.fst he
    have h₂ : decide (0 < depth w) = decide (0 < depth z) := congrArg Prod.snd he
    have heps : ε w = ε z := by
      rcases sign_cases (hε w) with hw | hw <;> rcases sign_cases (hε z) with hz | hz
      · exact hw.trans hz.symm
      · norm_num [hw, hz] at h₁
      · norm_num [hw, hz] at h₁
      · exact hw.trans hz.symm
    have signs : 0 < depth z * depth w := by
      have hequiv : 0 < depth w ↔ 0 < depth z := by simpa using h₂
      rcases lt_or_gt_of_ne (depth_ne w) with hw | hw
      · have hz : depth z < 0 := lt_of_le_of_ne
          (le_of_not_gt (fun hz => hw.not_gt (hequiv.2 hz))) (depth_ne z)
        exact mul_pos_of_neg_of_neg hz hw
      · exact mul_pos (hequiv.1 hw) hw
    have hzS : (z : KellyMoser.Primal.P) ∈ s := (mem_filter.1 z.2).1
    have hwS : (w : KellyMoser.Primal.P) ∈ s := (mem_filter.1 w.2).1
    have hfor := orient_nonneg (hδ z) signs (hcone w z hzS)
    have hback := orient_nonneg (hδ w) (by simpa [mul_comm] using signs) (hcone z w hwS)
    rw [← heps] at hback
    have hε0 : ε w ≠ 0 := by
      intro h
      simpa [h] using hε w
    have hδ0 : δ z ≠ 0 := by
      intro h
      simpa [h] using hδ z
    exact Subtype.ext (cones_unique hpq hε0 hδ0 (depth_ne w) hfor hback)
  have hcard := Fintype.card_le_of_injective label inj
  change W.card ≤ 4
  simpa using hcard

end OMA.OrdinaryAttachment
namespace OMA.TwoPencils

private theorem generated {L : AffineSubspace ℝ KellyMoser.Primal.P}
    (hL : Module.finrank ℝ L.direction = 1) {a b : KellyMoser.Primal.P}
    (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) : line[ℝ, a, b] = L := by
  apply (AffineSubspace.eq_iff_direction_eq_of_mem
    (left_mem_affineSpan_pair ℝ a b) ha).2
  apply Submodule.eq_of_le_of_finrank_eq
  · exact AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem ha hb)
  · rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hab)]
    exact hL.symm

private theorem collinear_subset {s : Set KellyMoser.Primal.P} {L : AffineSubspace ℝ KellyMoser.Primal.P}
    (hL : Module.finrank ℝ L.direction = 1) (hs : s ⊆ L) : Collinear ℝ s := by
  rw [collinear_iff_finrank_le_one]
  have hle : vectorSpan ℝ s ≤ L.direction := by
    rw [← direction_affineSpan]
    exact AffineSubspace.direction_le (affineSpan_le.2 hs)
  exact (Submodule.finrank_mono hle).trans hL.le

theorem count (s : Finset KellyMoser.Primal.P) (hs : 4 ≤ s.card) (hc : ¬ Collinear ℝ (s : Set KellyMoser.Primal.P))
    (L M : AffineSubspace ℝ KellyMoser.Primal.P) (hL : Module.finrank ℝ L.direction = 1)
    (hM : Module.finrank ℝ M.direction = 1) (hcov : ∀ p ∈ s, p ∈ L ∨ p ∈ M) :
    s.card ≤ 2 * (ordinaryLines s).card := by
  classical
  let A := s.filter (fun p => p ∈ L ∧ p ∉ M)
  let B := s.filter (fun p => p ∈ M ∧ p ∉ L)
  let I := s.filter (fun p => p ∈ L ∧ p ∈ M)
  have hLM : L ≠ M := by
    rintro rfl
    exact hc (collinear_subset hL (fun p hp => (hcov p hp).elim id id))
  have hA : A.Nonempty := by
    by_contra h
    apply hc (collinear_subset hM ?_)
    intro p hp
    by_contra hpm
    have hpl := (hcov p hp).resolve_right hpm
    exact h ⟨p, mem_filter.2 ⟨hp, hpl, hpm⟩⟩
  have hB : B.Nonempty := by
    by_contra h
    apply hc (collinear_subset hL ?_)
    intro p hp
    by_contra hpl
    have hpm := (hcov p hp).resolve_left hpl
    exact h ⟨p, mem_filter.2 ⟨hp, hpm, hpl⟩⟩
  have hI : I.card ≤ 1 := by
    apply card_le_one.2
    intro a ha b hb
    by_contra h
    obtain ⟨_, haL, haM⟩ := mem_filter.1 ha
    obtain ⟨_, hbL, hbM⟩ := mem_filter.1 hb
    exact hLM ((generated hL haL hbL h).symm.trans (generated hM haM hbM h))
  have hcard : s.card ≤ A.card + B.card + 1 := by
    have hsub : s ⊆ A ∪ B ∪ I := by
      intro p hp
      by_cases hpL : p ∈ L <;> by_cases hpM : p ∈ M
      · exact mem_union_right _ (mem_filter.2 ⟨hp, hpL, hpM⟩)
      · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hp, hpL, hpM⟩))
      · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hp, hpM, hpL⟩))
      · exact ((hcov p hp).elim hpL hpM).elim
    have h₁ := card_le_card hsub
    have h₂ := card_union_le (A ∪ B) I
    have h₃ := card_union_le A B
    omega
  have hcut (a b : KellyMoser.Primal.P) (ha : a ∈ A) (hb : b ∈ B) :
      s.filter (fun p => p ∈ line[ℝ, a, b]) = {a, b} := by
    obtain ⟨has, haL, haM⟩ := mem_filter.1 ha
    obtain ⟨hbs, hbM, hbL⟩ := mem_filter.1 hb
    have hab : a ≠ b := fun h => hbL (h ▸ haL)
    let N : AffineSubspace ℝ KellyMoser.Primal.P := line[ℝ, a, b]
    have haN : a ∈ N := left_mem_affineSpan_pair ℝ a b
    have hbN : b ∈ N := right_mem_affineSpan_pair ℝ a b
    have hN : Module.finrank ℝ N.direction = 1 := by
      rw [show N = line[ℝ, a, b] from rfl, direction_affineSpan, vectorSpan_pair,
        finrank_span_singleton (vsub_ne_zero.mpr hab)]
    ext z
    constructor
    · intro hz
      obtain ⟨hzs, hzN⟩ := mem_filter.1 hz
      rcases hcov z hzs with hzL | hzM
      · have hza : z = a := by
          by_contra hh
          have he := (generated hN hzN haN hh).symm.trans (generated hL hzL haL hh)
          exact hbL (he ▸ hbN)
        simp [hza]
      · have hzb : z = b := by
          by_contra hh
          have he := (generated hN hzN hbN hh).symm.trans (generated hM hzM hbM hh)
          exact haM (he ▸ haN)
        simp [hzb]
    · intro hz
      rcases mem_insert.1 hz with rfl | hz
      · exact mem_filter.2 ⟨has, haN⟩
      · obtain rfl := mem_singleton.1 hz
        exact mem_filter.2 ⟨hbs, hbN⟩
  have hcross : A.card * B.card ≤ (ordinaryLines s).card := by
    rw [← card_product]
    apply card_le_card_of_injOn (fun z : KellyMoser.Primal.P × KellyMoser.Primal.P => line[ℝ, z.1, z.2])
    · rintro ⟨a, b⟩ h
      obtain ⟨ha, hb⟩ := mem_product.1 h
      obtain ⟨has, haL, _⟩ := mem_filter.1 ha
      obtain ⟨hbs, _, hbL⟩ := mem_filter.1 hb
      have hab : a ≠ b := fun he => hbL (he ▸ haL)
      exact mem_ordinaryLines.2 ⟨⟨a, has, b, hbs, hab, rfl⟩, by rw [hcut a b ha hb]; simp [hab]⟩
    · rintro ⟨a, b⟩ h ⟨c, d⟩ h' he
      obtain ⟨ha, hb⟩ := mem_product.1 h
      obtain ⟨hc, hd⟩ := mem_product.1 h'
      change line[ℝ, a, b] = line[ℝ, c, d] at he
      have habcd : ({a, b} : Finset KellyMoser.Primal.P) = {c, d} := by
        rw [← hcut a b ha hb, ← hcut c d hc hd, he]
      have hca : a = c := by
        have hm : a ∈ ({c, d} : Finset KellyMoser.Primal.P) := habcd ▸ by simp
        have hmem := mem_insert.1 hm
        refine hmem.resolve_right ?_
        intro had
        exact (mem_filter.1 hd).2.2 ((mem_singleton.1 had) ▸ (mem_filter.1 ha).2.1)
      have hdb : b = d := by
        have hm : b ∈ ({c, d} : Finset KellyMoser.Primal.P) := habcd ▸ by simp
        have hmem := mem_insert.1 hm
        refine mem_singleton.1 (hmem.resolve_left ?_)
        intro hbc
        exact (mem_filter.1 hc).2.2 (hbc ▸ (mem_filter.1 hb).2.1)
      exact Prod.ext hca hdb
  have hA0 := card_pos.2 hA
  have hB0 := card_pos.2 hB
  have hsizes : A.card + B.card ≤ A.card * B.card + 1 := by
    obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hA0.ne'
    obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero hB0.ne'
    rw [ha, hb, Nat.succ_mul, Nat.mul_succ]
    omega
  omega

end OMA.TwoPencils
-- PrimalCone
namespace KellyMoser.Primal
open KellyMoser.Dual
open scoped Classical

def basisLine (l : Line) : H := ![l.slope,1,l.intercept]
def infinity : H := ![0,0,1]

def affineChart (w : P) (t A B x y : ℝ) : H →ₗ[ℝ] H where
  toFun z :=
    let u := -(z 0-w 0*z 2)
    let d := z 1-w 1*z 2+t*(z 0-w 0*z 2)
    ![u, A*d+B*u, A*(u*x+z 2-d*y)]
  map_add' z v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c z := by ext i; fin_cases i <;> simp <;> ring

theorem affineChart_inj {w : P} {t A B x y : ℝ} (ha : A ≠ 0) :
    Function.Injective (affineChart w t A B x y) := by
  intro z v he
  let u (p : H) := -(p 0-w 0*p 2)
  let d (p : H) := p 1-w 1*p 2+t*(p 0-w 0*p 2)
  have eu : u z=u v := congrFun he 0
  have e₁ : A*d z+B*u z=A*d v+B*u v := congrFun he 1
  have e₂ : A*(u z*x+z 2-d z*y)=A*(u v*x+v 2-d v*y) := congrFun he 2
  rw [eu] at e₁ e₂
  have ed : d z=d v := mul_left_cancel₀ ha (add_right_cancel e₁)
  rw [ed] at e₂
  have eZ := mul_left_cancel₀ ha e₂
  have h₂ : z 2=v 2 := by linarith only [eZ]
  dsimp only [u] at eu
  dsimp only [d] at ed
  rw [h₂] at eu ed
  have h₀ : z 0=v 0 := by linarith only [eu]
  rw [h₀] at ed
  ext i
  fin_cases i
  · exact h₀
  · change z 1 = v 1
    linarith only [ed]
  · exact h₂

noncomputable def scale (w : P) (t A B : ℝ) (z : P) :=
  den t w z * (A+B*(graph t w z).slope)

theorem chart_graph {w z : P} {t A B x y : ℝ} (hd : den t w z ≠ 0)
    (hd' : A+B*(graph t w z).slope ≠ 0) :
    affineChart w t A B x y (lift z) = scale w t A B z • basisLine (change A B x y (graph t w z)) := by
  let l := graph t w z
  let d := den t w z
  let D := A+B*l.slope
  have e₁ : l.slope*d = -dx w z := div_mul_cancel₀ _ hd
  have e₂ : l.intercept*d = 1 := div_mul_cancel₀ _ hd
  have e₃ : (change A B x y l).slope * D = l.slope := div_mul_cancel₀ _ hd'
  have e₄ : (change A B x y l).intercept * D = A*(l.slope*x+l.intercept-y) := div_mul_cancel₀ _ hd'
  let u := -dx w z
  have lhs : affineChart w t A B x y (lift z) = ![u,A*d+B*u,A*(u*x+1-d*y)] := by
    ext i; fin_cases i <;> simp [affineChart,lift,u,d,dx,den]
  rw [lhs]
  ext i
  fin_cases i
  · change -dx w z = (d*D)*(change A B x y l).slope
    linear_combination -e₁ - d*e₃
  · change A*d+B*(-dx w z)=(d*D)*1
    dsimp only [D]
    linear_combination -B*e₁
  · change A*((-dx w z)*x+1-d*y)=(d*D)*(change A B x y l).intercept
    linear_combination -A*x*e₁-A*e₂-d*e₄

theorem chart_infinity (w : P) (t A B x y : ℝ) :
    affineChart w t A B x y (lift w) = A • infinity := by
  ext i; fin_cases i <;> simp [affineChart,lift,infinity]

theorem sign_mul {a b c : ℝ} (h : SameSign a b c) (r : ℝ) :
    SameSign (r*a) (r*b) (r*c) := by
  rcases h with h | h <;> rcases le_total 0 r with hr | hr
  · exact Or.inl ⟨mul_nonneg hr h.1,mul_nonneg hr h.2.1,mul_nonneg hr h.2.2⟩
  · exact Or.inr ⟨mul_nonpos_of_nonpos_of_nonneg hr h.1,mul_nonpos_of_nonpos_of_nonneg hr h.2.1,
      mul_nonpos_of_nonpos_of_nonneg hr h.2.2⟩
  · exact Or.inr ⟨mul_nonpos_of_nonneg_of_nonpos hr h.1,mul_nonpos_of_nonneg_of_nonpos hr h.2.1,
      mul_nonpos_of_nonneg_of_nonpos hr h.2.2⟩
  · exact Or.inl ⟨mul_nonneg_of_nonpos_of_nonpos hr h.1,mul_nonneg_of_nonpos_of_nonpos hr h.2.1,
      mul_nonneg_of_nonpos_of_nonpos hr h.2.2⟩

noncomputable def orientSign (x : ℝ) : ℝ := if x < 0 then -1 else 1
theorem sign_sq (x : ℝ) : orientSign x ^ 2=1 := by unfold orientSign; split <;> norm_num
theorem sign_abs (x : ℝ) : orientSign x * |x|=x := by
  unfold orientSign
  split <;> rename_i h
  · rw [abs_of_neg h]; ring
  · rw [abs_of_nonneg (le_of_not_gt h),one_mul]

def Attached (s : Finset P) (w : P) (L : AffineSubspace ℝ P) : Prop :=
  ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
    ∃ ε δ : ℝ, ε^2=1 ∧ δ^2=1 ∧ ∀ z ∈ s, ∃ a b c : ℝ,
      lift z = a • lift p+b • (ε • lift q)+c • (δ • lift w) ∧ SameSign a b c

theorem cone_rescale {s : Finset P} {p q w : P} (i j k : ℝ)
    (h : ∀ z ∈ s, ∃ a b c : ℝ, lift z = a • (i • lift p)+b • (j • lift q)+c • (k • lift w) ∧ SameSign a b c) :
    ∃ ε δ : ℝ, ε^2=1 ∧ δ^2=1 ∧ ∀ z ∈ s, ∃ a b c : ℝ,
      lift z = a • lift p+b • (ε • lift q)+c • (δ • lift w) ∧ SameSign a b c := by
  refine ⟨orientSign i*orientSign j,orientSign i*orientSign k,?_,?_,?_⟩
  · rw [mul_pow,sign_sq,sign_sq,one_mul]
  · rw [mul_pow,sign_sq,sign_sq,one_mul]
  intro z hz
  obtain ⟨a,b,c,eq,hsg⟩ := h z hz
  have sgn : SameSign (a*|i|) (b*|j|) (c*|k|) := by
    rcases hsg with h | h
    · exact Or.inl ⟨mul_nonneg h.1 (abs_nonneg _),mul_nonneg h.2.1 (abs_nonneg _),
        mul_nonneg h.2.2 (abs_nonneg _)⟩
    · exact Or.inr ⟨mul_nonpos_of_nonpos_of_nonneg h.1 (abs_nonneg _),
        mul_nonpos_of_nonpos_of_nonneg h.2.1 (abs_nonneg _),mul_nonpos_of_nonpos_of_nonneg h.2.2 (abs_nonneg _)⟩
  refine ⟨_,_,_,?_,sign_mul sgn (orientSign i)⟩
  rw [eq,smul_smul,smul_smul,smul_smul,smul_smul,smul_smul]
  have e₁ : a*i=orientSign i*(a*|i|) := by linear_combination -a*sign_abs i
  have e₂ (b j : ℝ) : b*j=orientSign i*(b*|j|)*(orientSign i*orientSign j) := by
    linear_combination -b*sign_abs j - b * |j| * orientSign j*sign_sq i
  rw [e₁,e₂ b j,e₂ c k]

end KellyMoser.Primal
-- PrimalAttachment
namespace KellyMoser.Primal
open KellyMoser.Dual EuclideanGeometry
open scoped Classical

/-- Turn an exposed ordinary dual vertex into the signed cone certificate
used in the four-attachment bound. -/
theorem attached_vertex {s : Finset P} {w : P} {t : ℝ} (h : valid s w t)
    {v : XY} (hv : v ∈ exposed (vertices (graphs s w t)) (slopes (graphs s w t)))
    (ho : OrdinaryAt (graphs s w t) v.1 v.2) : Attached s w (cut w t v) := by
  classical
  let S := graphs s w t
  obtain ⟨A,B,ha,hd,hr⟩ := exists_chart hv
  let f := change A B v.1 v.2
  let G := fun z => f (graph t w z)
  let I := (S.image f).filter (fun l => l.intercept=0)
  let T := affineChart w t A B v.1 v.2
  let κ := scale w t A B
  have CI : I.card=2 := (change_inc_card (x₀ := v.1) (y₀ := v.2) ha hd).trans ho
  have hG (z : P) (hz : z ∈ s.erase w) : G z ∈ S.image f :=
    Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hz)
  have hκ (z : P) (hz : z ∈ s.erase w) : κ z ≠ 0 :=
    mul_ne_zero (h z hz) (hd _ (Finset.mem_image_of_mem _ hz))
  have chart (z : P) (hz : z ∈ s.erase w) : T (lift z) = κ z • basisLine (G z) :=
    chart_graph (h z hz) (hd _ (Finset.mem_image_of_mem _ hz))
  have inc (z : P) (hz : z ∈ s.erase w) :
      (G z).intercept=0 ↔ z ∈ cut w t v :=
    (change_intercept_zero _ ha (hd _ (Finset.mem_image_of_mem _ hz))).trans (graph_pass h hz v)
  obtain ⟨p₀,hp₀,q₀,hq₀,hsep,he₁,he₂⟩ := cut_of_vertex h (Finset.mem_filter.mp hv).1
  have hn : (G p₀).slope ≠ (G q₀).slope := fun e => hsep
    ((change_slope_eq ha (hd _ (Finset.mem_image_of_mem _ hp₀)) (hd _ (Finset.mem_image_of_mem _ hq₀))).mp e)
  have ordered : ∃ p ∈ s.erase w, ∃ q ∈ s.erase w, (G p).slope < (G q).slope ∧
      p ∈ cut w t v ∧ q ∈ cut w t v := by
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · exact ⟨p₀,hp₀,q₀,hq₀,hlt,he₁,he₂⟩
    · exact ⟨q₀,hq₀,p₀,hp₀,hgt,he₂,he₁⟩
  obtain ⟨p,hp,q,hq,hlt,hep,heq⟩ := ordered
  have pne : G p ≠ G q := fun e => hlt.ne (congrArg Line.slope e)
  have hp0 := (inc p hp).mpr hep
  have hq0 := (inc q hq).mpr heq
  have Ie : ({G p,G q} : Finset Line) = I := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | he
      · exact Finset.mem_filter.mpr ⟨hG p hp,hp0⟩
      · rw [Finset.mem_singleton.mp he]
        exact Finset.mem_filter.mpr ⟨hG q hq,hq0⟩
    · simp [CI,pne]
  have two (k : Line) (hk : k ∈ S.image f) (hk0 : k.intercept = 0) :
      k = G p ∨ k = G q := by
    have hm : k ∈ I := Finset.mem_filter.mpr ⟨hk,hk0⟩
    simpa [← Ie] using hm
  refine ⟨p,(Finset.mem_erase.mp hp).2,q,(Finset.mem_erase.mp hq).2,
    fun e => pne (congrArg G e),hep,heq,not_mem_cut w t v,?_⟩
  apply cone_rescale (-(κ p)⁻¹) ((κ q)⁻¹) (A⁻¹)
  intro z hz
  by_cases hw : z=w
  · subst z
    refine ⟨0,0,A,?_,?_⟩
    · simp [smul_smul,ha]
    · rcases le_total 0 A with H | H
      · exact Or.inl ⟨le_rfl,le_rfl,H⟩
      · exact Or.inr ⟨le_rfl,le_rfl,H⟩
  have he := Finset.mem_erase.mpr ⟨hw,hz⟩
  obtain ⟨a,b,c,es,em,ei,sgn⟩ := signed_coordinates hr (hG p hp) (hG q hq) hlt hp0 hq0 two (G z) (hG z he)
  have vec : basisLine (G z) = (-a) • basisLine (G p)+b • basisLine (G q)+c • infinity := by
    ext i
    fin_cases i
    · simpa [basisLine,infinity] using es
    · simpa [basisLine,infinity] using em
    · simpa [basisLine,infinity,hp0,hq0] using ei
  refine ⟨κ z*a,κ z*b,κ z*c,?_,sign_mul sgn (κ z)⟩
  apply (affineChart_inj (w := w) (t := t) (B := B) (x := v.1) (y := v.2) ha)
  change T (lift z) = T _
  rw [map_add,map_add,map_smul,map_smul,map_smul,map_smul,map_smul,map_smul,
      chart z he,chart p hp,chart q hq,show T (lift w) = A • infinity from chart_infinity ..,vec]
  simp [smul_add,smul_smul,hκ p hp,hκ q hq,ha]

end KellyMoser.Primal
-- PrimalCount
namespace KellyMoser.Primal
open KellyMoser.Dual EuclideanGeometry
open scoped Classical

def TwoCovered (s : Finset P) : Prop :=
  ∃ L M : AffineSubspace ℝ P, Module.finrank ℝ L.direction=1 ∧
    Module.finrank ℝ M.direction=1 ∧ (∀ z ∈ s, z ∈ L ∨ z ∈ M)

theorem many_slopes {s : Finset P} {w : P} {t : ℝ} (h : valid s w t)
    (n : 4 ≤ s.card) (hw : w ∈ s) (uncov : ¬ TwoCovered s) :
    3 ≤ (slopes (graphs s w t)).card := by
  classical
  let U := slopes (graphs s w t)
  have hm (z : P) (hz : z ∈ s.erase w) : (graph t w z).slope ∈ U :=
    Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hz)
  have rank (z : P) (hz : z ∈ s.erase w) : Module.finrank ℝ (line[ℝ,w,z]).direction=1 := by
    rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton
      (vsub_ne_zero.mpr (Finset.mem_erase.mp hz).1.symm)]
  by_contra! small
  have hcard := Finset.card_erase_of_mem hw
  obtain ⟨p,hp⟩ : (s.erase w).Nonempty := Finset.card_pos.mp (by omega)
  apply uncov
  by_cases diff : ∃ q ∈ s.erase w, (graph t w p).slope ≠ (graph t w q).slope
  · obtain ⟨q,hq,hne⟩ := diff
    have e : ({(graph t w p).slope,(graph t w q).slope} : Finset ℝ) = U := by
      apply Finset.eq_of_subset_of_card_le
      · simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro (hm p hp) (hm q hq)
      · simp [hne,U] at *
        omega
    refine ⟨_,_,rank p hp,rank q hq,?_⟩
    intro z hz
    by_cases he : z=w
    · exact Or.inl (he ▸ left_mem_affineSpan_pair ℝ w p)
    have hz' := Finset.mem_erase.mpr ⟨he,hz⟩
    have hh := hm z hz'
    rw [← e,Finset.mem_insert,Finset.mem_singleton] at hh
    exact hh.imp ((slope_iff_join h hp hz').mp) ((slope_iff_join h hq hz').mp)
  · refine ⟨_,_,rank p hp,rank p hp,?_⟩
    intro z hz
    by_cases he : z=w
    · exact Or.inl (he ▸ left_mem_affineSpan_pair ℝ w p)
    have hz' := Finset.mem_erase.mpr ⟨he,hz⟩
    exact Or.inl ((slope_iff_join h hp hz').mp (by
      by_contra e
      exact diff ⟨z,hz',Ne.symm e⟩))

noncomputable def degree (s : Finset P) (w : P) :=
  ((ordinaryLines s).filter (fun L => w ∈ L)).card

noncomputable def attachedCount (s : Finset P) (w : P) :=
  ((ordinaryLines s).filter (Attached s w)).card

theorem point_counts {s : Finset P} (n : 4 ≤ s.card) (uncov : ¬ TwoCovered s)
    {w : P} (hw : w ∈ s) (hdeg : degree s w ≤ 1) :
    (degree s w=0 → 3 ≤ attachedCount s w) ∧ 2 ≤ attachedCount s w := by
  classical
  obtain ⟨t,h⟩ := exists_valid s w
  let S := graphs s w t
  let E := exposed (vertices S) (slopes S)
  let O := E.filter (fun v => OrdinaryAt S v.1 v.2)
  let D := (ordinaryLines s).filter (fun L => w ∈ L)
  have one (l : Line) (hl : l ∈ S) (k : Line) (hk : k ∈ S)
      (H : SingletonSlope S l) (K : SingletonSlope S k) : l=k := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hk
    have eq := (Finset.card_le_one (s := D)).mp hdeg _ (singleton_line h hw hp H) _ (singleton_line h hw hq K)
    exact (singleton_inj h hp hq H eq).symm
  have nc := grid_of_three (many_slopes h n hw uncov) one
  obtain ⟨hz,ho⟩ := local_counts S nc
  have card : O.card ≤ attachedCount s w := by
    apply Finset.card_le_card_of_injOn (cut w t)
    · intro v hv
      obtain ⟨he,hord⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨ordinary_cut h (Finset.mem_filter.mp he).1 hord, attached_vertex h he hord⟩
    · intro v hv v' hv' eq
      exact cut_injective h (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1
        (Finset.mem_filter.mp (Finset.mem_filter.mp hv').1).1 eq
  by_cases single : ∃ l ∈ S, SingletonSlope S l
  · obtain ⟨l,hl,hlS⟩ := single
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hl
    have hd : 0 < degree s w := Finset.card_pos.mpr ⟨_,singleton_line h hw hp hlS⟩
    refine ⟨fun e => (hd.ne' e).elim,?_⟩
    exact (ho _ (Finset.mem_image_of_mem _ hp) (fun k hk H => one _ hk _ (Finset.mem_image_of_mem _ hp) H hlS)).trans card
  · push Not at single
    have hh := (hz single).trans card
    exact ⟨fun _ => hh,by omega⟩

theorem three_point {s : Finset P} (n : s.card=3) (hc : ¬ Collinear ℝ (s : Set P)) :
    2 ≤ (ordinaryLines s).card := by
  classical
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp n
  have o (p q r : P) (hpq : p ≠ q) (hr : r ∉ line[ℝ,p,q]) :
      line[ℝ,p,q] ∈ ordinaryLines ({p,q,r} : Finset P) := by
    apply mem_ordinaryLines.mpr
    refine ⟨⟨p,by simp,q,by simp,hpq,rfl⟩,?_⟩
    have eq : ({p,q,r} : Finset P).filter (fun z => z ∈ line[ℝ,p,q]) = {p,q} := by
      ext z
      simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨h,hz⟩
        rcases h with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact (hr hz).elim
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl,left_mem_affineSpan_pair ..⟩
        · exact ⟨Or.inr (Or.inl rfl),right_mem_affineSpan_pair ..⟩
    simp [eq,hpq]
  have nc (p q r : P) (eq : ({a,b,c} : Finset P) = {p,q,r}) : r ∉ line[ℝ,p,q] := by
    intro h
    apply hc
    rw [eq]
    have permute : (({p,q,r} : Finset P) : Set P) = ({r,p,q} : Set P) := by
      ext z
      simp [or_comm,or_left_comm]
    rw [permute]
    exact collinear_insert_of_mem_affineSpan_pair h
  have H := nc a b c rfl
  have perm : ({a,b,c} : Finset P) = {a,c,b} := by ext z; simp [or_comm]
  exact Finset.one_lt_card.mpr ⟨_,o a b c hab H,_,perm ▸ o a c b hac (nc a c b perm),
    fun e => H (e.symm ▸ right_mem_affineSpan_pair ℝ a c)⟩

theorem configuration (s : Finset P) (hc : ¬ Collinear ℝ (s : Set P))
    (n : 3 ≤ s.card) : 3*s.card ≤ 7*(ordinaryLines s).card := by
  classical
  by_cases hn : s.card=3
  · have h := three_point hn hc
    omega
  have hn' : 4 ≤ s.card := by omega
  by_cases cov : TwoCovered s
  · obtain ⟨L,M,hL,hM,hcov⟩ := cov
    have h := OMA.TwoPencils.count s hn' hc L M hL hM hcov
    omega
  apply countOrdinary s (ordinaryLines s) (fun p L => p ∈ L) (Attached s)
  · exact fun L hL => (mem_ordinaryLines.mp hL).2
  · intro L hL
    refine (Finset.card_le_card ?_).trans (OMA.OrdinaryAttachment.four_attachments s L hL)
    intro w hw
    obtain ⟨hw,hatt⟩ := Finset.mem_filter.mp hw
    apply Finset.mem_filter.mpr
    exact ⟨hw,hatt⟩
  · intro p hp h0
    change degree s p = 0 at h0
    exact (point_counts hn' cov hp (by omega)).1 h0
  · intro p hp h1
    exact (point_counts hn' cov hp (show degree s p ≤ 1 from h1.le)).2

end KellyMoser.Primal

theorem OMA.solution : type_of% @Erdos210.erdos_210.lower_bound := by
  intro n hn
  obtain ⟨s, hs, hc, hf⟩ := Erdos210.f_attained hn
  have H := KellyMoser.Primal.configuration s hc (hs ▸ hn)
  simpa only [hs, hf] using H
