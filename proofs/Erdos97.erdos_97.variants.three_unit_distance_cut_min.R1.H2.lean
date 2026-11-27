import OMAReductions.R_Erdos97_erdos_97_variants_three_unit_distance_cut_min_R1
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Ring.Nat

/-! The lower bound for the Fishburn–Reeds cut minimum. -/

/- Reduction of the Erdős 97 lower bound to finite column obstructions. -/

section
/- Existence of the crossing orders for a convex cut. -/

/- Distance inequalities for crossing diagonals of an ordered convex cut. -/

open scoped EuclideanGeometry
open EuclideanGeometry AffineSubspace

namespace OrderedUnitCuts

abbrev Point := ℝ²

def DiagonalsMeet (a b c d : Point) : Prop :=
  ∃ p, Sbtw ℝ a p c ∧ Sbtw ℝ b p d

theorem strict_monge_of_crossing {a b c d : Point} (hq : DiagonalsMeet a b c d)
    (hn : ¬Collinear ℝ ({d, a, c} : Set Point)) :
    dist a d + dist b c < dist a c + dist b d := by
  obtain ⟨p, hapc, hbpd⟩ := hq
  have hp : dist a p + dist p c = dist a c := hapc.wbtw.dist_add_dist
  have hq : dist b p + dist p d = dist b d := hbpd.wbtw.dist_add_dist
  have hbad : ¬ Wbtw ℝ a p d := by
    intro hw
    have hline : line[ℝ, a, p] = line[ℝ, a, c] :=
      affineSpan_pair_eq_of_right_mem_of_ne hapc.wbtw.mem_affineSpan hapc.ne_left
    have had : line[ℝ, a, p] = line[ℝ, a, d] :=
      affineSpan_pair_eq_of_right_mem_of_ne hw.mem_affineSpan hapc.ne_left
    apply hn
    apply collinear_insert_of_mem_affineSpan_pair
    rw [← hline, had]
    exact right_mem_affineSpan_pair _ _ _
  have h₁ := dist_lt_dist_add_dist_iff.mpr hbad
  have h₂ := dist_triangle b p c
  linarith

theorem angle_sum_of_crossing {a b c d : Point} (hq : DiagonalsMeet a b c d)
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a) :
    ∠ d a b + ∠ a b c + ∠ b c d + ∠ c d a = 2 * Real.pi := by
  obtain ⟨p, hapc, hbpd⟩ := hq
  have hA : ∠ d a p + ∠ p a b = ∠ d a b := angle_add_angle_eq_of_sbtw hbpd.symm
  have hB : ∠ a b p + ∠ p b c = ∠ a b c := angle_add_angle_eq_of_sbtw hapc
  have hC : ∠ b c p + ∠ p c d = ∠ b c d := angle_add_angle_eq_of_sbtw hbpd
  have hD : ∠ c d p + ∠ p d a = ∠ c d a := angle_add_angle_eq_of_sbtw hapc.symm
  have hP₁ := angle_add_angle_eq_pi_of_angle_eq_pi b hapc.angle₁₂₃_eq_pi
  have hP₂ := angle_add_angle_eq_pi_of_angle_eq_pi d hapc.angle₁₂₃_eq_pi
  have e₁ := angle_add_angle_add_angle_eq_pi p hab.symm
  have e₂ := angle_add_angle_add_angle_eq_pi p hbc.symm
  have e₃ := angle_add_angle_add_angle_eq_pi p hcd.symm
  have e₄ := angle_add_angle_add_angle_eq_pi p hda.symm
  rw [angle_comm b p c] at hP₁
  rw [angle_comm d p a] at hP₂
  linarith only [hA,hB,hC,hD,hP₁,hP₂,e₁,e₂,e₃,e₄]

theorem acute_of_shorter {a d v : Point} (hn : ¬Collinear ℝ ({d,v,a} : Set Point))
    (hshort : dist v d ≤ dist a d) : ∠ d a v < Real.pi/2 := by
  have hcomp := (angle_le_iff_dist_le hn).2 (by simpa only [dist_comm] using hshort)
  have he := angle_add_angle_add_angle_eq_pi a (ne₁₂_of_not_collinear hn).symm
  have hpos := angle_pos_of_not_collinear (p₁ := v) (p₂ := d) (p₃ := a) (by rwa [Set.insert_comm])
  rw [angle_comm v a d, angle_comm a d v] at he
  linarith only [he,hcomp,hpos]

theorem angle_le_of_crossing {a b d v : Point} (hq : DiagonalsMeet a v b d) :
    ∠ d a b ≤ ∠ d a v := by
  obtain ⟨p, hapb, hvpd⟩ := hq
  have he : ∠ d a p + ∠ p a v = ∠ d a v := angle_add_angle_eq_of_sbtw hvpd.symm
  rw [hapb.angle_eq_right d] at he
  linarith only [he,angle_nonneg p a v]

def StrictMonge {a b : ℕ} (d : Fin a → Fin b → ℝ) : Prop :=
  ∀ i k j l, i < k → j < l → d i j + d k l < d i l + d k j

def NoAcuteCorners {a b : ℕ} (d : Fin a → Fin b → ℝ) : Prop :=
  ∀ i k j l r₁ r₂ c₁ c₂, i < r₁ → r₁ ≤ k → i ≤ r₂ → r₂ < k →
    j < c₁ → c₁ ≤ l → j ≤ c₂ → c₂ < l →
    d r₁ j ≤ d i j → d i c₁ ≤ d i j →
    d r₂ l ≤ d k l → d k c₂ ≤ d k l → False

theorem no_unit_rectangle {a b : ℕ} {d : Fin a → Fin b → ℝ}
    (monge : StrictMonge d) {i k : Fin a} {j l : Fin b} (hik : i < k) (hjl : j < l)
    (h₁ : d i j = 1) (h₂ : d i l = 1) (h₃ : d k j = 1) (h₄ : d k l = 1) : False := by
  have h := monge i k j l hik hjl
  rw [h₁, h₂, h₃, h₄] at h
  exact (lt_irrefl _ h)

/-- The only permissible ordered six-cycle has its missing unit edges on the main diagonal. -/
theorem six_cycle_order {a b : ℕ} {d : Fin a → Fin b → ℝ}
    (monge : StrictMonge d) (noAcute : NoAcuteCorners d)
    {x y z : Fin a} {j k l : Fin b} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hjk : j < k) (hkl : k < l)
    (hxj : d x j = 1) (hxk : d x k = 1) (hyj : d y j = 1) (hyl : d y l = 1)
    (hzk : d z k = 1) (hzl : d z l = 1) : z < y ∧ y < x := by
  have horder :
      (x < y ∧ y < z) ∨
      (x < z ∧ z < y) ∨
      (y < x ∧ x < z) ∨
      (y < z ∧ z < x) ∨
      (z < x ∧ x < y) ∨
      (z < y ∧ y < x) := by omega
  rcases horder with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact (noAcute x z j l y y k k h₁ h₂.le h₁.le h₂ hjk hkl.le hjk.le hkl
      (by rw [hyj, hxj]) (by rw [hxk, hxj]) (by rw [hyl, hzl]) (by rw [hzk, hzl])).elim
  · have v0 := monge z y j l (by omega) (by omega)
    have v1 := monge x z j k (by omega) (by omega)
    simp only [hxj, hxk, hyj, hyl, hzk, hzl] at v0 v1
    linarith
  · have v0 := monge y z k l (by omega) (by omega)
    have v1 := monge y x j k (by omega) (by omega)
    simp only [hxj, hxk, hyj, hyl, hzk, hzl] at v0 v1
    linarith
  · have v0 := monge y z k l (by omega) (by omega)
    have v1 := monge y x j k (by omega) (by omega)
    simp only [hxj, hxk, hyj, hyl, hzk, hzl] at v0 v1
    linarith
  · have v0 := monge z x k l (by omega) (by omega)
    have v1 := monge x y j l (by omega) (by omega)
    simp only [hxj, hxk, hyj, hyl, hzk, hzl] at v0 v1
    linarith
  · exact ⟨h₁, h₂⟩

structure CrossOrdered {a b : ℕ} (u : Fin a → Point) (v : Fin b → Point) : Prop where
  distinct : ∀ i j, u i ≠ v j
  noncollinearU : ∀ i k j, i ≠ k → ¬Collinear ℝ ({v j, u i, u k} : Set Point)
  noncollinearV : ∀ i j l, j ≠ l → ¬Collinear ℝ ({u i, v j, v l} : Set Point)
  twoTwo : ∀ i k j l, i < k → j < l → DiagonalsMeet (u i) (u k) (v l) (v j)
  threeOne : ∀ i r k j, i < r → r < k → DiagonalsMeet (u i) (u r) (u k) (v j)
  oneThree : ∀ i j c l, j < c → c < l → DiagonalsMeet (v j) (v c) (v l) (u i)

private theorem DiagonalsMeet.swapEnds {a b c d : Point} (h : DiagonalsMeet a b c d) :
    DiagonalsMeet c b a d := by
  obtain ⟨p, h₁, h₂⟩ := h
  exact ⟨p, h₁.symm, h₂⟩

theorem CrossOrdered.strictMonge {a b : ℕ} {u : Fin a → Point} {v : Fin b → Point}
    (h : CrossOrdered u v) : StrictMonge (fun i j => dist (u i) (v j)) := by
  intro i k j l hik hjl
  apply strict_monge_of_crossing (h.twoTwo i k j l hik hjl)
  rw [Set.insert_comm]
  exact h.noncollinearV i j l hjl.ne

theorem CrossOrdered.noAcuteCorners {a b : ℕ} {u : Fin a → Point} {v : Fin b → Point}
    (h : CrossOrdered u v) : NoAcuteCorners (fun i j => dist (u i) (v j)) := by
  intro i k j l r₁ r₂ c₁ c₂ hir₁ hr₁k hir₂ hr₂k hjc₁ hc₁l hjc₂ hc₂l
    hd₁ hd₂ hd₃ hd₄
  have hik := hir₁.trans_le hr₁k
  have hjl := hjc₁.trans_le hc₁l
  have hA' := acute_of_shorter (h.noncollinearU r₁ i j hir₁.ne.symm) hd₁
  have hA : ∠ (v j) (u i) (u k) < Real.pi / 2 := by
    rcases hr₁k.eq_or_lt with rfl | hr₁k
    · exact hA'
    · exact (angle_le_of_crossing (h.threeOne i r₁ k j hir₁ hr₁k)).trans_lt hA'
  have hB' := acute_of_shorter (h.noncollinearU r₂ k l hr₂k.ne) hd₃
  have hB : ∠ (u i) (u k) (v l) < Real.pi / 2 := by
    rw [angle_comm]
    rcases hir₂.eq_or_lt with rfl | hir₂
    · exact hB'
    · exact (angle_le_of_crossing (h.threeOne i r₂ k l hir₂ hr₂k).swapEnds).trans_lt hB'
  have hC' := acute_of_shorter (h.noncollinearV k c₂ l hc₂l.ne) (by
    simpa only [dist_comm] using hd₄)
  have hC : ∠ (u k) (v l) (v j) < Real.pi / 2 := by
    rcases hjc₂.eq_or_lt with rfl | hjc₂
    · exact hC'
    · exact (angle_le_of_crossing (h.oneThree k j c₂ l hjc₂ hc₂l).swapEnds).trans_lt hC'
  have hD' := acute_of_shorter (h.noncollinearV i c₁ j hjc₁.ne.symm) (by
    simpa only [dist_comm] using hd₂)
  have hD : ∠ (v l) (v j) (u i) < Real.pi / 2 := by
    rw [angle_comm]
    rcases hc₁l.eq_or_lt with rfl | hc₁l
    · exact hD'
    · exact (angle_le_of_crossing (h.oneThree i j c₁ l hjc₁ hc₁l)).trans_lt hD'
  have hab := ne₂₃_of_not_collinear (h.noncollinearU i k j hik.ne)
  have hcd := ne₂₃_of_not_collinear (h.noncollinearV i l j hjl.ne.symm)
  have hsum := angle_sum_of_crossing (h.twoTwo i k j l hik hjl)
    hab (h.distinct k l) hcd (h.distinct i j).symm
  linarith only [hA,hB,hC,hD,hsum]

end OrderedUnitCuts

/- Determinant tests for the radial ordering of the two sides of a convex cut. -/

open Set AffineMap

namespace OrderedUnitCuts.Radial

abbrev XY := ℝ × ℝ

def cross (a b : XY) : ℝ := a.1*b.2-a.2*b.1

def turn (a b c : XY) : ℝ := cross a b+cross b c+cross c a

theorem cross_swap (a b : XY) : cross b a = -cross a b := by
  unfold cross
  ring

theorem turn_cycle (a b c : XY) : turn a b c=turn b c a := by
  unfold turn
  ring

theorem turn_swap (a b c : XY) : turn a c b = -turn a b c := by
  unfold turn cross
  ring

/-- A vertex cannot be represented as a combination of other vertices and the radial origin. -/
def Extreme (S : Set XY) : Prop :=
  ∀ ⦃a b c : XY⦄, a ∈ S → b ∈ S → c ∈ S → a ≠ b → c ≠ b →
    ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → r+s ≤ 1 → b ≠ r • a+s • c

private theorem turn_neg_of_cross_pos {S : Set XY} (hS : Extreme S) {a b c : XY}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hcb : c ≠ b)
    (h₁ : cross a b ≤ 0) (h₂ : cross b c ≤ 0) (h₃ : 0 < cross c a) :
    turn a b c < 0 := by
  let r := -cross b c / cross c a
  let s := -cross a b / cross c a
  have hr := div_nonneg (neg_nonneg.mpr h₂) h₃.le
  have hs := div_nonneg (neg_nonneg.mpr h₁) h₃.le
  have heq : b=r • a+s • c := by
    apply Prod.ext
    · change b.1=(-cross b c/cross c a)*a.1+(-cross a b/cross c a)*c.1
      field_simp [h₃.ne']
      unfold cross
      ring
    · change b.2=(-cross b c/cross c a)*a.2+(-cross a b/cross c a)*c.2
      field_simp [h₃.ne']
      unfold cross
      ring
  by_contra! hnot
  have hsum : r+s ≤ 1 := by
    change -cross b c / cross c a + -cross a b / cross c a ≤ 1
    rw [← add_div, div_le_iff₀ h₃, one_mul]
    unfold turn at hnot
    linarith
  exact hS ha hb hc hab hcb r s hr hs hsum heq

/-- Of the three successive radial determinants, at most one may have the opposite sign. -/
theorem turn_neg {S : Set XY} (hS : Extreme S) {a b c : XY}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h₁ : cross a b < 0) (h₂ : cross b c ≤ 0 ∨ cross c a ≤ 0) :
    turn a b c < 0 := by
  rcases h₂ with hn | hn
  · by_cases hca : 0 < cross c a
    · exact turn_neg_of_cross_pos hS ha hb hc hab hbc.symm h₁.le hn hca
    · unfold turn
      linarith
  · by_cases hbc' : 0 < cross b c
    · rw [← turn_cycle c a b]
      exact turn_neg_of_cross_pos hS hc ha hb hac.symm hab.symm hn h₁.le hbc'
    · unfold turn
      linarith

noncomputable def slope (a : XY) : ℝ := a.2/|a.1|

private theorem cross_left_left {a b : XY} (ha : a.1 < 0) (hb : b.1 < 0) :
    cross a b = (-a.1)*(-b.1)*(slope a-slope b) := by
  simp only [slope, abs_of_neg ha, abs_of_neg hb, cross]
  field_simp [ha.ne,hb.ne]
  ring

private theorem cross_left_right {a b : XY} (ha : a.1 < 0) (hb : 0 < b.1) :
    cross b a = (-a.1)*b.1*(slope a+slope b) := by
  simp only [slope, abs_of_neg ha, abs_of_pos hb, cross]
  field_simp [ha.ne,hb.ne']
  ring

theorem turn_left_three {S : Set XY} (hS : Extreme S) {a b c : XY}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hax : a.1 < 0) (hbx : b.1 < 0) (hcx : c.1 < 0)
    (hab : slope a < slope b) (hbc : slope b < slope c) :
    turn a b c < 0 := by
  apply turn_neg hS ha hb hc (ne_of_apply_ne slope hab.ne) (ne_of_apply_ne slope hbc.ne)
    (ne_of_apply_ne slope (hab.trans hbc).ne)
  · rw [cross_left_left hax hbx]
    exact mul_neg_of_pos_of_neg (mul_pos (neg_pos.mpr hax) (neg_pos.mpr hbx)) (sub_neg.mpr hab)
  · left
    rw [cross_left_left hbx hcx]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (neg_nonneg.mpr hbx.le)
      (neg_nonneg.mpr hcx.le)) (sub_nonpos.mpr hbc.le)

theorem turn_left_two {S : Set XY} (hS : Extreme S) {a b c : XY}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hax : a.1 < 0) (hbx : b.1 < 0) (hcx : 0 < c.1) (hab : slope a < slope b) :
    turn a b c < 0 := by
  have hba : b ≠ c := fun h => by subst c; linarith
  have hca : a ≠ c := fun h => by subst c; linarith
  apply turn_neg hS ha hb hc (ne_of_apply_ne slope hab.ne) hba hca
  · rw [cross_left_left hax hbx]
    exact mul_neg_of_pos_of_neg (mul_pos (neg_pos.mpr hax) (neg_pos.mpr hbx)) (sub_neg.mpr hab)
  by_cases hs : 0 ≤ slope b+slope c
  · left
    rw [cross_swap c b, cross_left_right hbx hcx]
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (neg_nonneg.mpr hbx.le) hcx.le) hs)
  · right
    rw [cross_left_right hax hcx]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (neg_nonneg.mpr hax.le) hcx.le) (by linarith)

def reflect (a : XY) : XY := (-a.1,a.2)

theorem reflect_slope (a : XY) : slope (reflect a)=slope a := by
  simp [slope, reflect]

theorem reflect_turn (a b c : XY) : turn (reflect a) (reflect b) (reflect c) = -turn a b c := by
  dsimp [turn, cross, reflect]
  ring

theorem reflect_extreme {S : Set XY} (hS : Extreme S) : Extreme (reflect '' S) := by
  rintro _ _ _ ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩ ⟨c,hc,rfl⟩ hab hcb r s hr hs hrs he
  have hab' (p q : XY) (h : reflect p ≠ reflect q) : p ≠ q := fun he' => h (congrArg reflect he')
  refine hS ha hb hc (hab' a b hab) (hab' c b hcb) r s hr hs hrs ?_
  apply Prod.ext
  · have hx := congrArg Prod.fst he
    change -b.1=r*(-a.1)+s*(-c.1) at hx
    change b.1=r*a.1+s*c.1
    linarith
  · have hy := congrArg Prod.snd he
    exact hy

theorem turn_right_three {S : Set XY} (hS : Extreme S) {a b c : XY}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hax : 0 < a.1) (hbx : 0 < b.1) (hcx : 0 < c.1)
    (hab : slope a < slope b) (hbc : slope b < slope c) :
    0 < turn a b c := by
  have h := turn_left_three (reflect_extreme hS) (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
    (mem_image_of_mem _ hc) (show (reflect a).1 < 0 from neg_neg_of_pos hax)
    (show (reflect b).1 < 0 from neg_neg_of_pos hbx) (show (reflect c).1 < 0 from neg_neg_of_pos hcx)
    (by simpa only [reflect_slope] using hab) (by simpa only [reflect_slope] using hbc)
  rwa [reflect_turn, neg_lt_zero] at h

theorem turn_right_two {S : Set XY} (hS : Extreme S) {a b c : XY}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hax : 0 < a.1) (hbx : 0 < b.1) (hcx : c.1 < 0) (hab : slope a < slope b) :
    0 < turn a b c := by
  have h := turn_left_two (reflect_extreme hS) (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
    (mem_image_of_mem _ hc) (show (reflect a).1 < 0 from neg_neg_of_pos hax)
    (show (reflect b).1 < 0 from neg_neg_of_pos hbx) (show 0 < (reflect c).1 from neg_pos.mpr hcx)
    (by simpa only [reflect_slope] using hab)
  rwa [reflect_turn, neg_lt_zero] at h

private theorem frac_mem {u v : ℝ} (h : u*v<0) : u/(u-v) ∈ Ioo (0 : ℝ) 1 := by
  rcases mul_neg_iff.mp h with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · have hd : 0 < u-v := by linarith
    exact ⟨div_pos hu hd,(div_lt_one hd).mpr (by linarith)⟩
  · have hd : u-v < 0 := by linarith
    refine ⟨div_pos_of_neg_of_neg hu hd,?_⟩
    rw [div_lt_iff_of_neg hd, one_mul]
    linarith

/-- Opposite strict determinant signs give a common point in the open diagonals. -/
theorem crossing_parameters {a b c d : XY}
    (h₁ : turn a c b*turn a c d < 0) (h₂ : turn b d a*turn b d c < 0) :
    ∃ r ∈ Ioo (0 : ℝ) 1, ∃ s ∈ Ioo (0 : ℝ) 1,
      lineMap a c r = lineMap b d s := by
  let p := turn b d a
  let q := turn b d c
  let x := turn a c b
  let y := turn a c d
  have hr : p/(p-q) ∈ Ioo (0 : ℝ) 1 := frac_mem h₂
  have hs : x/(x-y) ∈ Ioo (0 : ℝ) 1 := frac_mem h₁
  have hp : p-q ≠ 0 := by
    intro he
    have he' : p=q := sub_eq_zero.mp he
    change p*q<0 at h₂
    rw [← he'] at h₂
    nlinarith
  have hx : x-y ≠ 0 := by
    intro he
    have he' : x=y := sub_eq_zero.mp he
    change x*y<0 at h₁
    rw [← he'] at h₁
    nlinarith
  refine ⟨p/(p-q),hr,x/(x-y),hs,?_⟩
  apply Prod.ext
  · rw [lineMap_apply_module', lineMap_apply_module']
    change (p/(p-q))*(c.1-a.1)+a.1=(x/(x-y))*(d.1-b.1)+b.1
    field_simp [hp,hx]
    unfold p q x y turn cross
    ring
  · rw [lineMap_apply_module', lineMap_apply_module']
    change (p/(p-q))*(c.2-a.2)+a.2=(x/(x-y))*(d.2-b.2)+b.2
    field_simp [hp,hx]
    unfold p q x y turn cross
    ring

/-- Four successive negative turns imply intersecting diagonals. -/
theorem crossing_of_turns_neg {a b c d : XY} (h₁ : turn a b c < 0)
    (h₂ : turn b c d < 0) (h₃ : turn c d a < 0) (h₄ : turn d a b < 0) :
    ∃ r ∈ Ioo (0 : ℝ) 1, ∃ s ∈ Ioo (0 : ℝ) 1,
      lineMap a c r = lineMap b d s := by
  apply crossing_parameters
  · rw [turn_swap a b c, turn_cycle a c d]
    exact mul_neg_of_pos_of_neg (neg_pos.mpr h₁) h₃
  · rw [turn_swap b c d, turn_cycle b d a]
    exact mul_neg_of_neg_of_pos h₄ (neg_pos.mpr h₂)

/-- Four successive positive turns imply intersecting diagonals. -/
theorem crossing_of_turns_pos {a b c d : XY} (h₁ : 0 < turn a b c)
    (h₂ : 0 < turn b c d) (h₃ : 0 < turn c d a) (h₄ : 0 < turn d a b) :
    ∃ r ∈ Ioo (0 : ℝ) 1, ∃ s ∈ Ioo (0 : ℝ) 1,
      lineMap a c r = lineMap b d s := by
  apply crossing_parameters
  · rw [turn_swap a b c, turn_cycle a c d]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos h₁) h₃
  · rw [turn_swap b c d, turn_cycle b d a]
    exact mul_neg_of_pos_of_neg h₄ (neg_neg_of_pos h₂)

end OrderedUnitCuts.Radial

open Set AffineMap EuclideanGeometry

namespace OrderedUnitCuts.Radial

abbrev Plane := EuclideanSpace ℝ (Fin 2)

private noncomputable def coords : Plane ≃ₗ[ℝ] XY :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv.trans
    (LinearEquiv.piFinTwo ℝ (fun _ => ℝ))

private theorem lift_separator (f : Plane →L[ℝ] ℝ) (hf : f ≠ 0) :
    ∃ e : Plane →ₗ[ℝ] XY, Function.Injective e ∧ ∀ x, (e x).1=f x := by
  let g : XY →ₗ[ℝ] ℝ := f.toLinearMap.comp coords.symm.toLinearMap
  let p := g (1,0)
  let q := g (0,1)
  have hg (x : Plane) : f x=(coords x).1*p+(coords x).2*q := by
    have he : coords x=(coords x).1 • ((1,0) : XY)+(coords x).2 • ((0,1) : XY) := by
      apply Prod.ext <;> simp
    have hh := congrArg g he
    change g (coords x) = g ((coords x).1 • ((1,0) : XY)+(coords x).2 • ((0,1) : XY)) at hh
    rw [map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul] at hh
    simpa [g,p,q] using hh
  by_cases hp : p=0
  · have hq : q ≠ 0 := by
      intro hq
      apply hf
      apply ContinuousLinearMap.ext
      intro x
      change f x=0
      simp [hg x,hp,hq]
    let e := f.toLinearMap.prod ((LinearMap.fst ℝ ℝ ℝ).comp coords.toLinearMap)
    refine ⟨e,?_,fun _ => rfl⟩
    intro x y he
    have hF := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    change f x=f y at hF
    change (coords x).1=(coords y).1 at h2
    rw [hg x,hg y,hp,mul_zero,mul_zero,zero_add,zero_add] at hF
    exact coords.injective (Prod.ext h2 (mul_right_cancel₀ hq hF))
  · let e := f.toLinearMap.prod ((LinearMap.snd ℝ ℝ ℝ).comp coords.toLinearMap)
    refine ⟨e,?_,fun _ => rfl⟩
    intro x y he
    have hF := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    change f x=f y at hF
    change (coords x).2=(coords y).2 at h2
    rw [hg x,hg y,h2] at hF
    exact coords.injective (Prod.ext (mul_right_cancel₀ hp (add_right_cancel hF)) h2)

private theorem image_extreme {V : Finset Plane} (hV : ConvexIndep (V : Set Plane))
    {o : Plane} (ho : o ∈ convexHull ℝ (V : Set Plane)) (e : Plane →ₗ[ℝ] XY)
    (he : Function.Injective e) (hn : ∀ x ∈ V, x≠o) :
    Extreme ((fun x => e (x-o)) '' (V : Set Plane)) := by
  classical
  rintro _ _ _ ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩ ⟨c,hc,rfl⟩ hab hcb r s hr hs hrs hEq
  have hnab : a≠b := fun h => hab (h ▸ rfl)
  have hncb : c≠b := fun h => hcb (h ▸ rfl)
  let T : Set Plane := (V : Set Plane) \ {b}
  have htc : IsClosed (convexHull ℝ T) :=
    (V.finite_toSet.sdiff (t := {b})).isClosed_convexHull ℝ
  obtain ⟨g,k,hkg,hgb⟩ := geometric_hahn_banach_closed_point (convex_convexHull _ _) htc (hV b hb)
  have hGa : g a < g b := (hkg a (subset_convexHull ℝ T ⟨ha,hnab⟩)).trans hgb
  have hGc : g c < g b := (hkg c (subset_convexHull ℝ T ⟨hc,hncb⟩)).trans hgb
  have hGo : g o ≤ g b := by
    let H : Set Plane := {p | g p ≤ g b}
    have hH : Convex ℝ H := by
      intro x hx y hy t u ht hu htu
      change g x≤g b at hx
      change g y≤g b at hy
      change g (t • x+u • y) ≤ g b
      rw [map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
      have h₁ := mul_le_mul_of_nonneg_left hx ht
      have h₂ := mul_le_mul_of_nonneg_left hy hu
      have hEq : t*g b+u*g b=g b := by rw [← add_mul, htu, one_mul]
      linarith
    apply (convexHull_min (t := H) ?_ hH) ho
    intro x hx
    change g x ≤ g b
    rcases eq_or_ne x b with rfl | hne
    · rfl
    · exact ((hkg x (subset_convexHull ℝ T ⟨hx,hne⟩)).trans hgb).le
  have hRep : b-o = r • (a-o)+s • (c-o) := he <| by
    rw [map_add,map_smul,map_smul]
    exact hEq
  have hh := congrArg g hRep
  rw [map_sub, map_add, map_smul, map_smul, map_sub, map_sub, smul_eq_mul, smul_eq_mul] at hh
  have hrs' : 0 < r+s := by
    by_contra! hsum
    have hr0 : r=0 := by linarith
    have hs0 : s=0 := by linarith
    rw [hr0,hs0,zero_smul,zero_smul,add_zero] at hRep
    exact hn b hb (sub_eq_zero.mp hRep)
  have hstrict : 0 < r*(g b-g a)+s*(g b-g c) := by
    by_cases hl : 0<r
    · exact add_pos_of_pos_of_nonneg (mul_pos hl (sub_pos.mpr hGa))
        (mul_nonneg hs (sub_nonneg.mpr hGc.le))
    · have hk : 0<s := by linarith
      exact add_pos_of_nonneg_of_pos (mul_nonneg hr (sub_nonneg.mpr hGa.le))
        (mul_pos hk (sub_pos.mpr hGc))
  have hu : (r+s)*(g b-g o) ≤ g b-g o := by
    simpa using mul_le_mul_of_nonneg_right hrs (sub_nonneg.mpr hGo)
  nlinarith

/-- Separator coordinates centered at a point of the combined hull. -/
theorem separator_chart {V A B : Finset Plane} (hV : ConvexIndep (V : Set Plane))
    (hA : A.Nonempty) (hB : B.Nonempty) (hCut : Erdos97.IsCut V A B) :
    ∃ (o : Plane) (e : Plane →ₗ[ℝ] XY), Function.Injective e ∧
      (∀ x ∈ A, (e (x-o)).1 < 0) ∧ (∀ x ∈ B, 0 < (e (x-o)).1) ∧
      Extreme ((fun x => e (x-o)) '' (V : Set Plane)) := by
  classical
  rcases hCut with ⟨hUnion,_,hDisj⟩
  obtain ⟨f,u,v,hL,huv,hR⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull _ _) (A.finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull _ _) (B.finite_toSet.isClosed_convexHull ℝ) hDisj
  let k := (u+v)/2
  have hA' (a : Plane) (ha : a ∈ A) : f a < k :=
    (hL a (subset_convexHull ℝ _ ha)).trans (by dsimp [k]; linarith)
  have hB' (b : Plane) (hb : b ∈ B) : k < f b :=
    (show k < v by dsimp [k]; linarith).trans (hR b (subset_convexHull ℝ _ hb))
  obtain ⟨a,ha⟩ := hA
  obtain ⟨b,hb⟩ := hB
  have haF := hA' a ha
  have hbF := hB' b hb
  have hf : f ≠ 0 := by
    intro he
    have hh := haF.trans hbF
    simp [he] at hh
  obtain ⟨e,he,heF⟩ := lift_separator f hf
  let θ := (k-f a)/(f b-f a)
  have hdp : 0 < f b-f a := sub_pos.mpr (haF.trans hbF)
  have hθ₀ : 0 < θ := div_pos (sub_pos.mpr haF) hdp
  have hθ₁ : θ < 1 := (div_lt_one hdp).mpr (by linarith)
  let o := lineMap a b θ
  have hfo : f o=k := by
    rw [show o=lineMap a b θ by rfl, lineMap_apply_module',map_add,map_smul, map_sub,smul_eq_mul]
    dsimp [θ]
    field_simp [hdp.ne']
    ring
  have hAV : A ⊆ V := hUnion ▸ Finset.subset_union_left
  have hBV : B ⊆ V := hUnion ▸ Finset.subset_union_right
  have ho : o ∈ convexHull ℝ (V : Set Plane) := by
    rw [show o=lineMap a b θ by rfl, lineMap_apply_module]
    exact convex_convexHull ℝ _ (subset_convexHull ℝ _ (hAV ha)) (subset_convexHull ℝ _ (hBV hb))
      (sub_nonneg.mpr hθ₁.le) hθ₀.le (by ring)
  refine ⟨o,e,he,?_,?_,image_extreme hV ho e he ?_⟩
  · intro x h
    rw [heF,map_sub,hfo]
    exact sub_neg.mpr (hA' x h)
  · intro x h
    rw [heF,map_sub,hfo]
    exact sub_pos.mpr (hB' x h)
  · intro x hx h
    have hx' : x ∈ A ∨ x ∈ B := Finset.mem_union.mp (hUnion.symm ▸ hx)
    rcases hx' with hxa | hxb
    · exact (hA' x hxa).ne ((congrArg f h).trans hfo)
    · exact (hB' x hxb).ne' ((congrArg f h).trans hfo)

end OrderedUnitCuts.Radial

open Set AffineMap EuclideanGeometry

namespace OrderedUnitCuts.Radial

private theorem slope_eq {S : Set XY} (hS : Extreme S) {a b : XY}
    (ha : a ∈ S) (hb : b ∈ S)
    (hx : (a.1 < 0 ∧ b.1 < 0) ∨ (0 < a.1 ∧ 0 < b.1))
    (hs : slope a=slope b) : a=b := by
  by_contra! hne
  have ha0 : a.1≠0 := hx.elim (fun h => h.1.ne) (fun h => h.1.ne')
  have hb0 : b.1≠0 := hx.elim (fun h => h.2.ne) (fun h => h.2.ne')
  let t := |a.1|/|b.1|
  have ht : 0<t := div_pos (abs_pos.mpr ha0) (abs_pos.mpr hb0)
  have he : a=t • b := by
    apply Prod.ext
    · change a.1=(|a.1|/|b.1|)*b.1
      rcases hx with ⟨hax,hbx⟩ | ⟨hax,hbx⟩
      · rw [abs_of_neg hax, abs_of_neg hbx, neg_div_neg_eq, div_mul_cancel₀ _ hb0]
      · rw [abs_of_pos hax, abs_of_pos hbx, div_mul_cancel₀ _ hb0]
    · have hmul : a.2*|b.1|=b.2*|a.1| := (div_eq_div_iff
        (abs_ne_zero.mpr ha0) (abs_ne_zero.mpr hb0)).mp hs
      change a.2=(|a.1|/|b.1|)*b.2
      rw [div_mul_eq_mul_div, eq_div_iff (abs_ne_zero.mpr hb0),mul_comm |a.1| b.2]
      exact hmul
  by_cases hle : t≤1
  · apply hS hb ha hb hne.symm hne.symm t 0 ht.le le_rfl (by rwa [add_zero])
    simpa using he
  · have hInv : b=t⁻¹ • a := by rw [he,smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
    have hInvLe : t⁻¹≤1 := (inv_lt_one_of_one_lt₀ (lt_of_not_ge hle)).le
    apply hS ha hb ha hne hne t⁻¹ 0 (inv_nonneg.mpr ht.le) le_rfl (by rwa [add_zero])
    simpa using hInv

private theorem sorted_embedding {X : Type*} (A : Finset X) (key : X → ℝ)
    (hKey : InjOn key (A : Set X)) :
    ∃ u : Fin A.card ↪ X, Set.range u=(A : Set X) ∧ StrictMono (key ∘ u) := by
  classical
  let B := A.image key
  have hcard : B.card=A.card := Finset.card_image_of_injOn hKey
  let o : Fin A.card ↪o ℝ := B.orderEmbOfFin hcard
  have hpoint (i : Fin A.card) : ∃ p∈A, key p=o i :=
    Finset.mem_image.mp (B.orderEmbOfFin_mem hcard i)
  choose u hu huKey using hpoint
  have hm : StrictMono (key ∘ u) := by
    intro i j hij
    change key (u i)<key (u j)
    rw [huKey,huKey]
    exact o.strictMono hij
  refine ⟨⟨u,fun _ _ he => hm.injective (congrArg key he)⟩,?_,hm⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨i,rfl⟩
    exact hu i
  · intro p hp
    have hpKey : key p ∈ Set.range o := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_image_of_mem key hp
    obtain ⟨i,hi⟩ := hpKey
    exact ⟨i,hKey (hu i) hp ((huKey i).trans hi)⟩

private theorem chart_injective (e : Plane →ₗ[ℝ] XY) (he : Function.Injective e) (o : Plane) :
    Function.Injective (fun x => e (x-o)) := by
  intro a b h
  simpa using congrArg (fun t => t+o) (he h)

private theorem turn_eq_zero_of_collinear (e : Plane →ₗ[ℝ] XY) (o : Plane)
    {S : Set Plane} (h : Collinear ℝ S) {a b c : Plane} (ha : a∈S) (hb : b∈S) (hc : c∈S) :
    turn (e (a-o)) (e (b-o)) (e (c-o))=0 := by
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem ha).mp h
  obtain ⟨r,hr⟩ := hv b hb
  obtain ⟨s,hs⟩ := hv c hc
  change b=r • v+a at hr
  change c=s • v+a at hs
  have hB : e (b-o)=r • e v+e (a-o) := by rw [hr,add_sub_assoc,map_add,map_smul]
  have hC : e (c-o)=s • e v+e (a-o) := by rw [hs,add_sub_assoc,map_add,map_smul]
  rw [hB,hC]
  let z := e (a-o)
  let w := e v
  change z.1*(r*w.2+z.2)-z.2*(r*w.1+z.1) +
    ((r*w.1+z.1)*(s*w.2+z.2)-(r*w.2+z.2)*(s*w.1+z.1)) +
    ((s*w.1+z.1)*z.2-(s*w.2+z.2)*z.1)=0
  ring

private theorem meet_of_parameters (e : Plane →ₗ[ℝ] XY) (he : Function.Injective e) (o : Plane)
    {a b c d : Plane} (hac : a≠c) (hbd : b≠d)
    (h : ∃ r ∈ Ioo (0 : ℝ) 1, ∃ s ∈ Ioo (0 : ℝ) 1,
      lineMap (e (a-o)) (e (c-o)) r = lineMap (e (b-o)) (e (d-o)) s) :
    DiagonalsMeet a b c d := by
  obtain ⟨r,hr,s,hs,h⟩ := h
  have hmap (p q : Plane) (t : ℝ) :
      e (lineMap p q t-o)=lineMap (e (p-o)) (e (q-o)) t := by
    rw [lineMap_apply_module',lineMap_apply_module',add_sub_assoc,map_add,map_smul,← map_sub]
    have hh : (q-o)-(p-o)=q-p := by abel
    rw [hh]
  rw [← hmap,← hmap] at h
  have hp := chart_injective e he o h
  exact ⟨lineMap a c r, sbtw_iff_mem_image_Ioo_and_ne.mpr ⟨⟨r,hr,rfl⟩,hac⟩,
    sbtw_iff_mem_image_Ioo_and_ne.mpr ⟨⟨s,hs,hp.symm⟩,hbd⟩⟩

private theorem turn_swap_first (a b c : XY) : turn b a c = -turn a b c := by
  rw [turn_cycle b a c,turn_swap]

end OrderedUnitCuts.Radial

namespace OrderedUnitCuts

open Radial

/-- A convex cut admits opposite boundary orders with the required strict intersections. -/
theorem exists_crossOrdered {V A B : Finset Plane} (hV : ConvexIndep (V : Set Plane))
    (hA : A.Nonempty) (hB : B.Nonempty) (hCut : Erdos97.IsCut V A B) :
    ∃ (u : Fin A.card ↪ Plane) (v : Fin B.card ↪ Plane),
      Set.range u=(A : Set Plane) ∧ Set.range v=(B : Set Plane) ∧ CrossOrdered u v := by
  classical
  obtain ⟨o,e,he,hA0,hB0,hS⟩ := separator_chart hV hA hB hCut
  let Φ (x : Plane) := e (x-o)
  let S := Φ '' (V : Set Plane)
  have hAV : A ⊆ V := hCut.1 ▸ Finset.subset_union_left
  have hBV : B ⊆ V := hCut.1 ▸ Finset.subset_union_right
  have hAM {x : Plane} (hx : x∈A) : Φ x∈S := mem_image_of_mem Φ (hAV hx)
  have hBM {x : Plane} (hx : x∈B) : Φ x∈S := mem_image_of_mem Φ (hBV hx)
  have hKeyA : InjOn (slope ∘ Φ) (A : Set Plane) := by
    intro a ha b hb h
    exact chart_injective e he o (slope_eq hS (hAM ha) (hAM hb) (Or.inl ⟨hA0 a ha,hA0 b hb⟩) h)
  have hKeyB : InjOn (slope ∘ Φ) (B : Set Plane) := by
    intro a ha b hb h
    exact chart_injective e he o (slope_eq hS (hBM ha) (hBM hb) (Or.inr ⟨hB0 a ha,hB0 b hb⟩) h)
  obtain ⟨u,hur,hum⟩ := sorted_embedding A (slope ∘ Φ) hKeyA
  obtain ⟨v,hvr,hvm⟩ := sorted_embedding B (slope ∘ Φ) hKeyB
  let a (i : Fin A.card) := Φ (u i)
  let b (j : Fin B.card) := Φ (v j)
  have hu (i : Fin A.card) : u i ∈ A := by
    change u i ∈ (A : Set Plane)
    rw [← hur]
    exact Set.mem_range_self i
  have hv (j : Fin B.card) : v j ∈ B := by
    change v j ∈ (B : Set Plane)
    rw [← hvr]
    exact Set.mem_range_self j
  have disj (i : Fin A.card) (j : Fin B.card) : u i ≠ v j := by
    intro h
    exact (Finset.disjoint_left.mp hCut.2.1) (hu i) (h.symm ▸ hv j)
  have left₂ {i k : Fin A.card} (h : i<k) (j : Fin B.card) : turn (a i) (a k) (b j)<0 :=
    turn_left_two hS (hAM (hu i)) (hAM (hu k)) (hBM (hv j))
      (hA0 _ (hu i)) (hA0 _ (hu k)) (hB0 _ (hv j)) (hum h)
  have right₂ {j l : Fin B.card} (h : j<l) (i : Fin A.card) : 0<turn (b j) (b l) (a i) :=
    turn_right_two hS (hBM (hv j)) (hBM (hv l)) (hAM (hu i))
      (hB0 _ (hv j)) (hB0 _ (hv l)) (hA0 _ (hu i)) (hvm h)
  have left₃ {i r k : Fin A.card} (hir : i<r) (hrk : r<k) : turn (a i) (a r) (a k)<0 :=
    turn_left_three hS (hAM (hu i)) (hAM (hu r)) (hAM (hu k))
      (hA0 _ (hu i)) (hA0 _ (hu r)) (hA0 _ (hu k)) (hum hir) (hum hrk)
  have right₃ {j r l : Fin B.card} (hjr : j<r) (hrl : r<l) : 0<turn (b j) (b r) (b l) :=
    turn_right_three hS (hBM (hv j)) (hBM (hv r)) (hBM (hv l))
      (hB0 _ (hv j)) (hB0 _ (hv r)) (hB0 _ (hv l)) (hvm hjr) (hvm hrl)
  refine ⟨u,v,hur,hvr,⟨disj,?_,?_,?_,?_,?_⟩⟩
  · intro i k j hik hC
    rcases lt_or_gt_of_ne hik with h | h
    · have h0 : turn (a i) (a k) (b j)=0 :=
        turn_eq_zero_of_collinear e o hC (by simp) (by simp) (by simp)
      exact (left₂ h j).ne h0
    · have h0 : turn (a k) (a i) (b j)=0 :=
        turn_eq_zero_of_collinear e o hC (by simp) (by simp) (by simp)
      exact (left₂ h j).ne h0
  · intro i j l hjl hC
    rcases lt_or_gt_of_ne hjl with h | h
    · have h0 : turn (b j) (b l) (a i)=0 :=
        turn_eq_zero_of_collinear e o hC (by simp) (by simp) (by simp)
      exact (right₂ h i).ne' h0
    · have h0 : turn (b l) (b j) (a i)=0 :=
        turn_eq_zero_of_collinear e o hC (by simp) (by simp) (by simp)
      exact (right₂ h i).ne' h0
  · intro i k j l hik hjl
    apply meet_of_parameters e he o (disj i l) (disj k j)
    apply crossing_of_turns_neg
    · exact left₂ hik l
    · change turn (a k) (b l) (b j)<0
      rw [turn_swap (a k) (b j) (b l),neg_lt_zero,turn_cycle (a k) (b j) (b l)]
      exact right₂ hjl k
    · change turn (b l) (b j) (a i)<0
      rw [turn_swap_first (b j) (b l) (a i),neg_lt_zero]
      exact right₂ hjl i
    · change turn (b j) (a i) (a k)<0
      rw [turn_cycle (b j) (a i) (a k)]
      exact left₂ hik j
  · intro i r k j hir hrk
    apply meet_of_parameters e he o (u.injective.ne (hir.trans hrk).ne) (disj r j)
    apply crossing_of_turns_neg
    · exact left₃ hir hrk
    · exact left₂ hrk j
    · change turn (a k) (b j) (a i)<0
      rw [← turn_cycle (a i) (a k) (b j)]
      exact left₂ (hir.trans hrk) j
    · change turn (b j) (a i) (a r)<0
      rw [turn_cycle (b j) (a i) (a r)]
      exact left₂ hir j
  · intro i j r l hjr hrl
    apply meet_of_parameters e he o (v.injective.ne (hjr.trans hrl).ne) (disj i r).symm
    apply crossing_of_turns_pos
    · exact right₃ hjr hrl
    · exact right₂ hrl i
    · change 0<turn (b l) (a i) (b j)
      rw [← turn_cycle (b j) (b l) (a i)]
      exact right₂ (hjr.trans hrl) i
    · change 0<turn (a i) (b j) (b r)
      rw [turn_cycle (a i) (b j) (b r)]
      exact right₂ hjr i

end OrderedUnitCuts
end

namespace OrderedUnitCuts

open Finset

private theorem no_two_common {a b : ℕ} {d : Fin a → Fin b → ℝ}
    (hm : StrictMonge d) {x y : Fin a} {j l : Fin b} (hxy : x ≠ y) (hjl : j ≠ l)
    (hxj : d x j = 1) (hxl : d x l = 1) (hyj : d y j = 1) (hyl : d y l = 1) : False := by
  rcases lt_or_gt_of_ne hxy with hxy | hyx <;> rcases lt_or_gt_of_ne hjl with hjl | hlj
  · exact no_unit_rectangle hm hxy hjl hxj hxl hyj hyl
  · exact no_unit_rectangle hm hxy hlj hxl hxj hyl hyj
  · exact no_unit_rectangle hm hyx hjl hyj hyl hxj hxl
  · exact no_unit_rectangle hm hyx hlj hyl hyj hxl hxj

private theorem pair_pool_card {a b : ℕ} {d : Fin a → Fin b → ℝ} (hm : StrictMonge d)
    (S : Fin b → Finset (Fin a)) (hc : ∀ j, (S j).card = 3)
    (hS : ∀ j i, i ∈ S j → d i j = 1) :
    (univ.biUnion (fun j => (S j).powersetCard 2)).card = 3 * b := by
  classical
  rw [card_biUnion]
  · simp [card_powersetCard, hc, Nat.mul_comm]
  · intro j hj l hl hjl
    apply disjoint_left.2
    intro p hp hq
    obtain ⟨hpj, hcard⟩ := mem_powersetCard.1 hp
    have hpl := (mem_powersetCard.1 hq).1
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 hcard
    have hmx : x ∈ ({x, y} : Finset (Fin a)) := by simp
    have hmy : y ∈ ({x, y} : Finset (Fin a)) := by simp
    exact no_two_common hm hxy hjl (hS j x (hpj hmx)) (hS l x (hpl hmx))
      (hS j y (hpj hmy)) (hS l y (hpl hmy))

theorem column_pair_bound {a b : ℕ} {d : Fin a → Fin b → ℝ} (hm : StrictMonge d)
    (hdeg : ∀ j, 3 ≤ (univ.filter (fun i => d i j = 1)).card) :
    3*b ≤ a.choose 2 := by
  classical
  choose S hsub hc using fun j => exists_subset_card_eq (hdeg j)
  have hs (j i) (hi : i ∈ S j) : d i j = 1 := (mem_filter.1 (hsub j hi)).2
  calc
    3 * b = (univ.biUnion fun j => (S j).powersetCard 2).card :=
      (pair_pool_card hm S hc hs).symm
    _ ≤ ((univ : Finset (Fin a)).powersetCard 2).card := by
      apply card_le_card
      intro p hp
      obtain ⟨j, _, hj⟩ := mem_biUnion.1 hp
      exact mem_powersetCard.2 ⟨subset_univ _, (mem_powersetCard.1 hj).2⟩
    _ = a.choose 2 := by simp [card_powersetCard]

theorem intersection_pair_order {a b : ℕ} {d : Fin a → Fin b → ℝ}
    (hm : StrictMonge d) (hn : NoAcuteCorners d) {c e f : Fin b} {x y z : Fin a}
    (hce : c < e)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxc : d x c = 1) (hxf : d x f = 1) (hye : d y e = 1) (hyf : d y f = 1)
    (hzc : d z c = 1) (hze : d z e = 1) : y < x := by
  have hfc : f ≠ c := by
    rintro rfl
    exact no_two_common hm hyz hce.ne hyf hye hzc hze
  have hfe : f ≠ e := by
    rintro rfl
    exact no_two_common hm hxz hce.ne hxc hxf hzc hze
  have hcases : f < c ∨ (c < f ∧ f < e) ∨ e < f := by omega
  rcases hcases with h | ⟨h₁, h₂⟩ | h
  · exact (six_cycle_order hm hn hxy hyz hxz h hce hxf hxc hyf hye hzc hze).2
  · exact (six_cycle_order hm hn hxz hyz.symm hxy h₁ h₂ hxc hxf hzc hze hyf hye).1.trans
      (six_cycle_order hm hn hxz hyz.symm hxy h₁ h₂ hxc hxf hzc hze hyf hye).2
  · exact (six_cycle_order hm hn hxz.symm hxy hyz.symm hce h hzc hze hxc hxf hye hyf).1

theorem no_seven_columns {d : Fin 7 → Fin 7 → ℝ} (hm : StrictMonge d)
    (hn : NoAcuteCorners d) (hdeg : ∀ j, 3 ≤ (univ.filter (fun i => d i j = 1)).card) : False := by
  classical
  choose S hsub hc using fun j => exists_subset_card_eq (hdeg j)
  have hs (j i) (hi : i ∈ S j) : d i j = 1 := (mem_filter.1 (hsub j hi)).2
  have hcoverage :
      univ.biUnion (fun j => (S j).powersetCard 2) = (univ : Finset (Fin 7)).powersetCard 2 := by
    apply eq_of_subset_of_card_le
    · intro p hp
      obtain ⟨j, _, hj⟩ := mem_biUnion.1 hp
      exact mem_powersetCard.2 ⟨subset_univ _, (mem_powersetCard.1 hj).2⟩
    · rw [pair_pool_card hm S hc hs, card_powersetCard, card_univ, Fintype.card_fin]
      decide
  have hcover (x y : Fin 7) (hxy : x ≠ y) : ∃ j, x ∈ S j ∧ y ∈ S j := by
    have hpair : ({x, y} : Finset (Fin 7)) ∈ (univ : Finset (Fin 7)).powersetCard 2 :=
      mem_powersetCard.2 ⟨subset_univ _, by simp [hxy]⟩
    rw [← hcoverage] at hpair
    obtain ⟨j, _, hj⟩ := mem_biUnion.1 hpair
    have hh := (mem_powersetCard.1 hj).1
    exact ⟨j, hh (by simp), hh (by simp)⟩
  have hnoskip (j : Fin 7) (x y z r : Fin 7) (hx : x ∈ S j) (hy : y ∈ S j) (hz : z ∈ S j)
      (hxr : x < r) (hry : r < y) (hxz : x ≠ z) (hyz : y ≠ z) (hrz : r ≠ z)
      (hr : r ∉ S j) : False := by
    obtain ⟨k, hrk, hzk⟩ := hcover r z hrz
    have hjk : j ≠ k := by rintro rfl; exact hr hrk
    rcases lt_or_gt_of_ne hjk with hjk | hkj
    · obtain ⟨l, hxl, hrl⟩ := hcover x r hxr.ne
      exact hxr.not_gt (intersection_pair_order hm hn hjk hxr.ne hxz hrz (hs j x hx)
        (hs l x hxl) (hs k r hrk) (hs l r hrl) (hs j z hz) (hs k z hzk))
    · obtain ⟨l, hyl, hrl⟩ := hcover y r hry.ne.symm
      exact hry.not_gt (intersection_pair_order hm hn hkj hry.ne hrz hyz (hs k r hrk)
        (hs l r hrl) (hs j y hy) (hs l y hyl) (hs k z hzk) (hs j z hz))
  obtain ⟨j, hzero, hsix⟩ := hcover 0 6 (by decide)
  have hpair := insert_subset hzero (singleton_subset_iff.mpr hsix)
  obtain ⟨r, hr, hrne⟩ := exists_mem_notMem_of_card_lt_card (s := ({0,6} : Finset (Fin 7)))
    (t := S j) (by rw [hc]; decide)
  have hr0 : r ≠ 0 := by rintro rfl; exact hrne (by simp)
  have hr6 : r ≠ 6 := by rintro rfl; exact hrne (by simp)
  have hj : S j = {r, 0, 6} := by
    symm
    exact eq_of_subset_of_card_le (insert_subset hr hpair) (by
      rw [hc, card_insert_of_notMem hrne]
      decide)
  have hr5 : r = 5 := by
    by_contra hne
    have r5 : r < 5 := by omega
    exact hnoskip j r 6 0 5 hr hsix hzero r5 (by decide) hr0 (by decide) (by decide) (by
      rw [hj]
      simp only [mem_insert, mem_singleton, not_or]; omega)
  have hrOne : r = 1 := by
    by_contra hne
    have oneR : (1 : Fin 7) < r := by omega
    exact hnoskip j 0 r 6 1 hzero hr hsix (by decide) oneR (by decide) hr6 (by decide) (by
      rw [hj]
      simp only [mem_insert, mem_singleton, not_or]; omega)
  exact (by decide : (5 : Fin 7) ≠ 1) (hr5.symm.trans hrOne)

private def occursWith {a b : ℕ} (S : Fin b → Finset (Fin a)) (x : Fin a) : Finset (Fin a) :=
  (univ.filter fun j => x ∈ S j).biUnion fun j => (S j).erase x

private theorem occursWith_mem {a b : ℕ} {S : Fin b → Finset (Fin a)} {x y : Fin a} :
    y ∈ occursWith S x ↔ y ≠ x ∧ ∃ j, x ∈ S j ∧ y ∈ S j := by
  simp only [occursWith, mem_biUnion, mem_filter, mem_univ, true_and, mem_erase]
  aesop

private theorem occursWith_card {a b : ℕ} {d : Fin a → Fin b → ℝ} (hm : StrictMonge d)
    (S : Fin b → Finset (Fin a)) (hc : ∀ j, (S j).card = 3)
    (hs : ∀ j i, i ∈ S j → d i j = 1) (x : Fin a) :
    (occursWith S x).card = 2 * (univ.filter fun j => x ∈ S j).card := by
  classical
  unfold occursWith
  rw [card_biUnion]
  · rw [show (∑ j ∈ univ.filter (fun j => x ∈ S j), ((S j).erase x).card) =
        ∑ j ∈ univ.filter (fun j => x ∈ S j), 2 by
      apply sum_congr rfl
      intro j hj
      rw [card_erase_of_mem (mem_filter.1 hj).2, hc]]
    simp [Nat.mul_comm]
  · intro j hj k hk hjk
    apply disjoint_left.2
    intro y hy hy'
    obtain ⟨hn, hy⟩ := mem_erase.1 hy
    have hy' := (mem_erase.1 hy').2
    exact no_two_common hm hn hjk (hs j y hy) (hs k y hy') (hs j x (mem_filter.1 hj).2)
      (hs k x (mem_filter.1 hk).2)

/-- Eight rows and at least nine triples contradict the parity of the omitted row pairs. -/
theorem eight_row_count {b : ℕ} {d : Fin 8 → Fin b → ℝ} (hm : StrictMonge d)
    (hdeg : ∀ j, 3 ≤ (univ.filter (fun i => d i j = 1)).card) : b ≤ 8 := by
  classical
  choose S hsub hc using fun j => exists_subset_card_eq (hdeg j)
  have hs (j i) (hi : i ∈ S j) : d i j = 1 := (mem_filter.1 (hsub j hi)).2
  have each (x : Fin 8) : (univ.filter fun j => x ∈ S j).card ≤ 3 := by
    have h := card_le_card (show occursWith S x ⊆ univ.erase x from
      fun y hy => mem_erase.2 ⟨(occursWith_mem.1 hy).1, mem_univ y⟩)
    rw [occursWith_card hm S hc hs, card_erase_of_mem (mem_univ x), card_univ,
      Fintype.card_fin] at h
    omega
  have hsum : (∑ x : Fin 8, (univ.filter fun j => x ∈ S j).card) = 3*b := by
    simp only [card_filter]
    rw [sum_comm]
    simp only [← card_filter, filter_mem_eq_inter, univ_inter, hc, sum_const, card_univ,
      Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
  have hbound : (∑ x : Fin 8, (univ.filter fun j => x ∈ S j).card) ≤ 24 := by
    calc
      _ ≤ ∑ x : Fin 8, 3 := sum_le_sum fun x _ => each x
      _ = 24 := by decide
  omega

set_option maxHeartbeats 1800000 in
theorem no_eight_columns {d : Fin 8 → Fin 8 → ℝ} (hm : StrictMonge d)
    (hn : NoAcuteCorners d) (hdeg : ∀ j, 3 ≤ (univ.filter (fun i => d i j = 1)).card) : False := by
  classical
  choose S hsub hc using fun j => exists_subset_card_eq (hdeg j)
  have hs (j i) (hi : i ∈ S j) : d i j = 1 := (mem_filter.1 (hsub j hi)).2
  let n (x : Fin 8) := (univ.filter fun j => x ∈ S j).card
  let N (x : Fin 8) := (univ.erase x) \ occursWith S x
  have nSum : (∑ x, n x) = 24 := by
    simp only [n, card_filter]
    rw [sum_comm]
    simp only [← card_filter, filter_mem_eq_inter, univ_inter, hc, sum_const, card_univ,
      Fintype.card_fin, smul_eq_mul]
  have nPart (x : Fin 8) : (N x).card + 2 * n x = 7 := by
    have hsub : occursWith S x ⊆ univ.erase x :=
      fun y hy => mem_erase.2 ⟨(occursWith_mem.1 hy).1, mem_univ y⟩
    have h := card_sdiff_add_card_eq_card hsub
    rw [occursWith_card hm S hc hs, card_erase_of_mem (mem_univ x), card_univ,
      Fintype.card_fin] at h
    exact h
  have nOne (x : Fin 8) : 1 ≤ (N x).card := by
    have h := nPart x
    omega
  have nBoth : (∑ x, ((N x).card + 2 * n x)) = 56 := by simp [nPart]
  rw [sum_add_distrib, ← mul_sum, nSum] at nBoth
  have nTotal : (∑ x, (N x).card) = 8 := by omega
  have nCard (x : Fin 8) : (N x).card = 1 := by
    have he := sum_erase_add univ (fun y => (N y).card) (mem_univ x)
    rw [nTotal] at he
    have hb : 7 ≤ ∑ y ∈ univ.erase x, (N y).card := by
      calc
        7 = ∑ y ∈ univ.erase x, 1 := by simp
        _ ≤ _ := sum_le_sum fun y _ => nOne y
    have h := nOne x
    omega
  have nUnique {x y z : Fin 8} (hy : y ∈ N x) (hz : z ∈ N x) : y = z := by
    obtain ⟨m, hm⟩ := card_eq_one.1 (nCard x)
    rw [hm,mem_singleton] at hy hz
    exact hy.trans hz.symm
  have nMem {x y : Fin 8} : y ∈ N x ↔ y ≠ x ∧ ¬∃ j, x ∈ S j ∧ y ∈ S j := by
    unfold N
    rw [mem_sdiff, mem_erase, occursWith_mem]
    simp only [mem_univ, and_true]
    constructor
    · rintro ⟨hne, h⟩
      exact ⟨hne, fun hc => h ⟨hne,hc⟩⟩
    · rintro ⟨hne, h⟩
      exact ⟨hne, fun hc => h hc.2⟩
  have cover {x y : Fin 8} (hxy : x ≠ y) (hy : y ∉ N x) : ∃ j, x ∈ S j ∧ y ∈ S j := by
    by_contra h
    exact hy (nMem.2 ⟨hxy.symm,h⟩)
  let r : Fin 8 := if 7 ∈ N 0 then 6 else 7
  have rpos : (0 : Fin 8) < r := by unfold r; split <;> decide
  have rCover : r ∉ N 0 := by
    unfold r
    split
    · rename_i h7
      intro h6
      exact (by decide : (6 : Fin 8) ≠ 7) (nUnique h6 h7)
    · assumption
  obtain ⟨j, h0, hr⟩ := cover rpos.ne rCover
  have hpair := insert_subset h0 (singleton_subset_iff.mpr hr)
  obtain ⟨t, ht, htne⟩ := exists_mem_notMem_of_card_lt_card (s := ({0,r} : Finset (Fin 8)))
    (t := S j) (by rw [hc, card_insert_of_notMem (by simpa using rpos.ne), card_singleton]; decide)
  have ht0 : t ≠ 0 := by rintro rfl; exact htne (by simp)
  have htr : t ≠ r := by rintro rfl; exact htne (by simp)
  have hJ : S j = {t, 0, r} := by
    symm
    exact eq_of_subset_of_card_le (insert_subset ht hpair) (by
      rw [hc, card_insert_of_notMem htne, card_insert_of_notMem (by simpa using rpos.ne),
        card_singleton])
  have maxHit {k : Fin 8} {f : Fin 8} (hk : 0 ∈ S k) (hf : f ∈ S k) : f ≤ r := by
    by_cases h7 : 7 ∈ N 0
    · have hf7 : f ≠ 7 := by
        rintro rfl
        exact (nMem.1 h7).2 ⟨k,hk,hf⟩
      rw [show r = 6 by simp [r,h7]]
      omega
    · rw [show r = 7 by simp [r,h7]]
      omega
  have hi_before {k : Fin 8} (hk : 0 ∈ S k) (hkj : k ≠ j) : j < k := by
    rcases lt_or_gt_of_ne hkj with hkj | hjk
    · obtain ⟨f, hf, hfN⟩ := exists_mem_notMem_of_card_lt_card (s := N r)
        (t := (S k).erase 0) (by rw [nCard, card_erase_of_mem hk, hc]; decide)
      obtain ⟨hf0,hf⟩ := mem_erase.1 hf
      have hfr : f ≠ r := by
        rintro rfl
        exact no_two_common hm rpos.ne hkj.ne (hs k 0 hk) (hs j 0 h0) (hs k r hf) (hs j r hr)
      obtain ⟨l, hrl, hfl⟩ := cover hfr.symm hfN
      exact False.elim ((maxHit hk hf).not_gt (intersection_pair_order hm hn hkj hfr hf0 rpos.ne.symm
        (hs k f hf) (hs l f hfl) (hs j r hr) (hs l r hrl) (hs k 0 hk) (hs j 0 h0)))
    · exact hjk
  have lo_after {k : Fin 8} (hk : r ∈ S k) (hkj : k ≠ j) : k < j := by
    rcases lt_or_gt_of_ne hkj with hkj | hjk
    · exact hkj
    · obtain ⟨f, hf, hfN⟩ := exists_mem_notMem_of_card_lt_card (s := N 0)
        (t := (S k).erase r) (by rw [nCard, card_erase_of_mem hk, hc]; decide)
      obtain ⟨hfr,hf⟩ := mem_erase.1 hf
      have hf0 : f ≠ 0 := by
        rintro rfl
        exact no_two_common hm rpos.ne hjk.ne (hs j 0 h0) (hs k 0 hf) (hs j r hr) (hs k r hk)
      obtain ⟨l, h0l, hfl⟩ := cover hf0.symm hfN
      have h := intersection_pair_order hm hn hjk hf0.symm rpos.ne hfr
        (hs j 0 h0) (hs l 0 h0l) (hs k f hf) (hs l f hfl) (hs j r hr) (hs k r hk)
      omega
  have above (f : Fin 8) (htf : t < f) (hfr : f < r) : f ∈ N 0 ∪ N t := by
    have hf0 : f ≠ 0 := by omega
    by_cases hfn : f ∈ N 0
    · exact mem_union_left _ hfn
    by_cases hft : f ∈ N t
    · exact mem_union_right _ hft
    obtain ⟨k, h0k, hfk⟩ := cover hf0.symm hfn
    have hkj : k ≠ j := by
      rintro rfl
      rw [hJ] at hfk
      simp only [mem_insert,mem_singleton] at hfk
      omega
    obtain ⟨l, htl, hfl⟩ := cover htf.ne hft
    exact False.elim (htf.not_gt (intersection_pair_order hm hn (hi_before h0k hkj)
      htf.ne ht0 hf0 (hs j t ht) (hs l t htl) (hs k f hfk) (hs l f hfl) (hs j 0 h0) (hs k 0 h0k)))
  have below (f : Fin 8) (h0f : (0 : Fin 8) < f) (hft : f < t) : f ∈ N r ∪ N t := by
    have htr' : t ≤ r := maxHit h0 ht
    have hfr : f ≠ r := by omega
    by_cases hfn : f ∈ N r
    · exact mem_union_left _ hfn
    by_cases hftN : f ∈ N t
    · exact mem_union_right _ hftN
    obtain ⟨k, hrk, hfk⟩ := cover hfr.symm hfn
    have hkj : k ≠ j := by
      rintro rfl
      rw [hJ] at hfk
      simp only [mem_insert,mem_singleton] at hfk
      omega
    obtain ⟨l, htl, hfl⟩ := cover hft.ne.symm hftN
    exact False.elim (hft.not_gt (intersection_pair_order hm hn (lo_after hrk hkj)
      hft.ne hfr htr (hs k f hfk) (hs l f hfl) (hs j t ht) (hs l t htl) (hs k r hrk) (hs j r hr)))
  have tlarge : (4 : Fin 8) ≤ t := by
    by_contra hlow
    have h4 : t < 4 := lt_of_not_ge hlow
    by_cases h7 : 7 ∈ N 0
    · have hr6 : r = 6 := by simp [r,h7]
      have htwo : ({4,5} : Finset (Fin 8)) ⊆ N t := by
        intro f hf
        have hcases : f = 4 ∨ f = 5 := by simpa only [mem_insert,mem_singleton] using hf
        have h := mem_union.1 (above f (by omega) (by omega))
        rcases h with hn0 | hnt
        · exact False.elim (by have he := nUnique hn0 h7; omega)
        · exact hnt
      have h := card_le_card htwo
      rw [nCard] at h
      exact (by decide : ¬ (2 : ℕ) ≤ 1) h
    · have hr7 : r = 7 := by simp [r,h7]
      have hthree : ({4,5,6} : Finset (Fin 8)) ⊆ N 0 ∪ N t := by
        intro f hf
        have hcases : f = 4 ∨ f = 5 ∨ f = 6 := by
          simpa only [mem_insert,mem_singleton] using hf
        exact above f (by omega) (by omega)
      have h := (card_le_card hthree).trans (card_union_le (N 0) (N t))
      rw [nCard, nCard] at h
      exact (by decide : ¬ (3 : ℕ) ≤ 1+1) h
  have hthree : ({1,2,3} : Finset (Fin 8)) ⊆ N r ∪ N t := by
    intro f hf
    have hcases : f = 1 ∨ f = 2 ∨ f = 3 := by simpa only [mem_insert,mem_singleton] using hf
    exact below f (by omega) (by omega)
  have h := (card_le_card hthree).trans (card_union_le (N r) (N t))
  rw [nCard,nCard] at h
  exact (by decide : ¬ (3 : ℕ) ≤ 1+1) h

end OrderedUnitCuts

namespace OrderedUnitCuts

open Finset Erdos97 EuclideanGeometry

private theorem unit_degree_on_embedding {S : Finset Point} (e : Fin S.card ↪ Point)
    (he : Set.range e = (S : Set Point)) (p : Point) (hp : HasNUnitDistancePointsAt 3 S p) :
    3 ≤ (univ.filter fun i => dist (e i) p = 1).card := by
  classical
  have hmap : S.filter (fun x => dist p x = 1) =
      (univ.filter fun i => dist (e i) p = 1).map e := by
    ext x
    simp only [mem_filter, mem_map]
    constructor
    · rintro ⟨hx,hd⟩
      obtain ⟨i,rfl⟩ : x ∈ Set.range e := by rw [he]; exact hx
      exact ⟨i,⟨Finset.mem_univ _,by simpa only [dist_comm] using hd⟩,rfl⟩
    · rintro ⟨i,hd,rfl⟩
      exact ⟨by change e i ∈ (S : Set Point); rw [← he]; exact ⟨i,rfl⟩,
        by simpa only [dist_comm] using hd.2⟩
  unfold HasNUnitDistancePointsAt at hp
  rwa [hmap,card_map] at hp

private theorem restrict_columns {a b c : ℕ} (hcb : c ≤ b)
    (d : Fin a → Fin b → ℝ) (hm : StrictMonge d) (hn : NoAcuteCorners d)
    (hdeg : ∀ j, 3 ≤ (univ.filter fun i => d i j = 1).card) :
    let d' := fun (i : Fin a) (j : Fin c) => d i (Fin.castLE hcb j)
    StrictMonge d' ∧ NoAcuteCorners d' ∧ (∀ j, 3 ≤ (univ.filter fun i => d' i j = 1).card) := by
  dsimp only
  refine ⟨?_,?_,fun j => hdeg (Fin.castLE hcb j)⟩
  · intro i k j l hik hjl
    exact hm i k _ _ hik hjl
  · intro i k j l r₁ r₂ c₁ c₂ hr₁ hr₂ hr₃ hr₄ hc₁ hc₂ hc₃ hc₄ h₁ h₂ h₃ h₄
    exact hn i k _ _ r₁ r₂ _ _ hr₁ hr₂ hr₃ hr₄ hc₁ hc₂ hc₃ hc₄ h₁ h₂ h₃ h₄

private theorem small_side_cases {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (hsize : a + b < 20) (hpairs : 3*b ≤ a.choose 2) : a = 7 ∨ a = 8 ∨ a = 9 := by
  have htop : a ≤ 9 := by omega
  interval_cases a <;> norm_num [Nat.choose] at hpairs ⊢ <;> omega

private theorem ordered_minimum
    (h8 : ∀ d : Fin 8 → Fin 8 → ℝ, StrictMonge d → NoAcuteCorners d →
      (∀ j, 3 ≤ (univ.filter fun i => d i j = 1).card) → False)
    (h9 : ∀ d : Fin 9 → Fin 9 → ℝ, StrictMonge d → NoAcuteCorners d →
      (∀ j, 3 ≤ (univ.filter fun i => d i j = 1).card) → False) :
    ∀ {a b : ℕ}, 0 < a → a ≤ b → ∀ d : Fin a → Fin b → ℝ, StrictMonge d →
      NoAcuteCorners d → (∀ j, 3 ≤ (univ.filter fun i => d i j = 1).card) → 20 ≤ a+b := by
  intro a b ha hab d hm hn hdeg
  by_contra! h
  rcases small_side_cases ha hab h (column_pair_bound hm hdeg) with rfl | rfl | rfl
  · obtain ⟨hm',hn',deg'⟩ := restrict_columns hab d hm hn hdeg
    exact no_seven_columns hm' hn' deg'
  · obtain ⟨hm',hn',deg'⟩ := restrict_columns hab d hm hn hdeg
    exact h8 _ hm' hn' deg'
  · obtain ⟨hm',hn',deg'⟩ := restrict_columns hab d hm hn hdeg
    exact h9 _ hm' hn' deg'

private theorem cut_minimum_of_ordered_sides
    (h8 : ∀ d : Fin 8 → Fin 8 → ℝ, StrictMonge d → NoAcuteCorners d →
      (∀ j, 3 ≤ (univ.filter fun i => d i j = 1).card) → False)
    (h9 : ∀ d : Fin 9 → Fin 9 → ℝ, StrictMonge d → NoAcuteCorners d →
      (∀ j, 3 ≤ (univ.filter fun i => d i j = 1).card) → False)
    {V A B : Finset Point} (hV : ConvexIndep V) (hA : A.Nonempty) (hB : B.Nonempty)
    (hcut : IsCut V A B) (hBdeg : HasNUnitDistancePointsOn 3 A B) (hab : A.card ≤ B.card) :
    20 ≤ V.card := by
  classical
  obtain ⟨u,v,hu,hv,hgeom⟩ := exists_crossOrdered hV hA hB hcut
  let d (i : Fin A.card) (j : Fin B.card) := dist (u i) (v j)
  have hdeg (j : Fin B.card) : 3 ≤ (univ.filter fun i => d i j = 1).card := by
    have hj : v j ∈ B := by
      change v j ∈ (B : Set Point)
      rw [← hv]
      exact ⟨j,rfl⟩
    exact unit_degree_on_embedding u hu (v j) (hBdeg _ hj)
  have hcard : V.card = A.card + B.card := by
    rw [← hcut.1, card_union_of_disjoint hcut.2.1]
  rw [hcard]
  exact ordered_minimum h8 h9 hA.card_pos hab d hgeom.strictMonge hgeom.noAcuteCorners hdeg

/-- The two remaining square matrix obstructions imply the exact lower bound for a cut. -/
theorem cut_minimum_of_small_cases
    (h8 : ∀ d : Fin 8 → Fin 8 → ℝ, StrictMonge d → NoAcuteCorners d →
      (∀ j, 3 ≤ (univ.filter fun i => d i j = 1).card) → False)
    (h9 : ∀ d : Fin 9 → Fin 9 → ℝ, StrictMonge d → NoAcuteCorners d →
      (∀ j, 3 ≤ (univ.filter fun i => d i j = 1).card) → False) :
    ∀ V A B : Finset Point, ConvexIndep V → A.Nonempty → B.Nonempty → IsCut V A B →
      HasNUnitDistancePointsOn 3 B A → HasNUnitDistancePointsOn 3 A B → 20 ≤ V.card := by
  intro V A B hV hA hB hcut hAdeg hBdeg
  rcases le_total A.card B.card with hab | hba
  · exact cut_minimum_of_ordered_sides h8 h9 hV hA hB hcut hBdeg hab
  · have hcut' : IsCut V B A := ⟨(Finset.union_comm _ _).trans hcut.1, hcut.2.1.symm, hcut.2.2.symm⟩
    exact cut_minimum_of_ordered_sides h8 h9 hV hB hA hcut' hAdeg hba

/-- The verified geometric and small-cardinality cases leave only the nine-by-nine obstruction. -/
theorem cut_minimum_of_nine_case
    (h9 : ∀ d : Fin 9 → Fin 9 → ℝ, StrictMonge d → NoAcuteCorners d →
      (∀ j, 3 ≤ (univ.filter fun i => d i j = 1).card) → False) :
    ∀ V A B : Finset Point, ConvexIndep V → A.Nonempty → B.Nonempty → IsCut V A B →
      HasNUnitDistancePointsOn 3 B A → HasNUnitDistancePointsOn 3 A B → 20 ≤ V.card :=
  cut_minimum_of_small_cases (fun _ => no_eight_columns) h9

end OrderedUnitCuts

/- Verification of the search for nine ordered triples on nine rows. -/

namespace NineCutSearch

structure Triple where
  rows : List ℕ
  edges : List ℕ
deriving DecidableEq

private def pairIndex (i j : ℕ) : ℕ :=
  let a := min i j
  let b := max i j
  a * (17 - a) / 2 + (b - a - 1)

private def c0 : Triple := ⟨[0,1,2], [0,1,8]⟩
private def c1 : Triple := ⟨[0,1,3], [0,2,9]⟩
private def c2 : Triple := ⟨[0,1,4], [0,3,10]⟩
private def c3 : Triple := ⟨[0,1,5], [0,4,11]⟩
private def c4 : Triple := ⟨[0,1,6], [0,5,12]⟩
private def c5 : Triple := ⟨[0,1,7], [0,6,13]⟩
private def c6 : Triple := ⟨[0,1,8], [0,7,14]⟩
private def c7 : Triple := ⟨[0,2,3], [1,2,15]⟩
private def c8 : Triple := ⟨[0,2,4], [1,3,16]⟩
private def c9 : Triple := ⟨[0,2,5], [1,4,17]⟩
private def c10 : Triple := ⟨[0,2,6], [1,5,18]⟩
private def c11 : Triple := ⟨[0,2,7], [1,6,19]⟩
private def c12 : Triple := ⟨[0,2,8], [1,7,20]⟩
private def c13 : Triple := ⟨[0,3,4], [2,3,21]⟩
private def c14 : Triple := ⟨[0,3,5], [2,4,22]⟩
private def c15 : Triple := ⟨[0,3,6], [2,5,23]⟩
private def c16 : Triple := ⟨[0,3,7], [2,6,24]⟩
private def c17 : Triple := ⟨[0,3,8], [2,7,25]⟩
private def c18 : Triple := ⟨[0,4,5], [3,4,26]⟩
private def c19 : Triple := ⟨[0,4,6], [3,5,27]⟩
private def c20 : Triple := ⟨[0,4,7], [3,6,28]⟩
private def c21 : Triple := ⟨[0,4,8], [3,7,29]⟩
private def c22 : Triple := ⟨[0,5,6], [4,5,30]⟩
private def c23 : Triple := ⟨[0,5,7], [4,6,31]⟩
private def c24 : Triple := ⟨[0,5,8], [4,7,32]⟩
private def c25 : Triple := ⟨[0,6,7], [5,6,33]⟩
private def c26 : Triple := ⟨[0,6,8], [5,7,34]⟩
private def c27 : Triple := ⟨[0,7,8], [6,7,35]⟩
private def c28 : Triple := ⟨[1,2,3], [8,9,15]⟩
private def c29 : Triple := ⟨[1,2,4], [8,10,16]⟩
private def c30 : Triple := ⟨[1,2,5], [8,11,17]⟩
private def c31 : Triple := ⟨[1,2,6], [8,12,18]⟩
private def c32 : Triple := ⟨[1,2,7], [8,13,19]⟩
private def c33 : Triple := ⟨[1,2,8], [8,14,20]⟩
private def c34 : Triple := ⟨[1,3,4], [9,10,21]⟩
private def c35 : Triple := ⟨[1,3,5], [9,11,22]⟩
private def c36 : Triple := ⟨[1,3,6], [9,12,23]⟩
private def c37 : Triple := ⟨[1,3,7], [9,13,24]⟩
private def c38 : Triple := ⟨[1,3,8], [9,14,25]⟩
private def c39 : Triple := ⟨[1,4,5], [10,11,26]⟩
private def c40 : Triple := ⟨[1,4,6], [10,12,27]⟩
private def c41 : Triple := ⟨[1,4,7], [10,13,28]⟩
private def c42 : Triple := ⟨[1,4,8], [10,14,29]⟩
private def c43 : Triple := ⟨[1,5,6], [11,12,30]⟩
private def c44 : Triple := ⟨[1,5,7], [11,13,31]⟩
private def c45 : Triple := ⟨[1,5,8], [11,14,32]⟩
private def c46 : Triple := ⟨[1,6,7], [12,13,33]⟩
private def c47 : Triple := ⟨[1,6,8], [12,14,34]⟩
private def c48 : Triple := ⟨[1,7,8], [13,14,35]⟩
private def c49 : Triple := ⟨[2,3,4], [15,16,21]⟩
private def c50 : Triple := ⟨[2,3,5], [15,17,22]⟩
private def c51 : Triple := ⟨[2,3,6], [15,18,23]⟩
private def c52 : Triple := ⟨[2,3,7], [15,19,24]⟩
private def c53 : Triple := ⟨[2,3,8], [15,20,25]⟩
private def c54 : Triple := ⟨[2,4,5], [16,17,26]⟩
private def c55 : Triple := ⟨[2,4,6], [16,18,27]⟩
private def c56 : Triple := ⟨[2,4,7], [16,19,28]⟩
private def c57 : Triple := ⟨[2,4,8], [16,20,29]⟩
private def c58 : Triple := ⟨[2,5,6], [17,18,30]⟩
private def c59 : Triple := ⟨[2,5,7], [17,19,31]⟩
private def c60 : Triple := ⟨[2,5,8], [17,20,32]⟩
private def c61 : Triple := ⟨[2,6,7], [18,19,33]⟩
private def c62 : Triple := ⟨[2,6,8], [18,20,34]⟩
private def c63 : Triple := ⟨[2,7,8], [19,20,35]⟩
private def c64 : Triple := ⟨[3,4,5], [21,22,26]⟩
private def c65 : Triple := ⟨[3,4,6], [21,23,27]⟩
private def c66 : Triple := ⟨[3,4,7], [21,24,28]⟩
private def c67 : Triple := ⟨[3,4,8], [21,25,29]⟩
private def c68 : Triple := ⟨[3,5,6], [22,23,30]⟩
private def c69 : Triple := ⟨[3,5,7], [22,24,31]⟩
private def c70 : Triple := ⟨[3,5,8], [22,25,32]⟩
private def c71 : Triple := ⟨[3,6,7], [23,24,33]⟩
private def c72 : Triple := ⟨[3,6,8], [23,25,34]⟩
private def c73 : Triple := ⟨[3,7,8], [24,25,35]⟩
private def c74 : Triple := ⟨[4,5,6], [26,27,30]⟩
private def c75 : Triple := ⟨[4,5,7], [26,28,31]⟩
private def c76 : Triple := ⟨[4,5,8], [26,29,32]⟩
private def c77 : Triple := ⟨[4,6,7], [27,28,33]⟩
private def c78 : Triple := ⟨[4,6,8], [27,29,34]⟩
private def c79 : Triple := ⟨[4,7,8], [28,29,35]⟩
private def c80 : Triple := ⟨[5,6,7], [30,31,33]⟩
private def c81 : Triple := ⟨[5,6,8], [30,32,34]⟩
private def c82 : Triple := ⟨[5,7,8], [31,32,35]⟩
private def c83 : Triple := ⟨[6,7,8], [33,34,35]⟩

private def containing : Array (List Triple) := #[[c0,c1,c2,c3,c4,c5,c6],
  [c0,c7,c8,c9,c10,c11,c12],
  [c1,c7,c13,c14,c15,c16,c17],
  [c2,c8,c13,c18,c19,c20,c21],
  [c3,c9,c14,c18,c22,c23,c24],
  [c4,c10,c15,c19,c22,c25,c26],
  [c5,c11,c16,c20,c23,c25,c27],
  [c6,c12,c17,c21,c24,c26,c27],
  [c0,c28,c29,c30,c31,c32,c33],
  [c1,c28,c34,c35,c36,c37,c38],
  [c2,c29,c34,c39,c40,c41,c42],
  [c3,c30,c35,c39,c43,c44,c45],
  [c4,c31,c36,c40,c43,c46,c47],
  [c5,c32,c37,c41,c44,c46,c48],
  [c6,c33,c38,c42,c45,c47,c48],
  [c7,c28,c49,c50,c51,c52,c53],
  [c8,c29,c49,c54,c55,c56,c57],
  [c9,c30,c50,c54,c58,c59,c60],
  [c10,c31,c51,c55,c58,c61,c62],
  [c11,c32,c52,c56,c59,c61,c63],
  [c12,c33,c53,c57,c60,c62,c63],
  [c13,c34,c49,c64,c65,c66,c67],
  [c14,c35,c50,c64,c68,c69,c70],
  [c15,c36,c51,c65,c68,c71,c72],
  [c16,c37,c52,c66,c69,c71,c73],
  [c17,c38,c53,c67,c70,c72,c73],
  [c18,c39,c54,c64,c74,c75,c76],
  [c19,c40,c55,c65,c74,c77,c78],
  [c20,c41,c56,c66,c75,c77,c79],
  [c21,c42,c57,c67,c76,c78,c79],
  [c22,c43,c58,c68,c74,c80,c81],
  [c23,c44,c59,c69,c75,c80,c82],
  [c24,c45,c60,c70,c76,c81,c82],
  [c25,c46,c61,c71,c77,c80,c83],
  [c26,c47,c62,c72,c78,c81,c83],
  [c27,c48,c63,c73,c79,c82,c83]]

private def hasBit (mask index : ℕ) : Bool := decide (mask / 2^index % 2 = 1)

private def available (used missing : ℕ) (t : Triple) : Bool :=
  t.edges.all fun f => !(hasBit (used + missing) f)

abbrev Constraint := List ℕ × List ℕ

private def direction (t s : Triple) : Option Constraint :=
  match t.rows.filter (fun i => s.rows.contains i) with
  | [z] =>
    let pending := (t.rows.erase z).flatMap fun i =>
      (s.rows.erase z).map fun j => (i, j, pairIndex i j)
    some ((pending.filter fun p => p.1 < p.2.1).map fun p => p.2.2,
      (pending.filter fun p => p.2.1 < p.1).map fun p => p.2.2)
  | _ => none

structure SearchState where
  used : ℕ
  missing : ℕ
  omitted : ℕ
  selected : List Triple
  constraints : List Constraint
deriving DecidableEq

private def mark (p : ℕ × ℕ) (f : ℕ) : ℕ × ℕ :=
  if hasBit p.1 f then p else (p.1 + 2^f, p.2 + 1)

private def propagate (u : ℕ) (c : Constraint) (p : ℕ × ℕ) : Option (ℕ × ℕ) :=
  let up := c.1.any (hasBit u)
  let down := c.2.any (hasBit u)
  if up then
    if down then none else some (c.2.foldl mark p)
  else if down then some (c.1.foldl mark p) else some p

private def addTriangle (s : SearchState) (t : Triple) : Option SearchState := do
  let u := s.used + (t.edges.map (fun e => 2^e)).sum
  let cs := s.constraints ++ (s.selected.filterMap fun q => direction t q)
  let (m, k) ← cs.foldlM (fun p c => propagate u c p) (s.missing, s.omitted)
  return ⟨u, m, k, t :: s.selected, cs⟩

private def choices (s : SearchState) (e : ℕ) : List Triple :=
  (containing[e]?.getD []).filter (available s.used s.missing)

private def omitEdge (s : SearchState) (f : ℕ) : SearchState :=
  { s with missing := s.missing + 2^f, omitted := s.omitted + 1 }

private def inspectNat {α : Type} (n : ℕ) (f : ℕ → α) : α :=
  match n with
  | 0 => f 0
  | n+1 => f (n+1)

private def inspectState (s : SearchState) : SearchState :=
  inspectNat s.used fun u => inspectNat s.missing fun m => inspectNat s.omitted fun k =>
    ⟨u,m,k,s.selected,s.constraints⟩

private def localEdges (v : Fin 9) : List ℕ :=
  ((List.finRange 9).erase v).map (fun w => pairIndex v.val w.val)

private def oddCount (mask : ℕ) : ℕ :=
  (List.finRange 9).countP fun v => decide ((localEdges v).countP (hasBit mask) % 2 = 1)

private def overBudget (s : SearchState) : Bool :=
  decide (9 < s.omitted) || decide (2*(9-s.omitted) < oddCount s.missing)

private def viable (s : SearchState) (e : ℕ) : List SearchState :=
  (choices s e).filterMap fun t =>
    match addTriangle s t with
    | none => none
    | some next =>
      let next := inspectState next
      if overBudget next then none else some next

private def verifyStep (next : SearchState → List ℕ → Option (List ℕ))
    (input : SearchState) (cert : List ℕ) : Option (List ℕ) :=
  let s := inspectState input
  if s.omitted > 9 then some cert
  else if s.selected.length ≥ 9 then none
  else
    match cert with
    | [] => none
    | c :: rest =>
      let code := c
      let force := 36 ≤ code
      let e := code % 36
      if code = 72 then
        if 2*(9-s.omitted) < oddCount s.missing then some rest else none
      else if hasBit (s.used + s.missing) e then none
      else
        let opts := viable s e
        if force then
          if opts.isEmpty then next (omitEdge s e) rest else none
        else do
          let left ← opts.foldlM (fun txt child => next child txt) rest
          if s.omitted < 9 then next (omitEdge s e) left else some left

private def verify : ℕ → SearchState → List ℕ → Option (List ℕ)
  | 0 => fun _ _ => none
  | fuel+1 => verifyStep (verify fuel)


def init : SearchState := ⟨0,0,0,[],[]⟩

private def triples : List Triple := [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34,c35,c36,c37,c38,c39,c40,c41,c42,c43,c44,c45,c46,c47,c48,c49,c50,c51,c52,c53,c54,c55,c56,c57,c58,c59,c60,c61,c62,c63,c64,c65,c66,c67,c68,c69,c70,c71,c72,c73,c74,c75,c76,c77,c78,c79,c80,c81,c82,c83]

open Finset

private def flags (u : ℕ) : Finset ℕ := Finset.equivBitIndices u

private theorem flags_mem {u e : ℕ} : e ∈ flags u ↔ hasBit u e = true := by
  simp [flags, hasBit, Nat.testBit_eq_decide_div_mod_eq]

private theorem flags_add {u m : ℕ} (h : Disjoint (flags u) (flags m)) :
    flags (u + m) = flags u ∪ flags m := by
  apply Finset.equivBitIndices.symm.injective
  simp only [flags, Equiv.symm_apply_apply, Finset.equivBitIndices_symm_apply]
  change u + m = ∑ i ∈ flags u ∪ flags m, 2^i
  rw [sum_union h]
  simp [flags]

private theorem flags_zero : flags 0 = ∅ := by simp [flags]

private theorem flags_single (e : ℕ) : flags (2^e) = {e} := by simp [flags]

private theorem flags_not_mem {u e : ℕ} :
    e ∉ flags u ↔ hasBit u e = false := by simp [flags_mem]

private def covered (F : Finset Triple) : Finset ℕ := F.biUnion fun t => t.edges.toFinset

private theorem covered_mem {F : Finset Triple} {e : ℕ} :
    e ∈ covered F ↔ ∃ t ∈ F, e ∈ t.edges := by
  simp only [covered, mem_biUnion, List.mem_toFinset]

private theorem covered_mono {F G : Finset Triple} (h : F ⊆ G) :
    covered F ⊆ covered G := by
  intro e he
  obtain ⟨t, ht, hte⟩ := covered_mem.1 he
  exact covered_mem.2 ⟨t,h ht,hte⟩

private theorem edge_facts :
    ∀ t ∈ triples.toFinset, (∀ e ∈ t.edges.toFinset, e < 36) ∧ t.edges.toFinset.card = 3 ∧
      flags (t.edges.map (fun e => 2^e)).sum = t.edges.toFinset := by
  decide +kernel

private theorem table_facts :
    ∀ e : Fin 36, ∀ t ∈ triples.toFinset,
      e.val ∈ t.edges ↔ t ∈ (containing[e.val]?.getD []) := by
  decide +kernel

structure SafePair (F : Finset Triple) (c : Constraint) : Prop where
  leftBound : ∀ e ∈ c.1, e < 36
  rightBound : ∀ e ∈ c.2, e < 36
  consistent : ¬ ((∃ e ∈ c.1, e ∈ covered F) ∧ (∃ e ∈ c.2, e ∈ covered F))
structure Model (F : Finset Triple) : Prop where
  sub : F ⊆ triples.toFinset
  count : F.card = 9
  separate : ∀ t ∈ F, ∀ t' ∈ F, t ≠ t' → Disjoint t.edges.toFinset t'.edges.toFinset
  order : ∀ t ∈ F, ∀ t' ∈ F, ∀ c, direction t t' = some c → SafePair F c

private def absent (F : Finset Triple) : Finset ℕ := range 36 \ covered F

private theorem absent_card {F : Finset Triple} (h : Model F) :
    (absent F).card = 9 := by
  have hb : (covered F).card = 27 := by
    unfold covered
    rw [card_biUnion]
    · have he : ∀ t ∈ F, t.edges.toFinset.card = 3 :=
        fun t ht => (edge_facts t (h.sub ht)).2.1
      calc
        _ = ∑ _t ∈ F, 3 := sum_congr rfl he
        _ = 27 := by simp [h.count]
    · intro t ht t' ht' hne
      exact h.separate t ht t' ht' hne
  have hr : covered F ⊆ range 36 := by
    intro e he
    obtain ⟨t, ht, he⟩ := covered_mem.1 he
    exact mem_range.2 ((edge_facts t (h.sub ht)).1 e (List.mem_toFinset.2 he))
  rw [absent, card_sdiff_of_subset hr, card_range, hb]

structure Valid (F : Finset Triple) (s : SearchState) : Prop where
  chosen : s.selected.toFinset ⊆ F
  used : flags s.used = covered s.selected.toFinset
  missing : flags s.missing ⊆ absent F
  omitted : (flags s.missing).card = s.omitted
  rules : ∀ c ∈ s.constraints, SafePair F c

private theorem init_valid (F : Finset Triple) : Valid F init := by
  constructor
  · simp [init]
  · simp [init, flags_zero, covered]
  · simp [init, flags_zero]
  · simp [init, flags_zero]
  · simp [init]

private theorem disjoint_flags {F : Finset Triple} {s : SearchState} (h : Valid F s) :
    Disjoint (flags s.used) (flags s.missing) := by
  apply disjoint_left.2
  intro e he hm
  exact (mem_sdiff.1 (h.missing hm)).2 (covered_mono h.chosen (h.used ▸ he))

private theorem unavailable_of_used_or_missing {F : Finset Triple} {s : SearchState} (hv : Valid F s)
    {e : ℕ} (h : hasBit (s.used + s.missing) e = false) :
    e ∉ flags s.used ∧ e ∉ flags s.missing := by
  have hn := flags_not_mem.2 h
  rwa [flags_add (disjoint_flags hv), mem_union, not_or] at hn

private theorem available_iff {F : Finset Triple} {s : SearchState} (hv : Valid F s) (t : Triple) :
    available s.used s.missing t = true ↔
      Disjoint t.edges.toFinset (flags s.used) ∧ Disjoint t.edges.toFinset (flags s.missing) := by
  simp only [available, List.all_eq_true, Bool.not_eq_true', ← flags_not_mem,
    flags_add (disjoint_flags hv), mem_union, not_or, disjoint_left, List.mem_toFinset]
  exact ⟨fun h => ⟨fun _ ha => (h _ ha).1, fun _ ha => (h _ ha).2⟩,
    fun h _ ha => ⟨h.1 ha,h.2 ha⟩⟩

private theorem has_choice {F : Finset Triple} (hm : Model F) {s : SearchState} (hv : Valid F s)
    {e : ℕ} (he : e < 36) (hfree : hasBit (s.used + s.missing) e = false)
    (hcovered : e ∈ covered F) : ∃ t ∈ choices s e, t ∈ F := by
  obtain ⟨t, ht, het⟩ := covered_mem.1 hcovered
  have hnot : t ∉ s.selected.toFinset := by
    intro h
    have hu := covered_mem.2 ⟨t,h,het⟩
    exact (unavailable_of_used_or_missing hv hfree).1 (hv.used.symm ▸ hu)
  have hu : Disjoint t.edges.toFinset (flags s.used) := by
    apply disjoint_left.2
    intro f hf hf'
    obtain ⟨q, hqs, hq⟩ := covered_mem.1 (hv.used ▸ hf')
    have hne : t ≠ q := by rintro rfl; exact hnot hqs
    exact disjoint_left.1 (hm.separate t ht q (hv.chosen hqs) hne) hf (List.mem_toFinset.2 hq)
  have hM : Disjoint t.edges.toFinset (flags s.missing) := by
    apply disjoint_left.2
    intro f hf hf'
    exact (mem_sdiff.1 (hv.missing hf')).2 (covered_mem.2 ⟨t,ht,List.mem_toFinset.1 hf⟩)
  refine ⟨t, List.mem_filter.2 ⟨?_, (available_iff hv t).2 ⟨hu,hM⟩⟩, ht⟩
  exact (table_facts ⟨e,he⟩ t (hm.sub ht)).1 het

private theorem valid_omit {F : Finset Triple} {s : SearchState} (hv : Valid F s)
    {e : ℕ} (he : e < 36) (hfree : hasBit (s.used + s.missing) e = false)
    (hn : e ∉ covered F) : Valid F (omitEdge s e) := by
  have hnot := (unavailable_of_used_or_missing hv hfree).2
  have hf : flags (s.missing + 2^e) = insert e (flags s.missing) := by
    rw [flags_add (by simpa [flags_single] using hnot), flags_single, union_comm, singleton_union]
  refine ⟨hv.chosen,hv.used,?_,?_,hv.rules⟩
  · simp only [omitEdge,hf,insert_subset_iff]
    exact ⟨mem_sdiff.2 ⟨mem_range.2 he,hn⟩, hv.missing⟩
  · simp [omitEdge,hf,Finset.card_insert_of_notMem hnot,hv.omitted]

private theorem unused_miss_room {F : Finset Triple} (hm : Model F) {s : SearchState} (hv : Valid F s)
    {e : ℕ} (he : e < 36) (hfree : hasBit (s.used + s.missing) e = false)
    (hn : e ∉ covered F) : s.omitted < 9 := by
  have hv' := valid_omit hv he hfree hn
  have hc := card_le_card hv'.missing
  rw [hv'.omitted, absent_card hm] at hc
  exact hc

private def MissingValid (F : Finset Triple) (p : ℕ × ℕ) : Prop :=
  flags p.1 ⊆ absent F ∧ (flags p.1).card = p.2

private theorem mark_valid {F : Finset Triple} {p : ℕ × ℕ} {e : ℕ}
    (hp : MissingValid F p) (he : e ∈ absent F) : MissingValid F (mark p e) := by
  unfold mark
  split
  · exact hp
  · rename_i h
    have hn : e ∉ flags p.1 := by
      simpa only [flags_mem] using h
    have hf : flags (p.1+2^e) = insert e (flags p.1) := by
      rw [flags_add (by simpa [flags_single] using hn), flags_single, union_comm, singleton_union]
    exact ⟨by simpa only [hf,insert_subset_iff] using And.intro he hp.1,
      by simp [hf, card_insert_of_notMem hn, hp.2]⟩

private theorem mark_all_valid {F : Finset Triple} {p : ℕ × ℕ} {L : List ℕ}
    (hp : MissingValid F p) (hL : ∀ e ∈ L, e ∈ absent F) : MissingValid F (L.foldl mark p) := by
  induction L generalizing p with
  | nil => exact hp
  | cons e L ih =>
    exact ih (mark_valid hp (hL _ (by simp))) (fun x hx => hL x (by simp [hx]))

private theorem propagate_valid {F : Finset Triple} {u : ℕ} {p : ℕ × ℕ} {c : Constraint}
    (hu : flags u ⊆ covered F) (hp : MissingValid F p) (hc : SafePair F c) :
    ∃ q, propagate u c p = some q ∧ MissingValid F q := by
  have hit {l : List ℕ} (h : l.any (hasBit u)) : ∃ e ∈ l, e ∈ covered F := by
    obtain ⟨e,he,hf⟩ := List.any_eq_true.1 h
    exact ⟨e,he,hu (flags_mem.2 hf)⟩
  by_cases h₁ : c.1.any (hasBit u)
  · have h₂ : ¬c.2.any (hasBit u) := fun h => hc.consistent ⟨hit h₁,hit h⟩
    refine ⟨c.2.foldl mark p, by simp [propagate,h₁,h₂], mark_all_valid hp ?_⟩
    intro e he
    exact mem_sdiff.2 ⟨mem_range.2 (hc.rightBound e he),
      fun h => hc.consistent ⟨hit h₁, ⟨e,he,h⟩⟩⟩
  by_cases h₂ : c.2.any (hasBit u)
  · refine ⟨c.1.foldl mark p, by simp [propagate,h₁,h₂], mark_all_valid hp ?_⟩
    intro e he
    exact mem_sdiff.2 ⟨mem_range.2 (hc.leftBound e he),
      fun h => hc.consistent ⟨⟨e,he,h⟩,hit h₂⟩⟩
  exact ⟨p, by simp [propagate,h₁,h₂], hp⟩

private theorem propagate_list_valid {F : Finset Triple} {u : ℕ} {p : ℕ × ℕ}
    (hu : flags u ⊆ covered F) (hp : MissingValid F p) {cs : List Constraint}
    (hc : ∀ c ∈ cs, SafePair F c) :
    ∃ q, cs.foldlM (fun p c => propagate u c p) p = some q ∧ MissingValid F q := by
  induction cs generalizing p with
  | nil => exact ⟨p,rfl,hp⟩
  | cons c cs ih =>
    obtain ⟨q,hq,hq'⟩ := propagate_valid hu hp (hc c (by simp))
    obtain ⟨r,hr,hr'⟩ := ih hq' (fun c h => hc c (by simp [h]))
    exact ⟨r, by simpa [List.foldlM_cons,hq] using hr, hr'⟩

private theorem add_valid {F : Finset Triple} (hm : Model F) {s : SearchState} (hv : Valid F s)
    {t : Triple} (ht : t ∈ F) (ha : available s.used s.missing t = true) :
    ∃ s', addTriangle s t = some s' ∧ Valid F s' := by
  let u := s.used + (t.edges.map (fun e => 2^e)).sum
  let cs := s.constraints ++ s.selected.filterMap (direction t)
  have hflag := (edge_facts t (hm.sub ht)).2.2
  have hu : flags u = covered (t :: s.selected).toFinset := by
    have hdis := (available_iff hv t).1 ha
    have hdis' : Disjoint (flags s.used) (flags (t.edges.map (fun e => 2^e)).sum) := by
      rw [hflag]
      exact hdis.1.symm
    rw [show u = s.used + (t.edges.map (fun e => 2^e)).sum by rfl, flags_add hdis',
      hv.used,hflag,List.toFinset_cons]
    simp only [covered,biUnion_insert]
    exact union_comm _ _
  have hch : (t :: s.selected).toFinset ⊆ F := by
    simpa only [List.toFinset_cons,insert_subset_iff] using And.intro ht hv.chosen
  have hc : ∀ c ∈ cs, SafePair F c := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hv.rules c hc
    · obtain ⟨v, hvs, hvd⟩ := List.mem_filterMap.1 hc
      exact hm.order t ht v (hv.chosen (List.mem_toFinset.2 hvs)) c hvd
  have hu' : flags u ⊆ covered F := by rw [hu]; exact covered_mono hch
  have hp : MissingValid F (s.missing,s.omitted) := ⟨hv.missing,hv.omitted⟩
  obtain ⟨q,hq,hmq⟩ := propagate_list_valid hu' hp hc
  refine ⟨⟨u,q.1,q.2,t :: s.selected,cs⟩, ?_, ⟨hch,hu,hmq.1,hmq.2,hc⟩⟩
  unfold addTriangle
  change (do
    let (m,k) ← cs.foldlM (fun p c => propagate u c p) (s.missing,s.omitted)
    pure (⟨u,m,k,t :: s.selected,cs⟩ : SearchState)) = _
  rw [hq]
  cases q
  rfl

private theorem fold_none_if {α β : Type} {f : β → α → Option β} {xs : List α}
    {a : α} (ha : a ∈ xs) (hf : ∀ x, f x a = none) (y : β) : xs.foldlM f y = none := by
  induction xs generalizing y with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.1 ha with rfl | h
    · simp [List.foldlM_cons,hf]
    · cases hy : f y x with
      | none => simp [List.foldlM_cons,hy]
      | some z => simp [List.foldlM_cons,hy,ih h z]

theorem odd_partial_degree_bound {V E : Type*} [Fintype V] [DecidableEq E]
    (I : V → Finset E) {known full : Finset E} (hsub : known ⊆ full)
    (heven : ∀ v, Even ((full ∩ I v).card))
    (hend : ∀ e ∈ full \ known, (univ.filter fun v => e ∈ I v).card ≤ 2) :
    (univ.filter fun v => Odd ((known ∩ I v).card)).card ≤ 2 * (full.card-known.card) := by
  classical
  let M := full \ known
  have hforce (v : V) (hodd : Odd ((known ∩ I v).card)) : 1 ≤ (M ∩ I v).card := by
    by_contra! h
    have hzero : (M ∩ I v).card = 0 := by omega
    have hnone := card_eq_zero.mp hzero
    have hEq : known ∩ I v = full ∩ I v := by
      ext e
      constructor
      · intro he
        exact mem_inter.2 ⟨hsub (mem_inter.1 he).1,(mem_inter.1 he).2⟩
      · intro he
        obtain ⟨hf,hi⟩ := mem_inter.1 he
        by_cases hk : e ∈ known
        · exact mem_inter.2 ⟨hk,hi⟩
        · have hmem : e ∈ M ∩ I v := mem_inter.2 ⟨mem_sdiff.2 ⟨hf,hk⟩,hi⟩
          simp only [hnone,notMem_empty] at hmem
    rw [hEq] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (heven v)
  have hf (v : V) : (if Odd ((known ∩ I v).card) then 1 else 0) ≤ (M ∩ I v).card := by
    split
    · exact hforce v ‹_›
    · exact Nat.zero_le _
  calc
    (univ.filter fun v => Odd ((known ∩ I v).card)).card =
        ∑ v : V, if Odd ((known ∩ I v).card) then 1 else 0 := by
          simp
    _ ≤ ∑ v : V, (M ∩ I v).card := sum_le_sum fun v _ => hf v
    _ = ∑ e ∈ M, (univ.filter fun v => e ∈ I v).card := by
      have hi (v : V) : M ∩ I v = M.filter (fun e => e ∈ I v) := by
        ext e
        simp
      simp_rw [hi,card_eq_sum_ones,sum_filter]
      exact sum_comm
    _ ≤ ∑ _e ∈ M, 2 := sum_le_sum fun e he => hend e he
    _ = 2*(full.card-known.card) := by
      simp [M,card_sdiff_of_subset hsub,Nat.mul_comm]

private def vertexEdges (v : Fin 9) : Finset ℕ :=
  ((univ : Finset (Fin 9)).erase v).image (fun w => pairIndex v.val w.val)

private theorem vertexEdges_card :
    ∀ v : Fin 9, (vertexEdges v).card = 8 := by decide +kernel

private theorem vertexEdges_small :
    ∀ v : Fin 9, ∀ e ∈ vertexEdges v, e < 36 := by decide +kernel

private theorem vertexEdges_double :
    ∀ e : Fin 36, ((univ : Finset (Fin 9)).filter (fun v => e.val ∈ vertexEdges v)).card = 2 := by
  decide +kernel

private theorem triangle_vertex_even :
    ∀ t ∈ triples.toFinset, ∀ v : Fin 9, ((t.edges.toFinset ∩ vertexEdges v).card % 2) = 0 := by
  decide +kernel

private theorem even_absent {F : Finset Triple} (hm : Model F) (v : Fin 9) :
    Even ((absent F ∩ vertexEdges v).card) := by
  classical
  have heq : covered F ∩ vertexEdges v = F.biUnion (fun t => t.edges.toFinset ∩ vertexEdges v) := by
    ext e
    simp only [mem_inter, covered_mem, mem_biUnion, List.mem_toFinset]
    constructor
    · rintro ⟨⟨t,ht,hte⟩,hv⟩
      exact ⟨t,ht,hte,hv⟩
    · rintro ⟨t,ht,hte,hv⟩
      exact ⟨⟨t,ht,hte⟩,hv⟩
  have hp : Even ((covered F ∩ vertexEdges v).card) := by
    rw [heq,card_biUnion]
    · apply Finset.even_sum
      intro t ht
      exact Nat.even_iff.mpr (triangle_vertex_even t (hm.sub ht) v)
    · intro t ht t' ht' hn
      apply disjoint_left.2
      intro e he he'
      exact disjoint_left.1 (hm.separate t ht t' ht' hn)
        (mem_inter.1 he).1 (mem_inter.1 he').1
  have hf : absent F ∩ vertexEdges v = vertexEdges v \ (covered F ∩ vertexEdges v) := by
    ext e
    simp only [absent,mem_inter,mem_sdiff,mem_range]
    constructor
    · rintro ⟨⟨_,hn⟩,hv⟩
      exact ⟨hv,fun h => hn h.1⟩
    · rintro ⟨hv,hn⟩
      exact ⟨⟨vertexEdges_small v e hv,fun hc => hn ⟨hc,hv⟩⟩,hv⟩
  rw [hf, card_sdiff_of_subset (fun e he => (mem_inter.1 he).2), vertexEdges_card]
  have hp' := Nat.even_iff.mp hp
  have hb : (covered F ∩ vertexEdges v).card ≤ 8 := by
    simpa only [vertexEdges_card] using card_le_card
      (show covered F ∩ vertexEdges v ⊆ vertexEdges v from inter_subset_right)
  apply Nat.even_iff.mpr
  omega

private theorem vertex_local :
    ∀ v : Fin 9, (localEdges v).Nodup ∧ (localEdges v).toFinset = vertexEdges v := by
  decide +kernel

private theorem incidentCount (m : ℕ) (v : Fin 9) :
    (localEdges v).countP (hasBit m) = ((flags m) ∩ vertexEdges v).card := by
  have hn := (vertex_local v).1.filter (hasBit m)
  have he : ((localEdges v).filter (hasBit m)).toFinset = (flags m) ∩ vertexEdges v := by
    ext e
    simp only [List.mem_toFinset, List.mem_filter, mem_inter, flags_mem,
      ← (vertex_local v).2, and_comm]
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup hn, he]

private theorem oddCount_eq (m : ℕ) :
    oddCount m = (univ.filter fun v => Odd ((flags m) ∩ vertexEdges v).card).card := by
  unfold oddCount
  simp_rw [incidentCount, ← Nat.odd_iff]
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange 9).filter _)]
  congr 1
  ext v
  simp

private theorem parity_limit {F : Finset Triple} (hm : Model F) {s : SearchState}
    (hv : Valid F s) : oddCount s.missing ≤ 2*(9-s.omitted) := by
  have h := odd_partial_degree_bound vertexEdges hv.missing (even_absent hm) (fun e he => by
    have helt := mem_range.1 (mem_sdiff.1 (mem_sdiff.1 he).1).1
    exact (vertexEdges_double ⟨e,helt⟩).le)
  rw [absent_card hm,hv.omitted] at h
  exact (oddCount_eq s.missing).trans_le h

private theorem inspectState_eq (s : SearchState) : inspectState s = s := by
  rcases s with ⟨u,m,k,a,l⟩
  cases u <;> cases m <;> cases k <;> rfl

private theorem overBudget_false {F : Finset Triple} {s : SearchState}
    (hm : Model F) (hv : Valid F s) : overBudget s = false := by
  have hb := card_le_card hv.missing
  rw [hv.omitted,absent_card hm] at hb
  simp [overBudget, Nat.not_lt.mpr hb, Nat.not_lt.mpr (parity_limit hm hv)]

private theorem has_viable {F : Finset Triple} (hm : Model F) {s : SearchState}
    (hv : Valid F s) {e : ℕ} (he : e < 36) (hfree : hasBit (s.used+s.missing) e = false)
    (hcovered : e ∈ covered F) : ∃ t ∈ viable s e, Valid F t := by
  obtain ⟨t,ht,hF⟩ := has_choice hm hv he hfree hcovered
  obtain ⟨s', hs', hv'⟩ := add_valid hm hv hF (List.mem_filter.1 ht).2
  refine ⟨s', List.mem_filterMap.2 ⟨t, ht, ?_⟩, hv'⟩
  simp [hs',inspectState_eq,overBudget_false hm hv']

private theorem verify_rejects {F : Finset Triple} (hm : Model F) (fuel : ℕ)
    (s : SearchState) (hv : Valid F s) (cert : List ℕ) : verify fuel s cert = none := by
  induction fuel generalizing s cert with
  | zero => rfl
  | succ fuel ih =>
    have hb : s.omitted ≤ 9 := by
      have h := card_le_card hv.missing
      rwa [hv.omitted,absent_card hm] at h
    change verifyStep (verify fuel) s cert = none
    unfold verifyStep
    have hsame : inspectState s = s := by
      rcases s with ⟨u,m,k,a,l⟩
      cases u <;> cases m <;> cases k <;> rfl
    rw [hsame]
    simp only [Nat.not_lt.mpr hb,if_false]
    split
    · rfl
    cases cert with
    | nil => rfl
    | cons c rest =>
      simp only []
      by_cases hp : c = 72
      · simp [hp, Nat.not_lt.mpr (parity_limit hm hv)]
      simp only [hp, if_false]
      let e := (c) % 36
      have he : e < 36 := Nat.mod_lt _ (by decide)
      by_cases hh : hasBit (s.used + s.missing) e = true
      · simp [e,hh]
      have hfree : hasBit (s.used+s.missing) e = false := by simpa using hh
      simp only [e] at hfree
      simp only [hfree,Bool.false_eq_true,if_false]
      split
      · rename_i hf
        by_cases h : (viable s e).isEmpty = true
        · have hn : e ∉ covered F := by
            intro hc
            obtain ⟨t,ht,_⟩ := has_viable hm hv he hfree hc
            simp [List.isEmpty_iff.mp h] at ht
          have hn' := ih (omitEdge s e) (valid_omit hv he hfree hn) rest
          simpa [e,h] using hn'
        · simp [← show e = (c)%36 by rfl,h]
      · by_cases hcov : e ∈ covered F
        · obtain ⟨t,ht,hvt⟩ := has_viable hm hv he hfree hcov
          have hc := fold_none_if ht (f := fun txt t => verify fuel t txt) (ih t hvt) rest
          simp [e,hc]

        · have hroom := unused_miss_room hm hv he hfree hcov
          have hs' := valid_omit hv he hfree hcov
          have kk : ∀ x, verify fuel (omitEdge s e) x = none := ih _ hs'
          simp only [← show e = (c)%36 by rfl]
          generalize (viable s e).foldlM (fun txt t => verify fuel t txt) rest = result
          cases result <;> simp [hroom,kk]

theorem no_model_of_success (cert : List ℕ) (result : verify 38 init cert = some [])
    (F : Finset Triple) : ¬ Model F := by
  intro h
  have rejected := verify_rejects h 38 init (init_valid F) cert
  rw [result] at rejected
  contradiction

private def advanceForced (s : SearchState) (e : ℕ) : Option SearchState :=
  if e < 36 ∧ hasBit (s.used + s.missing) e = false ∧ (viable s e).isEmpty then
    some (omitEdge s e)
  else none

private def forceAll (s : SearchState) (es : List ℕ) : Option SearchState :=
  es.foldlM advanceForced s

private theorem advanceForced_valid {F : Finset Triple} (hm : Model F) {s s' : SearchState}
    (hv : Valid F s) {e : ℕ} (h : advanceForced s e = some s') : Valid F s' := by
  unfold advanceForced at h
  split at h
  · rename_i hb
    injection h with he
    subst s'
    obtain ⟨hr,hfree,hzero⟩ := hb
    apply valid_omit hv hr hfree
    intro hc
    obtain ⟨t,ht,_⟩ := has_viable hm hv hr hfree hc
    simp [List.isEmpty_iff.mp hzero] at ht
  · contradiction

private theorem forceAll_valid {F : Finset Triple} (hm : Model F)
    {s s' : SearchState} (hv : Valid F s) {es : List ℕ}
    (h : forceAll s es = some s') : Valid F s' := by
  induction es generalizing s with
  | nil =>
    change some s = some s' at h
    injection h with he
    exact he ▸ hv
  | cons e es ih =>
    unfold forceAll at h
    simp only [List.foldlM_cons] at h
    cases ho : advanceForced s e with
    | none => simp [ho] at h
    | some q =>
      have hnext : forceAll q es = some s' := by simpa [ho,forceAll] using h
      exact ih (advanceForced_valid hm hv ho) hnext

private def childStates (s : SearchState) (e : ℕ) : List SearchState :=
  viable s e ++ if s.omitted < 9 then [omitEdge s e] else []

private theorem some_child_valid {F : Finset Triple} (hm : Model F) {s : SearchState} (hv : Valid F s)
    {e : ℕ} (he : e < 36) (hfree : hasBit (s.used + s.missing) e = false) :
    ∃ s' ∈ childStates s e, Valid F s' := by
  by_cases h : e ∈ covered F
  · obtain ⟨t,ht,hvt⟩ := has_viable hm hv he hfree h
    exact ⟨t,List.mem_append_left _ ht,hvt⟩
  · have hroom := unused_miss_room hm hv he hfree h
    refine ⟨omitEdge s e,?_,valid_omit hv he hfree h⟩
    apply List.mem_append_right
    simp [hroom]

private theorem certificate_rejects_at {F : Finset Triple} (hm : Model F)
    {s : SearchState} (hv : Valid F s) {cert : List ℕ}
    (h : verify 38 s cert = some []) : False := by
  rw [verify_rejects hm 38 s hv cert] at h
  contradiction

private structure DeadState where
  state : SearchState
  excluded : ∀ (F : Finset Triple), Model F → ¬ Valid F state

private def DeadState.leaf (state : SearchState) (cert : List ℕ)
    (h : verify 38 state cert = some []) : DeadState :=
  ⟨state, fun _ hm hv => certificate_rejects_at hm hv h⟩

private def DeadState.fork (s n : SearchState) (es : List ℕ) (e : ℕ)
    (xs : List DeadState) (hn : forceAll s es = some n) (he : e < 36)
    (hf : hasBit (n.used + n.missing) e = false)
    (hc : childStates n e = xs.map DeadState.state) : DeadState := by
  refine ⟨s, ?_⟩
  intro F hm hv
  have hn' := forceAll_valid hm hv hn
  obtain ⟨s',hs',hvs'⟩ := some_child_valid hm hn' he hf
  rw [hc] at hs'
  obtain ⟨q, _, rfl⟩ := List.mem_map.1 hs'
  exact q.excluded F hm hvs'

private def decodeTape : ℕ → ℕ → List ℕ
  | 0, _ => []
  | len + 1, n => (n % 128) :: decodeTape len (n / 128)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead4 : DeadState :=
  DeadState.leaf ⟨35435577855,0,0,[c27,c22,c13,c0],[([],[9,15,10,16]),([],[22,26,23,27]),([],[11,17,12,18]),([],[31,33,32,34]),([],[24,28,25,29]),([],[13,19,14,20])]⟩ (decodeTape 86 7056414720287263511315716421077294885054780367411401766532145039039202751134793655647538146317376889911918104767300968502153174336032304327471564473413866976355234799647212473981065) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead6 : DeadState :=
  DeadState.leaf ⟨1080036159,8393920,5,[c35,c22,c13,c0],[([],[9,15,10,16]),([],[22,26,23,27]),([],[11,17,12,18]),([12,23],[0,2]),([10],[0,4,26]),([],[2,15,4,17])]⟩ (decodeTape 10 483463330620171557261) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead7 : DeadState :=
  DeadState.leaf ⟨1084232511,4197568,5,[c36,c22,c13,c0],[([],[9,15,10,16]),([],[22,26,23,27]),([],[11,17,12,18]),([11,22],[0,2]),([10],[0,5,27]),([],[2,15,5,18])]⟩ (decodeTape 10 483463330620171557261) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead8 : DeadState :=
  DeadState.leaf ⟨1092625215,1216,3,[c37,c22,c13,c0],[([],[9,15,10,16]),([],[22,26,23,27]),([],[11,17,12,18]),([10],[0,6,28]),([],[2,15,6,19])]⟩ (decodeTape 19 4374112421805952833186285280468897978763) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead9 : DeadState :=
  DeadState.leaf ⟨1109410623,1216,3,[c38,c22,c13,c0],[([],[9,15,10,16]),([],[22,26,23,27]),([],[11,17,12,18]),([10],[0,7,29]),([],[2,15,7,20])]⟩ (decodeTape 19 4629308579224349218940532446285058103691) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead10 : DeadState :=
  DeadState.leaf ⟨1075839295,704,3,[c22,c13,c0],[([],[9,15,10,16]),([],[22,26,23,27]),([],[11,17,12,18])]⟩ (decodeTape 69 9830731536783612044745925190077975916253737904506293767424343695714374297194846970769584097486376794686033086629376843062756412284501541568453899) (by decide +kernel)

private def dead5 : DeadState :=
  DeadState.fork ⟨1075839295,64,1,[c22,c13,c0],[([],[9,15,10,16]),([],[22,26,23,27]),([],[11,17,12,18])]⟩ ⟨1075839295,192,2,[c22,c13,c0],[([],[9,15,10,16]),([],[22,26,23,27]),([],[11,17,12,18])]⟩ [7] 9 [dead6, dead7, dead8, dead9, dead10]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead3 : DeadState :=
  DeadState.fork ⟨1075839295,0,0,[c22,c13,c0],[([],[9,15,10,16]),([],[22,26,23,27]),([],[11,17,12,18])]⟩ ⟨1075839295,0,0,[c22,c13,c0],[([],[9,15,10,16]),([],[22,26,23,27]),([],[11,17,12,18])]⟩ [] 6 [dead4, dead5]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead12 : DeadState :=
  DeadState.leaf ⟨19329450495,0,0,[c26,c23,c13,c0],[([],[9,15,10,16]),([],[22,26,24,28]),([],[11,17,13,19]),([33],[30,32,35]),([],[23,27,25,29]),([],[12,18,14,20])]⟩ (decodeTape 80 1574726711277264805982037995195376922294492652843012746549479046277602786348087397255681834005638998220391403067795182131986579843397587722575259048112182614395550734345) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead13 : DeadState :=
  DeadState.leaf ⟨2149581151,32,1,[c23,c13,c0],[([],[9,15,10,16]),([],[22,26,24,28]),([],[11,17,13,19])]⟩ (decodeTape 120 2885986454244244865559758917948367760640074648862388314466921682084046871813533894673578205652613392939929557737734220869440920473304462765796093351578724902161875315188486556794453818151621742932000303180551435379458078164671777632666255530513261593771) (by decide +kernel)

private def dead11 : DeadState :=
  DeadState.fork ⟨2149581151,0,0,[c23,c13,c0],[([],[9,15,10,16]),([],[22,26,24,28]),([],[11,17,13,19])]⟩ ⟨2149581151,0,0,[c23,c13,c0],[([],[9,15,10,16]),([],[22,26,24,28]),([],[11,17,13,19])]⟩ [] 5 [dead12, dead13]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead15 : DeadState :=
  DeadState.leaf ⟨12886999551,0,0,[c25,c24,c13,c0],[([],[9,15,10,16]),([],[22,26,25,29]),([],[11,17,14,20]),([34,35],[30,31]),([],[23,27,24,28]),([],[12,18,13,19])]⟩ (decodeTape 64 280302144865643179187243764689248669782772552699173953445755137151857927231827089466934074377153730671194824637423438418333532360038409) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead16 : DeadState :=
  DeadState.leaf ⟨4297064863,32,1,[c24,c13,c0],[([],[9,15,10,16]),([],[22,26,25,29]),([],[11,17,14,20])]⟩ (decodeTape 118 176146634172010806647389416081923488987752029302658893229899302577284826148988120248445641660293298795404529915292381077701750330809496128013006473812715777502882146770170258321011954821826380640103886435757830670598874694526833504853220750505739434) (by decide +kernel)

private def dead14 : DeadState :=
  DeadState.fork ⟨4297064863,0,0,[c24,c13,c0],[([],[9,15,10,16]),([],[22,26,25,29]),([],[11,17,14,20])]⟩ ⟨4297064863,0,0,[c24,c13,c0],[([],[9,15,10,16]),([],[22,26,25,29]),([],[11,17,14,20])]⟩ [] 5 [dead15, dead16]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead18 : DeadState :=
  DeadState.leaf ⟨8592032111,16,1,[c25,c13,c0],[([],[9,15,10,16]),([],[23,27,24,28]),([],[12,18,13,19])]⟩ (decodeTape 118 176146422473746182786545345975862302654228800583869876119427671655979962993928823417546915353833940439025374033629919569056178755329959830659390014758053384214978819521802351122517868652374079721182782840908606107867782009794030262674280483555312811) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead19 : DeadState :=
  DeadState.leaf ⟨17181966767,16,1,[c26,c13,c0],[([],[9,15,10,16]),([],[23,27,25,29]),([],[12,18,14,20])]⟩ (decodeTape 116 10751124418675294320229865712796536211664210056371023042142997011049448637196725145707607310571748017934193871630563662379328276194257254899541734992882543859532638713970868202302025291481585949839525469693923149273306713928683136310656194774186) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead21 : DeadState :=
  DeadState.leaf ⟨34361835983,48,2,[c27,c13,c0],[([],[9,15,10,16]),([],[24,28,25,29]),([],[13,19,14,20])]⟩ (decodeTape 113 5227486115456432191618212230985896988825431200993203424499603341830382041406557640428238759653167091646771825824633292353973367457685199732807119500122655267921638453195261023297525007698701587477031702987290100369139088544465892095608457) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead22 : DeadState :=
  DeadState.leaf ⟨2097423,112,3,[c13,c0],[([],[9,15,10,16])]⟩ (decodeTape 57 730069530250551150999270083435421069404493498566782951400829063207445271589773327093041497129077417320533629093536400555) (by decide +kernel)

private def dead20 : DeadState :=
  DeadState.fork ⟨2097423,48,2,[c13,c0],[([],[9,15,10,16])]⟩ ⟨2097423,48,2,[c13,c0],[([],[9,15,10,16])]⟩ [] 6 [dead21, dead22]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead17 : DeadState :=
  DeadState.fork ⟨2097423,16,1,[c13,c0],[([],[9,15,10,16])]⟩ ⟨2097423,16,1,[c13,c0],[([],[9,15,10,16])]⟩ [] 5 [dead18, dead19, dead20]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead2 : DeadState :=
  DeadState.fork ⟨2097423,0,0,[c13,c0],[([],[9,15,10,16])]⟩ ⟨2097423,0,0,[c13,c0],[([],[9,15,10,16])]⟩ [] 4 [dead3, dead11, dead14, dead17]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead25 : DeadState :=
  DeadState.leaf ⟨34498150911,0,0,[c27,c19,c14,c0],[([],[9,15,11,17]),([26],[21,23,30]),([],[10,16,12,18]),([],[28,33,29,34]),([],[24,31,25,32]),([],[13,19,14,20])]⟩ (decodeTape 65 34458934262526912500108275373499286068191669080430847082633181823380688567608238746082100108892063572667436151493014427176562265852516489) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead26 : DeadState :=
  DeadState.leaf ⟨138412351,64,1,[c19,c14,c0],[([],[9,15,11,17]),([26],[21,23,30]),([],[10,16,12,18])]⟩ (decodeTape 115 82313634809825526781023119718640962094055028056009120542875633517537637352723739783944862505307734774564939810958707425435684668716018653853958543190073596197198513670257058143044442072357242128015425003129223153872774587894528713642339372331) (by decide +kernel)

private def dead24 : DeadState :=
  DeadState.fork ⟨138412351,0,0,[c19,c14,c0],[([],[9,15,11,17]),([26],[21,23,30]),([],[10,16,12,18])]⟩ ⟨138412351,0,0,[c19,c14,c0],[([],[9,15,11,17]),([26],[21,23,30]),([],[10,16,12,18])]⟩ [] 6 [dead25, dead26]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead28 : DeadState :=
  DeadState.leaf ⟨17452499455,0,0,[c26,c20,c14,c0],[([],[9,15,11,17]),([26],[21,24,31]),([],[10,16,13,19]),([33],[27,29,35]),([],[23,30,25,32]),([],[12,18,14,20])]⟩ (decodeTape 61 136428625505422368904093123578430888108494553288645780992440234735430012483509379740400281617059434416103647157989210118891018249) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead29 : DeadState :=
  DeadState.leaf ⟨272630111,32,1,[c20,c14,c0],[([],[9,15,11,17]),([26],[21,24,31]),([],[10,16,13,19])]⟩ (decodeTape 91 220004978279118187983501112977167349252079347324162627998543114709914271132618406584715410245396480238573922689116192213160577744528032965245571602040528873943298876229641523421835238247746859) (by decide +kernel)

private def dead27 : DeadState :=
  DeadState.fork ⟨272630111,0,0,[c20,c14,c0],[([],[9,15,11,17]),([26],[21,24,31]),([],[10,16,13,19])]⟩ ⟨272630111,0,0,[c20,c14,c0],[([],[9,15,11,17]),([26],[21,24,31]),([],[10,16,13,19])]⟩ [] 5 [dead28, dead29]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead31 : DeadState :=
  DeadState.leaf ⟨9131000319,0,0,[c25,c21,c14,c0],[([],[9,15,11,17]),([26],[21,25,32]),([],[10,16,14,20]),([34,35],[27,28]),([],[23,30,24,31]),([],[12,18,13,19])]⟩ (decodeTape 50 902808928749132610950373767832986117632126322166950837944809773628160086996091891688233082132379546179593) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead32 : DeadState :=
  DeadState.leaf ⟨541065631,32,1,[c21,c14,c0],[([],[9,15,11,17]),([26],[21,25,32]),([],[10,16,14,20])]⟩ (decodeTape 86 6402987596647419428861555902936482641717262946135874989490941663860260191653408259562197618410992030289449840675943912175967889904233922894583645387856181968986833730710067200363818) (by decide +kernel)

private def dead30 : DeadState :=
  DeadState.fork ⟨541065631,0,0,[c21,c14,c0],[([],[9,15,11,17]),([26],[21,25,32]),([],[10,16,14,20])]⟩ ⟨541065631,0,0,[c21,c14,c0],[([],[9,15,11,17]),([26],[21,25,32]),([],[10,16,14,20])]⟩ [] 5 [dead31, dead32]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead34 : DeadState :=
  DeadState.leaf ⟨8594129271,8,1,[c25,c14,c0],[([],[9,15,11,17]),([],[23,30,24,31]),([],[12,18,13,19])]⟩ (decodeTape 117 1348416654046319724921713005335243500926608320342527053278891050616515748213692445773208606796234414635552871414149680136329340713380736760467698125954826753743699720506379773148980092947653232049608699946721610133009846937447314723608088562304171) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead35 : DeadState :=
  DeadState.leaf ⟨17184063927,8,1,[c26,c14,c0],[([],[9,15,11,17]),([],[23,30,25,32]),([],[12,18,14,20])]⟩ (decodeTape 115 82300821176029388555879786196816156684201372349494132134927225676126223376893950352476996172220820290185959416416358283165551088854165788784856724258334471481074638875953258863951634229241320804964053162794188868003123985794672242527819728042) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead37 : DeadState :=
  DeadState.leaf ⟨34363933143,40,2,[c27,c14,c0],[([],[9,15,11,17]),([],[24,31,25,32]),([],[13,19,14,20])]⟩ (decodeTape 112 38449006738374661067527027844774427471909208742674100723936322790342316132747600464722492629753280537230893478153923125678957802287967233316246876496884861718631443371324666547536703874756510185637692745669042434311604314738049676002953) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead38 : DeadState :=
  DeadState.leaf ⟨4194583,104,3,[c14,c0],[([],[9,15,11,17])]⟩ (decodeTape 48 79154297076311925618088937245500602801643496793952992693395896033022400035055406485530243977528001707) (by decide +kernel)

private def dead36 : DeadState :=
  DeadState.fork ⟨4194583,40,2,[c14,c0],[([],[9,15,11,17])]⟩ ⟨4194583,40,2,[c14,c0],[([],[9,15,11,17])]⟩ [] 6 [dead37, dead38]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead33 : DeadState :=
  DeadState.fork ⟨4194583,8,1,[c14,c0],[([],[9,15,11,17])]⟩ ⟨4194583,8,1,[c14,c0],[([],[9,15,11,17])]⟩ [] 5 [dead34, dead35, dead36]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead23 : DeadState :=
  DeadState.fork ⟨4194583,0,0,[c14,c0],[([],[9,15,11,17])]⟩ ⟨4194583,0,0,[c14,c0],[([],[9,15,11,17])]⟩ [] 3 [dead24, dead27, dead30, dead33]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead40 : DeadState :=
  DeadState.leaf ⟨75497791,0,0,[c18,c15,c0],[([],[9,15,12,18]),([27,30],[21,22]),([],[10,16,11,17])]⟩ (decodeTape 119 32387866589385152363367213896553929886179979551063622892397252379074173633718901653419029109732899679663038462090490749435164733457477374674682784764042199266297178446508897600508929900012115498233961030884272480696295975451724011353870753702569854086) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead42 : DeadState :=
  DeadState.leaf ⟨4571791871,0,0,[c24,c20,c15,c0],[([],[9,15,12,18]),([27],[21,24,33]),([],[10,16,13,19]),([31],[26,29,35]),([30],[22,25,34]),([],[11,17,14,20])]⟩ (decodeTape 52 14791639266471185073899434672198828152622373667289845409249551224522751012212444763878731727323023474850305929) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead43 : DeadState :=
  DeadState.leaf ⟨276824431,16,1,[c20,c15,c0],[([],[9,15,12,18]),([27],[21,24,33]),([],[10,16,13,19])]⟩ (decodeTape 82 24339710987605204879688256252516317740694381869833271329833042636275333217486256260451368742690118061067792753118646365438354102673784294782644388354525235636420013447712171) (by decide +kernel)

private def dead41 : DeadState :=
  DeadState.fork ⟨276824431,0,0,[c20,c15,c0],[([],[9,15,12,18]),([27],[21,24,33]),([],[10,16,13,19])]⟩ ⟨276824431,0,0,[c20,c15,c0],[([],[9,15,12,18]),([27],[21,24,33]),([],[10,16,13,19])]⟩ [] 4 [dead42, dead43]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead45 : DeadState :=
  DeadState.leaf ⟨2692743679,0,0,[c23,c21,c15,c0],[([],[9,15,12,18]),([27],[21,25,34]),([],[10,16,14,20]),([32,35],[26,28]),([30],[22,24,33]),([],[11,17,13,19])]⟩ (decodeTape 46 3363229385875259881777662975656611906859162744746331258293600745171696214061341338559873112889225) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead46 : DeadState :=
  DeadState.leaf ⟨545259951,16,1,[c21,c15,c0],[([],[9,15,12,18]),([27],[21,25,34]),([],[10,16,14,20])]⟩ (decodeTape 82 24339710987605204879688662229676409555243630120322617385852090062353830384415416702082672082669581192130426063980280298098283004373887047018022488111275052009618486931983786) (by decide +kernel)

private def dead44 : DeadState :=
  DeadState.fork ⟨545259951,0,0,[c21,c15,c0],[([],[9,15,12,18]),([27],[21,25,34]),([],[10,16,14,20])]⟩ ⟨545259951,0,0,[c21,c15,c0],[([],[9,15,12,18]),([27],[21,25,34]),([],[10,16,14,20])]⟩ [] 4 [dead45, dead46]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead48 : DeadState :=
  DeadState.leaf ⟨2155872631,8,1,[c23,c15,c0],[([],[9,15,12,18]),([30],[22,24,33]),([],[11,17,13,19])]⟩ (decodeTape 81 190153993890231180938621976712948740997307756597422779673662092472783902780705095138785471316721713314779485063256864031980030991983407346097022780699566028361348999286571) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead49 : DeadState :=
  DeadState.leaf ⟨4303356343,8,1,[c24,c15,c0],[([],[9,15,12,18]),([30],[22,25,34]),([],[11,17,14,20])]⟩ (decodeTape 76 5534209598024052833884612708656393835841350644233553863650786795448944224543408449650745828940467361609654951248085641164657133159760747740955088515414568455978) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead51 : DeadState :=
  DeadState.leaf ⟨34368127463,24,2,[c27,c15,c0],[([],[9,15,12,18]),([],[24,33,25,34]),([],[13,19,14,20])]⟩ (decodeTape 100 1947956481388367955534091679459415275830719682546684780853779272722238729553868012418872984526346779049483668828816099177547750578182840452936664448216583495361389384396627028014742429961542181590865338126091913) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead52 : DeadState :=
  DeadState.leaf ⟨8388903,88,3,[c15,c0],[([],[9,15,12,18])]⟩ (decodeTape 41 140606276986662943764339760130992446474232197255193578754398934831637532621571529426091) (by decide +kernel)

private def dead50 : DeadState :=
  DeadState.fork ⟨8388903,24,2,[c15,c0],[([],[9,15,12,18])]⟩ ⟨8388903,24,2,[c15,c0],[([],[9,15,12,18])]⟩ [] 6 [dead51, dead52]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead47 : DeadState :=
  DeadState.fork ⟨8388903,8,1,[c15,c0],[([],[9,15,12,18])]⟩ ⟨8388903,8,1,[c15,c0],[([],[9,15,12,18])]⟩ [] 4 [dead48, dead49, dead50]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead39 : DeadState :=
  DeadState.fork ⟨8388903,0,0,[c15,c0],[([],[9,15,12,18])]⟩ ⟨8388903,0,0,[c15,c0],[([],[9,15,12,18])]⟩ [] 3 [dead40, dead41, dead44, dead47]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead54 : DeadState :=
  DeadState.leaf ⟨83886431,0,0,[c18,c16,c0],[([],[9,15,13,19]),([28,31],[21,22]),([],[10,16,11,17])]⟩ (decodeTape 107 1674413457792661051955626229248969692152610048893588788790474145962244562262962859568167585615651615201220748534936923190245396440435603793724504634657745309269833275261467360717715666134533593483724447945156259321060430447749) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead55 : DeadState :=
  DeadState.leaf ⟨150995311,0,0,[c19,c16,c0],[([],[9,15,13,19]),([28,33],[21,23]),([],[10,16,12,18])]⟩ (decodeTape 83 4475309453999132009072825042239506854830344440669163617916768509200781071661373330259869553545563716485103575446059628381454905800320342467720850334640678127741860105543206020) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead56 : DeadState :=
  DeadState.leaf ⟨553648591,0,0,[c21,c16,c0],[([],[9,15,13,19]),([28],[21,25,35]),([],[10,16,14,20])]⟩ (decodeTape 115 82313634809825526871381649254534864623339780314792060733422211528504903411101427856971152635611322256997176768673996486707688672102470440337478681452396821872195969116686462610548490350342059742512866309700697289994751471424843676733961651332) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead58 : DeadState :=
  DeadState.leaf ⟨1090519415,8,1,[c22,c16,c0],[([],[9,15,13,19]),([31,33],[22,23]),([],[11,17,12,18])]⟩ (decodeTape 36 4092626432546696353442931397393707905373890175623085970084928391393696697131) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead59 : DeadState :=
  DeadState.leaf ⟨4311744983,8,1,[c24,c16,c0],[([],[9,15,13,19]),([31],[22,25,35]),([],[11,17,14,20])]⟩ (decodeTape 71 157846025822926531964956821363118358482847800421968602900706142692180923031130234299816451621187798355941718785498985927773361267345597567728561639337) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead60 : DeadState :=
  DeadState.leaf ⟨16777543,24,2,[c16,c0],[([],[9,15,13,19])]⟩ (decodeTape 108 214324922546520906141788359699039041481470841216516315453879490619614086784837881424695085785953231887984033271475860522680324725401562680890316825150835647962794827680306668675110911451246174797006125353664915208992157076246661) (by decide +kernel)

private def dead57 : DeadState :=
  DeadState.fork ⟨16777543,8,1,[c16,c0],[([],[9,15,13,19])]⟩ ⟨16777543,8,1,[c16,c0],[([],[9,15,13,19])]⟩ [] 4 [dead58, dead59, dead60]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead53 : DeadState :=
  DeadState.fork ⟨16777543,0,0,[c16,c0],[([],[9,15,13,19])]⟩ ⟨16777543,0,0,[c16,c0],[([],[9,15,13,19])]⟩ [] 3 [dead54, dead55, dead56, dead57]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead62 : DeadState :=
  DeadState.leaf ⟨100663711,0,0,[c18,c17,c0],[([],[9,15,14,20]),([29,32],[21,22]),([],[10,16,11,17])]⟩ (decodeTape 80 2133806770590033259488800950802793588276076139603845109986140361812776093433215328112637172609791999045100073801063400353857395657622478490116940435748910258111671698565) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead63 : DeadState :=
  DeadState.leaf ⟨167772591,0,0,[c19,c17,c0],[([],[9,15,14,20]),([29,34],[21,23]),([],[10,16,12,18])]⟩ (decodeTape 70 1807174409770010307623399782049143769035453124345684999614943407039041743890392456984135528641620901675433111463217976400999563795508991531986699396) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead64 : DeadState :=
  DeadState.leaf ⟨301990351,0,0,[c20,c17,c0],[([],[9,15,14,20]),([29,35],[21,24]),([],[10,16,13,19])]⟩ (decodeTape 69 14120107122021703052239481532572510707609278070857516532259861070793613999231098436277568316244280862203494393085913113667350759871630294158918788) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead65 : DeadState :=
  DeadState.leaf ⟨33554823,8,1,[c17,c0],[([],[9,15,14,20])]⟩ (decodeTape 125 142812352970914337998199296445643889703742355266930058667502980678565895823961167448116662387870888495890969026015775222029789056302524378410181488865603069902333122398946803617956387182643624439465726017639978873131027430450493703873734611543160398460524683433220) (by decide +kernel)

private def dead61 : DeadState :=
  DeadState.fork ⟨33554823,0,0,[c17,c0],[([],[9,15,14,20])]⟩ ⟨33554823,0,0,[c17,c0],[([],[9,15,14,20])]⟩ [] 3 [dead62, dead63, dead64, dead65]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead68 : DeadState :=
  DeadState.leaf ⟨8657043835,4,1,[c25,c18,c0],[([],[10,16,11,17]),([],[27,30,28,31]),([],[12,18,13,19])]⟩ (decodeTape 116 10534504395969834328880118205953517110579084850865603083516140923647280996341926560398877277683969038821699175016867060192604950104070137840939953350933775817476807023527672770066658432832404064114963735642122850917610605333660245502785573029163) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead69 : DeadState :=
  DeadState.leaf ⟨17246978491,4,1,[c26,c18,c0],[([],[10,16,11,17]),([],[27,30,29,32]),([],[12,18,14,20])]⟩ (decodeTape 114 642975121824330708369063890691352445417914452181754451061241811975146799503285561963721640522600372314365555881739932689969066005076462281886804841844558424188365356529797186554600097258275723299252303974009397913050590135706109970061919530) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead71 : DeadState :=
  DeadState.leaf ⟨34426847707,36,2,[c27,c18,c0],[([],[10,16,11,17]),([],[28,31,29,32]),([],[13,19,14,20])]⟩ (decodeTape 111 300384736549737231020745127603951636408952934200138710242563397663695605088861583175974674616750331240964051793901446882887375445445588011009966573083419043452036227136979234701229301544606271195856128511280147946505659052176756754058) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead72 : DeadState :=
  DeadState.leaf ⟨67109147,100,3,[c18,c0],[([],[10,16,11,17])]⟩ (decodeTape 79 16673655222615419715445653411553688831639668048245935367525060240183171185145773097639706964032028981424514821630122726900077834379025763092396156478502535353019974955) (by decide +kernel)

private def dead70 : DeadState :=
  DeadState.fork ⟨67109147,36,2,[c18,c0],[([],[10,16,11,17])]⟩ ⟨67109147,36,2,[c18,c0],[([],[10,16,11,17])]⟩ [] 6 [dead71, dead72]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead67 : DeadState :=
  DeadState.fork ⟨67109147,4,1,[c18,c0],[([],[10,16,11,17])]⟩ ⟨67109147,4,1,[c18,c0],[([],[10,16,11,17])]⟩ [] 5 [dead68, dead69, dead70]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead74 : DeadState :=
  DeadState.leaf ⟨2281701755,4,1,[c23,c19,c0],[([],[10,16,12,18]),([30],[26,28,33]),([],[11,17,13,19])]⟩ (decodeTape 66 4687657865841581709935935287140606781175950925443435575433602250030283762504767130441386576071736571693756922013272170947045098547386175275) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead75 : DeadState :=
  DeadState.leaf ⟨4429185467,4,1,[c24,c19,c0],[([],[10,16,12,18]),([30],[26,29,34]),([],[11,17,14,20])]⟩ (decodeTape 66 4687657866883933772522776025322653497650330662428589749029193346418528137308526372980105208007158768169623193936172415113934991160429498154) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead77 : DeadState :=
  DeadState.leaf ⟨34493956587,20,2,[c27,c19,c0],[([],[10,16,12,18]),([],[28,33,29,34]),([],[13,19,14,20])]⟩ (decodeTape 94 442987041787889343021944635364743604147691204345240195956467960642849345891846290582098744075921550407365400249080504025167407049495662300618351759021621762267302007668402488215574992327041673381514) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead78 : DeadState :=
  DeadState.leaf ⟨134218027,84,3,[c19,c0],[([],[10,16,12,18])]⟩ (decodeTape 82 35054166912052021731872305015614294779334168306790484911483707161134042323757014992277908655514414531543459787113835057901217053501255359383265867034545811918037205685945643) (by decide +kernel)

private def dead76 : DeadState :=
  DeadState.fork ⟨134218027,20,2,[c19,c0],[([],[10,16,12,18])]⟩ ⟨134218027,20,2,[c19,c0],[([],[10,16,12,18])]⟩ [] 6 [dead77, dead78]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead73 : DeadState :=
  DeadState.fork ⟨134218027,4,1,[c19,c0],[([],[10,16,12,18])]⟩ ⟨134218027,4,1,[c19,c0],[([],[10,16,12,18])]⟩ [] 4 [dead74, dead75, dead76]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead80 : DeadState :=
  DeadState.leaf ⟨1342177659,4,1,[c22,c20,c0],[([],[10,16,13,19]),([31,33],[26,27]),([],[11,17,12,18])]⟩ (decodeTape 38 45740553952520774882929356944630681821722536908669262919447865596922144217009451) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead81 : DeadState :=
  DeadState.leaf ⟨4563403227,4,1,[c24,c20,c0],[([],[10,16,13,19]),([31],[26,29,35]),([],[11,17,14,20])]⟩ (decodeTape 61 133700785786633879497536255079731253876391265540761353011282989318625391029616054940348163867824003152851319490492169293759483817) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead83 : DeadState :=
  DeadState.leaf ⟨17448305131,20,2,[c26,c20,c0],[([],[10,16,13,19]),([33],[27,29,35]),([],[12,18,14,20])]⟩ (decodeTape 60 1044373416090813855061573740474474858847267238782130453306008840847577916509754888100759903970722882199385950333788726670087969) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead84 : DeadState :=
  DeadState.leaf ⟨268435787,52,3,[c20,c0],[([],[10,16,13,19])]⟩ (decodeTape 81 273860679000406419659677167762950298254090362945758444042182446799255422644966119962568330016081866171177631497822382906951102324266848072630844824064562364427362166949163) (by decide +kernel)

private def dead82 : DeadState :=
  DeadState.fork ⟨268435787,20,2,[c20,c0],[([],[10,16,13,19])]⟩ ⟨268435787,20,2,[c20,c0],[([],[10,16,13,19])]⟩ [] 5 [dead83, dead84]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead79 : DeadState :=
  DeadState.fork ⟨268435787,4,1,[c20,c0],[([],[10,16,13,19])]⟩ ⟨268435787,4,1,[c20,c0],[([],[10,16,13,19])]⟩ [] 4 [dead80, dead81, dead82]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead86 : DeadState :=
  DeadState.leaf ⟨1610613179,4,1,[c22,c21,c0],[([],[10,16,14,20]),([32,34],[26,27]),([],[11,17,12,18])]⟩ (decodeTape 29 4959200796601345076066458632786295669216570725442099759254826) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead87 : DeadState :=
  DeadState.leaf ⟨2684355035,4,1,[c23,c21,c0],[([],[10,16,14,20]),([32,35],[26,28]),([],[11,17,13,19])]⟩ (decodeTape 25 18474462794109548360617363796480410912998230334054185) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead88 : DeadState :=
  DeadState.leaf ⟨536871307,20,2,[c21,c0],[([],[10,16,14,20])]⟩ (decodeTape 101 381706076392790607487321006792067025799787199782958519283814803317664563488582010646034611089481049557594070717118455555440014470514146710348419013411850976412746843500754719443735893679031870320940506983320002437) (by decide +kernel)

private def dead85 : DeadState :=
  DeadState.fork ⟨536871307,4,1,[c21,c0],[([],[10,16,14,20])]⟩ ⟨536871307,4,1,[c21,c0],[([],[10,16,14,20])]⟩ [] 4 [dead86, dead87, dead88]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead90 : DeadState :=
  DeadState.leaf ⟨1073742131,12,2,[c22,c0],[([],[11,17,12,18])]⟩ (decodeTape 128 298757333466658149711527356075184856604615920931046997610279580162830112314204614428772009948981705735679168123782003912766949087989587032593943898631120847562479932241478323362575232764429616554534177126185211570197903859387423226011461647622248746335744849923350414726) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead91 : DeadState :=
  DeadState.leaf ⟨2147483987,12,2,[c23,c0],[([],[11,17,13,19])]⟩ (decodeTape 89 19682618864230321078219035901641856544069077209311936371546092885400160953335855864129093356994832088849861617741946534937681161967478942050207969662488770474812029391554027120601407365765) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead92 : DeadState :=
  DeadState.leaf ⟨4294967699,12,2,[c24,c0],[([],[11,17,14,20])]⟩ (decodeTape 54 348048562410016218581862017648673503825583450484008889627521882041695709543837256838922806311903069787361656234245) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead93 : DeadState :=
  DeadState.leaf ⟨259,28,3,[c0],[]⟩ (decodeTape 98 181540270691405702653489998529642158679683843466507723104796160481155247833914391749268904401946953495636569323491166299425517454360580266892421955721898656924092108502384154310219268603913075400259775174021) (by decide +kernel)

private def dead89 : DeadState :=
  DeadState.fork ⟨259,12,2,[c0],[]⟩ ⟨259,12,2,[c0],[]⟩ [] 4 [dead90, dead91, dead92, dead93]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead66 : DeadState :=
  DeadState.fork ⟨259,4,1,[c0],[]⟩ ⟨259,4,1,[c0],[]⟩ [] 3 [dead67, dead73, dead79, dead85, dead89]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead1 : DeadState :=
  DeadState.fork ⟨259,0,0,[c0],[]⟩ ⟨259,0,0,[c0],[]⟩ [] 2 [dead2, dead23, dead39, dead53, dead61, dead66]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead97 : DeadState :=
  DeadState.leaf ⟨35433546495,0,0,[c27,c22,c8,c1],[([15],[8,10,21]),([],[17,26,18,27]),([],[11,22,12,23]),([],[31,33,32,34]),([],[19,28,20,29]),([],[13,24,14,25])]⟩ (decodeTape 78 99741160632272437501243114530739291768883995210805813059523820484190428033942741080681211463461170910867447842746492239097999107933701021909780676489696830512994440) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead98 : DeadState :=
  DeadState.leaf ⟨1073807935,64,1,[c22,c8,c1],[([15],[8,10,21]),([],[17,26,18,27]),([],[11,22,12,23])]⟩ (decodeTape 93 3604535212597555761614761433955478704349814330232527698473432875990206841586137819461011262136995263339716993547307261723040917821375089593424521410625815900106252275713947863928737447653243307051) (by decide +kernel)

private def dead96 : DeadState :=
  DeadState.fork ⟨1073807935,0,0,[c22,c8,c1],[([15],[8,10,21]),([],[17,26,18,27]),([],[11,22,12,23])]⟩ ⟨1073807935,0,0,[c22,c8,c1],[([15],[8,10,21]),([],[17,26,18,27]),([],[11,22,12,23])]⟩ [] 6 [dead97, dead98]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead100 : DeadState :=
  DeadState.leaf ⟨19327419135,0,0,[c26,c23,c8,c1],[([15],[8,10,21]),([],[17,26,19,28]),([],[11,22,13,24]),([33],[30,32,35]),([],[18,27,20,29]),([],[12,23,14,25])]⟩ (decodeTape 72 22266093650894294345558545652325011058669887433389304438767702725719420115028717637560866140949115477863555592545549769761475446218032646556421655926792) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead101 : DeadState :=
  DeadState.leaf ⟨2147549791,32,1,[c23,c8,c1],[([15],[8,10,21]),([],[17,26,19,28]),([],[11,22,13,24])]⟩ (decodeTape 87 819576419436906867501125155763104635444504446868544542921931960725277003890991441859980097389381666664526613172927893765029576099201956798937273006775491859937394134885325292819383339) (by decide +kernel)

private def dead99 : DeadState :=
  DeadState.fork ⟨2147549791,0,0,[c23,c8,c1],[([15],[8,10,21]),([],[17,26,19,28]),([],[11,22,13,24])]⟩ ⟨2147549791,0,0,[c23,c8,c1],[([15],[8,10,21]),([],[17,26,19,28]),([],[11,22,13,24])]⟩ [] 5 [dead100, dead101]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead103 : DeadState :=
  DeadState.leaf ⟨12884968191,0,0,[c25,c24,c8,c1],[([15],[8,10,21]),([],[17,26,20,29]),([],[11,22,14,25]),([34,35],[30,31]),([],[18,27,19,28]),([],[12,23,13,24])]⟩ (decodeTape 58 65054163580094452697974135465574464208273730779743091847012729035434917528454246345616116381936645382788346648502127581192) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead104 : DeadState :=
  DeadState.leaf ⟨4295033503,32,1,[c24,c8,c1],[([15],[8,10,21]),([],[17,26,20,29]),([],[11,22,14,25])]⟩ (decodeTape 87 819576420424281343727665794705991288130570767105052679257621644357658319273207539640574677286095862428413631733866432039243825825055799303602145546810249612608464133789964730823279658) (by decide +kernel)

private def dead102 : DeadState :=
  DeadState.fork ⟨4295033503,0,0,[c24,c8,c1],[([15],[8,10,21]),([],[17,26,20,29]),([],[11,22,14,25])]⟩ ⟨4295033503,0,0,[c24,c8,c1],[([15],[8,10,21]),([],[17,26,20,29]),([],[11,22,14,25])]⟩ [] 5 [dead103, dead104]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead106 : DeadState :=
  DeadState.leaf ⟨8590000751,16,1,[c25,c8,c1],[([15],[8,10,21]),([],[18,27,19,28]),([],[12,23,13,24])]⟩ (decodeTape 86 6401927773362804650633101125066632109458881800822219300511758442193724558061538343624802690700918769334999900039487571817227314472587084999142955746521560565456275333319467957683243) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead107 : DeadState :=
  DeadState.leaf ⟨17179935407,16,1,[c26,c8,c1],[([15],[8,10,21]),([],[18,27,20,29]),([],[12,23,14,25])]⟩ (decodeTape 86 6401927773313568302262154776475952198899826120797482587307619059258482150175343032453399320798308373606589762097477701484436918477542961055119003912581590401758471551890851509765162) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead108 : DeadState :=
  DeadState.leaf ⟨66063,48,2,[c8,c1],[([15],[8,10,21])]⟩ (decodeTape 102 48731845373001435981121813909744403621464924755786834526522620134299145216890432881181709836332661664734383113671972119279108219481626338387078917420681484302760021240179384113587895151457335395330959483176646558726) (by decide +kernel)

private def dead105 : DeadState :=
  DeadState.fork ⟨66063,16,1,[c8,c1],[([15],[8,10,21])]⟩ ⟨66063,16,1,[c8,c1],[([15],[8,10,21])]⟩ [] 5 [dead106, dead107, dead108]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead95 : DeadState :=
  DeadState.fork ⟨66063,0,0,[c8,c1],[([15],[8,10,21])]⟩ ⟨66063,0,0,[c8,c1],[([15],[8,10,21])]⟩ [] 4 [dead96, dead99, dead102, dead105]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead110 : DeadState :=
  DeadState.leaf ⟨134349375,0,0,[c19,c9,c1],[([15],[8,11,22]),([26],[16,18,30]),([],[10,21,12,23])]⟩ (decodeTape 119 32374479740613473163667909840985207484428435569100310801384024286262199309722299582713422884313690605014277258100959190930989967499086139889332407879357920561447295974990975345961454496281724698921581345177036416636348764538628191350280641710075429894) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead111 : DeadState :=
  DeadState.leaf ⟨268567135,0,0,[c20,c9,c1],[([15],[8,11,22]),([26],[16,19,31]),([],[10,21,13,24])]⟩ (decodeTape 98 181465233779316087222029704173579222327463197300764782802650052480954436970314464049189986728172420868017561200689981495011514485571243411322405768895484789720632251651326745997852171703097453799916750767109) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead112 : DeadState :=
  DeadState.leaf ⟨537002655,0,0,[c21,c9,c1],[([15],[8,11,22]),([26],[16,20,32]),([],[10,21,14,25])]⟩ (decodeTape 84 572603797408363807425071678473855085083988722011928328799435657353962982912687604642229660371105779379313753242752332786359718179658411160986392729881404546419301633486786135045) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead114 : DeadState :=
  DeadState.leaf ⟨8590066295,8,1,[c25,c9,c1],[([15],[8,11,22]),([],[18,30,19,31]),([],[12,23,13,24])]⟩ (decodeTape 72 19379578214492820615680223496251765595520024030055342141211016272695373431104021274975156258788756624292521119206977748722042885821039078815596135253035) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead115 : DeadState :=
  DeadState.leaf ⟨17180000951,8,1,[c26,c9,c1],[([15],[8,11,22]),([],[18,30,20,32]),([],[12,23,14,25])]⟩ (decodeTape 70 1182835584380665320781284794909562176565316969902644695029051063192878275870876373571905231357548877836324575598869681593827144357397894819987260458) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead116 : DeadState :=
  DeadState.leaf ⟨131607,40,2,[c9,c1],[([15],[8,11,22])]⟩ (decodeTape 87 1201332739188634015040611107770505545176536130141199052055208952101048622267322034397375451870870012896961946974949957480231670436926229265513309060024595001114723256463340345957237766) (by decide +kernel)

private def dead113 : DeadState :=
  DeadState.fork ⟨131607,8,1,[c9,c1],[([15],[8,11,22])]⟩ ⟨131607,8,1,[c9,c1],[([15],[8,11,22])]⟩ [] 5 [dead114, dead115, dead116]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead109 : DeadState :=
  DeadState.fork ⟨131607,0,0,[c9,c1],[([15],[8,11,22])]⟩ ⟨131607,0,0,[c9,c1],[([15],[8,11,22])]⟩ [] 3 [dead110, dead111, dead112, dead113]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead118 : DeadState :=
  DeadState.leaf ⟨67371583,0,0,[c18,c10,c1],[([15],[8,12,23]),([27,30],[16,17]),([],[10,21,11,22])]⟩ (decodeTape 92 41277478625825549343133189135772870024908502387955935301463782180420695334992760352022497061672577810121863818063112065290932095262044763650326201332580365808902224858475673275432419614165582854) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead119 : DeadState :=
  DeadState.leaf ⟨268698223,0,0,[c20,c10,c1],[([15],[8,12,23]),([27],[16,19,33]),([],[10,21,13,24])]⟩ (decodeTape 86 9381476682312949188780334825669634045576891785679956513653990663775498120193004068320950342940486803522573912342939193584189085025539263339589461756967866698150783203344455140361220) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead120 : DeadState :=
  DeadState.leaf ⟨537133743,0,0,[c21,c10,c1],[([15],[8,12,23]),([27],[16,20,34]),([],[10,21,14,25])]⟩ (decodeTape 75 62081405029820381393113809630493490155201662621464193456474120580584522315207855228254127721665762463453618747652021386539319680952568585927864329296778347524) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead122 : DeadState :=
  DeadState.leaf ⟨2147746423,8,1,[c23,c10,c1],[([15],[8,12,23]),([30],[17,19,33]),([],[11,22,13,24])]⟩ (decodeTape 44 294746593391561435249386976539716304296724132203555382988730755450592321280519710855396050859) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead123 : DeadState :=
  DeadState.leaf ⟨4295230135,8,1,[c24,c10,c1],[([15],[8,12,23]),([30],[17,20,34]),([],[11,22,14,25])]⟩ (decodeTape 38 67017616263810767288282376361097024598842635193671591003362381276084938459563946) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead124 : DeadState :=
  DeadState.leaf ⟨262695,24,2,[c10,c1],[([15],[8,12,23])]⟩ (decodeTape 68 110324988159905284843581743313528001242287910447937786086788301348359412628104878411734626024161337648398724496855401307204480284586218688955398) (by decide +kernel)

private def dead121 : DeadState :=
  DeadState.fork ⟨262695,8,1,[c10,c1],[([15],[8,12,23])]⟩ ⟨262695,8,1,[c10,c1],[([15],[8,12,23])]⟩ [] 4 [dead122, dead123, dead124]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead117 : DeadState :=
  DeadState.fork ⟨262695,0,0,[c10,c1],[([15],[8,12,23])]⟩ ⟨262695,0,0,[c10,c1],[([15],[8,12,23])]⟩ [] 3 [dead118, dead119, dead120, dead121]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead126 : DeadState :=
  DeadState.leaf ⟨67633759,0,0,[c18,c11,c1],[([15],[8,13,24]),([28,31],[16,17]),([],[10,21,11,22])]⟩ (decodeTape 86 9385412028179632962032352489727788355368526494071510136573693763685722285998601665352569371943916432847894869948289272693937787848423001239082375985558247404936640318194144747717637) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead127 : DeadState :=
  DeadState.leaf ⟨134742639,0,0,[c19,c11,c1],[([15],[8,13,24]),([28,33],[16,18]),([],[10,21,12,23])]⟩ (decodeTape 64 410992264167726249166408943002096906320275426783118444412546689087933114315919818397026618911779371040480111993098329255648015049016324) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead128 : DeadState :=
  DeadState.leaf ⟨537395919,0,0,[c21,c11,c1],[([15],[8,13,24]),([28],[16,20,35]),([],[10,21,14,25])]⟩ (decodeTape 72 29692034701215852865967674599280349990634698177114812066185830629119831003867496207507577992552519257996830532648223633325883845916756706954823269598212) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead129 : DeadState :=
  DeadState.leaf ⟨524871,8,1,[c11,c1],[([15],[8,13,24])]⟩ (decodeTape 121 530642806074152350355049879929247934405158675433042930762713361362936541240859584604072189124652259788183663016055877173264973225567272800467614888283752009765845987957759355598869100273308765184887295232642391348222822386513773549932796916259456706434436) (by decide +kernel)

private def dead125 : DeadState :=
  DeadState.fork ⟨524871,0,0,[c11,c1],[([15],[8,13,24])]⟩ ⟨524871,0,0,[c11,c1],[([15],[8,13,24])]⟩ [] 3 [dead126, dead127, dead128, dead129]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead131 : DeadState :=
  DeadState.leaf ⟨68158111,0,0,[c18,c12,c1],[([15],[8,14,25]),([29,32],[16,17]),([],[10,21,11,22])]⟩ (decodeTape 71 231347801314798321349008469461760402931757982867182281983528739075334480719490449250274200046142719456807046337109585933533723225684489216692948042757) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead132 : DeadState :=
  DeadState.leaf ⟨135266991,0,0,[c19,c12,c1],[([15],[8,14,25]),([29,34],[16,18]),([],[10,21,12,23])]⟩ (decodeTape 61 195934242113285414258911488928823286947126583660703778061069363577336726753599204819937099971285856211338304140552295658426188804) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead133 : DeadState :=
  DeadState.leaf ⟨269484751,0,0,[c20,c12,c1],[([15],[8,14,25]),([29,35],[16,19]),([],[10,21,13,24])]⟩ (decodeTape 60 1530915421222843405564639442659533762505217650042165035846572944441272478001439846146942928606409905321364492234728010645488644) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead134 : DeadState :=
  DeadState.leaf ⟨1049223,8,1,[c12,c1],[([15],[8,14,25])]⟩ (decodeTape 85 73513481140520559067008303347968051641960796980336597776346829192042620101650105485412318644480321016640242117514662483692220940519321910412276146673090381108917876154336102601988) (by decide +kernel)

private def dead130 : DeadState :=
  DeadState.fork ⟨1049223,0,0,[c12,c1],[([15],[8,14,25])]⟩ ⟨1049223,0,0,[c12,c1],[([15],[8,14,25])]⟩ [] 3 [dead131, dead132, dead133, dead134]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead137 : DeadState :=
  DeadState.leaf ⟨8657044093,2,1,[c25,c18,c1],[([],[10,21,11,22]),([],[27,30,28,31]),([],[12,23,13,24])]⟩ (decodeTape 90 1718531920829469156951949811680654270482421336394981143754333876831511596764050814900886493715959113984363180465765097243830377444313559212184680074541678883604116347954057238811298479932715) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead138 : DeadState :=
  DeadState.leaf ⟨17246978749,2,1,[c26,c18,c1],[([],[10,21,11,22]),([],[27,30,29,32]),([],[12,23,14,25])]⟩ (decodeTape 88 104890864308439279569630293150431547088507790373097951020022087688811011948100757226182248323656925036087245941335453661129471852646284103173873053186435039116734082592290228414571545898) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead140 : DeadState :=
  DeadState.leaf ⟨34426847965,34,2,[c27,c18,c1],[([],[10,21,11,22]),([],[28,31,29,32]),([],[13,24,14,25])]⟩ (decodeTape 87 802862828199965400599891206783776893811216847007448268270198016483265049889539551967412075045750946137998216205720503393074005983547165035649137162009338991838745444209917328540665482) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead141 : DeadState :=
  DeadState.leaf ⟨67109405,98,3,[c18,c1],[([],[10,21,11,22])]⟩ (decodeTape 100 2974679591159279888841741140868172138346022994625447563443622138971911259839255062036851066652720732740419919792057400163871128226796726626478349653479642831589735466492800160685421834102803427200561069588382763) (by decide +kernel)

private def dead139 : DeadState :=
  DeadState.fork ⟨67109405,34,2,[c18,c1],[([],[10,21,11,22])]⟩ ⟨67109405,34,2,[c18,c1],[([],[10,21,11,22])]⟩ [] 6 [dead140, dead141]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead136 : DeadState :=
  DeadState.fork ⟨67109405,2,1,[c18,c1],[([],[10,21,11,22])]⟩ ⟨67109405,2,1,[c18,c1],[([],[10,21,11,22])]⟩ [] 5 [dead137, dead138, dead139]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead143 : DeadState :=
  DeadState.leaf ⟨2281702013,2,1,[c23,c19,c1],[([],[10,21,12,23]),([30],[26,28,33]),([],[11,22,13,24])]⟩ (decodeTape 52 14791640809576975172748470301781421163741443377807133456075901611279676988182884913926002384956942455000518443) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead144 : DeadState :=
  DeadState.leaf ⟨4429185725,2,1,[c24,c19,c1],[([],[10,21,12,23]),([30],[26,29,34]),([],[11,22,14,25])]⟩ (decodeTape 55 31020319116331356820835080699717233749577613986269287308281788552509171937482558562798271982430015196835085799903018) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead146 : DeadState :=
  DeadState.leaf ⟨34493956845,18,2,[c27,c19,c1],[([],[10,21,12,23]),([],[28,33,29,34]),([],[13,24,14,25])]⟩ (decodeTape 75 40715454293850624387418327226067272038062828227298937668557311068165639258678901426008114698365822441135588141242730390538472179987467873907960501725528055818) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead147 : DeadState :=
  DeadState.leaf ⟨134218285,82,3,[c19,c1],[([],[10,21,12,23])]⟩ (decodeTape 107 1678758253535917366101661913865954555640998208881911049564218105699113778253412407767101843174320619963823402044801474724015259925157765399964980448270184826636736105076633152477648950898696703409074798927286503135285549892651) (by decide +kernel)

private def dead145 : DeadState :=
  DeadState.fork ⟨134218285,18,2,[c19,c1],[([],[10,21,12,23])]⟩ ⟨134218285,18,2,[c19,c1],[([],[10,21,12,23])]⟩ [] 6 [dead146, dead147]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead142 : DeadState :=
  DeadState.fork ⟨134218285,2,1,[c19,c1],[([],[10,21,12,23])]⟩ ⟨134218285,2,1,[c19,c1],[([],[10,21,12,23])]⟩ [] 4 [dead143, dead144, dead145]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead149 : DeadState :=
  DeadState.leaf ⟨1342177917,2,1,[c22,c20,c1],[([],[10,21,13,24]),([31,33],[26,27]),([],[11,22,12,23])]⟩ (decodeTape 29 4959201229480530246840741931625449418182919289142597378608427) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead150 : DeadState :=
  DeadState.leaf ⟨4563403485,2,1,[c24,c20,c1],[([],[10,21,13,24]),([31],[26,29,35]),([],[11,22,14,25])]⟩ (decodeTape 54 237501784535916161799505641288647234790972769816440778309337062401143127164885899888619682254563601002706800185257) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead152 : DeadState :=
  DeadState.leaf ⟨17448305389,18,2,[c26,c20,c1],[([],[10,21,13,24]),([33],[27,29,35]),([],[12,23,14,25])]⟩ (decodeTape 53 1855191417784668292127942583884929501874110062714165501324609251579021719487900085889259786189294556348100056865) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead153 : DeadState :=
  DeadState.leaf ⟨268436045,50,3,[c20,c1],[([],[10,21,13,24])]⟩ (decodeTape 106 13115298855749354098350605157516489729830118727399198876665615257386637227538571511121393185878242760367208940864944193006656260420394968158130892647243870675690149251873871845893883375253752651587547654432216114689824949291) (by decide +kernel)

private def dead151 : DeadState :=
  DeadState.fork ⟨268436045,18,2,[c20,c1],[([],[10,21,13,24])]⟩ ⟨268436045,18,2,[c20,c1],[([],[10,21,13,24])]⟩ [] 5 [dead152, dead153]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead148 : DeadState :=
  DeadState.fork ⟨268436045,2,1,[c20,c1],[([],[10,21,13,24])]⟩ ⟨268436045,2,1,[c20,c1],[([],[10,21,13,24])]⟩ [] 4 [dead149, dead150, dead151]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead155 : DeadState :=
  DeadState.leaf ⟨1610613437,2,1,[c22,c21,c1],[([],[10,21,14,25]),([32,34],[26,27]),([],[11,22,12,23])]⟩ (decodeTape 26 2364731421040338247593534237999825395225885420586503466) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead156 : DeadState :=
  DeadState.leaf ⟨2684355293,2,1,[c23,c21,c1],[([],[10,21,14,25]),([32,35],[26,28]),([],[11,22,13,24])]⟩ (decodeTape 22 8809311021274820134690533201414014668020064041) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead157 : DeadState :=
  DeadState.leaf ⟨536871565,18,2,[c21,c1],[([],[10,21,14,25])]⟩ (decodeTape 121 532019726933224940537836136418592766083834289496220410116133867497467377875265223140172471249471025806132974499769610330817071406480461213871302312751611163519335181879705741063650521943031855542055789091099859777936987319259991403269562272622031984926597) (by decide +kernel)

private def dead154 : DeadState :=
  DeadState.fork ⟨536871565,2,1,[c21,c1],[([],[10,21,14,25])]⟩ ⟨536871565,2,1,[c21,c1],[([],[10,21,14,25])]⟩ [] 4 [dead155, dead156, dead157]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead160 : DeadState :=
  DeadState.leaf ⟨35433480949,10,2,[c27,c22,c1],[([],[11,22,12,23]),([],[31,33,32,34]),([],[13,24,14,25])]⟩ (decodeTape 75 39864059727510833310542220930092342362612762281290507492313063487981749453838314580313667690799104958408262185989479626336722404256913540994623727028077830539) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead161 : DeadState :=
  DeadState.leaf ⟨1073742389,74,3,[c22,c1],[([],[11,22,12,23])]⟩ (decodeTape 92 41384586110345546184348829593661040380100015906381701884232558728883976821010364189143057425268974811569279079610004691902063284609981351394494117423006579402945414593312056941743531568180413483) (by decide +kernel)

private def dead159 : DeadState :=
  DeadState.fork ⟨1073742389,10,2,[c22,c1],[([],[11,22,12,23])]⟩ ⟨1073742389,10,2,[c22,c1],[([],[11,22,12,23])]⟩ [] 6 [dead160, dead161]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead163 : DeadState :=
  DeadState.leaf ⟨19327353589,10,2,[c26,c23,c1],[([],[11,22,13,24]),([33],[30,32,35]),([],[12,23,14,25])]⟩ (decodeTape 49 6924139089713940466380804078388892088304761357356082315091985886849706413773377857240076772746600351301) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead164 : DeadState :=
  DeadState.leaf ⟨2147484245,42,3,[c23,c1],[([],[11,22,13,24])]⟩ (decodeTape 91 323317078987074579565229005162887640257478527390230430361576776027589860415661847119284761136751455342197239943448605207096081818984480877431836054242350655529100974832122474660406861699925035) (by decide +kernel)

private def dead162 : DeadState :=
  DeadState.fork ⟨2147484245,10,2,[c23,c1],[([],[11,22,13,24])]⟩ ⟨2147484245,10,2,[c23,c1],[([],[11,22,13,24])]⟩ [] 5 [dead163, dead164]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead165 : DeadState :=
  DeadState.leaf ⟨4294967957,10,2,[c24,c1],[([],[11,22,14,25])]⟩ (decodeTape 106 13115298855744094286767764321518219075939407223326608819705675269577495294983437576337246932571955811351328114748454188934151712782130856657065776559441937242199411032797487380651266981817672765765047164661847272141368647941) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead167 : DeadState :=
  DeadState.leaf ⟨8589935205,26,3,[c25,c1],[([],[12,23,13,24])]⟩ (decodeTape 75 62100696236486314034225456513199923617007484774995288775658259545128535184000942046903304831400621809999379001823105062578623288772690466337486602921763341355) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead168 : DeadState :=
  DeadState.leaf ⟨17179869861,26,3,[c26,c1],[([],[12,23,14,25])]⟩ (decodeTape 72 29609097456676066645477688676429308736892423855732065003087859467906930934118833547740127498653139761985761423997575646459705852081255844669884949791786) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead169 : DeadState :=
  DeadState.leaf ⟨517,58,4,[c1],[]⟩ (decodeTape 81 273151440184955256076497095436295343810475560214034985532432667430031273950799850449859739708546207176343899966865165602253829175262258944718111658811014808738905857410054) (by decide +kernel)

private def dead166 : DeadState :=
  DeadState.fork ⟨517,26,3,[c1],[]⟩ ⟨517,26,3,[c1],[]⟩ [] 5 [dead167, dead168, dead169]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead158 : DeadState :=
  DeadState.fork ⟨517,10,2,[c1],[]⟩ ⟨517,10,2,[c1],[]⟩ [] 4 [dead159, dead162, dead165, dead166]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead135 : DeadState :=
  DeadState.fork ⟨517,2,1,[c1],[]⟩ ⟨517,2,1,[c1],[]⟩ [] 3 [dead136, dead142, dead148, dead154, dead158]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead94 : DeadState :=
  DeadState.fork ⟨517,0,0,[c1],[]⟩ ⟨517,0,0,[c1],[]⟩ [] 1 [dead95, dead109, dead117, dead125, dead130, dead135]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead173 : DeadState :=
  DeadState.leaf ⟨35433514239,0,0,[c27,c22,c7,c2],[([16,21],[8,9]),([],[17,22,18,23]),([],[11,26,12,27]),([],[31,33,32,34]),([],[19,24,20,25]),([],[13,28,14,29])]⟩ (decodeTape 70 1384186674868345043894802836092352871430223453424752981700477105007440385597391975098096169420252003973611504348632924594004876197565904917084543112) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead174 : DeadState :=
  DeadState.leaf ⟨1073775679,64,1,[c22,c7,c2],[([16,21],[8,9]),([],[17,22,18,23]),([],[11,26,12,27])]⟩ (decodeTape 74 324168147106767666023278051791024946342287681073145691837368329371505467786559888286050560318600930888355881662477880192305922290006862921095343142469534763) (by decide +kernel)

private def dead172 : DeadState :=
  DeadState.fork ⟨1073775679,0,0,[c22,c7,c2],[([16,21],[8,9]),([],[17,22,18,23]),([],[11,26,12,27])]⟩ ⟨1073775679,0,0,[c22,c7,c2],[([16,21],[8,9]),([],[17,22,18,23]),([],[11,26,12,27])]⟩ [] 6 [dead173, dead174]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead176 : DeadState :=
  DeadState.leaf ⟨19327386879,0,0,[c26,c23,c7,c2],[([16,21],[8,9]),([],[17,22,19,24]),([],[11,26,13,28]),([33],[30,32,35]),([],[18,23,20,25]),([],[12,27,14,29])]⟩ (decodeTape 64 309004469579912782457463130692390498995836253161524136807610556365225721778235791404643026437950607906666588283230337677587483015813128) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead177 : DeadState :=
  DeadState.leaf ⟨2147517535,32,1,[c23,c7,c2],[([16,21],[8,9]),([],[17,22,19,24]),([],[11,26,13,28])]⟩ (decodeTape 66 4498736759600103578680929533683362857609067333127991574329782289640521815483523131091508641621732038076140519865353349103521936776587281451) (by decide +kernel)

private def dead175 : DeadState :=
  DeadState.fork ⟨2147517535,0,0,[c23,c7,c2],[([16,21],[8,9]),([],[17,22,19,24]),([],[11,26,13,28])]⟩ ⟨2147517535,0,0,[c23,c7,c2],[([16,21],[8,9]),([],[17,22,19,24]),([],[11,26,13,28])]⟩ [] 5 [dead176, dead177]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead178 : DeadState :=
  DeadState.leaf ⟨4295001247,0,0,[c24,c7,c2],[([16,21],[8,9]),([],[17,22,20,25]),([],[11,26,14,29])]⟩ (decodeTape 116 10317846531045253244374716368761664074378195470330931247510576962983432809687488308402296014475862852459851978977728533878444332830621739301750881827387248926213377489560234973079001483076753267029496752779400535577092700077870919103367810384901) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead180 : DeadState :=
  DeadState.leaf ⟨8589968495,16,1,[c25,c7,c2],[([16,21],[8,9]),([],[18,23,19,24]),([],[12,27,13,28])]⟩ (decodeTape 66 4405707081317778302318360936255929178911930445547944107978254589884993609293570927131640535910090138457694996046392738443870039771411842091) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead181 : DeadState :=
  DeadState.leaf ⟨17179903151,16,1,[c26,c7,c2],[([16,21],[8,9]),([],[18,23,20,25]),([],[12,27,14,29])]⟩ (decodeTape 63 2100804844363087449515517090083320674040925143263115784379675525846559269642511252256359363576999768353958438887587954819524158751786) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead182 : DeadState :=
  DeadState.leaf ⟨33807,48,2,[c7,c2],[([16,21],[8,9])]⟩ (decodeTape 80 2134920632450989243152941399656824091761761310479783401953814727620342457435709875453505864019551004869992765868680391785805809883434797411478416710884300220449280967686) (by decide +kernel)

private def dead179 : DeadState :=
  DeadState.fork ⟨33807,16,1,[c7,c2],[([16,21],[8,9])]⟩ ⟨33807,16,1,[c7,c2],[([16,21],[8,9])]⟩ [] 5 [dead180, dead181, dead182]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead171 : DeadState :=
  DeadState.fork ⟨33807,0,0,[c7,c2],[([16,21],[8,9])]⟩ ⟨33807,0,0,[c7,c2],[([16,21],[8,9])]⟩ [] 4 [dead172, dead175, dead178, dead179]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead184 : DeadState :=
  DeadState.leaf ⟨8520767,0,0,[c15,c9,c2],[([16],[8,11,26]),([22],[15,18,30]),([21],[9,12,27])]⟩ (decodeTape 105 102155842883727931223197160714828901000247400943619605422164052285241452427487622881879432347466216916484063225336977744510481875202685427605834055661173927713269751550418169436432288121504617124434764990201452856154539014) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead185 : DeadState :=
  DeadState.leaf ⟨16909407,0,0,[c16,c9,c2],[([16],[8,11,26]),([22],[15,19,31]),([21],[9,13,28])]⟩ (decodeTape 84 572603299245095227462925194567865270854105937812508102500506472609341382307876020895078057189129332148942972390843947491742536927087948861393100468309757931298338616200047363077) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead186 : DeadState :=
  DeadState.leaf ⟨33686687,0,0,[c17,c9,c2],[([16],[8,11,26]),([22],[15,20,32]),([21],[9,14,29])]⟩ (decodeTape 62 25074650025649534052978248143618874539281217461330218528033040808368498154429024249048289051716029304057688209088371378403656074245) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead188 : DeadState :=
  DeadState.leaf ⟨8590066811,4,1,[c25,c9,c2],[([16],[8,11,26]),([],[18,30,19,31]),([],[12,27,13,28])]⟩ (decodeTape 61 128222137236867171732734265932856743440688469450703615484680273340209256107730205844679539826561235196283196888533999273875850283) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead189 : DeadState :=
  DeadState.leaf ⟨17180001467,4,1,[c26,c9,c2],[([16],[8,11,26]),([],[18,30,20,32]),([],[12,27,14,29])]⟩ (decodeTape 60 1001735447163024779161986452600441214406263345316796436238355335027380015763210526538342281990302360681949281513172326291588138) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead190 : DeadState :=
  DeadState.leaf ⟨132123,36,2,[c9,c2],[([16],[8,11,26])]⟩ (decodeTape 77 1017568403794629391942760157634097782057492809292546905806096288645376916243515372043959106918386284275511719763602344244775333186434045048477694710609846807299078) (by decide +kernel)

private def dead187 : DeadState :=
  DeadState.fork ⟨132123,4,1,[c9,c2],[([16],[8,11,26])]⟩ ⟨132123,4,1,[c9,c2],[([16],[8,11,26])]⟩ [] 5 [dead188, dead189, dead190]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead183 : DeadState :=
  DeadState.fork ⟨132123,0,0,[c9,c2],[([16],[8,11,26])]⟩ ⟨132123,0,0,[c9,c2],[([16],[8,11,26])]⟩ [] 2 [dead184, dead185, dead186, dead187]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead192 : DeadState :=
  DeadState.leaf ⟨4457535,0,0,[c14,c10,c2],[([16],[8,12,27]),([23,30],[15,17]),([21],[9,11,26])]⟩ (decodeTape 92 41264870523705513649383887686106221262049836703473749756693514841402070585538946104315827113505935562429090492580482751698940331579457785416946060594146378372736004010484545848373965772775244806) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead193 : DeadState :=
  DeadState.leaf ⟨17040495,0,0,[c16,c10,c2],[([16],[8,12,27]),([23],[15,19,33]),([21],[9,13,28])]⟩ (decodeTape 78 130193703373995643235100206018172156711489803052044126571341300544611277348208799320626580831700722158195953730151486358625691829474865213822282279012678444656608260) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead194 : DeadState :=
  DeadState.leaf ⟨33817775,0,0,[c17,c10,c2],[([16],[8,12,27]),([23],[15,20,34]),([21],[9,14,29])]⟩ (decodeTape 59 11956403345997187913489391527375868483726051802331341423256673017795344036977046143171636656558225454256208764043456588530692) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead196 : DeadState :=
  DeadState.leaf ⟨2147746939,4,1,[c23,c10,c2],[([16],[8,12,27]),([30],[17,19,33]),([],[11,26,13,28])]⟩ (decodeTape 39 5854834274060339967900799087524376944703605081977279223531201393545064689655597099) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead197 : DeadState :=
  DeadState.leaf ⟨4295230651,4,1,[c24,c10,c2],[([16],[8,12,27]),([30],[17,20,34]),([],[11,26,14,29])]⟩ (decodeTape 35 21810957320259388267473584944450261484532628717055831853303478232900421674) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead198 : DeadState :=
  DeadState.leaf ⟨263211,20,2,[c10,c2],[([16],[8,12,27])]⟩ (decodeTape 66 6733702844870168922206831371198955853820221692659566000229115593489998670269841029939198295372748360681338830859976236681545492654203945990) (by decide +kernel)

private def dead195 : DeadState :=
  DeadState.fork ⟨263211,4,1,[c10,c2],[([16],[8,12,27])]⟩ ⟨263211,4,1,[c10,c2],[([16],[8,12,27])]⟩ [] 4 [dead196, dead197, dead198]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead191 : DeadState :=
  DeadState.fork ⟨263211,0,0,[c10,c2],[([16],[8,12,27])]⟩ ⟨263211,0,0,[c10,c2],[([16],[8,12,27])]⟩ [] 2 [dead192, dead193, dead194, dead195]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead200 : DeadState :=
  DeadState.leaf ⟨4719711,0,0,[c14,c11,c2],[([16],[8,13,28]),([24,31],[15,17]),([21],[9,11,26])]⟩ (decodeTape 82 34952704667416998871749534491716332513026102889249808772022270331582083424969841695942717887083101967902870681404211598350362072857687782176816379762523298953366449328751621) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead201 : DeadState :=
  DeadState.leaf ⟨8914031,0,0,[c15,c11,c2],[([16],[8,13,28]),([24,33],[15,18]),([21],[9,12,27])]⟩ (decodeTape 56 5701820143382664211857155139647481546574413699931054570344795321816858014204577605787482241812059011015478844200829956) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead202 : DeadState :=
  DeadState.leaf ⟨34079951,0,0,[c17,c11,c2],[([16],[8,13,28]),([24],[15,20,35]),([21],[9,14,29])]⟩ (decodeTape 58 93691541489019327657791454574848994663105968073364547377374473551675154271938141548219566707497937807139351079196163818500) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead203 : DeadState :=
  DeadState.leaf ⟨525387,4,1,[c11,c2],[([16],[8,13,28])]⟩ (decodeTape 105 102198086304849962540510349255811451502389943584263572366796496361398526824759285597453440004492376949643532434288185489889901074009860362762741228907121393334866453877659817308011079203160566895468401670635103987614111108) (by decide +kernel)

private def dead199 : DeadState :=
  DeadState.fork ⟨525387,0,0,[c11,c2],[([16],[8,13,28])]⟩ ⟨525387,0,0,[c11,c2],[([16],[8,13,28])]⟩ [] 2 [dead200, dead201, dead202, dead203]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead205 : DeadState :=
  DeadState.leaf ⟨5244063,0,0,[c14,c12,c2],[([16],[8,14,29]),([25,32],[15,17]),([21],[9,11,26])]⟩ (decodeTape 57 729847143448119734702710428817275290145124660518049290366300230797617048442473565166543302466702059786479929566362862597) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead206 : DeadState :=
  DeadState.leaf ⟨9438383,0,0,[c15,c12,c2],[([16],[8,14,29]),([25,34],[15,18]),([21],[9,12,27])]⟩ (decodeTape 52 21240935263718158795897483850361682703504421435665045999581243952938511539468296942004351613436974272265044996) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead207 : DeadState :=
  DeadState.leaf ⟨17827023,0,0,[c16,c12,c2],[([16],[8,14,29]),([25,35],[15,19]),([21],[9,13,28])]⟩ (decodeTape 46 4843739167497263850293520296212766703533593107410272490034517088903266316661727888730505375106052) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead208 : DeadState :=
  DeadState.leaf ⟨1049739,4,1,[c12,c2],[([16],[8,14,29])]⟩ (decodeTape 83 4486910610641375373545343510990373401015804329498911039149965109328929604472813899128644223896722655739077376627361296197632691982423052832490598855163207179433937554190390532) (by decide +kernel)

private def dead204 : DeadState :=
  DeadState.fork ⟨1049739,0,0,[c12,c2],[([16],[8,14,29])]⟩ ⟨1049739,0,0,[c12,c2],[([16],[8,14,29])]⟩ [] 2 [dead205, dead206, dead207, dead208]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead211 : DeadState :=
  DeadState.leaf ⟨8594130045,2,1,[c25,c14,c2],[([21],[9,11,26]),([],[23,30,24,31]),([],[12,27,13,28])]⟩ (decodeTape 61 128201809705152125271426511822177738477276741835819967516545137321312527011403607953986620108672546923245052510188755198420173995) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead212 : DeadState :=
  DeadState.leaf ⟨17184064701,2,1,[c26,c14,c2],[([21],[9,11,26]),([],[23,30,25,32]),([],[12,27,14,29])]⟩ (decodeTape 60 1001576638321500978683019483635260606014153565270304294040760404790861035459021431481071639782210750757575640439759297559119018) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead213 : DeadState :=
  DeadState.leaf ⟨4195357,34,2,[c14,c2],[([21],[9,11,26])]⟩ (decodeTape 108 214348258629369475450286175860050632886545210678615679719529767604585748055187310277560994679289791773699530788669943733658425956984715325945025220786188787240245172611445187879873739190965024291125104221046234496029469218702470) (by decide +kernel)

private def dead210 : DeadState :=
  DeadState.fork ⟨4195357,2,1,[c14,c2],[([21],[9,11,26])]⟩ ⟨4195357,2,1,[c14,c2],[([21],[9,11,26])]⟩ [] 5 [dead211, dead212, dead213]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead215 : DeadState :=
  DeadState.leaf ⟨2155873405,2,1,[c23,c15,c2],[([21],[9,12,27]),([30],[22,24,33]),([],[11,26,13,28])]⟩ (decodeTape 37 357856042995865418054429344727556686499700369463826988906204090352376937664299) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead216 : DeadState :=
  DeadState.leaf ⟨4303357117,2,1,[c24,c15,c2],[([21],[9,12,27]),([30],[22,25,34]),([],[11,26,14,29])]⟩ (decodeTape 36 2795750335905211434054583327606240948975647824526158600513640447641907842858) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead217 : DeadState :=
  DeadState.leaf ⟨8389677,18,2,[c15,c2],[([21],[9,12,27])]⟩ (decodeTape 107 1678756852562935727459935814425843947250217983053394017639895042139456763852581006515168783817497710734593248736257090586007675916638590561746914253684168146777310420393116082386332675586281914989413788392155063324021703476358) (by decide +kernel)

private def dead214 : DeadState :=
  DeadState.fork ⟨8389677,2,1,[c15,c2],[([21],[9,12,27])]⟩ ⟨8389677,2,1,[c15,c2],[([21],[9,12,27])]⟩ [] 4 [dead215, dead216, dead217]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead219 : DeadState :=
  DeadState.leaf ⟨1090520189,2,1,[c22,c16,c2],[([21],[9,13,28]),([31,33],[22,23]),([],[11,26,12,27])]⟩ (decodeTape 23 1127591723354370732559932383209706411686380653355) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead220 : DeadState :=
  DeadState.leaf ⟨4311745757,2,1,[c24,c16,c2],[([21],[9,13,28]),([31],[22,25,35]),([],[11,26,14,29])]⟩ (decodeTape 32 10184637679792202926876646928404179637682365915720637360303053164457) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead221 : DeadState :=
  DeadState.leaf ⟨16778317,18,2,[c16,c2],[([21],[9,13,28])]⟩ (decodeTape 96 11109080973044814996816204546711021175640399470574694752204367220368628095530533465550307527728441343633499885832084187045803919153296096827093107606859327462581763283996674267840145673258357822298214533) (by decide +kernel)

private def dead218 : DeadState :=
  DeadState.fork ⟨16778317,2,1,[c16,c2],[([21],[9,13,28])]⟩ ⟨16778317,2,1,[c16,c2],[([21],[9,13,28])]⟩ [] 4 [dead219, dead220, dead221]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead222 : DeadState :=
  DeadState.leaf ⟨33555597,2,1,[c17,c2],[([21],[9,14,29])]⟩ (decodeTape 116 15483799010607317063804309580424276719729842707136935418275538717162832454038934095515254562999247891891213764067224097771955494994202401939569359006958833042841185743542775215549826213662850378390020742253467379247704805446625722409936155415812) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead224 : DeadState :=
  DeadState.leaf ⟨1073742905,6,2,[c22,c2],[([],[11,26,12,27])]⟩ (decodeTape 98 181559557764314475969394964814101483994505620815791689042785249603427430787549095676905420237193700283301896175917722366336073224263661698771373655951286453911229378110095938399962327920069659507933683172742) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead225 : DeadState :=
  DeadState.leaf ⟨2147484761,6,2,[c23,c2],[([],[11,26,13,28])]⟩ (decodeTape 66 6733691445450229699305639515740771706693912230891435974959679701235143404135152486410544596373900530066898073711294799430192270664064508549) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead226 : DeadState :=
  DeadState.leaf ⟨4294968473,6,2,[c24,c2],[([],[11,26,14,29])]⟩ (decodeTape 38 67024425306418343085890110767741931847957943171998441436654524928911494551232773) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead227 : DeadState :=
  DeadState.leaf ⟨1033,22,3,[c2],[]⟩ (decodeTape 84 572840085342280927864446078910775182533050575336678394840648832097730794358500973609796702087672936984091890294400131544991560828759842213688172351026347037885247744233668023685) (by decide +kernel)

private def dead223 : DeadState :=
  DeadState.fork ⟨1033,6,2,[c2],[]⟩ ⟨1033,6,2,[c2],[]⟩ [] 4 [dead224, dead225, dead226, dead227]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead209 : DeadState :=
  DeadState.fork ⟨1033,2,1,[c2],[]⟩ ⟨1033,2,1,[c2],[]⟩ [] 2 [dead210, dead214, dead218, dead222, dead223]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead170 : DeadState :=
  DeadState.fork ⟨1033,0,0,[c2],[]⟩ ⟨1033,0,0,[c2],[]⟩ [] 1 [dead171, dead183, dead191, dead199, dead204, dead209]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead230 : DeadState :=
  DeadState.leaf ⟨134252607,0,0,[c19,c7,c3],[([17,22],[8,9]),([],[16,21,18,23]),([26],[10,12,30])]⟩ (decodeTape 88 107047181061178374526021403078781588221054995639650956172295900129575337657656868988643509258634437147552942165315986704569579423547463040737052333272207509539555998551340781485131842566) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead231 : DeadState :=
  DeadState.leaf ⟨268470367,0,0,[c20,c7,c3],[([17,22],[8,9]),([],[16,21,19,24]),([26],[10,13,31])]⟩ (decodeTape 79 11606078612788077326588367933068798209513716297969965000696814799868920130525202738269631815334407426714064881685593740489236961045711510666471286113702838616743216133) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead232 : DeadState :=
  DeadState.leaf ⟨536905887,0,0,[c21,c7,c3],[([17,22],[8,9]),([],[16,21,20,25]),([26],[10,14,32])]⟩ (decodeTape 68 76802585730161446706431252252546663161761369931775702265463443922397735394095914170192360827831367013952319120679358709080725333991919924806661) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead234 : DeadState :=
  DeadState.leaf ⟨8589969527,8,1,[c25,c7,c3],[([17,22],[8,9]),([],[18,23,19,24]),([],[12,30,13,31])]⟩ (decodeTape 54 222959904724829934784575861189873705180343882346927671755867351345917923990155191605771614734276256089934115292203) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead235 : DeadState :=
  DeadState.leaf ⟨17179904183,8,1,[c26,c7,c3],[([17,22],[8,9]),([],[18,23,20,25]),([],[12,30,14,32])]⟩ (decodeTape 52 13608392621245786441500619629260092315961397281587960643837370636151261590947809344191509549421370360919409706) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead236 : DeadState :=
  DeadState.leaf ⟨34839,40,2,[c7,c3],[([17,22],[8,9])]⟩ (decodeTape 69 14127719652023252284448278181564831033514682282692896429169404833805083166487121795990688449175231839403054710226991121985915944232990651026703366) (by decide +kernel)

private def dead233 : DeadState :=
  DeadState.fork ⟨34839,8,1,[c7,c3],[([17,22],[8,9])]⟩ ⟨34839,8,1,[c7,c3],[([17,22],[8,9])]⟩ [] 5 [dead234, dead235, dead236]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead229 : DeadState :=
  DeadState.fork ⟨34839,0,0,[c7,c3],[([17,22],[8,9])]⟩ ⟨34839,0,0,[c7,c3],[([17,22],[8,9])]⟩ [] 3 [dead230, dead231, dead232, dead233]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead238 : DeadState :=
  DeadState.leaf ⟨8456255,0,0,[c15,c8,c3],[([17,26],[8,10]),([21],[15,18,27]),([22],[9,12,30])]⟩ (decodeTape 85 50102608486756452023916126281879441034424074956789821208679432471630075991075059944822008514421154399082505509717035166736044310812925436841559622022840752016362883055597550060550) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead239 : DeadState :=
  DeadState.leaf ⟨16844895,0,0,[c16,c8,c3],[([17,26],[8,10]),([21],[15,19,28]),([22],[9,13,31])]⟩ (decodeTape 70 1258333493803785260932546620566223619762680387368931380733345529204486717050581505532435320847763318237312394859127570524073628005718391059240453125) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead240 : DeadState :=
  DeadState.leaf ⟨33622175,0,0,[c17,c8,c3],[([17,26],[8,10]),([21],[15,20,29]),([22],[9,14,32])]⟩ (decodeTape 52 14791639131955201487247602292571778733941353991609254943537181075356394176069281669061191107931600909731890181) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead242 : DeadState :=
  DeadState.leaf ⟨8590002299,4,1,[c25,c8,c3],[([17,26],[8,10]),([],[18,27,19,28]),([],[12,30,13,31])]⟩ (decodeTape 47 388711305124239847926810333876776133752851432109515353154488870268939906834354591308205038714733611) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead243 : DeadState :=
  DeadState.leaf ⟨17179936955,4,1,[c26,c8,c3],[([17,26],[8,10]),([],[18,27,20,29]),([],[12,30,14,32])]⟩ (decodeTape 46 3036807071283123811928205733412313544944151764702180076587574217860378291823603198401700040786986) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead244 : DeadState :=
  DeadState.leaf ⟨67611,36,2,[c8,c3],[([17,26],[8,10])]⟩ (decodeTape 63 3211924958537994136417789166199826368804040383730758321242819800901368129572380603909173444173570414097000134092654524345107985679366) (by decide +kernel)

private def dead241 : DeadState :=
  DeadState.fork ⟨67611,4,1,[c8,c3],[([17,26],[8,10])]⟩ ⟨67611,4,1,[c8,c3],[([17,26],[8,10])]⟩ [] 5 [dead242, dead243, dead244]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead237 : DeadState :=
  DeadState.fork ⟨67611,0,0,[c8,c3],[([17,26],[8,10])]⟩ ⟨67611,0,0,[c8,c3],[([17,26],[8,10])]⟩ [] 2 [dead238, dead239, dead240, dead241]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead246 : DeadState :=
  DeadState.leaf ⟨2361407,0,0,[c13,c10,c3],[([17],[8,12,30]),([23,27],[15,16]),([22,26],[9,10])]⟩ (decodeTape 84 398783741934863709572771339128538848469945384321056088741199461906787761777276385153581790627379779187879992368239796078777938068107037907807035673017269683915012273491852149766) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead247 : DeadState :=
  DeadState.leaf ⟨17041527,0,0,[c16,c10,c3],[([17],[8,12,30]),([23],[15,19,33]),([22],[9,13,31])]⟩ (decodeTape 62 25074267110271054895042142882241553328357735668346246676075227676639522297985264491191309248476640914566727035929103665451254907907) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead248 : DeadState :=
  DeadState.leaf ⟨33818807,0,0,[c17,c10,c3],[([17],[8,12,30]),([23],[15,20,34]),([22],[9,14,32])]⟩ (decodeTape 54 347975358392799378236534365522409734730688709317634132068764349159275950081378681835456712267868913449017730106371) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead250 : DeadState :=
  DeadState.leaf ⟨268699771,4,1,[c20,c10,c3],[([17],[8,12,30]),([27],[16,19,33]),([26],[10,13,31])]⟩ (decodeTape 38 45740498745254036189415286622217608159105078822249667551769283773008476136769707) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead251 : DeadState :=
  DeadState.leaf ⟨537135291,4,1,[c21,c10,c3],[([17],[8,12,30]),([27],[16,20,34]),([26],[10,14,32])]⟩ (decodeTape 31 81251447789840566941270906843824066324464402591627815702544222378) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead252 : DeadState :=
  DeadState.leaf ⟨264243,12,2,[c10,c3],[([17],[8,12,30])]⟩ (decodeTape 64 410992258694007214903991519225780851242014700915007419721285526316541052298625613774661069688923090574019997537296085948675787215045638) (by decide +kernel)

private def dead249 : DeadState :=
  DeadState.fork ⟨264243,4,1,[c10,c3],[([17],[8,12,30])]⟩ ⟨264243,4,1,[c10,c3],[([17],[8,12,30])]⟩ [] 3 [dead250, dead251, dead252]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead245 : DeadState :=
  DeadState.fork ⟨264243,0,0,[c10,c3],[([17],[8,12,30])]⟩ ⟨264243,0,0,[c10,c3],[([17],[8,12,30])]⟩ [] 2 [dead246, dead247, dead248, dead249]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead254 : DeadState :=
  DeadState.leaf ⟨2623583,0,0,[c13,c11,c3],[([17],[8,13,31]),([24,28],[15,16]),([22,26],[9,10])]⟩ (decodeTape 74 337781325208902049220952593918872554098808464523150635262659420446795512892548958436618407895826026932311941043151652695042601134188184702032993380742202373) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead255 : DeadState :=
  DeadState.leaf ⟨8915063,0,0,[c15,c11,c3],[([17],[8,13,31]),([24,33],[15,18]),([22],[9,12,30])]⟩ (decodeTape 52 21241023874713146567636501698094194418794812202932522710402098217481258162219076370486058608974106319353775107) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead256 : DeadState :=
  DeadState.leaf ⟨34080983,0,0,[c17,c11,c3],[([17],[8,13,31]),([24],[15,20,35]),([22],[9,14,32])]⟩ (decodeTape 53 2726782720668508137597909294246570779967508419440195593956644930909339370020771216144813697426483911649363985411) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead257 : DeadState :=
  DeadState.leaf ⟨526419,4,1,[c11,c3],[([17],[8,13,31])]⟩ (decodeTape 96 11080329375679555866589559803811687665898055774592651105731345731446418618392368283666815390386906218522462921535844994600445992663418971817811226871014046704998522896073730381586669042442573798340564355) (by decide +kernel)

private def dead253 : DeadState :=
  DeadState.fork ⟨526419,0,0,[c11,c3],[([17],[8,13,31])]⟩ ⟨526419,0,0,[c11,c3],[([17],[8,13,31])]⟩ [] 2 [dead254, dead255, dead256, dead257]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead259 : DeadState :=
  DeadState.leaf ⟨3147935,0,0,[c13,c12,c3],[([17],[8,14,32]),([25,29],[15,16]),([22,26],[9,10])]⟩ (decodeTape 52 14791639134177027976789122276677974531933413658606105733564904043362911518735033041441059919206948012940854277) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead260 : DeadState :=
  DeadState.leaf ⟨9439415,0,0,[c15,c12,c3],[([17],[8,14,32]),([25,34],[15,18]),([22],[9,12,30])]⟩ (decodeTape 48 79128980169866780071096486418731389132525841306397077142211111780630447557957659996017794902230008835) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead261 : DeadState :=
  DeadState.leaf ⟨17828055,0,0,[c16,c12,c3],[([17],[8,14,32]),([25,35],[15,19]),([22],[9,13,31])]⟩ (decodeTape 43 2309674804410901202664570760847690214220706156401413849924482636105001150163297153745388547) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead262 : DeadState :=
  DeadState.leaf ⟨1050771,4,1,[c12,c3],[([17],[8,14,32])]⟩ (decodeTape 76 7970354298612890007186355780177259334252673490727180598683093633465212811709638231804384520592305370087413702324414090232772945811089841079504596402235332891907) (by decide +kernel)

private def dead258 : DeadState :=
  DeadState.fork ⟨1050771,0,0,[c12,c3],[([17],[8,14,32])]⟩ ⟨1050771,0,0,[c12,c3],[([17],[8,14,32])]⟩ [] 2 [dead259, dead260, dead261, dead262]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead265 : DeadState :=
  DeadState.leaf ⟨8592033917,2,1,[c25,c13,c3],[([22,26],[9,10]),([],[23,27,24,28]),([],[12,30,13,31])]⟩ (decodeTape 59 8327063516418216494056681526704451012423738754119649106749895219827962171440602707711956132730741052517161783521956900586539) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead266 : DeadState :=
  DeadState.leaf ⟨17181968573,2,1,[c26,c13,c3],[([22,26],[9,10]),([],[23,27,25,29]),([],[12,30,14,32])]⟩ (decodeTape 58 65055183722017316377734680391619992265872379377363303065732984960278553020146320303928534741817000585457932955355311719466) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead267 : DeadState :=
  DeadState.leaf ⟨2099229,34,2,[c13,c3],[([22,26],[9,10])]⟩ (decodeTape 75 62127664192676301610366681612810572941246721291536474214823421988593266356424360346985956643355056678477436698588166200635451545004228089311945914291188810758) (by decide +kernel)

private def dead264 : DeadState :=
  DeadState.fork ⟨2099229,2,1,[c13,c3],[([22,26],[9,10])]⟩ ⟨2099229,2,1,[c13,c3],[([22,26],[9,10])]⟩ [] 5 [dead265, dead266, dead267]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead269 : DeadState :=
  DeadState.leaf ⟨276826237,2,1,[c20,c15,c3],[([22],[9,12,30]),([27],[21,24,33]),([26],[10,13,31])]⟩ (decodeTape 36 2790453379531343460346537042319330366440613875505906966845274507926632615339) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead270 : DeadState :=
  DeadState.leaf ⟨545261757,2,1,[c21,c15,c3],[([22],[9,12,30]),([27],[21,25,34]),([26],[10,14,32])]⟩ (decodeTape 32 10395248903863012953414214460980767581243935762503885343237522279850) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead271 : DeadState :=
  DeadState.leaf ⟨8390709,10,2,[c15,c3],[([22],[9,12,30])]⟩ (decodeTape 96 11109081046043865149263465315383229652696655912658256668618791474877594349624051829163909076243763117015061717016085103232255179091266020236114020415617187724124922214416275021719039651608713803198071942) (by decide +kernel)

private def dead268 : DeadState :=
  DeadState.fork ⟨8390709,2,1,[c15,c3],[([22],[9,12,30])]⟩ ⟨8390709,2,1,[c15,c3],[([22],[9,12,30])]⟩ [] 3 [dead269, dead270, dead271]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead272 : DeadState :=
  DeadState.leaf ⟨16779349,2,1,[c16,c3],[([22],[9,13,31])]⟩ (decodeTape 127 2339845566581223736087944705709950530953190801151924966526073469156819695177132132963352249187610334951715667779962991328484258751182295224260540891178371374177556612386160258062488435170047517542412882565947575773485918610813777075068574185264249770416029407350445443) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead273 : DeadState :=
  DeadState.leaf ⟨33556629,2,1,[c17,c3],[([22],[9,14,32])]⟩ (decodeTape 103 6253856657448664096195950635161652670925196843772583829369757086954515287425298439098934948093412394151471996411558587426046844967740268435452542640246378421876822048264783528723119475905617452375968330608179235083523) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead275 : DeadState :=
  DeadState.leaf ⟨134219833,6,2,[c19,c3],[([26],[10,12,30])]⟩ (decodeTape 58 93458827960823352398721751521786757102744573271776480070806303973427975053515141731411462482970352885905220487990894871814) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead276 : DeadState :=
  DeadState.leaf ⟨268437593,6,2,[c20,c3],[([26],[10,13,31])]⟩ (decodeTape 35 31970111651303441434398874301882078227047020921955073337160876786209481349) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead277 : DeadState :=
  DeadState.leaf ⟨536873113,6,2,[c21,c3],[([26],[10,14,32])]⟩ (decodeTape 30 930150770876801141168399150766662625201059034479101171096100741) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead278 : DeadState :=
  DeadState.leaf ⟨2065,14,3,[c3],[]⟩ (decodeTape 82 34963354632847462933067842142850978645732236387472201431396936515119886908583704891040557002841479952619462230542766696873096405792388091492769858375396097491433840219198853) (by decide +kernel)

private def dead274 : DeadState :=
  DeadState.fork ⟨2065,6,2,[c3],[]⟩ ⟨2065,6,2,[c3],[]⟩ [] 3 [dead275, dead276, dead277, dead278]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead263 : DeadState :=
  DeadState.fork ⟨2065,2,1,[c3],[]⟩ ⟨2065,2,1,[c3],[]⟩ [] 2 [dead264, dead268, dead272, dead273, dead274]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead228 : DeadState :=
  DeadState.fork ⟨2065,0,0,[c3],[]⟩ ⟨2065,0,0,[c3],[]⟩ [] 1 [dead229, dead237, dead245, dead253, dead258, dead263]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead281 : DeadState :=
  DeadState.leaf ⟨67145791,0,0,[c18,c7,c4],[([18,23],[8,9]),([],[16,21,17,22]),([27,30],[10,11])]⟩ (decodeTape 84 573214006258537166558404552570091317352849876152853581893503796826959788841187385419078358075150039005700563452503178977276773471426527679604215292127429062034540783242459235334) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead282 : DeadState :=
  DeadState.leaf ⟨268472431,0,0,[c20,c7,c4],[([18,23],[8,9]),([],[16,21,19,24]),([27],[10,13,33])]⟩ (decodeTape 67 600019474177812715388828982588230150919426151536200982930494539462331979973111581743727455350108673512057025464446288485071170421561385272324) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead283 : DeadState :=
  DeadState.leaf ⟨536907951,0,0,[c21,c7,c4],[([18,23],[8,9]),([],[16,21,20,25]),([27],[10,14,34])]⟩ (decodeTape 58 65054241743757034225117842423460787908117410116268968938535619916606022297810088383453365686349958743298907518476776883204) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead284 : DeadState :=
  DeadState.leaf ⟨36903,8,1,[c7,c4],[([18,23],[8,9])]⟩ (decodeTape 124 1113320987265606861977004681043149091172241782196777237120546714607940236453140289573689920226972528914749869498669648000421617093773155421336325513828997714700169379491578931783309741708131957594177152908890224912219107945964502053774558558240215077520513570180) (by decide +kernel)

private def dead280 : DeadState :=
  DeadState.fork ⟨36903,0,0,[c7,c4],[([18,23],[8,9])]⟩ ⟨36903,0,0,[c7,c4],[([18,23],[8,9])]⟩ [] 3 [dead281, dead282, dead283, dead284]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead286 : DeadState :=
  DeadState.leaf ⟨4263999,0,0,[c14,c8,c4],[([18,27],[8,10]),([21],[15,17,26]),([23,30],[9,11])]⟩ (decodeTape 79 16677545209047055714476129891154044350354903260547708982715853405824683636611288159222867644854605044013730692882215425158617083789694154864975441636803526349023888390) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead287 : DeadState :=
  DeadState.leaf ⟨16846959,0,0,[c16,c8,c4],[([18,27],[8,10]),([21],[15,19,28]),([23],[9,13,33])]⟩ (decodeTape 61 136428625505341086448580614896181802361792035845255202366870815641781366825073784253246118950729333727751936298759504369071932420) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead288 : DeadState :=
  DeadState.leaf ⟨33624239,0,0,[c17,c8,c4],[([18,27],[8,10]),([21],[15,20,29]),([23],[9,14,34])]⟩ (decodeTape 46 3363225281188692464538957471438676689031472480635692822922786898962471551263148454789113317147652) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead289 : DeadState :=
  DeadState.leaf ⟨69675,4,1,[c8,c4],[([18,27],[8,10])]⟩ (decodeTape 105 102231353923033779073090456606788201364975797405266867636800312934925357762575894433465244317149336120511562225983360810720465018836846316642921381129695939578783525243177957495064365180858392583642687480150859697908487556) (by decide +kernel)

private def dead285 : DeadState :=
  DeadState.fork ⟨69675,0,0,[c8,c4],[([18,27],[8,10])]⟩ ⟨69675,0,0,[c8,c4],[([18,27],[8,10])]⟩ [] 2 [dead286, dead287, dead288, dead289]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead291 : DeadState :=
  DeadState.leaf ⟨2232383,0,0,[c13,c9,c4],[([18,30],[8,11]),([22,26],[15,16]),([23,27],[9,10])]⟩ (decodeTape 76 5534236307264382301492378455727009298970189705120580373936777317256158367433894644083731033890325109831130491610583649633662561647646050907843029125935194194950) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead292 : DeadState :=
  DeadState.leaf ⟨16912503,0,0,[c16,c9,c4],[([18,30],[8,11]),([22],[15,19,31]),([23],[9,13,33])]⟩ (decodeTape 45 26275165931264677636685423434279224050306827105146427005916070245653369237551933708584836891651) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead293 : DeadState :=
  DeadState.leaf ⟨33689783,0,0,[c17,c9,c4],[([18,30],[8,11]),([22],[15,20,32]),([23],[9,14,34])]⟩ (decodeTape 40 764707974427762320783656490564699363703526146556926576579230342985074662996070597635) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead294 : DeadState :=
  DeadState.leaf ⟨135219,4,1,[c9,c4],[([18,30],[8,11])]⟩ (decodeTape 93 5285237087702618512423188966068172622926551991495204342196785772927507670711446077479865649891379578111605140578831861044414557708824105431094841694296908403001751165716697943344374834566720001411) (by decide +kernel)

private def dead290 : DeadState :=
  DeadState.fork ⟨135219,0,0,[c9,c4],[([18,30],[8,11])]⟩ ⟨135219,0,0,[c9,c4],[([18,30],[8,11])]⟩ [] 2 [dead291, dead292, dead293, dead294]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead296 : DeadState :=
  DeadState.leaf ⟨2625647,0,0,[c13,c11,c4],[([18],[8,13,33]),([24,28],[15,16]),([23,27],[9,10])]⟩ (decodeTape 58 65054238088259884009863767087004553257384705142165497243014455461341231711991448331178664071566521827520253808667500725252) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead297 : DeadState :=
  DeadState.leaf ⟨4722807,0,0,[c14,c11,c4],[([18],[8,13,33]),([24,31],[15,17]),([23,30],[9,11])]⟩ (decodeTape 45 26263166998013882070064897606264712262417103094105027979601042061958580749775935505022512235523) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead298 : DeadState :=
  DeadState.leaf ⟨34083047,0,0,[c17,c11,c4],[([18],[8,13,33]),([24],[15,20,35]),([23],[9,14,34])]⟩ (decodeTape 48 79359755245092445971363431917289023860095975258106881751627745165265347765603074221082491921390863363) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead299 : DeadState :=
  DeadState.leaf ⟨528483,4,1,[c11,c4],[([18],[8,13,33])]⟩ (decodeTape 91 322445218895046553862732602584220138268286668151066492110645492163842153789603967763775343227298867347653338164185333813795259505200001911761844052411896344340202756463765158026941324333323651) (by decide +kernel)

private def dead295 : DeadState :=
  DeadState.fork ⟨528483,0,0,[c11,c4],[([18],[8,13,33])]⟩ ⟨528483,0,0,[c11,c4],[([18],[8,13,33])]⟩ [] 2 [dead296, dead297, dead298, dead299]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead301 : DeadState :=
  DeadState.leaf ⟨3149999,0,0,[c13,c12,c4],[([18],[8,14,34]),([25,29],[15,16]),([23,27],[9,10])]⟩ (decodeTape 48 55103083019378468068958716788015317897451390889364318280250270190197492607796715490614223445133345796) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead302 : DeadState :=
  DeadState.leaf ⟨5247159,0,0,[c14,c12,c4],[([18],[8,14,34]),([25,32],[15,17]),([23,30],[9,11])]⟩ (decodeTape 35 21803893179106707668264733106863627270862297577880037728537507310401717251) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead303 : DeadState :=
  DeadState.leaf ⟨17830119,0,0,[c16,c12,c4],[([18],[8,14,34]),([25,35],[15,19]),([23],[9,13,33])]⟩ (decodeTape 40 1101337843771942240688536898380925749154970474445158291365935723447619029331497157635) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead304 : DeadState :=
  DeadState.leaf ⟨1052835,4,1,[c12,c4],[([18],[8,14,34])]⟩ (decodeTape 66 6751147013787524474885872454619493840836548253107570370597102332829175978590087574841982637156002844315033570162458601224665275418112333059) (by decide +kernel)

private def dead300 : DeadState :=
  DeadState.fork ⟨1052835,0,0,[c12,c4],[([18],[8,14,34])]⟩ ⟨1052835,0,0,[c12,c4],[([18],[8,14,34])]⟩ [] 2 [dead301, dead302, dead303, dead304]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead306 : DeadState :=
  DeadState.leaf ⟨2101293,2,1,[c13,c4],[([23,27],[9,10])]⟩ (decodeTape 110 3512642572898166587624584741139007934367157320770931754711018155343837390177266356692705371745164516542317331502755101914887066176203108631767398354486143214298069534205255127181312779594935097844364472341042828073950808009007584644) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead307 : DeadState :=
  DeadState.leaf ⟨4198453,2,1,[c14,c4],[([23,30],[9,11])]⟩ (decodeTape 99 23244718527947884822640585042343067459812744190346956866366950360109287521875320783989136351165742453712435059554321192028552344948032861280838487766140655438975406100933680359935030271433391290673707081684355) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead308 : DeadState :=
  DeadState.leaf ⟨16781413,2,1,[c16,c4],[([23],[9,13,33])]⟩ (decodeTape 110 3511878958439351560147188664928656000295528186218502618526149725856122174321169443129439560644386645858430973214496428956177037736444326791518459692747679163695690881605762154096354568939538965361888470095644793907645734269294384515) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead309 : DeadState :=
  DeadState.leaf ⟨33558693,2,1,[c17,c4],[([23],[9,14,34])]⟩ (decodeTape 90 2525912604714093166773317022296809797113280891456546820774333732432807594120650137806394478039745587076222308214438051232786712092877141264102513028862386025323809620532944983381497887233283) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead311 : DeadState :=
  DeadState.leaf ⟨67113017,6,2,[c18,c4],[([27,30],[10,11])]⟩ (decodeTape 40 1098844097185347007644549259612074095237893624732006412457413759060190837039153857798) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead312 : DeadState :=
  DeadState.leaf ⟨268439657,6,2,[c20,c4],[([27],[10,13,33])]⟩ (decodeTape 32 15242891682686827358218926001547765702109377005868511761757922091396) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead313 : DeadState :=
  DeadState.leaf ⟨536875177,6,2,[c21,c4],[([27],[10,14,34])]⟩ (decodeTape 27 443530456177018375110448936040813168149191377738389266180) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead314 : DeadState :=
  DeadState.leaf ⟨4129,14,3,[c4],[]⟩ (decodeTape 83 4474826326042642919914838291243994460930650000255347163524667774190186366363849000403028660090923512089555782581662749416060510823468179195799246345716368748335656784894875012) (by decide +kernel)

private def dead310 : DeadState :=
  DeadState.fork ⟨4129,6,2,[c4],[]⟩ ⟨4129,6,2,[c4],[]⟩ [] 3 [dead311, dead312, dead313, dead314]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead305 : DeadState :=
  DeadState.fork ⟨4129,2,1,[c4],[]⟩ ⟨4129,2,1,[c4],[]⟩ [] 2 [dead306, dead307, dead308, dead309, dead310]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead279 : DeadState :=
  DeadState.fork ⟨4129,0,0,[c4],[]⟩ ⟨4129,0,0,[c4],[]⟩ [] 1 [dead280, dead285, dead290, dead295, dead300, dead305]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead317 : DeadState :=
  DeadState.leaf ⟨67149919,0,0,[c18,c7,c5],[([19,24],[8,9]),([],[16,21,17,22]),([28,31],[10,11])]⟩ (decodeTape 70 1808744479449162583667234947044388992810916737454169916846215086492880951486023910556212991657163227473132853143812575284862018789307026405455561733) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead318 : DeadState :=
  DeadState.leaf ⟨134258799,0,0,[c19,c7,c5],[([19,24],[8,9]),([],[16,21,18,23]),([28,33],[10,12])]⟩ (decodeTape 58 93509819681854573157546438409349044609494798837883877702059572045841834252090899025258135868296272200274259540294998148100) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead319 : DeadState :=
  DeadState.leaf ⟨536912079,0,0,[c21,c7,c5],[([19,24],[8,9]),([],[16,21,20,25]),([28],[10,14,35])]⟩ (decodeTape 52 14789328549834577540644380983234718522384356885447051326574860340179579417315471534459833743319386660568548356) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead320 : DeadState :=
  DeadState.leaf ⟨41031,8,1,[c7,c5],[([19,24],[8,9])]⟩ (decodeTape 89 19691150536702863912446306111122254769806821014927591188387652153993956121018849164998119490990607546814898708983895934702373717456710109839678722669207916245679716378063912004767489119620) (by decide +kernel)

private def dead316 : DeadState :=
  DeadState.fork ⟨41031,0,0,[c7,c5],[([19,24],[8,9])]⟩ ⟨41031,0,0,[c7,c5],[([19,24],[8,9])]⟩ [] 3 [dead317, dead318, dead319, dead320]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead322 : DeadState :=
  DeadState.leaf ⟨4268127,0,0,[c14,c8,c5],[([19,28],[8,10]),([21],[15,17,26]),([24,31],[9,11])]⟩ (decodeTape 71 231447432042096350906532040179245577894199615717117715011492222912670075551166977527313020850613795705705191033345286394251591522171979360336920445957) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead323 : DeadState :=
  DeadState.leaf ⟨8462447,0,0,[c15,c8,c5],[([19,28],[8,10]),([21],[15,18,27]),([24,33],[9,12])]⟩ (decodeTape 50 1297290217616406660319623006938048541345238834422553875421324672341516193291844082700287605025592981570564) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead324 : DeadState :=
  DeadState.leaf ⟨33628367,0,0,[c17,c8,c5],[([19,28],[8,10]),([21],[15,20,29]),([24],[9,14,35])]⟩ (decodeTape 40 764590322936099251329485106512391826366977198972903117916380690477791888735707317252) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead325 : DeadState :=
  DeadState.leaf ⟨73803,4,1,[c8,c5],[([19,28],[8,10])]⟩ (decodeTape 80 2134688474237607504564884983972152425919414726277430875614209280521431010355770735585225632782364440583854910761345081380631886016386939935894242999722128427334582277508) (by decide +kernel)

private def dead321 : DeadState :=
  DeadState.fork ⟨73803,0,0,[c8,c5],[([19,28],[8,10])]⟩ ⟨73803,0,0,[c8,c5],[([19,28],[8,10])]⟩ [] 2 [dead322, dead323, dead324, dead325]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead327 : DeadState :=
  DeadState.leaf ⟨2236511,0,0,[c13,c9,c5],[([19,31],[8,11]),([22,26],[15,16]),([24,28],[9,10])]⟩ (decodeTape 71 161042501205720059228965470497698065010028699521673499321001225132137506418997627231947592852621827988391305942305750590775680353099136267216059368453) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead328 : DeadState :=
  DeadState.leaf ⟨8527991,0,0,[c15,c9,c5],[([19,31],[8,11]),([22],[15,18,30]),([24,33],[9,12])]⟩ (decodeTape 44 294969394291824211471352607248849001929521707466508683463534755431423644735970491200319489027) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead329 : DeadState :=
  DeadState.leaf ⟨33693911,0,0,[c17,c9,c5],[([19,31],[8,11]),([22],[15,20,32]),([24],[9,14,35])]⟩ (decodeTape 34 173847502955230625276205386619874087417145248554675842549439314749260803) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead330 : DeadState :=
  DeadState.leaf ⟨139347,4,1,[c9,c5],[([19,31],[8,11])]⟩ (decodeTape 68 110360806756270788986988644810322436991595409235880154126949255342550361117046740926210163538397718607718543412924985220609156002241063571035523) (by decide +kernel)

private def dead326 : DeadState :=
  DeadState.fork ⟨139347,0,0,[c9,c5],[([19,31],[8,11])]⟩ ⟨139347,0,0,[c9,c5],[([19,31],[8,11])]⟩ [] 2 [dead327, dead328, dead329, dead330]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead332 : DeadState :=
  DeadState.leaf ⟨2367599,0,0,[c13,c10,c5],[([19,33],[8,12]),([23,27],[15,16]),([24,28],[9,10])]⟩ (decodeTape 49 7051041548402891889713650158400190375848850639815826850357393912009164852311108009077541973066410345476) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead333 : DeadState :=
  DeadState.leaf ⟨4464759,0,0,[c14,c10,c5],[([19,33],[8,12]),([23,30],[15,17]),([24,31],[9,11])]⟩ (decodeTape 45 27322266086333819796241491515538482578021691855488599746010598700681180578173075354844018738179) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead334 : DeadState :=
  DeadState.leaf ⟨33824999,0,0,[c17,c10,c5],[([19,33],[8,12]),([23],[15,20,34]),([24],[9,14,35])]⟩ (decodeTape 28 39522216105540058654058643658127407652404888905791373542403) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead335 : DeadState :=
  DeadState.leaf ⟨270435,4,1,[c10,c5],[([19,33],[8,12])]⟩ (decodeTape 62 25093121103262564347828949014914707765851444711005128625109555152310628703294047054527738287637297107505183383497943554512035911043) (by decide +kernel)

private def dead331 : DeadState :=
  DeadState.fork ⟨270435,0,0,[c10,c5],[([19,33],[8,12])]⟩ ⟨270435,0,0,[c10,c5],[([19,33],[8,12])]⟩ [] 2 [dead332, dead333, dead334, dead335]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead337 : DeadState :=
  DeadState.leaf ⟨3154127,0,0,[c13,c12,c5],[([19],[8,14,35]),([25,29],[15,16]),([24,28],[9,10])]⟩ (decodeTape 45 26271123445181182727661082452436888495381379334169672429169437553706251762601360156764995830788) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead338 : DeadState :=
  DeadState.leaf ⟨5251287,0,0,[c14,c12,c5],[([19],[8,14,35]),([25,32],[15,17]),([24,31],[9,11])]⟩ (decodeTape 32 10610809502615279949309818839220670083258231220379432769193436218371) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead339 : DeadState :=
  DeadState.leaf ⟨9445607,0,0,[c15,c12,c5],[([19],[8,14,35]),([25,34],[15,18]),([24,33],[9,12])]⟩ (decodeTape 28 37162556798079674238588534583415124577244115297412171138051) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead340 : DeadState :=
  DeadState.leaf ⟨1056963,4,1,[c12,c5],[([19],[8,14,35])]⟩ (decodeTape 57 731960825911745979200443892069523241381216281329848706048001384446172068782547944782440660429045566883520694189014815875) (by decide +kernel)

private def dead336 : DeadState :=
  DeadState.fork ⟨1056963,0,0,[c12,c5],[([19],[8,14,35])]⟩ ⟨1056963,0,0,[c12,c5],[([19],[8,14,35])]⟩ [] 2 [dead337, dead338, dead339, dead340]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead342 : DeadState :=
  DeadState.leaf ⟨2105421,2,1,[c13,c5],[([24,28],[9,10])]⟩ (decodeTape 79 16677253700690809273483880891290249967715732342675876958161119218069506444637206019671075014378314913036104637505972032905967573673220766954244398166913431184955544964) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead343 : DeadState :=
  DeadState.leaf ⟨4202581,2,1,[c14,c5],[([24,31],[9,11])]⟩ (decodeTape 68 110360806727878648611506252483996870783450435516208512460705776741340641392397909977731069182802863203151233200873189795022031070708604868892035) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead344 : DeadState :=
  DeadState.leaf ⟨8396901,2,1,[c15,c5],[([24,33],[9,12])]⟩ (decodeTape 64 411125696050084909355303311109629798317337685769837407035641673411461803215538748020435164434325759864927701752141604557220271083361667) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead345 : DeadState :=
  DeadState.leaf ⟨33562821,2,1,[c17,c5],[([24],[9,14,35])]⟩ (decodeTape 86 9409757782936675489432590403786153579391311690219986836038678623457222896569250778851925125139347579954353087539015537218237212437601941476492791298845007261234827298433976567501955) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead347 : DeadState :=
  DeadState.leaf ⟨67117145,6,2,[c18,c5],[([28,31],[10,11])]⟩ (decodeTape 30 930756369629940700037014971607993589065998948305039510117013253) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead348 : DeadState :=
  DeadState.leaf ⟨134226025,6,2,[c19,c5],[([28,33],[10,12])]⟩ (decodeTape 30 930755584992223799537882575434865762510428254430402500876834564) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead349 : DeadState :=
  DeadState.leaf ⟨536879305,6,2,[c21,c5],[([28],[10,14,35])]⟩ (decodeTape 24 211491803726435504044538912456640095247032981919620) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead350 : DeadState :=
  DeadState.leaf ⟨8257,14,3,[c5],[]⟩ (decodeTape 110 3511117512310583038860140219988641640279315975704397813083720993973393630859438138096835244139489211615285795430197046679748124177263425929397980975854171702203849206294072809392794983005641606972446168462936107601012977755447088516) (by decide +kernel)

private def dead346 : DeadState :=
  DeadState.fork ⟨8257,6,2,[c5],[]⟩ ⟨8257,6,2,[c5],[]⟩ [] 3 [dead347, dead348, dead349, dead350]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead341 : DeadState :=
  DeadState.fork ⟨8257,2,1,[c5],[]⟩ ⟨8257,2,1,[c5],[]⟩ [] 2 [dead342, dead343, dead344, dead345, dead346]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead315 : DeadState :=
  DeadState.fork ⟨8257,0,0,[c5],[]⟩ ⟨8257,0,0,[c5],[]⟩ [] 1 [dead316, dead321, dead326, dead331, dead336, dead341]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead353 : DeadState :=
  DeadState.leaf ⟨67158175,0,0,[c18,c7,c6],[([20,25],[8,9]),([],[16,21,17,22]),([29,32],[10,11])]⟩ (decodeTape 65 52636470455985559605545746919751809802668224730199741289604003876580083043075347526553528694510722276498974002153529691063711489061553157) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead354 : DeadState :=
  DeadState.leaf ⟨134267055,0,0,[c19,c7,c6],[([20,25],[8,9]),([],[16,21,18,23]),([29,34],[10,12])]⟩ (decodeTape 55 44579374901102309680113272754225221070305232559076452952715685889547836004518719182271727599671993230671991330817028) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead355 : DeadState :=
  DeadState.leaf ⟨268484815,0,0,[c20,c7,c6],[([20,25],[8,9]),([],[16,21,19,24]),([29,35],[10,13])]⟩ (decodeTape 52 21259486375016691483729970081171721775902849700740308210608412675145019473319346033690864867820872006883853316) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead356 : DeadState :=
  DeadState.leaf ⟨49287,8,1,[c7,c6],[([20,25],[8,9])]⟩ (decodeTape 81 273860451047004400023756621680633830828890812392413779873406354650688572958191115968545605796480557723639058535937235164248736941282715682936516408867963982041149662745860) (by decide +kernel)

private def dead352 : DeadState :=
  DeadState.fork ⟨49287,0,0,[c7,c6],[([20,25],[8,9])]⟩ ⟨49287,0,0,[c7,c6],[([20,25],[8,9])]⟩ [] 3 [dead353, dead354, dead355, dead356]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead358 : DeadState :=
  DeadState.leaf ⟨4276383,0,0,[c14,c8,c6],[([20,29],[8,10]),([21],[15,17,26]),([25,32],[9,11])]⟩ (decodeTape 53 2720653782276711402662978001335513045834290995200283791278575057407765326599580353733402314215721077665690289157) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead359 : DeadState :=
  DeadState.leaf ⟨8470703,0,0,[c15,c8,c6],[([20,29],[8,10]),([21],[15,18,27]),([25,34],[9,12])]⟩ (decodeTape 46 4832782661975945011971975740081920851314111070868447161058304955156402870588630614852017970725892) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead360 : DeadState :=
  DeadState.leaf ⟨16859343,0,0,[c16,c8,c6],[([20,29],[8,10]),([21],[15,19,28]),([25,35],[9,13])]⟩ (decodeTape 38 67068332307637963359631281789014154005395935187853306417662899668892651124147204) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead361 : DeadState :=
  DeadState.leaf ⟨82059,4,1,[c8,c6],[([20,29],[8,10])]⟩ (decodeTape 81 273860683148339534579001830182815547723353070530604109452792964720142744012376517114200771778948791383269349643065657684973817885850067065217752056816800640631769672062212) (by decide +kernel)

private def dead357 : DeadState :=
  DeadState.fork ⟨82059,0,0,[c8,c6],[([20,29],[8,10])]⟩ ⟨82059,0,0,[c8,c6],[([20,29],[8,10])]⟩ [] 2 [dead358, dead359, dead360, dead361]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead363 : DeadState :=
  DeadState.leaf ⟨2244767,0,0,[c13,c9,c6],[([20,32],[8,11]),([22,26],[15,16]),([25,29],[9,10])]⟩ (decodeTape 50 884756480584455914241411020836085675255185193709352792512234459198661926264254723889687528819569059431429) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead364 : DeadState :=
  DeadState.leaf ⟨8536247,0,0,[c15,c9,c6],[([20,32],[8,11]),([22],[15,18,30]),([25,34],[9,12])]⟩ (decodeTape 40 1098846622898519826946230901197668381985314401721249925570327018278983993263718630403) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead365 : DeadState :=
  DeadState.leaf ⟨16924887,0,0,[c16,c9,c6],[([20,32],[8,11]),([22],[15,19,31]),([25,35],[9,13])]⟩ (decodeTape 33 1951943714138093807528124664318578381365795828745020782925896571651075) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead366 : DeadState :=
  DeadState.leaf ⟨147603,4,1,[c9,c6],[([20,32],[8,11])]⟩ (decodeTape 74 486474294356510700330610491725468709373667171480318652872755203349120954420668966251118374347249282433500469503496004537352075202959174799969281210860049667) (by decide +kernel)

private def dead362 : DeadState :=
  DeadState.fork ⟨147603,0,0,[c9,c6],[([20,32],[8,11])]⟩ ⟨147603,0,0,[c9,c6],[([20,32],[8,11])]⟩ [] 2 [dead363, dead364, dead365, dead366]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead368 : DeadState :=
  DeadState.leaf ⟨2375855,0,0,[c13,c10,c6],[([20,34],[8,12]),([23,27],[15,16]),([25,29],[9,10])]⟩ (decodeTape 41 95910189540593092740437490611216461531707910873075632862416394033907111868817524638724) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead369 : DeadState :=
  DeadState.leaf ⟨4473015,0,0,[c14,c10,c6],[([20,34],[8,12]),([23,30],[15,17]),([25,32],[9,11])]⟩ (decodeTape 36 2790919139152023743008992151924942359511957901236556692128648342685117809667) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead370 : DeadState :=
  DeadState.leaf ⟨17055975,0,0,[c16,c10,c6],[([20,34],[8,12]),([23],[15,19,33]),([25,35],[9,13])]⟩ (decodeTape 28 56809038917384997792423328574348672279747299905532934718467) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead371 : DeadState :=
  DeadState.leaf ⟨278691,4,1,[c10,c6],[([20,34],[8,12])]⟩ (decodeTape 67 864151213133874153306808422611096394380780248534232142540556758266822502549200721457430889197624357957678207625114840949840096704004127593731) (by decide +kernel)

private def dead367 : DeadState :=
  DeadState.fork ⟨278691,0,0,[c10,c6],[([20,34],[8,12])]⟩ ⟨278691,0,0,[c10,c6],[([20,34],[8,12])]⟩ [] 2 [dead368, dead369, dead370, dead371]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead373 : DeadState :=
  DeadState.leaf ⟨2638031,0,0,[c13,c11,c6],[([20,35],[8,13]),([24,28],[15,16]),([25,29],[9,10])]⟩ (decodeTape 32 10187979003812989607753792685612525217001207808375193304613723554820) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead374 : DeadState :=
  DeadState.leaf ⟨4735191,0,0,[c14,c11,c6],[([20,35],[8,13]),([24,31],[15,17]),([25,32],[9,11])]⟩ (decodeTape 27 296461326061265605565247197591717497561255490987645174787) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead375 : DeadState :=
  DeadState.leaf ⟨8929511,0,0,[c15,c11,c6],[([20,35],[8,13]),([24,33],[15,18]),([25,34],[9,12])]⟩ (decodeTape 24 138441310955936850012125047015221880832192991167491) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead376 : DeadState :=
  DeadState.leaf ⟨540867,4,1,[c11,c6],[([20,35],[8,13])]⟩ (decodeTape 55 44675570613657499762502568849791480000209786494259439709738661999258957912178139554778510872018670378012595750376579) (by decide +kernel)

private def dead372 : DeadState :=
  DeadState.fork ⟨540867,0,0,[c11,c6],[([20,35],[8,13])]⟩ ⟨540867,0,0,[c11,c6],[([20,35],[8,13])]⟩ [] 2 [dead373, dead374, dead375, dead376]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead378 : DeadState :=
  DeadState.leaf ⟨2113677,2,1,[c13,c6],[([25,29],[9,10])]⟩ (decodeTape 79 16715129476820363335945390616402233841310129793778991031620369440842426245857698834588735607800128691799558609492986905783075462311011950752096228180029742620822607108) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead379 : DeadState :=
  DeadState.leaf ⟨4210837,2,1,[c14,c6],[([25,32],[9,11])]⟩ (decodeTape 75 62268710086682325675414682952256573075974283256078432300954969577919330060538737935220662440507337707134266715784273851508059851687921222884387754776757146883) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead380 : DeadState :=
  DeadState.leaf ⟨8405157,2,1,[c15,c6],[([25,34],[9,12])]⟩ (decodeTape 68 110611449043109512202184434334945381833483903629839538835028300400544799383426150709877388667121730722481753862742538311606419185524081367848195) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead381 : DeadState :=
  DeadState.leaf ⟨16793797,2,1,[c16,c6],[([25,35],[9,13])]⟩ (decodeTape 59 11992527422344486651868971593392055326323244957879531276932124657751170674895354461028543881009255734349002382185560772662403) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead383 : DeadState :=
  DeadState.leaf ⟨67125401,6,2,[c18,c6],[([29,32],[10,11])]⟩ (decodeTape 40 1101338779738701396144280871299398590269699139260027321490026765618344676039223662341) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead384 : DeadState :=
  DeadState.leaf ⟨134234281,6,2,[c19,c6],[([29,34],[10,12])]⟩ (decodeTape 37 525159253949499796082928397482163112109637109181913901456071447548489213138692) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead385 : DeadState :=
  DeadState.leaf ⟨268452041,6,2,[c20,c6],[([29,35],[10,13])]⟩ (decodeTape 34 250415656881936068906519114104385155678523446337765850802334513276633646) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead387 : DeadState :=
  DeadState.leaf ⟨1073758385,14,3,[c22,c6],[([32,34],[11,12])]⟩ (decodeTape 26 3475212426958706076533220075901007748963258058794604458) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead388 : DeadState :=
  DeadState.leaf ⟨2147500241,14,3,[c23,c6],[([32,35],[11,13])]⟩ (decodeTape 25 27150119921577974523466173158205656145379591092721577) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead389 : DeadState :=
  DeadState.leaf ⟨16513,30,4,[c6],[]⟩ (decodeTape 126 18279981185828503338004199560748909541733479882791513818938332537462988250253901500597248622988002641268112819966383660059242668671844909046697393271074254533761195338084314734232952632509035019606775087821885420900390015156885131262415438217123139978535209288882181) (by decide +kernel)

private def dead386 : DeadState :=
  DeadState.fork ⟨16513,14,3,[c6],[]⟩ ⟨16513,14,3,[c6],[]⟩ [] 4 [dead387, dead388, dead389]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead382 : DeadState :=
  DeadState.fork ⟨16513,6,2,[c6],[]⟩ ⟨16513,6,2,[c6],[]⟩ [] 3 [dead383, dead384, dead385, dead386]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead377 : DeadState :=
  DeadState.fork ⟨16513,2,1,[c6],[]⟩ ⟨16513,2,1,[c6],[]⟩ [] 2 [dead378, dead379, dead380, dead381, dead382]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead351 : DeadState :=
  DeadState.fork ⟨16513,0,0,[c6],[]⟩ ⟨16513,0,0,[c6],[]⟩ [] 1 [dead352, dead357, dead362, dead367, dead372, dead377]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead393 : DeadState :=
  DeadState.leaf ⟨8657076350,1,1,[c25,c18,c7],[([],[16,21,17,22]),([],[27,30,28,31]),([],[18,23,19,24])]⟩ (decodeTape 81 167807151125114867745973363751213501674338675969856376082168431817082634865837435907153790678985208420982529993300166738700665762045069735832115231690986805108490882975787) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead394 : DeadState :=
  DeadState.leaf ⟨17247011006,1,1,[c26,c18,c7],[([],[16,21,17,22]),([],[27,30,29,32]),([],[18,23,20,25])]⟩ (decodeTape 80 1310993368164959904265417099415639876535245709296913706125941659707124675565704955935504577710359766562413990291646486550188012588708374057120340876007010192065623689258) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead396 : DeadState :=
  DeadState.leaf ⟨34426880222,33,2,[c27,c18,c7],[([],[16,21,17,22]),([],[28,31,29,32]),([],[19,24,20,25])]⟩ (decodeTape 79 10906161415601183965916263027172760147416795393588797308150637977590969510139486293672656035444280182203465315128454301889771534678253828513611463675834100611707340432) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead397 : DeadState :=
  DeadState.leaf ⟨67141662,97,3,[c18,c7],[([],[16,21,17,22])]⟩ (decodeTape 118 169099653073199691703697065769485675051088636528770210630387621654697500175040890348855635157791222440634611040888415042017647608916254291449169051039839695322779136366466534864303524794798487440764315963895265663697257021892097410757345392638182443) (by decide +kernel)

private def dead395 : DeadState :=
  DeadState.fork ⟨67141662,33,2,[c18,c7],[([],[16,21,17,22])]⟩ ⟨67141662,33,2,[c18,c7],[([],[16,21,17,22])]⟩ [] 6 [dead396, dead397]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead392 : DeadState :=
  DeadState.fork ⟨67141662,1,1,[c18,c7],[([],[16,21,17,22])]⟩ ⟨67141662,1,1,[c18,c7],[([],[16,21,17,22])]⟩ [] 5 [dead393, dead394, dead395]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead399 : DeadState :=
  DeadState.leaf ⟨2281734270,1,1,[c23,c19,c7],[([],[16,21,18,23]),([30],[26,28,33]),([],[17,22,19,24])]⟩ (decodeTape 46 3026931393049981524565880897619258535893132107918708334053767402034860848181484103245048989863723) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead400 : DeadState :=
  DeadState.leaf ⟨4429217982,1,1,[c24,c19,c7],[([],[16,21,18,23]),([30],[26,29,34]),([],[17,22,20,25])]⟩ (decodeTape 44 184749230532835786411491754005094553251737623430563269811170585681365797288389086983402278698) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead402 : DeadState :=
  DeadState.leaf ⟨34493989102,17,2,[c27,c19,c7],[([],[16,21,18,23]),([],[28,33,29,34]),([],[19,24,20,25])]⟩ (decodeTape 62 16063184329740077292349431389734135982686685828004977547671074577450079149452479952582330950893668073626295043381991514805497585680) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead403 : DeadState :=
  DeadState.leaf ⟨134250542,81,3,[c19,c7],[([],[16,21,18,23])]⟩ (decodeTape 118 169099653073199691703696996192841767377380055445101091982965294177324105468035301357391599023992993564356976934749428246691560504805235267836443550338347008196994572926276349435574234411812123187696357863995362389958386822243094210391504800463340587) (by decide +kernel)

private def dead401 : DeadState :=
  DeadState.fork ⟨134250542,17,2,[c19,c7],[([],[16,21,18,23])]⟩ ⟨134250542,17,2,[c19,c7],[([],[16,21,18,23])]⟩ [] 6 [dead402, dead403]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead398 : DeadState :=
  DeadState.fork ⟨134250542,1,1,[c19,c7],[([],[16,21,18,23])]⟩ ⟨134250542,1,1,[c19,c7],[([],[16,21,18,23])]⟩ [] 4 [dead399, dead400, dead401]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead405 : DeadState :=
  DeadState.leaf ⟨1342210174,1,1,[c22,c20,c7],[([],[16,21,19,24]),([31,33],[26,27]),([],[17,22,18,23])]⟩ (decodeTape 30 621821003910998237124384749829837078979369319287225341602139435) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead406 : DeadState :=
  DeadState.leaf ⟨4563435742,1,1,[c24,c20,c7],[([],[16,21,19,24]),([31],[26,29,35]),([],[17,22,20,25])]⟩ (decodeTape 40 674720920023723309528726580072356568037947777753912491094332420760769364184277962665) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead408 : DeadState :=
  DeadState.leaf ⟨17448337646,17,2,[c26,c20,c7],[([],[16,21,19,24]),([33],[27,29,35]),([],[18,23,20,25])]⟩ (decodeTape 39 5272183524840948651451161057090805422004272138048414007455569796623176613277489185) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead409 : DeadState :=
  DeadState.leaf ⟨268468302,49,3,[c20,c7],[([],[16,21,19,24])]⟩ (decodeTape 118 169099653073199685347726635032044125627835863220540540019546144954916679573175499416517309922979949365377334762302123915892478409743957440673756463776713107564012541282751694819578459830414990351449171833289084074643000758327149715680306423159473195) (by decide +kernel)

private def dead407 : DeadState :=
  DeadState.fork ⟨268468302,17,2,[c20,c7],[([],[16,21,19,24])]⟩ ⟨268468302,17,2,[c20,c7],[([],[16,21,19,24])]⟩ [] 5 [dead408, dead409]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead404 : DeadState :=
  DeadState.fork ⟨268468302,1,1,[c20,c7],[([],[16,21,19,24])]⟩ ⟨268468302,1,1,[c20,c7],[([],[16,21,19,24])]⟩ [] 4 [dead405, dead406, dead407]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead411 : DeadState :=
  DeadState.leaf ⟨1610645694,1,1,[c22,c21,c7],[([],[16,21,20,25]),([32,34],[26,27]),([],[17,22,18,23])]⟩ (decodeTape 28 37952942133239638496362038504979159493805040970946484866346) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead412 : DeadState :=
  DeadState.leaf ⟨2684387550,1,1,[c23,c21,c7],[([],[16,21,20,25]),([32,35],[26,28]),([],[17,22,19,24])]⟩ (decodeTape 24 141385727137933082025586998215628369502966506790697) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead414 : DeadState :=
  DeadState.leaf ⟨9126838510,17,2,[c25,c21,c7],[([],[16,21,20,25]),([34,35],[27,28]),([],[18,23,19,24])]⟩ (decodeTape 19 4114866231626893644492294202285409574975) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead415 : DeadState :=
  DeadState.leaf ⟨536903822,49,3,[c21,c7],[([],[16,21,20,25])]⟩ (decodeTape 118 169099653073199685396242848550763628915661809296188029700387092967690728660887033637135412539611551996729081824175086744183100649636530514003339901185305594907669940128690103215586646458711785026230312406315145224877705097814501716399145158604637226) (by decide +kernel)

private def dead413 : DeadState :=
  DeadState.fork ⟨536903822,17,2,[c21,c7],[([],[16,21,20,25])]⟩ ⟨536903822,17,2,[c21,c7],[([],[16,21,20,25])]⟩ [] 5 [dead414, dead415]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead410 : DeadState :=
  DeadState.fork ⟨536903822,1,1,[c21,c7],[([],[16,21,20,25])]⟩ ⟨536903822,1,1,[c21,c7],[([],[16,21,20,25])]⟩ [] 4 [dead411, dead412, dead413]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead418 : DeadState :=
  DeadState.leaf ⟨35433513206,9,2,[c27,c22,c7],[([],[17,22,18,23]),([],[31,33,32,34]),([],[19,24,20,25])]⟩ (decodeTape 62 16063184829395341788617543182940518240942951266885755455808755119201784711565773525269019892890244854621078376689833153454481940881) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead419 : DeadState :=
  DeadState.leaf ⟨1073774646,73,3,[c22,c7],[([],[17,22,18,23])]⟩ (decodeTape 123 5810219894989047537033782749504009852876642915850419862939190254258501676877702414182758767165378446670919782031133008935838266716290721254568066981554021426316786492548856326762310123009833653716690153273376085704832837517942600819789322880315175403899733035) (by decide +kernel)

private def dead417 : DeadState :=
  DeadState.fork ⟨1073774646,9,2,[c22,c7],[([],[17,22,18,23])]⟩ ⟨1073774646,9,2,[c22,c7],[([],[17,22,18,23])]⟩ [] 6 [dead418, dead419]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead421 : DeadState :=
  DeadState.leaf ⟨19327385846,9,2,[c26,c23,c7],[([],[17,22,19,24]),([33],[30,32,35]),([],[18,23,20,25])]⟩ (decodeTape 35 19640414352259886127079584219830097609552284243185280123203091022171932997) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead422 : DeadState :=
  DeadState.leaf ⟨2147516502,41,3,[c23,c7],[([],[17,22,19,24])]⟩ (decodeTape 125 95194642759500554737105999219164493895248948095734804538136831397908942588208716252422487458835827465621258163714298425602312642744895648597250125846291787054549635525883688014239519349075178819182322292343323023990771488185770101068231424048417670754434258453547) (by decide +kernel)

private def dead420 : DeadState :=
  DeadState.fork ⟨2147516502,9,2,[c23,c7],[([],[17,22,19,24])]⟩ ⟨2147516502,9,2,[c23,c7],[([],[17,22,19,24])]⟩ [] 5 [dead421, dead422]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead424 : DeadState :=
  DeadState.leaf ⟨12884934902,9,2,[c25,c24,c7],[([],[17,22,20,25]),([34,35],[30,31]),([],[18,23,19,24])]⟩ (decodeTape 19 4029167371976776315663989981123671368130) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead425 : DeadState :=
  DeadState.leaf ⟨4295000214,41,3,[c24,c7],[([],[17,22,20,25])]⟩ (decodeTape 125 95194642759500554764418199359706065841312662681292457647642024963762180979384331587842045187346361397655355477983505269505870012704669913403257512214164258390367047891554256474386289769987280620894505352926673397060922833564097744135666641325601658248577931166762) (by decide +kernel)

private def dead423 : DeadState :=
  DeadState.fork ⟨4295000214,9,2,[c24,c7],[([],[17,22,20,25])]⟩ ⟨4295000214,9,2,[c24,c7],[([],[17,22,20,25])]⟩ [] 5 [dead424, dead425]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead427 : DeadState :=
  DeadState.leaf ⟨8589967462,25,3,[c25,c7],[([],[18,23,19,24])]⟩ (decodeTape 125 95194643690609046417437663967545928272813528121383049031191751901240688064225424159030455287438261736651843870776823816016152463043414698804036983126407763433572975440029229815939815200613458577602455645787693541864028177007748428065993226878406361388219581482027) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead428 : DeadState :=
  DeadState.leaf ⟨17179902118,25,3,[c26,c7],[([],[18,23,20,25])]⟩ (decodeTape 125 95194643690609046444749864108087500218877242695910070911888369061445397453059524572638109274144851181109030181170458913536291450854479012943871276215264728120787042974459381457461162803593521069623618037976835905343047259085868711430221703408643175922942697686058) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead430 : DeadState :=
  DeadState.leaf ⟨34359771334,57,4,[c27,c7],[([],[19,24,20,25])]⟩ (decodeTape 124 743708161164446074439149367394890379675686808587547660790324443113199377566421401038440539080638528526349082463841104628496613744094001811979974030169176404363607417444224161614316558308631937418669647219793836249644103863872603372450874992664511938902075065480) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead431 : DeadState :=
  DeadState.leaf ⟨32774,121,5,[c7],[]⟩ (decodeTape 23 1652818841348490351669125493186653092529597793323) (by decide +kernel)

private def dead429 : DeadState :=
  DeadState.fork ⟨32774,57,4,[c7],[]⟩ ⟨32774,57,4,[c7],[]⟩ [] 6 [dead430, dead431]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead426 : DeadState :=
  DeadState.fork ⟨32774,25,3,[c7],[]⟩ ⟨32774,25,3,[c7],[]⟩ [] 5 [dead427, dead428, dead429]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead416 : DeadState :=
  DeadState.fork ⟨32774,9,2,[c7],[]⟩ ⟨32774,9,2,[c7],[]⟩ [] 4 [dead417, dead420, dead423, dead426]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead391 : DeadState :=
  DeadState.fork ⟨32774,1,1,[c7],[]⟩ ⟨32774,1,1,[c7],[]⟩ [] 3 [dead392, dead398, dead404, dead410, dead416]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead434 : DeadState :=
  DeadState.leaf ⟨8594194558,1,1,[c25,c14,c8],[([21],[15,17,26]),([],[23,30,24,31]),([],[18,27,19,28])]⟩ (decodeTape 51 104003456293609605645453964793357936623254532251108903997705943885683238226476591004732436974302387818564267) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead435 : DeadState :=
  DeadState.leaf ⟨17184129214,1,1,[c26,c14,c8],[([21],[15,17,26]),([],[23,30,25,32]),([],[18,27,20,29])]⟩ (decodeTape 50 812527002293825044105109099948108879869172716791524300427129666999909727018438016779723687175728395029162) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead436 : DeadState :=
  DeadState.leaf ⟨4259870,33,2,[c14,c8],[([21],[15,17,26])]⟩ (decodeTape 97 1418282177883914514179020879817798130366418454822134410784777997359873146409764724225442214893604429451780254212992448111663112133397567614564487968426538593061787245085983821060990552667519390558536288902) (by decide +kernel)

private def dead433 : DeadState :=
  DeadState.fork ⟨4259870,1,1,[c14,c8],[([21],[15,17,26])]⟩ ⟨4259870,1,1,[c14,c8],[([21],[15,17,26])]⟩ [] 5 [dead434, dead435, dead436]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead438 : DeadState :=
  DeadState.leaf ⟨2155937918,1,1,[c23,c15,c8],[([21],[15,18,27]),([30],[22,24,33]),([],[17,26,19,28])]⟩ (decodeTape 31 77935231410192886369940772759964472040474225601145207245106793131) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead439 : DeadState :=
  DeadState.leaf ⟨4303421630,1,1,[c24,c15,c8],[([21],[15,18,27]),([30],[22,25,34]),([],[17,26,20,29])]⟩ (decodeTape 27 290331361480954203216710036931049371320836412135761988266) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead440 : DeadState :=
  DeadState.leaf ⟨8454190,17,2,[c15,c8],[([21],[15,18,27])]⟩ (decodeTape 95 86555731021199967208661324610467547888498396803152034702937593392636344553441203105442271717715132542430856358333248476374625316828826714950250570447480674113460892824496146554289157296248454384405126) (by decide +kernel)

private def dead437 : DeadState :=
  DeadState.fork ⟨8454190,1,1,[c15,c8],[([21],[15,18,27])]⟩ ⟨8454190,1,1,[c15,c8],[([21],[15,18,27])]⟩ [] 4 [dead438, dead439, dead440]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead441 : DeadState :=
  DeadState.leaf ⟨16842830,1,1,[c16,c8],[([21],[15,19,28])]⟩ (decodeTape 118 253002686882718352423479740221543632919536458229090615166187832102317909739817978662426137562961113842777697367631930356409224891496571825645397684071409003619726334216508490691706157711340933094038077492202098091775586015251564069061332499605837188) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead442 : DeadState :=
  DeadState.leaf ⟨33620110,1,1,[c17,c8],[([21],[15,20,29])]⟩ (decodeTape 103 6236997809771375356228723619952893276819005213011897380186693480230344280856587283435308751480326721410734454347756337993860072098191212116865762486854042315848202333413240897553993686227102964354069057101347441431812) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead444 : DeadState :=
  DeadState.leaf ⟨1073807418,5,2,[c22,c8],[([],[17,26,18,27])]⟩ (decodeTape 85 73307577671274236298349864988903382631879490492797821701493526130158869343370394346040989227174499439783790096388264600913799589623218904068498733569151868180083542015246332905606) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead445 : DeadState :=
  DeadState.leaf ⟨2147549274,5,2,[c23,c8],[([],[17,26,19,28])]⟩ (decodeTape 59 11958856603658387782827927365931245151361127457447973554883276073578835153643975614634334171475466759738436481148955755061893) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead446 : DeadState :=
  DeadState.leaf ⟨4295032986,5,2,[c24,c8],[([],[17,26,20,29])]⟩ (decodeTape 38 67024425306418333135734448544620506545715389317458389120464894362397955912163589) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead447 : DeadState :=
  DeadState.leaf ⟨65546,21,3,[c8],[]⟩ (decodeTape 74 485214425643033214992005247406830747526004733775755480341150256697504123416035373275646911523475090109038655418219892637278376551354632426866244251549996421) (by decide +kernel)

private def dead443 : DeadState :=
  DeadState.fork ⟨65546,5,2,[c8],[]⟩ ⟨65546,5,2,[c8],[]⟩ [] 4 [dead444, dead445, dead446, dead447]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead432 : DeadState :=
  DeadState.fork ⟨65546,1,1,[c8],[]⟩ ⟨65546,1,1,[c8],[]⟩ [] 2 [dead433, dead437, dead441, dead442, dead443]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead450 : DeadState :=
  DeadState.leaf ⟨8592162942,1,1,[c25,c13,c9],[([22,26],[15,16]),([],[23,27,24,28]),([],[18,30,19,31])]⟩ (decodeTape 55 28538866047922455885888800956529358993839253048989718175533359068526003447505367904573916011868688873492190088447019) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead451 : DeadState :=
  DeadState.leaf ⟨17182097598,1,1,[c26,c13,c9],[([22,26],[15,16]),([],[23,27,25,29]),([],[18,30,20,32])]⟩ (decodeTape 54 222959890999394186675243598800301264322214237943685889313145269203399691671795134868868598172483365350425515312170) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead452 : DeadState :=
  DeadState.leaf ⟨2228254,33,2,[c13,c9],[([22,26],[15,16])]⟩ (decodeTape 71 231368072745408865060112370560907380397247354566188316472885165431454617156022636706834216546529836682529339783690575560388759472860618402656003277830) (by decide +kernel)

private def dead449 : DeadState :=
  DeadState.fork ⟨2228254,1,1,[c13,c9],[([22,26],[15,16])]⟩ ⟨2228254,1,1,[c13,c9],[([22,26],[15,16])]⟩ [] 5 [dead450, dead451, dead452]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead454 : DeadState :=
  DeadState.leaf ⟨276955262,1,1,[c20,c15,c9],[([22],[15,18,30]),([27],[21,24,33]),([26],[16,19,31])]⟩ (decodeTape 28 37162460654632186143178701483542664090447333221138669718315) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead455 : DeadState :=
  DeadState.leaf ⟨545390782,1,1,[c21,c15,c9],[([22],[15,18,30]),([27],[21,25,34]),([26],[16,20,32])]⟩ (decodeTape 23 1081569965136487885555111650010159841564942879530) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead456 : DeadState :=
  DeadState.leaf ⟨8519734,9,2,[c15,c9],[([22],[15,18,30])]⟩ (decodeTape 91 322445225049555179570836523142535700460071056981853547901395914126967630643019812441121843977098028559739575532639838851972577406399907505043203548511687090349023643890830744453398096144714502) (by decide +kernel)

private def dead453 : DeadState :=
  DeadState.fork ⟨8519734,1,1,[c15,c9],[([22],[15,18,30])]⟩ ⟨8519734,1,1,[c15,c9],[([22],[15,18,30])]⟩ [] 3 [dead454, dead455, dead456]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead457 : DeadState :=
  DeadState.leaf ⟨16908374,1,1,[c16,c9],[([22],[15,19,31])]⟩ (decodeTape 112 57526150813536867752190102955481345936278335245869082771776568442867776572470479700133866918025985052904330079305845991893382934668801049756964431762410268613474171906097390146869381522220315206396571017570849002217259810634024410764675) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead458 : DeadState :=
  DeadState.leaf ⟨33685654,1,1,[c17,c9],[([22],[15,20,32])]⟩ (decodeTape 99 23234627432269511213245764439915360322576875044762896280715285988437890098167836903663778411112864383781461274130490959692898804222930405159129259392878671704164647963246355636030965983170116110487990590330115) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead460 : DeadState :=
  DeadState.leaf ⟨134348858,5,2,[c19,c9],[([26],[16,18,30])]⟩ (decodeTape 56 5702427198481092206679025356868543037827248341079397261606552943116158830819850244027219209220869320980290321668345094) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead461 : DeadState :=
  DeadState.leaf ⟨268566618,5,2,[c20,c9],[([26],[16,19,31])]⟩ (decodeTape 34 249712577382473847473959249316883629274837662119352684499393750635963013) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead462 : DeadState :=
  DeadState.leaf ⟨537002138,5,2,[c21,c9],[([26],[16,20,32])]⟩ (decodeTape 30 930150770876801003082250215710648635565511054010206497620893573) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead463 : DeadState :=
  DeadState.leaf ⟨131090,13,3,[c9],[]⟩ (decodeTape 62 25084976711435651973188364008697979697871289846517451838768092843905039061317382016047748859133545027662166792672179206400390763909) (by decide +kernel)

private def dead459 : DeadState :=
  DeadState.fork ⟨131090,5,2,[c9],[]⟩ ⟨131090,5,2,[c9],[]⟩ [] 3 [dead460, dead461, dead462, dead463]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead448 : DeadState :=
  DeadState.fork ⟨131090,1,1,[c9],[]⟩ ⟨131090,1,1,[c9],[]⟩ [] 2 [dead449, dead453, dead457, dead458, dead459]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead465 : DeadState :=
  DeadState.leaf ⟨2359342,1,1,[c13,c10],[([23,27],[15,16])]⟩ (decodeTape 109 27430605554766511624932414836157956571309970770551526307467450985253574662092735204057117116211657778477958110949069080176431354892296285479847158550607568300705155374533020591660940051622518789060929895772349751866300398662047108) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead466 : DeadState :=
  DeadState.leaf ⟨4456502,1,1,[c14,c10],[([23,30],[15,17])]⟩ (decodeTape 93 5282942463059967060872411024292207656946963060974553479375105377420314465867142457003724572917890949441932881677319448429811579079771775995924737348178002285663682408362861888395470764505282368899) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead467 : DeadState :=
  DeadState.leaf ⟨17039462,1,1,[c16,c10],[([23],[15,19,33])]⟩ (decodeTape 97 1418129106468222118492738047891650640708115582051603776277411006022755898379818984673481033596696218736871136306460992646006929580362367044055636067687784193175532258890985286731333010085875689986623542659) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead468 : DeadState :=
  DeadState.leaf ⟨33816742,1,1,[c17,c10],[([23],[15,20,34])]⟩ (decodeTape 83 4474826472079240816081250787180448637399205108636856160567624397186093292744399122394915250993916284082347591924340569375158110764027667715695341638998548294623514554347558147) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead470 : DeadState :=
  DeadState.leaf ⟨67371066,5,2,[c18,c10],[([27,30],[16,17])]⟩ (decodeTape 38 67039003505656370643481298253479749052974182626154667767021189549744649768323078) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead471 : DeadState :=
  DeadState.leaf ⟨268697706,5,2,[c20,c10],[([27],[16,19,33])]⟩ (decodeTape 31 119072235766636775719914989465275574696480734197411957494211993988) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead472 : DeadState :=
  DeadState.leaf ⟨537133226,5,2,[c21,c10],[([27],[16,20,34])]⟩ (decodeTape 27 443530456177018309350912684252198270038414435610379951876) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead473 : DeadState :=
  DeadState.leaf ⟨262178,13,3,[c10],[]⟩ (decodeTape 49 10130647782402953301317905537169639553775133827554068096252284038226087635460844487809450901507897382276) (by decide +kernel)

private def dead469 : DeadState :=
  DeadState.fork ⟨262178,5,2,[c10],[]⟩ ⟨262178,5,2,[c10],[]⟩ [] 3 [dead470, dead471, dead472, dead473]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead464 : DeadState :=
  DeadState.fork ⟨262178,1,1,[c10],[]⟩ ⟨262178,1,1,[c10],[]⟩ [] 2 [dead465, dead466, dead467, dead468, dead469]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead475 : DeadState :=
  DeadState.leaf ⟨2621518,1,1,[c13,c11],[([24,28],[15,16])]⟩ (decodeTape 81 273121723931330626468519911445991976074817129875633271912609531142477327407680883358390973441988755643805940852024709507540502895030491346380911007041194060046141222950276) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead476 : DeadState :=
  DeadState.leaf ⟨4718678,1,1,[c14,c11],[([24,31],[15,17])]⟩ (decodeTape 64 410947895767198107058340428221907412571128649748502106375873489168484903683317688003834058977661655959274602838749190994993648184202627) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead477 : DeadState :=
  DeadState.leaf ⟨8912998,1,1,[c15,c11],[([24,33],[15,18])]⟩ (decodeTape 60 1530900209275496643224872612847623636377866819629501345267665613914791378206834111036681778007671942432251466477395931373376899) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead478 : DeadState :=
  DeadState.leaf ⟨34078918,1,1,[c17,c11],[([24],[15,20,35])]⟩ (decodeTape 68 110312989420980519355788220266801928697793455166322096613939039482731433808255295417408806237523177445834019740409341357376260046329688136881283) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead480 : DeadState :=
  DeadState.leaf ⟨67633242,5,2,[c18,c11],[([28,31],[16,17])]⟩ (decodeTape 26 3465835249225493860060357498807834440840021108880923141) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead481 : DeadState :=
  DeadState.leaf ⟨134742122,5,2,[c19,c11],[([28,33],[16,18])]⟩ (decodeTape 26 3465835249226887656635265662754331538959513425760066052) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead482 : DeadState :=
  DeadState.leaf ⟨537395402,5,2,[c21,c11],[([28],[16,20,35])]⟩ (decodeTape 24 211491803726431495593265715534015446534818741721732) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead483 : DeadState :=
  DeadState.leaf ⟨524354,13,3,[c11],[]⟩ (decodeTape 56 5703047697525028090469673393269188434553281400739024284020413197070033094361371889251576598808191713943869512517244292) (by decide +kernel)

private def dead479 : DeadState :=
  DeadState.fork ⟨524354,5,2,[c11],[]⟩ ⟨524354,5,2,[c11],[]⟩ [] 3 [dead480, dead481, dead482, dead483]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead474 : DeadState :=
  DeadState.fork ⟨524354,1,1,[c11],[]⟩ ⟨524354,1,1,[c11],[]⟩ [] 2 [dead475, dead476, dead477, dead478, dead479]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead485 : DeadState :=
  DeadState.leaf ⟨3145870,1,1,[c13,c12],[([25,29],[15,16])]⟩ (decodeTape 65 52601330660909042961718731041215749639662432948251566161719564388508175334728030984324438659364571754978088832018372144958788485609821444) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead486 : DeadState :=
  DeadState.leaf ⟨5243030,1,1,[c14,c12],[([25,32],[15,17])]⟩ (decodeTape 65 52601330660909042961719346697564861802016115401246208084969968708684013766786561386159773139054117662948870576508641140443045076175820035) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead487 : DeadState :=
  DeadState.leaf ⟨9437350,1,1,[c15,c12],[([25,34],[15,18])]⟩ (decodeTape 60 1530900209354300655911229395212536229241867717076209567297838203437737138893687922519764860640897472889239591757564708850373891) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead488 : DeadState :=
  DeadState.leaf ⟨17825990,1,1,[c16,c12],[([25,35],[15,19])]⟩ (decodeTape 51 165980533284044632834443028930582477164922781259832712302953719082626216462319977596089494251174624207099011) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead490 : DeadState :=
  DeadState.leaf ⟨68157594,5,2,[c18,c12],[([29,32],[16,17])]⟩ (decodeTape 28 56784244726233494688779738878909779063091929308795356666373) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead491 : DeadState :=
  DeadState.leaf ⟨135266474,5,2,[c19,c12],[([29,34],[16,18])]⟩ (decodeTape 28 56784244726256330651863034237009187518663079267102385592836) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead492 : DeadState :=
  DeadState.leaf ⟨269484234,5,2,[c20,c12],[([29,35],[16,19])]⟩ (decodeTape 25 27076837885978856397563473814492917560690292409844276) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead493 : DeadState :=
  DeadState.leaf ⟨1048706,13,3,[c12],[]⟩ (decodeTape 75 62100690216855066894104686554017921220879219755162365216230425303021628232307336215782947559847633146284927928052915166498369249852525379786434845434673190148) (by decide +kernel)

private def dead489 : DeadState :=
  DeadState.fork ⟨1048706,5,2,[c12],[]⟩ ⟨1048706,5,2,[c12],[]⟩ [] 3 [dead490, dead491, dead492, dead493]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead484 : DeadState :=
  DeadState.fork ⟨1048706,1,1,[c12],[]⟩ ⟨1048706,1,1,[c12],[]⟩ [] 2 [dead485, dead486, dead487, dead488, dead489]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead496 : DeadState :=
  DeadState.leaf ⟨1075839036,3,2,[c22,c13],[([],[22,26,23,27])]⟩ (decodeTape 85 73307577671274236298899048801713831409078043311955195228046981990819587053542683425685145995520865945048709207926925921676699572804687054856728247839713298692496844914572949244678) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead497 : DeadState :=
  DeadState.leaf ⟨2149580892,3,2,[c23,c13],[([],[22,26,24,28])]⟩ (decodeTape 59 11958856603658387794295425914008414666945042865250160704553772153952943893497811720355928789074104749189638544770129717486213) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead498 : DeadState :=
  DeadState.leaf ⟨4297064604,3,2,[c24,c13],[([],[22,26,25,29])]⟩ (decodeTape 38 67024425306418333135838805362842032209197715051921517723608607846121840743342341) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead499 : DeadState :=
  DeadState.leaf ⟨2097164,19,3,[c13],[]⟩ (decodeTape 74 485214422446362687559903499250136618260651217472924688463842939999144353353048625240009175926190828438806988701503619670795517795274270506541274890219410821) (by decide +kernel)

private def dead495 : DeadState :=
  DeadState.fork ⟨2097164,3,2,[c13],[]⟩ ⟨2097164,3,2,[c13],[]⟩ [] 4 [dead496, dead497, dead498, dead499]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead501 : DeadState :=
  DeadState.leaf ⟨138412092,3,2,[c19,c14],[([26],[21,23,30])]⟩ (decodeTape 52 21243196720186964447504832241658162187036528393343780804009346198363281022823938486831352817522118648331701510) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead502 : DeadState :=
  DeadState.leaf ⟨272629852,3,2,[c20,c14],[([26],[21,24,31])]⟩ (decodeTape 29 7267592515053514150012394872143723887826742397038507693530885) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead503 : DeadState :=
  DeadState.leaf ⟨541065372,3,2,[c21,c14],[([26],[21,25,32])]⟩ (decodeTape 30 930150770876801003083698457490227218521784484041388660049829637) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead504 : DeadState :=
  DeadState.leaf ⟨4194324,11,3,[c14],[]⟩ (decodeTape 62 25084976546171659159969865158556790463798873032153759403661521048230856154003253467917065843587752580246692038515147823268934047109) (by decide +kernel)

private def dead500 : DeadState :=
  DeadState.fork ⟨4194324,3,2,[c14],[]⟩ ⟨4194324,3,2,[c14],[]⟩ [] 3 [dead501, dead502, dead503, dead504]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead506 : DeadState :=
  DeadState.leaf ⟨75497532,3,2,[c18,c15],[([27,30],[21,22])]⟩ (decodeTape 34 249712577328441211833885037176171397235128783530961225419241091096431238) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead507 : DeadState :=
  DeadState.leaf ⟨276824172,3,2,[c20,c15],[([27],[21,24,33])]⟩ (decodeTape 28 56778066523855579297114264626491184963147001122214122659716) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead508 : DeadState :=
  DeadState.leaf ⟨545259692,3,2,[c21,c15],[([27],[21,25,34])]⟩ (decodeTape 27 443530456177018309351603261319043366463865476811888516868) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead509 : DeadState :=
  DeadState.leaf ⟨8388644,11,3,[c15],[]⟩ (decodeTape 49 10130647715653358180127846331095172808882769389743995652421849708304864563764222826357887191981277222276) (by decide +kernel)

private def dead505 : DeadState :=
  DeadState.fork ⟨8388644,3,2,[c15],[]⟩ ⟨8388644,3,2,[c15],[]⟩ [] 3 [dead506, dead507, dead508, dead509]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead510 : DeadState :=
  DeadState.leaf ⟨16777284,3,2,[c16],[]⟩ (decodeTape 125 142427846118614103285449193178912087396696282132713548830613131720072050245126146661615546034870244139004659558511000081743526963573398847906476787923663509150041398313521910286383890162127320676908643161095310654242065507640298793296279021454620644321057143931523) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead512 : DeadState :=
  DeadState.leaf ⟨100663452,3,2,[c18,c17],[([29,32],[21,22])]⟩ (decodeTape 28 56771897636523497329661421321615606342764497287102254193797) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead513 : DeadState :=
  DeadState.leaf ⟨167772332,3,2,[c19,c17],[([29,34],[21,23])]⟩ (decodeTape 27 443530456177018298463252904292086212796790423809076141188) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead514 : DeadState :=
  DeadState.leaf ⟨301990092,3,2,[c20,c17],[([29,35],[21,24])]⟩ (decodeTape 23 1652279716612740867681639443821129933390443610681) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead515 : DeadState :=
  DeadState.leaf ⟨33554564,11,3,[c17],[]⟩ (decodeTape 69 14120062089132543265531163067398909487318171538481696402997671287784138435253804292433216014803271300839928891027460237761276473643794150116463876) (by decide +kernel)

private def dead511 : DeadState :=
  DeadState.fork ⟨33554564,3,2,[c17],[]⟩ ⟨33554564,3,2,[c17],[]⟩ [] 3 [dead512, dead513, dead514, dead515]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead517 : DeadState :=
  DeadState.leaf ⟨67108888,7,3,[c18],[]⟩ (decodeTape 62 25084955392380579068002012340485662127891880224157234386162328599004723062941117848463025490927954743905449809448920738244199896453) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead518 : DeadState :=
  DeadState.leaf ⟨134217768,7,3,[c19],[]⟩ (decodeTape 49 10130639171705182667800267953563871174426302990983774545201327100235607030459578913102184122340887991684) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead519 : DeadState :=
  DeadState.leaf ⟨268435528,7,3,[c20],[]⟩ (decodeTape 48 79145618533020811559917095236986526025161589926274100387823129005333657674290659750033431535958332804) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead520 : DeadState :=
  DeadState.leaf ⟨536871048,7,3,[c21],[]⟩ (decodeTape 49 10130639172748145091553685527881732102665155208168348959462781921419539991377372380755108130446860326148) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead522 : DeadState :=
  DeadState.leaf ⟨1073741872,15,4,[c22],[]⟩ (decodeTape 30 930251841102986241372142370427690645071371618610514192401244550) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead523 : DeadState :=
  DeadState.leaf ⟨2147483728,15,4,[c23],[]⟩ (decodeTape 30 930251841150876727201213562924147514346218927891417713091879173) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead524 : DeadState :=
  DeadState.leaf ⟨4294967440,15,4,[c24],[]⟩ (decodeTape 30 930251841198767213031678552000704844445289860306163369549816069) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private def dead525 : DeadState :=
  DeadState.leaf ⟨0,31,5,[],[]⟩ (decodeTape 71 231967448431530029172640788346326527767517622349413662879705683192672214757587415607716338255521266248178063741507075463000630369172618816098498975109) (by decide +kernel)

private def dead521 : DeadState :=
  DeadState.fork ⟨0,15,4,[],[]⟩ ⟨0,15,4,[],[]⟩ [] 4 [dead522, dead523, dead524, dead525]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead516 : DeadState :=
  DeadState.fork ⟨0,7,3,[],[]⟩ ⟨0,7,3,[],[]⟩ [] 3 [dead517, dead518, dead519, dead520, dead521]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead494 : DeadState :=
  DeadState.fork ⟨0,3,2,[],[]⟩ ⟨0,3,2,[],[]⟩ [] 2 [dead495, dead500, dead505, dead510, dead511, dead516]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead390 : DeadState :=
  DeadState.fork ⟨0,1,1,[],[]⟩ ⟨0,1,1,[],[]⟩ [] 1 [dead391, dead432, dead448, dead464, dead474, dead484, dead494]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

private def dead0 : DeadState :=
  DeadState.fork ⟨0,0,0,[],[]⟩ ⟨0,0,0,[],[]⟩ [] 0 [dead1, dead94, dead170, dead228, dead279, dead315, dead351, dead390]
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)

theorem no_models (F : Finset Triple) : ¬ Model F :=
  fun hm => dead0.excluded F hm (init_valid F)

end NineCutSearch

namespace NineCutSearch

open Finset OrderedUnitCuts

private theorem row_facts :
    ∀ t ∈ triples.toFinset, t.rows.Nodup ∧ t.rows.length = 3 ∧
      ∀ i ∈ t.rows.toFinset, i < 9 := by
  decide +kernel

private theorem pair_index_bound : ∀ x y : Fin 9, x ≠ y → pairIndex x.val y.val < 36 := by
  decide +kernel

private theorem triple_for_rows :
    ∀ S : Finset (Fin 9), S.card = 3 →
      ∃ t ∈ triples.toFinset, t.rows.toFinset = S.image Fin.val := by
  decide +kernel

private theorem edge_iff_rows :
    ∀ t ∈ triples.toFinset, ∀ x y : Fin 9, x ≠ y →
      (pairIndex x.val y.val ∈ t.edges ↔ x.val ∈ t.rows ∧ y.val ∈ t.rows) := by
  decide +kernel

private theorem edge_endpoints :
    ∀ t ∈ triples.toFinset, ∀ e ∈ t.edges.toFinset,
      ∃ x y : Fin 9, x < y ∧ x.val ∈ t.rows ∧ y.val ∈ t.rows ∧ e = pairIndex x.val y.val := by
  decide +kernel

private theorem pairIndex_swap (x y : ℕ) : pairIndex x y = pairIndex y x := by
  simp only [pairIndex,min_comm,max_comm]

private def crossData (t t' : Triple) (z : ℕ) : List (ℕ × ℕ × ℕ) :=
  (t.rows.erase z).flatMap fun i => (t'.rows.erase z).map fun j => (i,j,pairIndex i j)

private theorem cross_rows {t t' : Triple}
    (ht : t ∈ triples.toFinset) (ht' : t' ∈ triples.toFinset) {z : ℕ} {p : ℕ × ℕ × ℕ}
    (hp : p ∈ crossData t t' z) :
    ∃ x y : Fin 9, x.val ∈ t.rows ∧ y.val ∈ t'.rows ∧ x.val ≠ z ∧ y.val ≠ z ∧
      p = (x.val,y.val,pairIndex x.val y.val) := by
  have hA := (row_facts t ht).1
  have hB := (row_facts t' ht').1
  obtain ⟨i,hi,hpi⟩ := List.mem_flatMap.1 hp
  obtain ⟨j,hj,rfl⟩ := List.mem_map.1 hpi
  obtain ⟨hin,hit⟩ := hA.mem_erase_iff.1 hi
  obtain ⟨hjn,hjt⟩ := hB.mem_erase_iff.1 hj
  exact ⟨⟨i,(row_facts t ht).2.2 i (List.mem_toFinset.2 hit)⟩,
    ⟨j,(row_facts t' ht').2.2 j (List.mem_toFinset.2 hjt)⟩,hit,hjt,hin,hjn,rfl⟩

private theorem direction_shape {t t' : Triple}
    (ht : t ∈ triples.toFinset) (ht' : t' ∈ triples.toFinset) {c : Constraint}
    (hc : direction t t' = some c) :
    t ≠ t' ∧ ∃ z : Fin 9, z.val ∈ t.rows ∧ z.val ∈ t'.rows ∧
      (∀ e ∈ c.1, ∃ x y : Fin 9, x.val ∈ t.rows ∧ y.val ∈ t'.rows ∧
        x ≠ z ∧ y ≠ z ∧ x < y ∧ e = pairIndex x.val y.val) ∧
      (∀ e ∈ c.2, ∃ x y : Fin 9, x.val ∈ t.rows ∧ y.val ∈ t'.rows ∧
        x ≠ z ∧ y ≠ z ∧ y < x ∧ e = pairIndex x.val y.val) := by
  unfold direction at hc
  cases hL : t.rows.filter (fun i => t'.rows.contains i) with
  | nil => rw [hL] at hc; cases hc
  | cons z rest =>
    cases rest with
    | cons w ws => rw [hL] at hc; cases hc
    | nil =>
      simp only [hL, Option.some.injEq] at hc
      subst c
      have hz : z ∈ t.rows.filter (fun i => t'.rows.contains i) := by rw [hL]; simp
      obtain ⟨hzt,hzt'⟩ := List.mem_filter.1 hz
      have hzt' := List.contains_iff_mem.1 hzt'
      have hne : t ≠ t' := by
        rintro rfl
        have ha : t.rows.filter (fun i => t.rows.contains i) = t.rows :=
          List.filter_eq_self.2 fun i hi => List.contains_iff_mem.2 hi
        rw [ha] at hL
        have he := (row_facts t ht).2.1
        rw [hL] at he
        simp at he
      let z' : Fin 9 := ⟨z,(row_facts t ht).2.2 z (List.mem_toFinset.2 hzt)⟩
      refine ⟨hne,z',hzt,hzt',?_,?_⟩
      · intro e he
        obtain ⟨p,hp,rfl⟩ := List.mem_map.1 he
        obtain ⟨hprod,hlt⟩ := List.mem_filter.1 hp
        obtain ⟨x,y,hx,hy,hxz,hyz,rfl⟩ := cross_rows ht ht' hprod
        refine ⟨x,y,hx,hy,fun h => hxz (congrArg Fin.val h),
          fun h => hyz (congrArg Fin.val h), ?_, rfl⟩
        exact of_decide_eq_true hlt
      · intro e he
        obtain ⟨p,hp,rfl⟩ := List.mem_map.1 he
        obtain ⟨hprod,hlt⟩ := List.mem_filter.1 hp
        obtain ⟨x,y,hx,hy,hxz,hyz,rfl⟩ := cross_rows ht ht' hprod
        refine ⟨x,y,hx,hy,fun h => hxz (congrArg Fin.val h),
          fun h => hyz (congrArg Fin.val h), ?_, rfl⟩
        exact of_decide_eq_true hlt

private theorem ordered_column_safety {d : Fin 9 → Fin 9 → ℝ}
    (hm : StrictMonge d) (hn : NoAcuteCorners d) (F : Finset Triple)
    (col : Fin 9 → Triple) (htab : ∀ k, col k ∈ triples.toFinset)
    (hu : ∀ (k i : Fin 9), i.val ∈ (col k).rows → d i k = 1)
    (edgeCover : ∀ {x y : Fin 9}, x ≠ y → pairIndex x.val y.val ∈ covered F →
      ∃ l, d x l = 1 ∧ d y l = 1)
    {j k : Fin 9} {c : Constraint} (hdir : direction (col j) (col k) = some c) :
    SafePair F c := by
  obtain ⟨hne,z,hzj,hzk,hd₁,hd₂⟩ := direction_shape (htab j) (htab k) hdir
  have hjk : j ≠ k := fun he => hne (congrArg col he)
  refine ⟨?_,?_,?_⟩
  · intro e he
    obtain ⟨x,y,_,_,_,_,hxy,rfl⟩ := hd₁ e he
    exact pair_index_bound x y hxy.ne
  · intro e he
    obtain ⟨x,y,_,_,_,_,hyx,rfl⟩ := hd₂ e he
    exact pair_index_bound x y hyx.ne.symm
  · rintro ⟨⟨e,he,hec⟩,⟨f,hf,hfc⟩⟩
    rcases lt_or_gt_of_ne hjk with hjk | hkj
    · obtain ⟨x,y,hx,hy,hxz,hyz,hxy,rfl⟩ := hd₁ e he
      obtain ⟨l,hxl,hyl⟩ := edgeCover hxy.ne hec
      exact hxy.not_gt (intersection_pair_order hm hn hjk hxy.ne hxz hyz
        (hu j x hx) hxl (hu k y hy) hyl (hu j z hzj) (hu k z hzk))
    · obtain ⟨x,y,hx,hy,hxz,hyz,hyx,rfl⟩ := hd₂ f hf
      obtain ⟨l,hxl,hyl⟩ := edgeCover hyx.ne.symm hfc
      exact hyx.not_gt (intersection_pair_order hm hn hkj hyx.ne hyz hxz
        (hu k y hy) hyl (hu j x hx) hxl (hu k z hzk) (hu j z hzj))

private theorem ordered_column_separation {d : Fin 9 → Fin 9 → ℝ}
    (hm : StrictMonge d) (col : Fin 9 → Triple) (htab : ∀ k, col k ∈ triples.toFinset)
    (hu : ∀ (k i : Fin 9), i.val ∈ (col k).rows → d i k = 1)
    {j k : Fin 9} (hjk : j ≠ k) :
    Disjoint (col j).edges.toFinset (col k).edges.toFinset := by
  apply Finset.disjoint_left.2
  intro e he he'
  obtain ⟨x,y,hxy,hx,hy,rfl⟩ := edge_endpoints _ (htab j) e he
  obtain ⟨hx',hy'⟩ := (edge_iff_rows _ (htab k) x y hxy.ne).1 (List.mem_toFinset.1 he')
  exact no_two_common hm hxy.ne hjk (hu j x hx) (hu k x hx') (hu j y hy) (hu k y hy')

private theorem realize_covered_edge {d : Fin 9 → Fin 9 → ℝ} (F : Finset Triple)
    (col : Fin 9 → Triple) (hF : ∀ {t}, t ∈ F → ∃ l, col l = t)
    (htab : ∀ l, col l ∈ triples.toFinset)
    (hu : ∀ (l i : Fin 9), i.val ∈ (col l).rows → d i l = 1)
    {x y : Fin 9} (hxy : x ≠ y) (he : pairIndex x.val y.val ∈ covered F) :
    ∃ l, d x l = 1 ∧ d y l = 1 := by
  have hw : ∃ t ∈ F, pairIndex x.val y.val ∈ t.edges :=
    (covered_mem (F := F) (e := pairIndex x.val y.val)).1 he
  obtain ⟨t,ht,hent⟩ := hw
  obtain ⟨l,rfl⟩ := hF ht
  obtain ⟨hx,hy⟩ := (edge_iff_rows _ (htab l) x y hxy).1 hent
  exact ⟨l,hu l x hx,hu l y hy⟩
private theorem model_of_selected_rows {d : Fin 9 → Fin 9 → ℝ} (hm : StrictMonge d)
    (hn : NoAcuteCorners d) (S : Fin 9 → Finset (Fin 9)) (hc : ∀ j, (S j).card = 3)
    (hu : ∀ j i, i ∈ S j → d i j = 1)
    (col : Fin 9 → Triple) (htab : ∀ j, col j ∈ triples.toFinset)
    (hrows : ∀ j, (col j).rows.toFinset = (S j).image Fin.val) :
    ∃ F, Model F := by
  classical
  let F := univ.image col
  have hf {t : Triple} (ht : t ∈ F) : ∃ j, col j = t := by
    obtain ⟨j, _, hj⟩ := mem_image.1 ht
    exact ⟨j,hj⟩
  have row {j i} : i.val ∈ (col j).rows ↔ i ∈ S j := by
    rw [← List.mem_toFinset,hrows,mem_image]
    constructor
    · rintro ⟨x,hx,hx'⟩
      exact (Fin.ext hx') ▸ hx
    · intro hi
      exact ⟨i,hi,rfl⟩
  have hs {j i} (hi : i.val ∈ (col j).rows) : d i j = 1 :=
    hu j i (row.1 hi)
  have hinj : Function.Injective col := by
    intro j k hEq
    by_contra hne
    obtain ⟨x,y,hx,hy,hxy⟩ := one_lt_card_iff.1 (by rw [hc]; decide : 1 < (S j).card)
    have hxj := row.2 hx
    have hyj := row.2 hy
    have hxk : x.val ∈ (col k).rows := hEq ▸ hxj
    have hyk : y.val ∈ (col k).rows := hEq ▸ hyj
    exact no_two_common hm hxy hne (hs hxj) (hs hxk) (hs hyj) (hs hyk)
  have hFs : F ⊆ triples.toFinset := by
    intro t ht
    obtain ⟨j,rfl⟩ := hf ht
    exact htab j
  refine ⟨F,⟨hFs,?_,?_,?_⟩⟩
  · simp [F,card_image_of_injective _ hinj]
  · intro t ht t' ht' hne
    obtain ⟨j,rfl⟩ := hf ht
    obtain ⟨k,rfl⟩ := hf ht'
    exact ordered_column_separation hm col htab (fun _ _ => hs) (fun he => hne (congrArg col he))
  · intro t ht t' ht' c hdir
    obtain ⟨j,rfl⟩ := hf ht
    obtain ⟨k,rfl⟩ := hf ht'
    exact ordered_column_safety hm hn F col htab (fun _ _ => hs)
      (realize_covered_edge F col (@hf) htab (fun _ _ => hs)) hdir

theorem model_of_distances {d : Fin 9 → Fin 9 → ℝ} (hm : StrictMonge d)
    (hn : NoAcuteCorners d) (hdeg : ∀ j, 3 ≤ (univ.filter (fun i => d i j = 1)).card) :
    ∃ F, Model F := by
  classical
  choose S hsub hc using fun j => exists_subset_card_eq (hdeg j)
  choose col htab hrows using fun j => triple_for_rows (S j) (hc j)
  exact model_of_selected_rows hm hn S hc (fun j i hi => (mem_filter.1 (hsub j hi)).2)
    col htab hrows

theorem no_nine_columns (d : Fin 9 → Fin 9 → ℝ) (hm : StrictMonge d)
    (hn : NoAcuteCorners d) (hdeg : ∀ j, 3 ≤ (univ.filter fun i => d i j = 1).card) :
    False := by
  obtain ⟨F,hF⟩ := model_of_distances hm hn hdeg
  exact no_models F hF

end NineCutSearch

theorem OMA.solution : OMA.R_Erdos97_erdos_97_variants_three_unit_distance_cut_min_R1.H2 :=
  OrderedUnitCuts.cut_minimum_of_nine_case NineCutSearch.no_nine_columns