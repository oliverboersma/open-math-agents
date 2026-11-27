import OMAReductions.R_Hilbert17_hilbert_17th_problem_R1_H3_R1
import Mathlib

namespace Hilbert17H3Proof

section BasicHelpers

def sameSign {K₁ K₂ : Type} [LinearOrder K₁] [Zero K₁] [LinearOrder K₂] [Zero K₂]
    (x : K₁) (y : K₂) : Prop :=
  (x < 0 ↔ y < 0) ∧ (x = 0 ↔ y = 0)

lemma sameSign_pos {K₁ K₂ : Type} [LinearOrder K₁] [Zero K₁] [LinearOrder K₂] [Zero K₂]
    {x : K₁} {y : K₂} (h : sameSign x y) : 0 < x ↔ 0 < y := by
  constructor
  · intro hx
    have h1 : ¬ (x < 0) := not_lt.mpr hx.le
    have h2 : x ≠ 0 := hx.ne'
    have hy1 : ¬ (y < 0) := fun hy => h1 (h.1.mpr hy)
    have hy2 : y ≠ 0 := fun hy => h2 (h.2.mpr hy)
    exact lt_of_le_of_ne (not_lt.mp hy1) hy2.symm
  · intro hy
    have h1 : ¬ (y < 0) := not_lt.mpr hy.le
    have h2 : y ≠ 0 := hy.ne'
    have hx1 : ¬ (x < 0) := fun hx => h1 (h.1.mp hx)
    have hx2 : x ≠ 0 := fun hx => h2 (h.2.mp hx)
    exact lt_of_le_of_ne (not_lt.mp hx1) hx2.symm

lemma sameSign_symm {K₁ K₂ : Type} [LinearOrder K₁] [Zero K₁] [LinearOrder K₂] [Zero K₂]
    {x : K₁} {y : K₂} (h : sameSign x y) : sameSign y x :=
  ⟨h.1.symm, h.2.symm⟩

lemma sameSign_refl {K : Type} [LinearOrder K] [Zero K] (x : K) : sameSign x x :=
  ⟨Iff.rfl, Iff.rfl⟩

lemma sameSign_trans {K₁ K₂ K₃ : Type} [LinearOrder K₁] [Zero K₁] [LinearOrder K₂] [Zero K₂]
    [LinearOrder K₃] [Zero K₃] {x : K₁} {y : K₂} {z : K₃}
    (h1 : sameSign x y) (h2 : sameSign y z) : sameSign x z :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

lemma sameSign_of_mul_pos {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {x y : K} (h : 0 < x * y) : sameSign x y := by
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy, mul_zero] at h
    exact lt_irrefl 0 h
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · have hx : x < 0 := neg_of_mul_pos_left h hy.le
    exact ⟨⟨fun _ => hy, fun _ => hx⟩, ⟨fun hx0 => absurd hx0 hx.ne, fun hy0' => absurd hy0' hy.ne⟩⟩
  · exact absurd rfl hy0
  · have hx : 0 < x := pos_of_mul_pos_left h hy.le
    exact ⟨⟨fun hx' => absurd hx' (not_lt.mpr hx.le), fun hy' => absurd hy' (not_lt.mpr hy.le)⟩,
      ⟨fun hx0 => absurd hx0 hx.ne', fun hy0' => absurd hy0' hy.ne'⟩⟩

lemma sameSign_mul {K₁ K₂ : Type} [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂]
    {a₁ b₁ : K₁} {a₂ b₂ : K₂} (ha : sameSign a₁ a₂) (hb : sameSign b₁ b₂) :
    sameSign (a₁ * b₁) (a₂ * b₂) := by
  have h0 : a₁ * b₁ = 0 ↔ a₂ * b₂ = 0 := by
    simp only [mul_eq_zero, ha.2, hb.2]
  refine ⟨?_, h0⟩
  rcases lt_trichotomy a₁ 0 with ha1 | ha1 | ha1
  · have ha2 : a₂ < 0 := ha.1.mp ha1
    rcases lt_trichotomy b₁ 0 with hb1 | hb1 | hb1
    · have hb2 : b₂ < 0 := hb.1.mp hb1
      have h1 : 0 < a₁ * b₁ := mul_pos_of_neg_of_neg ha1 hb1
      have h2 : 0 < a₂ * b₂ := mul_pos_of_neg_of_neg ha2 hb2
      exact ⟨fun h => absurd h (not_lt.mpr h1.le), fun h => absurd h (not_lt.mpr h2.le)⟩
    · subst hb1
      have hb2 : b₂ = 0 := hb.2.mp rfl
      simp [hb2]
    · have hb2 : 0 < b₂ := (sameSign_pos hb).mp hb1
      exact ⟨fun _ => mul_neg_of_neg_of_pos ha2 hb2, fun _ => mul_neg_of_neg_of_pos ha1 hb1⟩
  · subst ha1
    have ha2 : a₂ = 0 := ha.2.mp rfl
    simp [ha2]
  · have ha2 : 0 < a₂ := (sameSign_pos ha).mp ha1
    rcases lt_trichotomy b₁ 0 with hb1 | hb1 | hb1
    · have hb2 : b₂ < 0 := hb.1.mp hb1
      exact ⟨fun _ => mul_neg_of_pos_of_neg ha2 hb2, fun _ => mul_neg_of_pos_of_neg ha1 hb1⟩
    · subst hb1
      have hb2 : b₂ = 0 := hb.2.mp rfl
      simp [hb2]
    · have hb2 : 0 < b₂ := (sameSign_pos hb).mp hb1
      have h1 : 0 < a₁ * b₁ := mul_pos ha1 hb1
      have h2 : 0 < a₂ * b₂ := mul_pos ha2 hb2
      exact ⟨fun h => absurd h (not_lt.mpr h1.le), fun h => absurd h (not_lt.mpr h2.le)⟩

lemma sameSign_zero {K₁ K₂ : Type} [LinearOrder K₁] [Zero K₁] [LinearOrder K₂] [Zero K₂] :
    sameSign (0 : K₁) (0 : K₂) :=
  ⟨by simp, by simp⟩

lemma sameSign_neg_one_pow {K₁ K₂ : Type} [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂] (d : ℕ) :
    sameSign ((-1 : K₁) ^ d) ((-1 : K₂) ^ d) := by
  induction d with
  | zero =>
    simp only [pow_zero]
    exact ⟨by simp [not_lt.mpr zero_le_one], by simp⟩
  | succ d ih =>
    rw [pow_succ, pow_succ]
    exact sameSign_mul ih ⟨by simp, by simp⟩

end BasicHelpers

section AnalyticHelpers

lemma poly_const_sign_no_root {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (p : Polynomial K) {a b : K} (hab : a ≤ b)
    (hno : ∀ c : K, a ≤ c → c ≤ b → p.eval c ≠ 0) :
    sameSign (p.eval a) (p.eval b) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact sameSign_refl _
  · have ha_ne : p.eval a ≠ 0 := hno a le_rfl hab
    have hb_ne : p.eval b ≠ 0 := hno b hab le_rfl
    rcases lt_trichotomy (p.eval a) 0 with ha | ha | ha <;>
    rcases lt_trichotomy (p.eval b) 0 with hb | hb | hb
    · exact ⟨⟨fun _ => hb, fun _ => ha⟩, ⟨fun h => absurd h ha_ne, fun h => absurd h hb_ne⟩⟩
    · exact absurd hb hb_ne
    · obtain ⟨c, hac, hcb, hc0⟩ := hIVT p hlt ha hb
      exact absurd hc0 (hno c hac.le hcb.le)
    · exact absurd ha ha_ne
    · exact absurd ha ha_ne
    · exact absurd ha ha_ne
    · obtain ⟨c, hac, hcb, hc0⟩ := hIVT (-p) hlt (by simpa using ha) (by simpa using hb)
      exact absurd (by simpa using hc0) (hno c hac.le hcb.le)
    · exact absurd hb hb_ne
    · exact ⟨⟨fun h => absurd h (not_lt.mpr ha.le), fun h => absurd h (not_lt.mpr hb.le)⟩,
        ⟨fun h => absurd h ha_ne, fun h => absurd h hb_ne⟩⟩

lemma poly_const_sign_open {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (p : Polynomial K) {x y : K} (hno : ∀ c : K, min x y ≤ c → c ≤ max x y → p.eval c ≠ 0) :
    sameSign (p.eval x) (p.eval y) := by
  rcases le_total x y with hxy | hyx
  · exact poly_const_sign_no_root hIVT p hxy (fun c hc1 hc2 =>
      hno c (by simpa [min_eq_left hxy] using hc1) (by simpa [max_eq_right hxy] using hc2))
  · exact sameSign_symm (poly_const_sign_no_root hIVT p hyx (fun c hc1 hc2 =>
      hno c (by simpa [min_eq_right hyx] using hc1) (by simpa [max_eq_left hyx] using hc2)))

lemma poly_unique_root_no_deriv {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hMVT : ∀ (p : Polynomial K) {u v : K}, u < v →
      ∃ c : K, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c)
    (p : Polynomial K) {r₁ r₂ : K}
    (hr₁ : p.eval r₁ = 0) (hr₂ : p.eval r₂ = 0)
    (hd : ∀ c : K, min r₁ r₂ < c → c < max r₁ r₂ → p.derivative.eval c ≠ 0) :
    r₁ = r₂ := by
  rcases lt_trichotomy r₁ r₂ with hlt | heq | hgt
  · obtain ⟨c, hc1, hc2, hmeq⟩ := hMVT p hlt
    rw [hr₁, hr₂, sub_zero] at hmeq
    have hc_ne : p.derivative.eval c ≠ 0 := hd c (by simpa [min_eq_left hlt.le] using hc1) (by simpa [max_eq_right hlt.le] using hc2)
    have hvu : r₂ - r₁ ≠ 0 := (sub_pos.mpr hlt).ne'
    have hmul : (r₂ - r₁) * p.derivative.eval c = 0 := hmeq.symm
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hvu
    · exact absurd h hc_ne
  · exact heq
  · obtain ⟨c, hc1, hc2, hmeq⟩ := hMVT p hgt
    rw [hr₁, hr₂, sub_zero] at hmeq
    have hc_ne : p.derivative.eval c ≠ 0 := hd c (by simpa [min_eq_right hgt.le] using hc1) (by simpa [max_eq_left hgt.le] using hc2)
    have hvu : r₁ - r₂ ≠ 0 := (sub_pos.mpr hgt).ne'
    have hmul : (r₁ - r₂) * p.derivative.eval c = 0 := hmeq.symm
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hvu
    · exact absurd h hc_ne

lemma poly_root_iff_opp_sign_on_bounded {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (hMVT : ∀ (p : Polynomial K) {u v : K}, u < v →
      ∃ c : K, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c)
    (p : Polynomial K) {a b : K} (hab : a < b)
    (hd : ∀ c : K, a < c → c < b → p.derivative.eval c ≠ 0) :
    (∃ r : K, a < r ∧ r < b ∧ p.eval r = 0) ↔ p.eval a * p.eval b < 0 := by
  constructor
  · rintro ⟨r, har, hrb, hr0⟩
    have hda : p.eval a ≠ 0 := by
      intro ha0
      obtain ⟨c, h1, h2, hmeq⟩ := hMVT p har
      rw [ha0, hr0, sub_zero] at hmeq
      rcases mul_eq_zero.mp hmeq.symm with h | h
      · exact (sub_pos.mpr har).ne' h
      · exact hd c h1 (lt_trans h2 hrb) h
    have hdb : p.eval b ≠ 0 := by
      intro hb0
      obtain ⟨c, h1, h2, hmeq⟩ := hMVT p hrb
      rw [hb0, hr0, sub_zero] at hmeq
      rcases mul_eq_zero.mp hmeq.symm with h | h
      · exact (sub_pos.mpr hrb).ne' h
      · exact hd c (lt_trans har h1) h2 h
    by_contra hnot
    have hnonneg : 0 ≤ p.eval a * p.eval b := not_lt.mp hnot
    have hpos : 0 < p.eval a * p.eval b := lt_of_le_of_ne hnonneg (mul_ne_zero hda hdb).symm
    obtain ⟨c₁, hac₁, hc₁r, hm₁⟩ := hMVT p har
    obtain ⟨c₂, hrc₂, hc₂b, hm₂⟩ := hMVT p hrb
    rw [hr0, zero_sub] at hm₁
    rw [hr0, sub_zero] at hm₂
    have hdc₁_ne : p.derivative.eval c₁ ≠ 0 := hd c₁ hac₁ (lt_trans hc₁r hrb)
    have hdc₂_ne : p.derivative.eval c₂ ≠ 0 := hd c₂ (lt_trans har hrc₂) hc₂b
    have hc₁c₂ : c₁ < c₂ := lt_trans hc₁r hrc₂
    have hprod_d : p.derivative.eval c₁ * p.derivative.eval c₂ < 0 := by
      have h1 : (r - a) * (b - r) > 0 := mul_pos (sub_pos.mpr har) (sub_pos.mpr hrb)
      have hmul_eq : ((r - a) * (b - r)) * (p.derivative.eval c₁ * p.derivative.eval c₂) =
          -(p.eval a * p.eval b) := by
        have e1 : (r - a) * p.derivative.eval c₁ = -p.eval a := hm₁.symm
        have e2 : (b - r) * p.derivative.eval c₂ = p.eval b := hm₂.symm
        calc
          ((r - a) * (b - r)) * (p.derivative.eval c₁ * p.derivative.eval c₂)
              = ((r - a) * p.derivative.eval c₁) * ((b - r) * p.derivative.eval c₂) := by ring
          _ = (-p.eval a) * p.eval b := by rw [e1, e2]
          _ = -(p.eval a * p.eval b) := by ring
      have hneg : ((r - a) * (b - r)) * (p.derivative.eval c₁ * p.derivative.eval c₂) < 0 := by
        rw [hmul_eq]
        exact neg_lt_zero.mpr hpos
      exact neg_of_mul_neg_right hneg h1.le
    rcases lt_trichotomy (p.derivative.eval c₁) 0 with hd₁ | hd₁ | hd₁
    · have hd₂ : 0 < p.derivative.eval c₂ := pos_of_mul_neg_right hprod_d hd₁.le
      obtain ⟨z, hz1, hz2, hz0⟩ := hIVT p.derivative hc₁c₂ hd₁ hd₂
      exact hd z (lt_trans hac₁ hz1) (lt_trans hz2 hc₂b) hz0
    · exact hdc₁_ne hd₁
    · have hd₂ : p.derivative.eval c₂ < 0 := neg_of_mul_neg_right hprod_d hd₁.le
      obtain ⟨z, hz1, hz2, hz0⟩ := hIVT (-p.derivative) hc₁c₂ (by simpa using hd₁) (by simpa using hd₂)
      exact hd z (lt_trans hac₁ hz1) (lt_trans hz2 hc₂b) (by simpa using hz0)
  · intro hmul
    rcases lt_trichotomy (p.eval a) 0 with ha | ha | ha
    · have hb : 0 < p.eval b := pos_of_mul_neg_right hmul ha.le
      exact hIVT p hab ha hb
    · rw [ha, zero_mul] at hmul
      exact absurd hmul (lt_irrefl 0)
    · have hb : p.eval b < 0 := neg_of_mul_neg_right hmul ha.le
      obtain ⟨c, hac, hcb, hc0⟩ := hIVT (-p) hab (by simpa using ha) (by simpa using hb)
      exact ⟨c, hac, hcb, by simpa using hc0⟩

lemma poly_no_root_bounded_left_sign {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (p : Polynomial K) {a b x : K} (hax : a < x) (hxb : x < b)
    (hno : ∀ c : K, a < c → c < b → p.eval c ≠ 0) (ha_ne : p.eval a ≠ 0) :
    sameSign (p.eval x) (p.eval a) :=
  sameSign_symm (poly_const_sign_no_root hIVT p hax.le (fun c hc1 hc2 => by
    rcases eq_or_lt_of_le hc1 with rfl | h1
    · exact ha_ne
    · exact hno c h1 (lt_of_le_of_lt hc2 hxb)))

lemma poly_no_root_bounded_right_sign {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (p : Polynomial K) {a b x : K} (hax : a < x) (hxb : x < b)
    (hno : ∀ c : K, a < c → c < b → p.eval c ≠ 0) (hb_ne : p.eval b ≠ 0) :
    sameSign (p.eval x) (p.eval b) :=
  poly_const_sign_no_root hIVT p hxb.le (fun c hc1 hc2 => by
    rcases eq_or_lt_of_le hc2 with rfl | h2
    · exact hb_ne
    · exact hno c (lt_of_lt_of_le hax hc1) h2)

lemma poly_asymp_neg {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hAsymp : ∀ (p : Polynomial K), p ≠ 0 →
      ∃ M : K, ∀ x : K, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))
    (p : Polynomial K) (hp : p ≠ 0) :
    ∃ M : K, ∀ x : K, x < M →
      sameSign (p.eval x) ((-1 : K) ^ p.natDegree * p.leadingCoeff) := by
  set q : Polynomial K := p.comp (-Polynomial.X)
  have hq : q ≠ 0 := by
    intro h0
    have hcomp : q.comp (-Polynomial.X) = p := by
      dsimp [q]
      rw [Polynomial.comp_assoc]
      simp
    rw [h0, Polynomial.zero_comp] at hcomp
    exact hp hcomp.symm
  have hdeg : q.natDegree = p.natDegree := by
    dsimp [q]
    rw [Polynomial.natDegree_comp]
    simp
  have hlead : q.leadingCoeff = p.leadingCoeff * (-1 : K) ^ p.natDegree := by
    dsimp [q]
    rw [Polynomial.leadingCoeff_comp]
    · simp
    · simp
  obtain ⟨M, hM⟩ := hAsymp q hq
  refine ⟨-M, fun x hx => ?_⟩
  have hnx : M < -x := by linarith
  have hqnx := hM (-x) hnx
  have hev : q.eval (-x) = p.eval x := by
    dsimp [q]
    rw [Polynomial.eval_comp]
    simp
  rw [hev, hlead] at hqnx
  have hne : p.leadingCoeff * (-1 : K) ^ p.natDegree ≠ 0 :=
    mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp) (pow_ne_zero _ (by norm_num))
  have hpx_ne : p.eval x ≠ 0 := by
    intro hp0
    rw [hp0] at hqnx
    rcases lt_trichotomy (p.leadingCoeff * (-1 : K) ^ p.natDegree) 0 with hl | hl | hl
    · exact lt_irrefl 0 (hqnx.2.mpr hl)
    · exact hne hl
    · exact lt_irrefl 0 (hqnx.1.mpr hl)
  have hss : sameSign (p.eval x) (p.leadingCoeff * (-1 : K) ^ p.natDegree) :=
    ⟨hqnx.2, ⟨fun h => absurd h hpx_ne, fun h => absurd h hne⟩⟩
  simpa [mul_comm] using hss

lemma poly_asymp_pos {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hAsymp : ∀ (p : Polynomial K), p ≠ 0 →
      ∃ M : K, ∀ x : K, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))
    (p : Polynomial K) (hp : p ≠ 0) :
    ∃ M : K, ∀ x : K, M < x → sameSign (p.eval x) p.leadingCoeff := by
  obtain ⟨M, hM⟩ := hAsymp p hp
  refine ⟨M, fun x hx => ?_⟩
  have hx' := hM x hx
  have hne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hpx_ne : p.eval x ≠ 0 := by
    intro hp0
    rw [hp0] at hx'
    rcases lt_trichotomy p.leadingCoeff 0 with hl | hl | hl
    · exact lt_irrefl 0 (hx'.2.mpr hl)
    · exact hne hl
    · exact lt_irrefl 0 (hx'.1.mpr hl)
  exact ⟨hx'.2, ⟨fun h => absurd h hpx_ne, fun h => absurd h hne⟩⟩

end AnalyticHelpers

section RootListAndCells

noncomputable def rootFinset {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (L : List (Polynomial K)) : Finset K := by
  classical
  exact (L.filter (fun p => decide (p ≠ 0))).toFinset.biUnion (fun p => p.roots.toFinset)

noncomputable def rootList {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (L : List (Polynomial K)) : List K :=
  (rootFinset L).sort (· ≤ ·)

lemma pairwise_lt_of_le_of_nodup {K : Type} [LinearOrder K] :
    ∀ {l : List K}, l.Pairwise (· ≤ ·) → l.Nodup → l.Pairwise (· < ·)
  | [], _, _ => List.Pairwise.nil
  | a :: t, hp, hn => by
    rw [List.pairwise_cons] at hp ⊢
    rw [List.nodup_cons] at hn
    exact ⟨fun b hb => lt_of_le_of_ne (hp.1 b hb) (fun h => hn.1 (h ▸ hb)),
      pairwise_lt_of_le_of_nodup hp.2 hn.2⟩

lemma rootList_pairwise_lt {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (L : List (Polynomial K)) : (rootList L).Pairwise (· < ·) :=
  pairwise_lt_of_le_of_nodup (Finset.pairwise_sort (rootFinset L) (· ≤ ·)) ((rootFinset L).sort_nodup (· ≤ ·))

lemma mem_rootList {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : List (Polynomial K)} {x : K} :
    x ∈ rootList L ↔ ∃ p ∈ L, p ≠ 0 ∧ p.eval x = 0 := by
  classical
  rw [rootList, Finset.mem_sort, rootFinset, Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, hxp⟩
    rw [List.mem_toFinset, List.mem_filter] at hp
    have hp0 : p ≠ 0 := by simpa using hp.2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0] at hxp
    exact ⟨p, hp.1, hp0, hxp⟩
  · rintro ⟨p, hpL, hp0, hpx⟩
    refine ⟨p, ?_, ?_⟩
    · rw [List.mem_toFinset, List.mem_filter]
      exact ⟨hpL, by simpa using hp0⟩
    · rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
      exact hpx

lemma list_eq_of_pairwise_lt_of_mem_iff {K : Type} [LinearOrder K] :
    ∀ {l₁ l₂ : List K}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
      (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: t₂, _, _, hmem => by
    have : b ∈ ([] : List K) := (hmem b).mpr (by simp)
    simp at this
  | a :: t₁, [], _, _, hmem => by
    have : a ∈ ([] : List K) := (hmem a).mp (by simp)
    simp at this
  | a :: t₁, b :: t₂, h1, h2, hmem => by
    rw [List.pairwise_cons] at h1 h2
    have ha2 : a = b ∨ a ∈ t₂ := List.mem_cons.mp ((hmem a).mp (by simp))
    have hb1 : b = a ∨ b ∈ t₁ := List.mem_cons.mp ((hmem b).mpr (by simp))
    have hab : a = b := by
      rcases ha2 with rfl | ha_t2
      · rfl
      · rcases hb1 with rfl | hb_t1
        · rfl
        · exact absurd (lt_trans (h2.1 a ha_t2) (h1.1 b hb_t1)) (lt_irrefl b)
    subst hab
    congr 1
    refine list_eq_of_pairwise_lt_of_mem_iff h1.2 h2.2 (fun x => ?_)
    have hx := hmem x
    simp only [List.mem_cons] at hx
    constructor
    · intro hxt1
      have hxa : x ≠ a := (h1.1 x hxt1).ne'
      rcases hx.mp (Or.inr hxt1) with rfl | hxt2
      · exact absurd rfl hxa
      · exact hxt2
    · intro hxt2
      have hxa : x ≠ a := (h2.1 x hxt2).ne'
      rcases hx.mpr (Or.inr hxt2) with rfl | hxt1
      · exact absurd rfl hxa
      · exact hxt1

lemma getElem_le_of_pairwise_lt {K : Type} [LinearOrder K] {R : List K}
    (hR : R.Pairwise (· < ·)) {i j : ℕ} (hi : i < R.length) (hj : j < R.length) (hij : i ≤ j) :
    R[i] ≤ R[j] := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact (List.pairwise_iff_getElem.mp hR i j hi hj hlt).le

def inCell {K : Type} [LinearOrder K] (R : List K) (j : ℕ) (x : K) : Prop :=
  (∀ i (hi : i < R.length), i < j → R[i] < x) ∧
  (∀ i (hi : i < R.length), j ≤ i → x < R[i])

lemma inCell_not_mem {K : Type} [LinearOrder K] {R : List K} {j : ℕ} {x : K}
    (hx : inCell R j x) : x ∉ R := by
  intro hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
  rcases lt_or_ge i j with hij | hji
  · exact lt_irrefl _ (hx.1 i hi hij)
  · exact lt_irrefl _ (hx.2 i hi hji)

lemma inCell_unique {K : Type} [LinearOrder K] {R : List K} {j₁ j₂ : ℕ} {x : K}
    (h1 : j₁ ≤ R.length) (h2 : j₂ ≤ R.length)
    (hx1 : inCell R j₁ x) (hx2 : inCell R j₂ x) : j₁ = j₂ := by
  rcases lt_trichotomy j₁ j₂ with hlt | heq | hgt
  · have hj1 : j₁ < R.length := lt_of_lt_of_le hlt h2
    exact absurd (lt_trans (hx2.1 j₁ hj1 hlt) (hx1.2 j₁ hj1 le_rfl)) (lt_irrefl _)
  · exact heq
  · have hj2 : j₂ < R.length := lt_of_lt_of_le hgt h1
    exact absurd (lt_trans (hx1.1 j₂ hj2 hgt) (hx2.2 j₂ hj2 le_rfl)) (lt_irrefl _)

lemma exists_inCell_of_not_mem {K : Type} [LinearOrder K] :
    ∀ {R : List K}, R.Pairwise (· < ·) → ∀ {x : K}, x ∉ R → ∃ j ≤ R.length, inCell R j x
  | [], _, x, _ => ⟨0, le_rfl, ⟨fun _ hi => by simp at hi, fun _ hi => by simp at hi⟩⟩
  | a :: t, hR, x, hx => by
    rw [List.pairwise_cons] at hR
    have hxa : x ≠ a := fun h => hx (by simp [h])
    have hxt : x ∉ t := fun h => hx (by simp [h])
    rcases lt_trichotomy x a with hlt | rfl | hgt
    · refine ⟨0, Nat.zero_le _, ⟨fun _ _ h => by omega, fun i hi _ => ?_⟩⟩
      cases i with
      | zero => exact hlt
      | succ i =>
        have hi' : i < t.length := by simpa using hi
        exact lt_trans hlt (hR.1 t[i] (List.getElem_mem hi'))
    · exact absurd rfl hxa
    · obtain ⟨j, hj_le, hj⟩ := exists_inCell_of_not_mem hR.2 hxt
      refine ⟨j + 1, Nat.succ_le_succ hj_le, ⟨?_, ?_⟩⟩
      · intro i hi hij
        cases i with
        | zero => exact hgt
        | succ i => exact hj.1 i (by simpa using hi) (Nat.succ_lt_succ_iff.mp hij)
      · intro i hi hij
        cases i with
        | zero => omega
        | succ i => exact hj.2 i (by simpa using hi) (Nat.succ_le_succ_iff.mp hij)

lemma exists_point_inCell {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {R : List K} (hR : R.Pairwise (· < ·)) {j : ℕ} (hj : j ≤ R.length) :
    ∃ x : K, inCell R j x := by
  by_cases hlen : R.length = 0
  · refine ⟨0, ⟨fun _ hi => by omega, fun _ hi => by omega⟩⟩
  · have hpos : 0 < R.length := Nat.pos_of_ne_zero hlen
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨R[0] - 1, ⟨fun _ _ h => by omega, fun i hi _ => ?_⟩⟩
      have hle : R[0] ≤ R[i] := getElem_le_of_pairwise_lt hR hpos hi (Nat.zero_le i)
      linarith
    · by_cases hjm : j = R.length
      · subst hjm
        refine ⟨R[R.length - 1] + 1, ⟨fun i hi hij => ?_, fun _ hi hji => by omega⟩⟩
        have hle : R[i] ≤ R[R.length - 1] := getElem_le_of_pairwise_lt hR hi (Nat.sub_lt hpos zero_lt_one) (Nat.le_sub_one_of_lt hij)
        linarith
      · have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
        have hj_lt : j < R.length := lt_of_le_of_ne hj hjm
        have hjm1 : j - 1 < R.length := lt_trans (Nat.sub_lt hj_pos zero_lt_one) hj_lt
        have hlt_adj : R[j - 1] < R[j] := List.pairwise_iff_getElem.mp hR (j - 1) j hjm1 hj_lt (by omega)
        set x := (R[j - 1] + R[j]) / 2
        have hx1 : R[j - 1] < x := by dsimp [x]; linarith
        have hx2 : x < R[j] := by dsimp [x]; linarith
        refine ⟨x, ⟨fun i hi hij => ?_, fun i hi hij => ?_⟩⟩
        · have hle : R[i] ≤ R[j - 1] := getElem_le_of_pairwise_lt hR hi hjm1 (Nat.le_sub_one_of_lt hij)
          exact lt_of_le_of_lt hle hx1
        · have hle : R[j] ≤ R[i] := getElem_le_of_pairwise_lt hR hj_lt hi hij
          exact lt_of_lt_of_le hx2 hle

lemma inCell_interval_no_root {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : List (Polynomial K)} {j : ℕ} {x y : K}
    (hx : inCell (rootList L) j x) (hy : inCell (rootList L) j y)
    {p : Polynomial K} (hpL : p ∈ L) (hp0 : p ≠ 0) :
    ∀ c : K, min x y ≤ c → c ≤ max x y → p.eval c ≠ 0 := by
  intro c hc1 hc2 hc0
  have hcR : c ∈ rootList L := mem_rootList.mpr ⟨p, hpL, hp0, hc0⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hcR
  rcases lt_or_ge i j with hij | hji
  · have h1 := hx.1 i hi hij
    have h2 := hy.1 i hi hij
    have : (rootList L)[i] < min x y := lt_min h1 h2
    exact lt_irrefl _ (lt_of_lt_of_le this hc1)
  · have h1 := hx.2 i hi hji
    have h2 := hy.2 i hi hji
    have : max x y < (rootList L)[i] := max_lt h1 h2
    exact lt_irrefl _ (lt_of_le_of_lt hc2 this)

lemma inCell_const_sign {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    {L : List (Polynomial K)} {j : ℕ} {x y : K}
    (hx : inCell (rootList L) j x) (hy : inCell (rootList L) j y)
    {p : Polynomial K} (hpL : p ∈ L) :
    sameSign (p.eval x) (p.eval y) := by
  by_cases hp0 : p = 0
  · subst hp0; simp [sameSign_refl]
  · exact poly_const_sign_open hIVT p (inCell_interval_no_root hx hy hpL hp0)

end RootListAndCells

section SignTableAndFilter

def SignTableMatch {A K₁ K₂ : Type} [CommRing A]
    [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂]
    (φ₁ : A →+* K₁) (φ₂ : A →+* K₂) (P : List (Polynomial A)) : Prop :=
  let R₁ := rootList (P.map (Polynomial.map φ₁))
  let R₂ := rootList (P.map (Polynomial.map φ₂))
  R₁.length = R₂.length ∧
  (∀ (i : ℕ) (h₁ : i < R₁.length) (h₂ : i < R₂.length), ∀ p ∈ P,
    sameSign ((p.map φ₁).eval R₁[i]) ((p.map φ₂).eval R₂[i])) ∧
  (∀ (j : ℕ) (x₁ : K₁) (x₂ : K₂),
    j ≤ R₁.length → inCell R₁ j x₁ → inCell R₂ j x₂ → ∀ p ∈ P,
    sameSign ((p.map φ₁).eval x₁) ((p.map φ₂).eval x₂))

lemma poly_map_eq_zero_iff_of_signTableMatch {A K₁ K₂ : Type} [CommRing A]
    [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂]
    {φ₁ : A →+* K₁} {φ₂ : A →+* K₂} {P : List (Polynomial A)}
    (hST : SignTableMatch φ₁ φ₂ P) {p : Polynomial A} (hp : p ∈ P) :
    p.map φ₁ = 0 ↔ p.map φ₂ = 0 := by
  set R₁ := rootList (P.map (Polynomial.map φ₁))
  set R₂ := rootList (P.map (Polynomial.map φ₂))
  have hR₁ : R₁.Pairwise (· < ·) := rootList_pairwise_lt _
  have hR₂ : R₂.Pairwise (· < ·) := rootList_pairwise_lt _
  obtain ⟨x₁, hx₁⟩ := exists_point_inCell hR₁ (Nat.zero_le R₁.length)
  have hbase_lt : ∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
      (R : List K), R.Pairwise (· < ·) → ∀ (k : ℕ),
      inCell R 0 ((if h : R.length = 0 then (0 : K) else R[0]) - ((k + 1 : ℕ) : K)) := by
    intro K _ _ _ R hR k
    refine ⟨fun _ _ h => by omega, fun i hi _ => ?_⟩
    have hk_pos : (0 : K) < ((k + 1 : ℕ) : K) := Nat.cast_pos.mpr (Nat.succ_pos k)
    by_cases hlen : R.length = 0
    · omega
    · simp only [dif_neg hlen]
      have hpos : 0 < R.length := Nat.pos_of_ne_zero hlen
      have hle : R[0] ≤ R[i] := getElem_le_of_pairwise_lt hR hpos hi (Nat.zero_le i)
      linarith
  constructor
  · intro hp1
    by_contra hp2
    set N := (p.map φ₂).natDegree
    have hroots : ∀ k : ℕ, (k : ℕ) ≤ N →
        (if h : R₂.length = 0 then (0 : K₂) else R₂[0]) - ((k + 1 : ℕ) : K₂) ∈ (p.map φ₂).roots := by
      intro k _
      rw [Polynomial.mem_roots hp2]
      have hx₂ := hbase_lt R₂ hR₂ k
      have hss := hST.2.2 0 x₁ _ (Nat.zero_le _) hx₁ hx₂ p hp
      rw [hp1, Polynomial.eval_zero] at hss
      exact hss.2.mp rfl
    set b : K₂ := if h : R₂.length = 0 then 0 else R₂[0]
    set S : Finset K₂ := (Finset.range (N + 1)).image (fun k => b - ((k + 1 : ℕ) : K₂))
    have hinj : Set.InjOn (fun k : ℕ => b - ((k + 1 : ℕ) : K₂)) (Finset.range (N + 1)) := by
      intro k₁ _ k₂ _ heq
      have hcast : ((k₁ + 1 : ℕ) : K₂) = ((k₂ + 1 : ℕ) : K₂) := by linarith
      exact Nat.succ.inj (Nat.cast_injective hcast)
    have hcard : S.card = N + 1 := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have hsub : S ⊆ (p.map φ₂).roots.toFinset := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      rw [Finset.mem_range] at hk
      rw [Multiset.mem_toFinset]
      exact hroots k (Nat.lt_succ_iff.mp hk)
    have hle1 : S.card ≤ (p.map φ₂).roots.toFinset.card := Finset.card_le_card hsub
    have hle2 : (p.map φ₂).roots.toFinset.card ≤ (p.map φ₂).roots.card := Multiset.toFinset_card_le _
    have hle3 : (p.map φ₂).roots.card ≤ N := Polynomial.card_roots' (p.map φ₂)
    omega
  · intro hp2
    by_contra hp1
    obtain ⟨x₂, hx₂⟩ := exists_point_inCell hR₂ (Nat.zero_le R₂.length)
    set N := (p.map φ₁).natDegree
    have hroots : ∀ k : ℕ, (k : ℕ) ≤ N →
        (if h : R₁.length = 0 then (0 : K₁) else R₁[0]) - ((k + 1 : ℕ) : K₁) ∈ (p.map φ₁).roots := by
      intro k _
      rw [Polynomial.mem_roots hp1]
      have hx₁' := hbase_lt R₁ hR₁ k
      have hss := hST.2.2 0 _ x₂ (Nat.zero_le _) hx₁' hx₂ p hp
      rw [hp2, Polynomial.eval_zero] at hss
      exact hss.2.mpr rfl
    set b : K₁ := if h : R₁.length = 0 then 0 else R₁[0]
    set S : Finset K₁ := (Finset.range (N + 1)).image (fun k => b - ((k + 1 : ℕ) : K₁))
    have hinj : Set.InjOn (fun k : ℕ => b - ((k + 1 : ℕ) : K₁)) (Finset.range (N + 1)) := by
      intro k₁ _ k₂ _ heq
      have hcast : ((k₁ + 1 : ℕ) : K₁) = ((k₂ + 1 : ℕ) : K₁) := by linarith
      exact Nat.succ.inj (Nat.cast_injective hcast)
    have hcard : S.card = N + 1 := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have hsub : S ⊆ (p.map φ₁).roots.toFinset := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      rw [Finset.mem_range] at hk
      rw [Multiset.mem_toFinset]
      exact hroots k (Nat.lt_succ_iff.mp hk)
    have hle1 : S.card ≤ (p.map φ₁).roots.toFinset.card := Finset.card_le_card hsub
    have hle2 : (p.map φ₁).roots.toFinset.card ≤ (p.map φ₁).roots.card := Multiset.toFinset_card_le _
    have hle3 : (p.map φ₁).roots.card ≤ N := Polynomial.card_roots' (p.map φ₁)
    omega

lemma forall₂_filter_and_cell {K₁ K₂ : Type} [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂]
    (b₁ : K₁ → Bool) (b₂ : K₂ → Bool) :
    ∀ {l₁ : List K₁} {l₂ : List K₂},
      List.Forall₂ (fun x y => b₁ x = b₂ y) l₁ l₂ →
      (l₁.filter b₁).length = (l₂.filter b₂).length ∧
      ∀ (j : ℕ), j ≤ (l₁.filter b₁).length →
        ∃ j' ≤ l₁.length, ∀ (y₁ : K₁) (y₂ : K₂),
          inCell l₁ j' y₁ → inCell l₂ j' y₂ →
          inCell (l₁.filter b₁) j y₁ ∧ inCell (l₂.filter b₂) j y₂
  | [], [], _ => ⟨rfl, fun _ hj => ⟨0, le_rfl, fun _ _ _ _ => ⟨⟨fun _ hi => by simp at hi, fun _ hi => by simp at hi⟩, ⟨fun _ hi => by simp at hi, fun _ hi => by simp at hi⟩⟩⟩⟩
  | a₁ :: t₁, a₂ :: t₂, hF => by
    rw [List.forall₂_cons] at hF
    obtain ⟨hlen_t, hcell_t⟩ := forall₂_filter_and_cell b₁ b₂ hF.2
    by_cases ha : b₁ a₁ = true
    · have ha2 : b₂ a₂ = true := hF.1.symm.trans ha
      simp only [List.filter_cons, ha, ha2, ↓reduceIte, List.length_cons]
      refine ⟨by omega, fun j hj => ?_⟩
      cases j with
      | zero =>
        refine ⟨0, Nat.zero_le _, fun y₁ y₂ hy₁ hy₂ => ⟨⟨fun _ _ h => by omega, fun i hi _ => ?_⟩, ⟨fun _ _ h => by omega, fun i hi _ => ?_⟩⟩⟩
        · cases i with
          | zero => exact hy₁.2 0 (by simp) le_rfl
          | succ i =>
            have hi' : i < (t₁.filter b₁).length := by simpa using hi
            have hmem : (t₁.filter b₁)[i]'hi' ∈ a₁ :: t₁ :=
              List.mem_cons_of_mem a₁ (List.mem_of_mem_filter (List.getElem_mem hi'))
            obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hmem
            change y₁ < (t₁.filter b₁)[i]'hi'
            rw [← hkeq]
            exact hy₁.2 k hk (Nat.zero_le k)
        · cases i with
          | zero => exact hy₂.2 0 (by simp) le_rfl
          | succ i =>
            have hi' : i < (t₂.filter b₂).length := by simpa using hi
            have hmem : (t₂.filter b₂)[i]'hi' ∈ a₂ :: t₂ :=
              List.mem_cons_of_mem a₂ (List.mem_of_mem_filter (List.getElem_mem hi'))
            obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hmem
            change y₂ < (t₂.filter b₂)[i]'hi'
            rw [← hkeq]
            exact hy₂.2 k hk (Nat.zero_le k)
      | succ j =>
        obtain ⟨j', hj', hcell'⟩ := hcell_t j (Nat.succ_le_succ_iff.mp hj)
        refine ⟨j' + 1, Nat.succ_le_succ hj', fun y₁ y₂ hy₁ hy₂ => ?_⟩
        have hy₁_t : inCell t₁ j' y₁ :=
          ⟨fun i hi hij => hy₁.1 (i + 1) (by simpa using hi) (Nat.succ_lt_succ hij),
           fun i hi hij => hy₁.2 (i + 1) (by simpa using hi) (Nat.succ_le_succ hij)⟩
        have hy₂_t : inCell t₂ j' y₂ :=
          ⟨fun i hi hij => hy₂.1 (i + 1) (by simpa using hi) (Nat.succ_lt_succ hij),
           fun i hi hij => hy₂.2 (i + 1) (by simpa using hi) (Nat.succ_le_succ hij)⟩
        obtain ⟨hc1, hc2⟩ := hcell' y₁ y₂ hy₁_t hy₂_t
        refine ⟨⟨fun i hi hij => ?_, fun i hi hij => ?_⟩, ⟨fun i hi hij => ?_, fun i hi hij => ?_⟩⟩
        · cases i with
          | zero => exact hy₁.1 0 (by simp) (Nat.zero_lt_succ j')
          | succ i => exact hc1.1 i (by simpa using hi) (Nat.succ_lt_succ_iff.mp hij)
        · cases i with
          | zero => omega
          | succ i => exact hc1.2 i (by simpa using hi) (Nat.succ_le_succ_iff.mp hij)
        · cases i with
          | zero => exact hy₂.1 0 (by simp) (Nat.zero_lt_succ j')
          | succ i => exact hc2.1 i (by simpa using hi) (Nat.succ_lt_succ_iff.mp hij)
        · cases i with
          | zero => omega
          | succ i => exact hc2.2 i (by simpa using hi) (Nat.succ_le_succ_iff.mp hij)
    · have ha1f : b₁ a₁ = false := Bool.eq_false_iff.mpr ha
      have ha2f : b₂ a₂ = false := hF.1.symm.trans ha1f
      simp only [List.filter_cons, ha1f, ha2f, Bool.false_eq_true, ↓reduceIte]
      refine ⟨hlen_t, fun j hj => ?_⟩
      obtain ⟨j', hj', hcell'⟩ := hcell_t j hj
      refine ⟨j' + 1, Nat.succ_le_succ hj', fun y₁ y₂ hy₁ hy₂ => ?_⟩
      have hy₁_t : inCell t₁ j' y₁ :=
        ⟨fun i hi hij => hy₁.1 (i + 1) (by simpa using hi) (Nat.succ_lt_succ hij),
         fun i hi hij => hy₁.2 (i + 1) (by simpa using hi) (Nat.succ_le_succ hij)⟩
      have hy₂_t : inCell t₂ j' y₂ :=
        ⟨fun i hi hij => hy₂.1 (i + 1) (by simpa using hi) (Nat.succ_lt_succ hij),
         fun i hi hij => hy₂.2 (i + 1) (by simpa using hi) (Nat.succ_le_succ hij)⟩
      exact hcell' y₁ y₂ hy₁_t hy₂_t

lemma forall₂_filter_getElem {K₁ K₂ : Type}
    (b₁ : K₁ → Bool) (b₂ : K₂ → Bool) (rel : K₁ → K₂ → Prop) :
    ∀ {l₁ : List K₁} {l₂ : List K₂},
      List.Forall₂ (fun x y => b₁ x = b₂ y ∧ rel x y) l₁ l₂ →
      List.Forall₂ rel (l₁.filter b₁) (l₂.filter b₂)
  | [], [], _ => List.Forall₂.nil
  | a₁ :: t₁, a₂ :: t₂, hF => by
    rw [List.forall₂_cons] at hF
    have ih := forall₂_filter_getElem b₁ b₂ rel hF.2
    by_cases ha : b₁ a₁ = true
    · have ha2 : b₂ a₂ = true := hF.1.1.symm.trans ha
      simp only [List.filter_cons, ha, ha2, ↓reduceIte]
      exact List.Forall₂.cons hF.1.2 ih
    · have ha1f : b₁ a₁ = false := Bool.eq_false_iff.mpr ha
      have ha2f : b₂ a₂ = false := hF.1.1.symm.trans ha1f
      simp only [List.filter_cons, ha1f, ha2f, Bool.false_eq_true, ↓reduceIte]
      exact ih

lemma forall₂_getElem {α β : Type} {rel : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ rel l₁ l₂) (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length) :
    rel l₁[i] l₂[i] :=
  (List.forall₂_iff_get.mp h).2 i h₁ h₂

lemma forall₂_of_getElem {α β : Type} {rel : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (hlen : l₁.length = l₂.length)
    (h : ∀ (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length), rel l₁[i] l₂[i]) :
    List.Forall₂ rel l₁ l₂ :=
  List.forall₂_iff_get.mpr ⟨hlen, h⟩

lemma forall₂_append_of {α β : Type} {rel : α → β → Prop} :
    ∀ {l₁ l₁' : List α} {l₂ l₂' : List β},
      List.Forall₂ rel l₁ l₂ → List.Forall₂ rel l₁' l₂' → List.Forall₂ rel (l₁ ++ l₁') (l₂ ++ l₂')
  | [], _, [], _, _, h2 => h2
  | _ :: _, _, _ :: _, _, List.Forall₂.cons h1 t1, h2 => List.Forall₂.cons h1 (forall₂_append_of t1 h2)

lemma countP_eq_of_forall₂ {α β : Type} (p₁ : α → Bool) (p₂ : β → Bool) :
    ∀ {l₁ : List α} {l₂ : List β},
      List.Forall₂ (fun x y => p₁ x = p₂ y) l₁ l₂ →
      l₁.countP p₁ = l₂.countP p₂
  | [], [], _ => rfl
  | _ :: _, _ :: _, List.Forall₂.cons hhead htail => by
    rw [List.countP_cons, List.countP_cons, hhead, countP_eq_of_forall₂ p₁ p₂ htail]

lemma filterSignTable_extra {A K₁ K₂ : Type} [CommRing A]
    [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂]
    (hIVT₁ : ∀ (p : Polynomial K₁) {a b : K₁}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₁, a < c ∧ c < b ∧ p.eval c = 0)
    (hIVT₂ : ∀ (p : Polynomial K₂) {a b : K₂}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₂, a < c ∧ c < b ∧ p.eval c = 0)
    {φ₁ : A →+* K₁} {φ₂ : A →+* K₂} {P P' : List (Polynomial A)}
    (hsub : ∀ p ∈ P, p ∈ P') (hST : SignTableMatch φ₁ φ₂ P') :
    SignTableMatch φ₁ φ₂ P ∧
    (∀ (i : ℕ) (h₁ : i < (rootList (P.map (Polynomial.map φ₁))).length)
        (h₂ : i < (rootList (P.map (Polynomial.map φ₂))).length), ∀ q ∈ P',
      sameSign ((q.map φ₁).eval (rootList (P.map (Polynomial.map φ₁)))[i])
               ((q.map φ₂).eval (rootList (P.map (Polynomial.map φ₂)))[i])) := by
  classical
  set R₁' := rootList (P'.map (Polynomial.map φ₁))
  set R₂' := rootList (P'.map (Polynomial.map φ₂))
  set R₁ := rootList (P.map (Polynomial.map φ₁))
  set R₂ := rootList (P.map (Polynomial.map φ₂))
  have hR₁' : R₁'.Pairwise (· < ·) := rootList_pairwise_lt _
  have hR₂' : R₂'.Pairwise (· < ·) := rootList_pairwise_lt _
  have hR₁ : R₁.Pairwise (· < ·) := rootList_pairwise_lt _
  have hR₂ : R₂.Pairwise (· < ·) := rootList_pairwise_lt _
  let b₁ : K₁ → Bool := fun r => P.any (fun p => decide (p.map φ₁ ≠ 0 ∧ (p.map φ₁).eval r = 0))
  let b₂ : K₂ → Bool := fun r => P.any (fun p => decide (p.map φ₂ ≠ 0 ∧ (p.map φ₂).eval r = 0))
  have hR₁_eq : R₁ = R₁'.filter b₁ := by
    refine list_eq_of_pairwise_lt_of_mem_iff hR₁ (hR₁'.filter b₁) (fun x => ?_)
    dsimp only [R₁, R₁']
    rw [mem_rootList, List.mem_filter, mem_rootList]
    simp only [b₁, List.any_eq_true, decide_eq_true_eq, List.mem_map]
    constructor
    · rintro ⟨_, ⟨p, hpP, rfl⟩, hp0, hpx⟩
      exact ⟨⟨p.map φ₁, ⟨p, hsub p hpP, rfl⟩, hp0, hpx⟩, ⟨p, hpP, hp0, hpx⟩⟩
    · rintro ⟨_, ⟨p, hpP, hp0, hpx⟩⟩
      exact ⟨p.map φ₁, ⟨p, hpP, rfl⟩, hp0, hpx⟩
  have hR₂_eq : R₂ = R₂'.filter b₂ := by
    refine list_eq_of_pairwise_lt_of_mem_iff hR₂ (hR₂'.filter b₂) (fun x => ?_)
    dsimp only [R₂, R₂']
    rw [mem_rootList, List.mem_filter, mem_rootList]
    simp only [b₂, List.any_eq_true, decide_eq_true_eq, List.mem_map]
    constructor
    · rintro ⟨_, ⟨p, hpP, rfl⟩, hp0, hpx⟩
      exact ⟨⟨p.map φ₂, ⟨p, hsub p hpP, rfl⟩, hp0, hpx⟩, ⟨p, hpP, hp0, hpx⟩⟩
    · rintro ⟨_, ⟨p, hpP, hp0, hpx⟩⟩
      exact ⟨p.map φ₂, ⟨p, hpP, rfl⟩, hp0, hpx⟩
  have hF_base : List.Forall₂ (fun r₁ r₂ => b₁ r₁ = b₂ r₂ ∧ ∀ p ∈ P', sameSign ((p.map φ₁).eval r₁) ((p.map φ₂).eval r₂)) R₁' R₂' := by
    refine forall₂_of_getElem hST.1 (fun i hi₁ hi₂ => ⟨?_, fun p hp => hST.2.1 i hi₁ hi₂ p hp⟩)
    rw [Bool.eq_iff_iff]
    simp only [b₁, b₂, List.any_eq_true, decide_eq_true_eq]
    constructor <;> rintro ⟨p, hpP, hp0, hpx⟩ <;> refine ⟨p, hpP, ?_, ?_⟩
    · exact (poly_map_eq_zero_iff_of_signTableMatch hST (hsub p hpP)).not.mp hp0
    · exact (hST.2.1 i hi₁ hi₂ p (hsub p hpP)).2.mp hpx
    · exact (poly_map_eq_zero_iff_of_signTableMatch hST (hsub p hpP)).not.mpr hp0
    · exact (hST.2.1 i hi₁ hi₂ p (hsub p hpP)).2.mpr hpx
  have hF_bool : List.Forall₂ (fun r₁ r₂ => b₁ r₁ = b₂ r₂) R₁' R₂' :=
    List.Forall₂.imp (fun _ _ h => h.1) hF_base
  have hF_filt := forall₂_filter_getElem b₁ b₂ (fun r₁ r₂ => ∀ p ∈ P', sameSign ((p.map φ₁).eval r₁) ((p.map φ₂).eval r₂)) hF_base
  rw [← hR₁_eq, ← hR₂_eq] at hF_filt
  obtain ⟨hlen_f, hcell_f⟩ := forall₂_filter_and_cell b₁ b₂ hF_bool
  rw [← hR₁_eq, ← hR₂_eq] at hlen_f hcell_f
  refine ⟨⟨hlen_f, fun i hi₁ hi₂ p hp => forall₂_getElem hF_filt i hi₁ hi₂ p (hsub p hp), ?_⟩,
    fun i hi₁ hi₂ q hq => forall₂_getElem hF_filt i hi₁ hi₂ q hq⟩
  intro j x₁ x₂ hj hx₁ hx₂ p hp
  obtain ⟨j', hj', hcells⟩ := hcell_f j hj
  obtain ⟨y₁, hy₁⟩ := exists_point_inCell hR₁' hj'
  obtain ⟨y₂, hy₂⟩ := exists_point_inCell hR₂' (hST.1 ▸ hj')
  obtain ⟨hy₁_f, hy₂_f⟩ := hcells y₁ y₂ hy₁ hy₂
  have h1 : sameSign ((p.map φ₁).eval x₁) ((p.map φ₁).eval y₁) :=
    inCell_const_sign hIVT₁ hx₁ hy₁_f (List.mem_map_of_mem hp)
  have h2 : sameSign ((p.map φ₁).eval y₁) ((p.map φ₂).eval y₂) :=
    hST.2.2 j' y₁ y₂ hj' hy₁ hy₂ p (hsub p hp)
  have h3 : sameSign ((p.map φ₂).eval y₂) ((p.map φ₂).eval x₂) :=
    inCell_const_sign hIVT₂ hy₂_f hx₂ (List.mem_map_of_mem hp)
  exact sameSign_trans h1 (sameSign_trans h2 h3)

end SignTableAndFilter

section StripAndPrem
open Classical

noncomputable def stripLeadAux {A K₁ : Type} [CommRing A] [Field K₁]
    (φ₁ : A →+* K₁) : ℕ → Polynomial A → Polynomial A × List A
  | 0, p => if φ₁ (p.coeff 0) = 0 then (0, [p.coeff 0]) else (p, [p.coeff 0])
  | n + 1, p =>
    if φ₁ (p.coeff (n + 1)) = 0 then
      let res := stripLeadAux φ₁ n (p.erase (n + 1))
      (res.1, p.coeff (n + 1) :: res.2)
    else (p, [p.coeff (n + 1)])

lemma stripLeadAux_spec {A K₁ K₂ : Type} [CommRing A] [Field K₁] [Field K₂]
    (φ₁ : A →+* K₁) :
    ∀ (n : ℕ) (p : Polynomial A), p.natDegree ≤ n →
      let (p', Q) := stripLeadAux φ₁ n p
      p'.natDegree ≤ p.natDegree ∧
      p'.map φ₁ = p.map φ₁ ∧
      (p' = 0 ∨ (φ₁ p'.leadingCoeff ≠ 0 ∧ p'.leadingCoeff ∈ Q)) ∧
      (∀ (φ₂ : A →+* K₂), (∀ r ∈ Q, φ₁ r = 0 ↔ φ₂ r = 0) → p'.map φ₂ = p.map φ₂)
  | 0, p, hdeg => by
    have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hdeg
    dsimp [stripLeadAux]
    by_cases h0 : φ₁ (p.coeff 0) = 0
    · rw [if_pos h0]
      refine ⟨Nat.zero_le _, ?_, Or.inl rfl, fun φ₂ hQ => ?_⟩
      · conv_rhs => rw [hpC]
        simp [h0]
      · conv_rhs => rw [hpC]
        have h2 : φ₂ (p.coeff 0) = 0 := (hQ (p.coeff 0) (by simp)).mp h0
        simp [h2]
    · rw [if_neg h0]
      have hlead : p.leadingCoeff = p.coeff 0 := by
        rw [Polynomial.leadingCoeff, Nat.le_zero.mp hdeg]
      refine ⟨le_rfl, rfl, Or.inr ⟨hlead ▸ h0, by simp [hlead]⟩, fun _ _ => rfl⟩
  | n + 1, p, hdeg => by
    dsimp [stripLeadAux]
    by_cases h0 : φ₁ (p.coeff (n + 1)) = 0
    · rw [if_pos h0]
      have herase_deg : (p.erase (n + 1)).natDegree ≤ n := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro m hm
        by_cases hmeq : m = n + 1
        · subst hmeq; simp
        · rw [Polynomial.coeff_erase, if_neg hmeq]
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega))
      have herase_le : (p.erase (n + 1)).natDegree ≤ p.natDegree := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro m hm
        by_cases hmeq : m = n + 1
        · subst hmeq; simp
        · rw [Polynomial.coeff_erase, if_neg hmeq]
          exact Polynomial.coeff_eq_zero_of_natDegree_lt hm
      have hdecomp : p = p.erase (n + 1) + Polynomial.monomial (n + 1) (p.coeff (n + 1)) := by
        ext m
        rw [Polynomial.coeff_add, Polynomial.coeff_monomial]
        by_cases hm : m = n + 1
        · subst hm; simp
        · simp [hm, Ne.symm hm]
      have ih := stripLeadAux_spec (K₂ := K₂) φ₁ n (p.erase (n + 1)) herase_deg
      refine ⟨le_trans ih.1 herase_le, ?_, ?_, fun φ₂ hQ => ?_⟩
      · rw [ih.2.1]
        conv_rhs => rw [hdecomp]
        simp [Polynomial.map_add, Polynomial.map_monomial, h0]
      · rcases ih.2.2.1 with hzero | ⟨hl, hm⟩
        · exact Or.inl hzero
        · exact Or.inr ⟨hl, List.mem_cons_of_mem _ hm⟩
      · rw [ih.2.2.2 φ₂ (fun r hr => hQ r (List.mem_cons_of_mem _ hr))]
        have h2 : φ₂ (p.coeff (n + 1)) = 0 := (hQ (p.coeff (n + 1)) (by simp)).mp h0
        conv_rhs => rw [hdecomp]
        simp [Polynomial.map_add, Polynomial.map_monomial, h2]
    · rw [if_neg h0]
      have hp_deg : p.natDegree = n + 1 :=
        le_antisymm hdeg (Polynomial.le_natDegree_of_ne_zero (fun hc => h0 (by simp [hc])))
      have hlead : p.leadingCoeff = p.coeff (n + 1) := by
        rw [Polynomial.leadingCoeff, hp_deg]
      refine ⟨le_rfl, rfl, Or.inr ⟨hlead ▸ h0, by simp [hlead]⟩, fun _ _ => rfl⟩

noncomputable def stripLead {A K₁ : Type} [CommRing A] [Field K₁]
    (φ₁ : A →+* K₁) (p : Polynomial A) : Polynomial A × List A :=
  stripLeadAux φ₁ p.natDegree p

noncomputable def stripList {A K₁ : Type} [CommRing A] [Field K₁]
    (φ₁ : A →+* K₁) : List (Polynomial A) → List (Polynomial A) × List A
  | [] => ([], [])
  | p :: ps =>
    let r1 := stripLead φ₁ p
    let r2 := stripList φ₁ ps
    if r1.1 = 0 then (r2.1, r1.2 ++ r2.2)
    else (r1.1 :: r2.1, r1.2 ++ r2.2)

lemma stripList_spec {A K₁ K₂ : Type} [CommRing A] [Field K₁] [Field K₂]
    (φ₁ : A →+* K₁) :
    ∀ (P : List (Polynomial A)),
      let (P', Q) := stripList φ₁ P
      (∀ p' ∈ P', p' ≠ 0 ∧ φ₁ p'.leadingCoeff ≠ 0 ∧ p'.leadingCoeff ∈ Q) ∧
      (∀ d : ℕ, (∀ p ∈ P, p.natDegree ≤ d) → ∀ p' ∈ P', p'.natDegree ≤ d) ∧
      (∀ d : ℕ, (∀ p ∈ P, p.natDegree ≤ d) →
        (P'.countP (fun p => decide (p.natDegree = d))) ≤ P.countP (fun p => decide (p.natDegree = d))) ∧
      (∀ (φ₂ : A →+* K₂), (∀ r ∈ Q, φ₁ r = 0 ↔ φ₂ r = 0) →
        ∀ (p : Polynomial A), p ∈ P →
          (p.map φ₁ = 0 ∧ p.map φ₂ = 0) ∨
          (∃ p' ∈ P', p'.map φ₁ = p.map φ₁ ∧ p'.map φ₂ = p.map φ₂))
  | [] => ⟨fun _ h => by simp at h, fun _ _ _ h => by simp at h, fun _ _ => le_rfl, fun _ _ _ h => by simp at h⟩
  | p :: ps => by
    classical
    dsimp [stripList]
    have h1 := stripLeadAux_spec (K₂ := K₂) φ₁ p.natDegree p le_rfl
    have h2 := stripList_spec (K₂ := K₂) φ₁ ps
    set r1 := stripLead φ₁ p
    set r2 := stripList φ₁ ps
    by_cases hr0 : r1.1 = 0
    · simp only [hr0, ↓reduceIte]
      refine ⟨fun p' hp' => ?_, fun d hd p' hp' => h2.2.1 d (fun q hq => hd q (List.mem_cons_of_mem p hq)) p' hp', fun d hd => ?_, fun φ₂ hQ q hq => ?_⟩
      · have hp'' := h2.1 p' hp'
        exact ⟨hp''.1, hp''.2.1, List.mem_append_right _ hp''.2.2⟩
      · refine le_trans (h2.2.2.1 d (fun q hq => hd q (List.mem_cons_of_mem p hq))) ?_
        rw [List.countP_cons]
        exact Nat.le_add_right _ _
      · rcases List.mem_cons.mp hq with rfl | hqps
        · left
          dsimp only [r1, stripLead] at hr0
          refine ⟨?_, ?_⟩
          · rw [← h1.2.1, hr0, Polynomial.map_zero]
          · rw [← h1.2.2.2 φ₂ (fun r hr => hQ r (List.mem_append_left _ hr)), hr0, Polynomial.map_zero]
        · exact h2.2.2.2 φ₂ (fun r hr => hQ r (List.mem_append_right _ hr)) q hqps
    · simp only [hr0, ↓reduceIte]
      have hlead1 : φ₁ r1.1.leadingCoeff ≠ 0 ∧ r1.1.leadingCoeff ∈ r1.2 :=
        (h1.2.2.1).resolve_left hr0
      refine ⟨fun p' hp' => ?_, fun d hd p' hp' => ?_, fun d hd => ?_, fun φ₂ hQ q hq => ?_⟩
      · rcases List.mem_cons.mp hp' with rfl | hp'ps
        · exact ⟨hr0, hlead1.1, List.mem_append_left _ hlead1.2⟩
        · have hp'' := h2.1 p' hp'ps
          exact ⟨hp''.1, hp''.2.1, List.mem_append_right _ hp''.2.2⟩
      · rcases List.mem_cons.mp hp' with rfl | hp'ps
        · exact le_trans h1.1 (hd p (by simp))
        · exact h2.2.1 d (fun q hq => hd q (List.mem_cons_of_mem p hq)) p' hp'ps
      · rw [List.countP_cons, List.countP_cons]
        have hle_ps := h2.2.2.1 d (fun q hq => hd q (List.mem_cons_of_mem p hq))
        dsimp only [r2] at hle_ps ⊢
        by_cases h1d : r1.1.natDegree = d
        · have hp_le : p.natDegree ≤ d := hd p (by simp)
          have h1_le : r1.1.natDegree ≤ p.natDegree := h1.1
          have hpd : p.natDegree = d := by omega
          simp only [h1d, hpd, decide_true, ↓reduceIte]
          omega
        · simp only [h1d, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact le_trans hle_ps (Nat.le_add_right _ _)
      · rcases List.mem_cons.mp hq with rfl | hqps
        · right
          refine ⟨r1.1, by simp, h1.2.1, h1.2.2.2 φ₂ (fun r hr => hQ r (List.mem_append_left _ hr))⟩
        · rcases h2.2.2.2 φ₂ (fun r hr => hQ r (List.mem_append_right _ hr)) q hqps with hzero | ⟨p', hp', hm1, hm2⟩
          · exact Or.inl hzero
          · exact Or.inr ⟨p', List.mem_cons_of_mem _ hp', hm1, hm2⟩

noncomputable def premAux {A : Type} [CommRing A] (g : Polynomial A) :
    ℕ → Polynomial A → Polynomial A
  | 0, f => f
  | k + 1, f =>
    if f = 0 ∨ f.natDegree < g.natDegree then f
    else
      let b := g.leadingCoeff
      let a := f.leadingCoeff
      let step := Polynomial.C (b ^ 2) * f -
        Polynomial.C (b * a) * Polynomial.X ^ (f.natDegree - g.natDegree) * g
      premAux g k step

noncomputable def prem {A : Type} [CommRing A] (f g : Polynomial A) : Polynomial A :=
  premAux g (f.natDegree + 1) f

lemma premAux_zero {A : Type} [CommRing A] (g : Polynomial A) :
    ∀ k : ℕ, premAux g k 0 = 0
  | 0 => rfl
  | _ + 1 => by simp [premAux]

lemma premAux_deg {A : Type} [CommRing A] {g : Polynomial A} (hg : g ≠ 0) :
    ∀ (k : ℕ) (f : Polynomial A), f.natDegree < k →
      premAux g k f = 0 ∨ (premAux g k f).natDegree < g.natDegree
  | 0, f, hk => by omega
  | k + 1, f, hk => by
    dsimp [premAux]
    split_ifs with hf
    · rcases hf with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr hlt
    · push Not at hf
      obtain ⟨hf0, hge⟩ := hf
      set b := g.leadingCoeff
      set a := f.leadingCoeff
      set d := f.natDegree - g.natDegree
      set step := Polynomial.C (b ^ 2) * f - Polynomial.C (b * a) * Polynomial.X ^ d * g
      have hstep_coeff : ∀ i : ℕ, f.natDegree ≤ i → step.coeff i = 0 := by
        intro i hi
        dsimp [step]
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
        rcases eq_or_lt_of_le hi with rfl | hgt
        · have hsub : f.natDegree - d = g.natDegree := by omega
          rw [if_pos (Nat.sub_le _ _), hsub]
          change b ^ 2 * a - b * a * b = 0
          ring
        · have hf_i : f.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hgt
          have hgt_g : g.natDegree < i - d := by omega
          have hg_i : g.coeff (i - d) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hgt_g
          rw [hf_i, mul_zero, zero_sub]
          split_ifs <;> simp [hg_i]
      by_cases hs0 : step = 0
      · rw [hs0, premAux_zero]
        exact Or.inl rfl
      · have hs_lt : step.natDegree < f.natDegree := by
          by_contra hnot
          have hle : f.natDegree ≤ step.natDegree := not_lt.mp hnot
          exact Polynomial.leadingCoeff_ne_zero.mpr hs0 (hstep_coeff step.natDegree hle)
        exact premAux_deg hg k step (lt_of_lt_of_le hs_lt (Nat.lt_succ_iff.mp hk))

lemma prem_deg {A : Type} [CommRing A] {f g : Polynomial A} (hg : g ≠ 0) :
    prem f g = 0 ∨ (prem f g).natDegree < g.natDegree :=
  premAux_deg hg (f.natDegree + 1) f (Nat.lt_succ_self _)

lemma premAux_sameSign {A K : Type} [CommRing A]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (φ : A →+* K) (g : Polynomial A) (hgb : φ g.leadingCoeff ≠ 0) :
    ∀ (k : ℕ) (f : Polynomial A) (x : K), (g.map φ).eval x = 0 →
      sameSign (((premAux g k f).map φ).eval x) ((f.map φ).eval x)
  | 0, f, x, _ => sameSign_refl _
  | k + 1, f, x, hxg => by
    dsimp [premAux]
    split_ifs with hf
    · exact sameSign_refl _
    · set b := g.leadingCoeff
      set a := f.leadingCoeff
      set d := f.natDegree - g.natDegree
      set step := Polynomial.C (b ^ 2) * f - Polynomial.C (b * a) * Polynomial.X ^ d * g
      have ih := premAux_sameSign φ g hgb k step x hxg
      have heval : (step.map φ).eval x = (φ b) ^ 2 * (f.map φ).eval x := by
        dsimp [step]
        simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
          Polynomial.map_X, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X, hxg, mul_zero, sub_zero, map_pow]
      have hss_step : sameSign ((step.map φ).eval x) ((f.map φ).eval x) := by
        rw [heval]
        have hb2 : 0 < (φ b) ^ 2 := sq_pos_of_ne_zero hgb
        exact ⟨⟨fun h => neg_of_mul_neg_right h hb2.le, fun h => mul_neg_of_pos_of_neg hb2 h⟩,
               ⟨fun h => (mul_eq_zero.mp h).resolve_left hb2.ne', fun h => by rw [h, mul_zero]⟩⟩
      exact sameSign_trans ih hss_step

lemma prem_sameSign {A K : Type} [CommRing A]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (φ : A →+* K) {f g : Polynomial A} (hgb : φ g.leadingCoeff ≠ 0)
    {x : K} (hxg : (g.map φ).eval x = 0) :
    sameSign (((prem f g).map φ).eval x) ((f.map φ).eval x) :=
  premAux_sameSign φ g hgb (f.natDegree + 1) f x hxg

end StripAndPrem

section CellRootAnalysis

noncomputable def cellLeftVal {K : Type} [CommRing K] (p : Polynomial K) (R : List K) (j : ℕ) : K :=
  if hj : 0 < j ∧ j - 1 < R.length then p.eval R[j - 1]
  else (-1 : K) ^ p.natDegree * p.leadingCoeff

noncomputable def cellRightVal {K : Type} [CommRing K] (p : Polynomial K) (R : List K) (j : ℕ) : K :=
  if hj : j < R.length then p.eval R[j]
  else p.leadingCoeff

lemma cell_root_analysis {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (hMVT : ∀ (p : Polynomial K) {u v : K}, u < v →
      ∃ c : K, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c)
    (hAsymp : ∀ (p : Polynomial K), p ≠ 0 →
      ∃ M : K, ∀ x : K, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))
    (p : Polynomial K) (hp : p ≠ 0) (R : List K) (hR : R.Pairwise (· < ·))
    (j : ℕ) (hj : j ≤ R.length)
    (hderiv : ∀ x : K, inCell R j x → p.derivative.eval x ≠ 0) :
    ¬ (cellLeftVal p R j = 0 ∧ cellRightVal p R j = 0) ∧
    ((∃ r : K, inCell R j r ∧ p.eval r = 0) ↔ cellLeftVal p R j * cellRightVal p R j < 0) ∧
    (∀ r₁ r₂ : K, inCell R j r₁ → inCell R j r₂ → p.eval r₁ = 0 → p.eval r₂ = 0 → r₁ = r₂) ∧
    ((¬ ∃ r : K, inCell R j r ∧ p.eval r = 0) → ∀ x : K, inCell R j x →
      (cellLeftVal p R j ≠ 0 → sameSign (p.eval x) (cellLeftVal p R j)) ∧
      (cellRightVal p R j ≠ 0 → sameSign (p.eval x) (cellRightVal p R j))) ∧
    (∀ r : K, inCell R j r → p.eval r = 0 → ∀ x : K, inCell R j x →
      (x < r → cellLeftVal p R j ≠ 0 ∧ sameSign (p.eval x) (cellLeftVal p R j)) ∧
      (r < x → cellRightVal p R j ≠ 0 ∧ sameSign (p.eval x) (cellRightVal p R j))) := by
  classical
  obtain ⟨M₁, hM₁⟩ := poly_asymp_neg hAsymp p hp
  obtain ⟨M₂, hM₂⟩ := poly_asymp_pos hAsymp p hp
  let a : K := if h : 0 < j ∧ j - 1 < R.length then R[j - 1]
    else if hRpos : 0 < R.length then min (M₁ - 1) (R[0] - 1) else M₁ - 1
  let b : K := if h : j < R.length then R[j]
    else if hRpos : 0 < R.length then max (M₂ + 1) (R[R.length - 1] + 1) else max (M₂ + 1) (a + 1)
  have ha_sign : sameSign (p.eval a) (cellLeftVal p R j) := by
    dsimp [a, cellLeftVal]
    split_ifs with h1 h2
    · exact sameSign_refl _
    · exact hM₁ _ (by have := min_le_left (M₁ - 1) (R[0] - 1); linarith)
    · exact hM₁ _ (by linarith)
  have hb_sign : sameSign (p.eval b) (cellRightVal p R j) := by
    dsimp [b, cellRightVal]
    split_ifs with h1 h2
    · exact sameSign_refl _
    · exact hM₂ _ (by have := le_max_left (M₂ + 1) (R[R.length - 1] + 1); linarith)
    · exact hM₂ _ (by have := le_max_left (M₂ + 1) (a + 1); linarith)
  have hab : a < b := by
    by_cases h1 : 0 < j ∧ j - 1 < R.length <;> by_cases h2 : j < R.length <;> by_cases hRpos : 0 < R.length
    · have ha_eq : a = R[j - 1] := dif_pos h1
      have hb_eq : b = R[j] := dif_pos h2
      rw [ha_eq, hb_eq]
      exact List.pairwise_iff_getElem.mp hR (j - 1) j h1.2 h2 (by omega)
    · omega
    · have ha_eq : a = R[j - 1] := dif_pos h1
      have hb_eq : b = max (M₂ + 1) (R[R.length - 1] + 1) := by simp only [b, dif_neg h2, dif_pos hRpos]
      rw [ha_eq, hb_eq]
      have hle : R[j - 1] ≤ R[R.length - 1] := getElem_le_of_pairwise_lt hR h1.2 (Nat.sub_lt hRpos zero_lt_one) (by omega)
      have hmax : R[R.length - 1] + 1 ≤ max (M₂ + 1) (R[R.length - 1] + 1) := le_max_right _ _
      linarith
    · omega
    · have ha_eq : a = min (M₁ - 1) (R[0] - 1) := by simp only [a, dif_neg h1, dif_pos hRpos]
      have hb_eq : b = R[j] := dif_pos h2
      rw [ha_eq, hb_eq]
      have hmin : min (M₁ - 1) (R[0] - 1) ≤ R[0] - 1 := min_le_right _ _
      have hle : R[0] ≤ R[j] := getElem_le_of_pairwise_lt hR hRpos h2 (Nat.zero_le j)
      linarith
    · omega
    · have ha_eq : a = min (M₁ - 1) (R[0] - 1) := by simp only [a, dif_neg h1, dif_pos hRpos]
      have hb_eq : b = max (M₂ + 1) (R[R.length - 1] + 1) := by simp only [b, dif_neg h2, dif_pos hRpos]
      rw [ha_eq, hb_eq]
      have hmin : min (M₁ - 1) (R[0] - 1) ≤ R[0] - 1 := min_le_right _ _
      have hle : R[0] ≤ R[R.length - 1] := getElem_le_of_pairwise_lt hR hRpos (Nat.sub_lt hRpos zero_lt_one) (Nat.zero_le _)
      have hmax : R[R.length - 1] + 1 ≤ max (M₂ + 1) (R[R.length - 1] + 1) := le_max_right _ _
      linarith
    · have ha_eq : a = M₁ - 1 := by simp only [a, dif_neg h1, dif_neg hRpos]
      have hb_eq : b = max (M₂ + 1) (a + 1) := by simp only [b, dif_neg h2, dif_neg hRpos]
      rw [hb_eq]
      have hmax : a + 1 ≤ max (M₂ + 1) (a + 1) := le_max_right _ _
      linarith
  have hIoo_inCell : ∀ c : K, a < c → c < b → inCell R j c := by
    intro c hca hcb
    refine ⟨fun i hi hij => ?_, fun i hi hji => ?_⟩
    · have hj_pos : 0 < j := by omega
      have hjm : j - 1 < R.length := by omega
      have ha_eq : a = R[j - 1] := by simp [a, hj_pos, hjm]
      have hle : R[i] ≤ R[j - 1] := getElem_le_of_pairwise_lt hR hi hjm (by omega)
      linarith
    · have hj_lt : j < R.length := lt_of_le_of_lt hji hi
      have hb_eq : b = R[j] := by simp [b, hj_lt]
      have hle : R[j] ≤ R[i] := getElem_le_of_pairwise_lt hR hj_lt hi hji
      linarith
  have hderiv_ab : ∀ c : K, a < c → c < b → p.derivative.eval c ≠ 0 :=
    fun c hca hcb => hderiv c (hIoo_inCell c hca hcb)
  have hleft_far : ∀ x : K, inCell R j x → x ≤ a → j = 0 ∧ sameSign (p.eval x) (cellLeftVal p R j) := by
    intro x hx hxa
    have hj0 : j = 0 := by
      by_contra hjp
      have hpos : 0 < j := Nat.pos_of_ne_zero hjp
      have hjm : j - 1 < R.length := by omega
      have ha_eq : a = R[j - 1] := by simp [a, hpos, hjm]
      have hlt : R[j - 1] < x := hx.1 (j - 1) hjm (by omega)
      linarith
    refine ⟨hj0, ?_⟩
    have ha_le_M : a < M₁ := by
      dsimp [a]
      split_ifs with h1 h2
      · omega
      · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · linarith
    have hss := hM₁ x (lt_of_le_of_lt hxa ha_le_M)
    have hlv : cellLeftVal p R j = (-1 : K) ^ p.natDegree * p.leadingCoeff := by
      simp [cellLeftVal, hj0]
    rwa [hlv]
  have hright_far : ∀ x : K, inCell R j x → b ≤ x → j = R.length ∧ sameSign (p.eval x) (cellRightVal p R j) := by
    intro x hx hbx
    have hjm : j = R.length := by
      by_contra hne
      have hj_lt : j < R.length := lt_of_le_of_ne hj hne
      have hb_eq : b = R[j] := by simp [b, hj_lt]
      have hlt : x < R[j] := hx.2 j hj_lt le_rfl
      linarith
    refine ⟨hjm, ?_⟩
    have hM_le_b : M₂ < b := by
      dsimp [b]
      split_ifs with h1 h2
      · omega
      · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
      · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hss := hM₂ x (lt_of_lt_of_le hM_le_b hbx)
    have hrv : cellRightVal p R j = p.leadingCoeff := by
      simp [cellRightVal, hjm]
    rwa [hrv]
  have hroot_in_ab : ∀ r : K, inCell R j r → p.eval r = 0 → a < r ∧ r < b := by
    intro r hr hr0
    refine ⟨?_, ?_⟩
    · by_contra hle
      obtain ⟨hj0, hss⟩ := hleft_far r hr (not_lt.mp hle)
      have hne : (-1 : K) ^ p.natDegree * p.leadingCoeff ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by norm_num)) (Polynomial.leadingCoeff_ne_zero.mpr hp)
      have hlv_ne : cellLeftVal p R j ≠ 0 := by simpa [cellLeftVal, hj0] using hne
      exact hlv_ne (hss.2.mp hr0)
    · by_contra hle
      obtain ⟨hjm, hss⟩ := hright_far r hr (not_lt.mp hle)
      have hne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
      have hrv_ne : cellRightVal p R j ≠ 0 := by simpa [cellRightVal, hjm] using hne
      exact hrv_ne (hss.2.mp hr0)
  have hnot_both_zero : ¬ (cellLeftVal p R j = 0 ∧ cellRightVal p R j = 0) := by
    rintro ⟨hl0, hr0⟩
    have ha0 : p.eval a = 0 := ha_sign.2.mpr hl0
    have hb0 : p.eval b = 0 := hb_sign.2.mpr hr0
    obtain ⟨c, hac, hcb, hmeq⟩ := hMVT p hab
    rw [ha0, hb0, sub_zero] at hmeq
    rcases mul_eq_zero.mp hmeq.symm with h | h
    · exact (sub_pos.mpr hab).ne' h
    · exact hderiv_ab c hac hcb h
  have hiff_root : (∃ r : K, inCell R j r ∧ p.eval r = 0) ↔ cellLeftVal p R j * cellRightVal p R j < 0 := by
    have hiff1 : (∃ r : K, inCell R j r ∧ p.eval r = 0) ↔ (∃ r : K, a < r ∧ r < b ∧ p.eval r = 0) := by
      constructor
      · rintro ⟨r, hr, hr0⟩
        obtain ⟨har, hrb⟩ := hroot_in_ab r hr hr0
        exact ⟨r, har, hrb, hr0⟩
      · rintro ⟨r, har, hrb, hr0⟩
        exact ⟨r, hIoo_inCell r har hrb, hr0⟩
    have hiff2 := poly_root_iff_opp_sign_on_bounded hIVT hMVT p hab hderiv_ab
    have hprod_ss : sameSign (p.eval a * p.eval b) (cellLeftVal p R j * cellRightVal p R j) :=
      sameSign_mul ha_sign hb_sign
    exact hiff1.trans (hiff2.trans hprod_ss.1)
  have huniq : ∀ r₁ r₂ : K, inCell R j r₁ → inCell R j r₂ → p.eval r₁ = 0 → p.eval r₂ = 0 → r₁ = r₂ := by
    intro r₁ r₂ hr₁ hr₂ hr₁0 hr₂0
    refine poly_unique_root_no_deriv hMVT p hr₁0 hr₂0 (fun c hc1 hc2 => ?_)
    have hc_in : inCell R j c := by
      refine ⟨fun i hi hij => ?_, fun i hi hji => ?_⟩
      · exact lt_trans (lt_min (hr₁.1 i hi hij) (hr₂.1 i hi hij)) hc1
      · exact lt_trans hc2 (max_lt (hr₁.2 i hi hji) (hr₂.2 i hi hji))
    exact hderiv c hc_in
  have hcell_between : ∀ x y : K, inCell R j x → inCell R j y → ∀ c : K, min x y ≤ c → c ≤ max x y → inCell R j c := by
    intro x y hx hy c hc1 hc2
    refine ⟨fun i hi hij => ?_, fun i hi hji => ?_⟩
    · exact lt_of_lt_of_le (lt_min (hx.1 i hi hij) (hy.1 i hi hij)) hc1
    · exact lt_of_le_of_lt hc2 (max_lt (hx.2 i hi hji) (hy.2 i hi hji))
  have hno_root_sign : (¬ ∃ r : K, inCell R j r ∧ p.eval r = 0) → ∀ x : K, inCell R j x →
      (cellLeftVal p R j ≠ 0 → sameSign (p.eval x) (cellLeftVal p R j)) ∧
      (cellRightVal p R j ≠ 0 → sameSign (p.eval x) (cellRightVal p R j)) := by
    intro hno x hx
    set m := (a + b) / 2
    have ham : a < m := by dsimp [m]; linarith
    have hmb : m < b := by dsimp [m]; linarith
    have hm_in : inCell R j m := hIoo_inCell m ham hmb
    have hxm : sameSign (p.eval x) (p.eval m) :=
      poly_const_sign_open hIVT p (fun c hc1 hc2 hc0 =>
        hno ⟨c, hcell_between x m hx hm_in c hc1 hc2, hc0⟩)
    have hno_ab : ∀ c : K, a < c → c < b → p.eval c ≠ 0 :=
      fun c hca hcb hc0 => hno ⟨c, hIoo_inCell c hca hcb, hc0⟩
    refine ⟨fun hl => ?_, fun hr => ?_⟩
    · have ha_ne : p.eval a ≠ 0 := fun ha0 => hl (ha_sign.2.mp ha0)
      have hma := poly_no_root_bounded_left_sign hIVT p ham hmb hno_ab ha_ne
      exact sameSign_trans hxm (sameSign_trans hma ha_sign)
    · have hb_ne : p.eval b ≠ 0 := fun hb0 => hr (hb_sign.2.mp hb0)
      have hmb' := poly_no_root_bounded_right_sign hIVT p ham hmb hno_ab hb_ne
      exact sameSign_trans hxm (sameSign_trans hmb' hb_sign)
  have hwith_root_sign : ∀ r : K, inCell R j r → p.eval r = 0 → ∀ x : K, inCell R j x →
      (x < r → cellLeftVal p R j ≠ 0 ∧ sameSign (p.eval x) (cellLeftVal p R j)) ∧
      (r < x → cellRightVal p R j ≠ 0 ∧ sameSign (p.eval x) (cellRightVal p R j)) := by
    intro r hr hr0 x hx
    obtain ⟨har, hrb⟩ := hroot_in_ab r hr hr0
    have hl_ne : cellLeftVal p R j ≠ 0 := by
      intro hl0
      have ha0 : p.eval a = 0 := ha_sign.2.mpr hl0
      obtain ⟨c, hac, hcr, hmeq⟩ := hMVT p har
      rw [ha0, hr0, sub_zero] at hmeq
      rcases mul_eq_zero.mp hmeq.symm with h | h
      · exact (sub_pos.mpr har).ne' h
      · exact hderiv_ab c hac (lt_trans hcr hrb) h
    have hr_ne : cellRightVal p R j ≠ 0 := by
      intro hr0'
      have hb0 : p.eval b = 0 := hb_sign.2.mpr hr0'
      obtain ⟨c, hrc, hcb, hmeq⟩ := hMVT p hrb
      rw [hr0, hb0, sub_zero] at hmeq
      rcases mul_eq_zero.mp hmeq.symm with h | h
      · exact (sub_pos.mpr hrb).ne' h
      · exact hderiv_ab c (lt_trans har hrc) hcb h
    refine ⟨fun hxr => ⟨hl_ne, ?_⟩, fun hrx => ⟨hr_ne, ?_⟩⟩
    · set m := (a + r) / 2
      have ham : a < m := by dsimp [m]; linarith
      have hmr : m < r := by dsimp [m]; linarith
      have hm_in : inCell R j m := hIoo_inCell m ham (lt_trans hmr hrb)
      have hxm : sameSign (p.eval x) (p.eval m) :=
        poly_const_sign_open hIVT p (fun c hc1 hc2 hc0 => by
          have hc_lt : c < r := lt_of_le_of_lt hc2 (max_lt hxr hmr)
          have hcr_eq := huniq c r (hcell_between x m hx hm_in c hc1 hc2) hr hc0 hr0
          exact hc_lt.ne hcr_eq)
      have ha_ne : p.eval a ≠ 0 := fun ha0 => hl_ne (ha_sign.2.mp ha0)
      have hno_ar : ∀ c : K, a < c → c < r → p.eval c ≠ 0 :=
        fun c hca hcr hc0 => hcr.ne (huniq c r (hIoo_inCell c hca (lt_trans hcr hrb)) hr hc0 hr0)
      have hma := poly_no_root_bounded_left_sign hIVT p ham hmr hno_ar ha_ne
      exact sameSign_trans hxm (sameSign_trans hma ha_sign)
    · set m := (r + b) / 2
      have hrm : r < m := by dsimp [m]; linarith
      have hmb : m < b := by dsimp [m]; linarith
      have hm_in : inCell R j m := hIoo_inCell m (lt_trans har hrm) hmb
      have hxm : sameSign (p.eval x) (p.eval m) :=
        poly_const_sign_open hIVT p (fun c hc1 hc2 hc0 => by
          have hrc_lt : r < c := lt_of_lt_of_le (lt_min hrx hrm) hc1
          have hcr_eq := huniq c r (hcell_between x m hx hm_in c hc1 hc2) hr hc0 hr0
          exact hrc_lt.ne' hcr_eq)
      have hb_ne : p.eval b ≠ 0 := fun hb0 => hr_ne (hb_sign.2.mp hb0)
      have hno_rb : ∀ c : K, r < c → c < b → p.eval c ≠ 0 :=
        fun c hrc hcb hc0 => hrc.ne' (huniq c r (hIoo_inCell c (lt_trans har hrc) hcb) hr hc0 hr0)
      have hmb' := poly_no_root_bounded_right_sign hIVT p hrm hmb hno_rb hb_ne
      exact sameSign_trans hxm (sameSign_trans hmb' hb_sign)
  exact ⟨hnot_both_zero, hiff_root, huniq, hno_root_sign, hwith_root_sign⟩

noncomputable def mergeCells {K : Type} (R : List K) (opt : ℕ → List K) (j : ℕ) : List K :=
  if hj : j < R.length then opt j ++ [R[j]] ++ mergeCells R opt (j + 1)
  else opt R.length
termination_by R.length - j

lemma mergeCells_mem_and_pairwise {K : Type} [LinearOrder K]
    (R : List K) (hR : R.Pairwise (· < ·)) (opt : ℕ → List K)
    (hopt_in : ∀ j ≤ R.length, ∀ x ∈ opt j, inCell R j x)
    (hopt_pw : ∀ j ≤ R.length, (opt j).Pairwise (· < ·)) :
    ∀ (j : ℕ), j ≤ R.length →
      (mergeCells R opt j).Pairwise (· < ·) ∧
      (∀ x ∈ mergeCells R opt j, ∀ i < j, ∀ hi : i < R.length, R[i] < x) ∧
      (∀ x, x ∈ mergeCells R opt j ↔ (∃ (i : ℕ) (hi : i < R.length), j ≤ i ∧ x = R[i]) ∨ (∃ k, j ≤ k ∧ k ≤ R.length ∧ x ∈ opt k)) := by
  intro j hj
  suffices h : ∀ n (j : ℕ), R.length - j = n → j ≤ R.length →
      (mergeCells R opt j).Pairwise (· < ·) ∧
      (∀ x ∈ mergeCells R opt j, ∀ i < j, ∀ hi : i < R.length, R[i] < x) ∧
      (∀ x, x ∈ mergeCells R opt j ↔ (∃ (i : ℕ) (hi : i < R.length), j ≤ i ∧ x = R[i]) ∨ (∃ k, j ≤ k ∧ k ≤ R.length ∧ x ∈ opt k)) from
    h (R.length - j) j rfl hj
  intro n
  induction n with
  | zero =>
    intro j hsub hj_le
    have hj_eq : j = R.length := by omega
    subst hj_eq
    have hmc : mergeCells R opt R.length = opt R.length := by
      unfold mergeCells
      simp
    rw [hmc]
    refine ⟨hopt_pw R.length le_rfl, fun x hx i hi hilen => (hopt_in R.length le_rfl x hx).1 i hilen hi, fun x => ?_⟩
    constructor
    · intro hx
      exact Or.inr ⟨R.length, le_rfl, le_rfl, hx⟩
    · rintro (⟨i, hi2, hi1, _⟩ | ⟨k, hk1, hk2, hx⟩)
      · omega
      · have : k = R.length := by omega
        subst this
        exact hx
  | succ n ih =>
    intro j hsub hj_le
    have hj_lt : j < R.length := by omega
    have hmc : mergeCells R opt j = opt j ++ [R[j]] ++ mergeCells R opt (j + 1) := by
      conv_lhs => unfold mergeCells; rw [dif_pos hj_lt]
    obtain ⟨ih_pw, ih_gt, ih_mem⟩ := ih (j + 1) (by omega) hj_lt
    have hoptj_pw := hopt_pw j hj_lt.le
    have hoptj_lt_Rj : ∀ x ∈ opt j, x < R[j] := fun x hx => (hopt_in j hj_lt.le x hx).2 j hj_lt le_rfl
    have hRj_lt_rest : ∀ y ∈ mergeCells R opt (j + 1), R[j] < y :=
      fun y hy => ih_gt y hy j (Nat.lt_succ_self j) hj_lt
    have hoptj_lt_rest : ∀ x ∈ opt j, ∀ y ∈ mergeCells R opt (j + 1), x < y :=
      fun x hx y hy => lt_trans (hoptj_lt_Rj x hx) (hRj_lt_rest y hy)
    rw [hmc]
    refine ⟨?_, ?_, fun x => ?_⟩
    · rw [List.append_assoc, List.pairwise_append]
      refine ⟨hoptj_pw, List.pairwise_cons.mpr ⟨hRj_lt_rest, ih_pw⟩, fun x hx y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hoptj_lt_Rj x hx
      · exact hoptj_lt_rest x hx y hy
    · intro x hx i hij hi
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with (hx | rfl) | hx
      · exact (hopt_in j hj_lt.le x hx).1 i hi hij
      · exact List.pairwise_iff_getElem.mp hR i j hi hj_lt hij
      · exact ih_gt x hx i (Nat.lt_succ_of_lt hij) hi
    · simp only [List.mem_append, List.mem_singleton, ih_mem]
      constructor
      · rintro ((hx | rfl) | (⟨i, hi2, hi1, rfl⟩ | ⟨k, hk1, hk2, hx⟩))
        · exact Or.inr ⟨j, le_rfl, hj_lt.le, hx⟩
        · exact Or.inl ⟨j, hj_lt, le_rfl, rfl⟩
        · exact Or.inl ⟨i, hi2, Nat.le_of_succ_le hi1, rfl⟩
        · exact Or.inr ⟨k, Nat.le_of_succ_le hk1, hk2, hx⟩
      · rintro (⟨i, hi2, hi1, rfl⟩ | ⟨k, hk1, hk2, hx⟩)
        · rcases eq_or_lt_of_le hi1 with rfl | hlt
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr (Or.inl ⟨i, hi2, hlt, rfl⟩)
        · rcases eq_or_lt_of_le hk1 with rfl | hlt
          · exact Or.inl (Or.inl hx)
          · exact Or.inr (Or.inr ⟨k, hlt, hk2, hx⟩)

lemma mergeCells_forall₂ {K₁ K₂ : Type}
    (R₁ : List K₁) (R₂ : List K₂) (hlen : R₁.length = R₂.length)
    (opt₁ : ℕ → List K₁) (opt₂ : ℕ → List K₂) (rel : K₁ → K₂ → Prop)
    (hrel_R : ∀ (j : ℕ) (h₁ : j < R₁.length) (h₂ : j < R₂.length), rel R₁[j] R₂[j])
    (hrel_opt : ∀ j ≤ R₁.length, List.Forall₂ rel (opt₁ j) (opt₂ j)) :
    ∀ (j : ℕ), j ≤ R₁.length →
      List.Forall₂ rel (mergeCells R₁ opt₁ j) (mergeCells R₂ opt₂ j) := by
  intro j hj
  suffices h : ∀ n (j : ℕ), R₁.length - j = n → j ≤ R₁.length →
      List.Forall₂ rel (mergeCells R₁ opt₁ j) (mergeCells R₂ opt₂ j) from
    h (R₁.length - j) j rfl hj
  intro n
  induction n with
  | zero =>
    intro j hsub hj_le
    have hj_eq : j = R₁.length := by omega
    subst hj_eq
    have hm1 : mergeCells R₁ opt₁ R₁.length = opt₁ R₁.length := by
      unfold mergeCells; simp
    have hm2 : mergeCells R₂ opt₂ R₁.length = opt₂ R₂.length := by
      unfold mergeCells; simp [hlen]
    rw [hm1, hm2, ← hlen]
    exact hrel_opt R₁.length le_rfl
  | succ n ih =>
    intro j hsub hj_le
    have hj1 : j < R₁.length := by omega
    have hj2 : j < R₂.length := hlen ▸ hj1
    have hm1 : mergeCells R₁ opt₁ j = opt₁ j ++ [R₁[j]] ++ mergeCells R₁ opt₁ (j + 1) := by
      conv_lhs => unfold mergeCells; rw [dif_pos hj1]
    have hm2 : mergeCells R₂ opt₂ j = opt₂ j ++ [R₂[j]] ++ mergeCells R₂ opt₂ (j + 1) := by
      conv_lhs => unfold mergeCells; rw [dif_pos hj2]
    rw [hm1, hm2]
    exact forall₂_append_of
      (forall₂_append_of (hrel_opt j hj1.le) (List.Forall₂.cons (hrel_R j hj1 hj2) List.Forall₂.nil))
      (ih (j + 1) (by omega) hj1)

lemma countP_take_lt_of_iff {K : Type} [LinearOrder K] :
    ∀ {R RF : List K}, RF.Pairwise (· < ·) → R.Pairwise (· < ·) →
      (∀ r, r ∈ R → r ∈ RF) →
      ∀ {i : ℕ} {x : K}, i ≤ RF.length →
      (∀ k (hk : k < RF.length), RF[k] ∈ R → (k < i ↔ RF[k] < x)) →
      ∀ {j : ℕ}, j ≤ R.length → inCell R j x →
      j = (RF.take i).countP (fun r => decide (r ∈ R)) := by
  classical
  intro R RF hRF hR hsub i x hi_le hiff j hj_le hjx
  have h1 : (RF.take i).countP (fun r => decide (r ∈ R)) = (RF.filter (fun r => decide (r ∈ R ∧ r < x))).length := by
    have hfilt : ∀ {l : List K} (k : ℕ), k ≤ l.length → l.Pairwise (· < ·) →
        (∀ m (hm : m < l.length), l[m] ∈ R → (m < k ↔ l[m] < x)) →
        (l.take k).countP (fun r => decide (r ∈ R)) = (l.filter (fun r => decide (r ∈ R ∧ r < x))).length := by
      intro l
      induction l with
      | nil =>
        intro k hk _ _
        simp at hk
        subst hk
        simp
      | cons a t ih =>
        intro k hk hpw hm_iff
        rw [List.pairwise_cons] at hpw
        cases k with
        | zero =>
          simp only [List.take_zero, List.countP_nil]
          symm
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro r hr
          simp only [decide_eq_true_eq, not_and, not_lt]
          intro hrR
          rcases List.mem_cons.mp hr with rfl | hrt
          · have h0 := hm_iff 0 (by simp) hrR
            by_contra hlt
            exact absurd (h0.mpr (not_le.mp hlt)) (Nat.not_lt_zero 0)
          · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hrt
            have hm' := hm_iff (m + 1) (by simp [hm]) hrR
            by_contra hlt
            exact absurd (hm'.mpr (not_le.mp hlt)) (Nat.not_lt_zero (m + 1))
        | succ k =>
          have hk' : k ≤ t.length := Nat.succ_le_succ_iff.mp hk
          have hm_iff' : ∀ m (hm : m < t.length), t[m] ∈ R → (m < k ↔ t[m] < x) := by
            intro m hm hmR
            have := hm_iff (m + 1) (by simp [hm]) hmR
            simpa [Nat.succ_lt_succ_iff] using this
          have ih' := ih k hk' hpw.2 hm_iff'
          rw [List.take_succ_cons, List.countP_cons, List.filter_cons]
          by_cases haR : a ∈ R
          · have hax : a < x := (hm_iff 0 (by simp) haR).mp (Nat.zero_lt_succ k)
            simp [haR, hax, ih', Nat.add_comm]
          · simp [haR, ih']
    exact hfilt i hi_le hRF hiff
  have h2 : (RF.filter (fun r => decide (r ∈ R ∧ r < x))).length = (R.filter (fun r => decide (r < x))).length := by
    have hp1 : (RF.filter (fun r => decide (r ∈ R ∧ r < x))).Pairwise (· < ·) := hRF.filter _
    have hp2 : (R.filter (fun r => decide (r < x))).Pairwise (· < ·) := hR.filter _
    have heq_l : RF.filter (fun r => decide (r ∈ R ∧ r < x)) = R.filter (fun r => decide (r < x)) := by
      refine list_eq_of_pairwise_lt_of_mem_iff hp1 hp2 (fun r => ?_)
      simp only [List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨_, hrR, hrx⟩; exact ⟨hrR, hrx⟩
      · rintro ⟨hrR, hrx⟩; exact ⟨hsub r hrR, hrR, hrx⟩
    rw [heq_l]
  have h3 : (R.filter (fun r => decide (r < x))).length = j := by
    have hfiltR : ∀ {l : List K} (k : ℕ), k ≤ l.length → l.Pairwise (· < ·) →
        (∀ m (hm : m < l.length), m < k → l[m] < x) →
        (∀ m (hm : m < l.length), k ≤ m → x < l[m]) →
        (l.filter (fun r => decide (r < x))).length = k := by
      intro l
      induction l with
      | nil =>
        intro k hk _ _ _
        simp at hk; subst hk; simp
      | cons a t ih =>
        intro k hk hpw hlt hgt
        rw [List.pairwise_cons] at hpw
        cases k with
        | zero =>
          have ha_gt : x < a := hgt 0 (by simp) le_rfl
          rw [List.filter_cons, if_neg (by simp [not_lt.mpr ha_gt.le])]
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro r hr
          simp only [decide_eq_true_eq, not_lt]
          obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hr
          exact (hgt (m + 1) (by simp [hm]) (Nat.zero_le _)).le
        | succ k =>
          have hax : a < x := hlt 0 (by simp) (Nat.zero_lt_succ k)
          rw [List.filter_cons, if_pos (by simp [hax]), List.length_cons]
          have ih' := ih k (Nat.succ_le_succ_iff.mp hk) hpw.2
            (fun m hm hmk => hlt (m + 1) (by simp [hm]) (Nat.succ_lt_succ hmk))
            (fun m hm hkm => hgt (m + 1) (by simp [hm]) (Nat.succ_le_succ hkm))
          omega
    exact hfiltR j hj_le hR hjx.1 hjx.2
  omega

lemma addPolySignTable {A K₁ K₂ : Type} [CommRing A]
    [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂]
    (hIVT₁ : ∀ (p : Polynomial K₁) {a b : K₁}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₁, a < c ∧ c < b ∧ p.eval c = 0)
    (hIVT₂ : ∀ (p : Polynomial K₂) {a b : K₂}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₂, a < c ∧ c < b ∧ p.eval c = 0)
    (hMVT₁ : ∀ (p : Polynomial K₁) {u v : K₁}, u < v →
      ∃ c : K₁, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c)
    (hMVT₂ : ∀ (p : Polynomial K₂) {u v : K₂}, u < v →
      ∃ c : K₂, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c)
    (hAsymp₁ : ∀ (p : Polynomial K₁), p ≠ 0 →
      ∃ M : K₁, ∀ x : K₁, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))
    (hAsymp₂ : ∀ (p : Polynomial K₂), p ≠ 0 →
      ∃ M : K₂, ∀ x : K₂, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))
    {φ₁ : A →+* K₁} {φ₂ : A →+* K₂} {P₁ : List (Polynomial A)} {f : Polynomial A}
    (hf_nz : φ₁ f.leadingCoeff ≠ 0) (hf_deriv : f.derivative ∈ P₁)
    (hP₁_nz : ∀ g ∈ P₁, g ≠ 0 ∧ φ₁ g.leadingCoeff ≠ 0)
    (hlead_f : sameSign (φ₁ f.leadingCoeff) (φ₂ f.leadingCoeff))
    (hlead_P : ∀ g ∈ P₁, sameSign (φ₁ g.leadingCoeff) (φ₂ g.leadingCoeff))
    (hST : SignTableMatch φ₁ φ₂ P₁)
    (hprem : ∀ g ∈ P₁, ∀ (i : ℕ) (h₁ : i < (rootList (P₁.map (Polynomial.map φ₁))).length)
        (h₂ : i < (rootList (P₁.map (Polynomial.map φ₂))).length),
      (g.map φ₁).eval (rootList (P₁.map (Polynomial.map φ₁)))[i] = 0 →
      sameSign (((prem f g).map φ₁).eval (rootList (P₁.map (Polynomial.map φ₁)))[i])
               (((prem f g).map φ₂).eval (rootList (P₁.map (Polynomial.map φ₂)))[i])) :
    SignTableMatch φ₁ φ₂ (P₁ ++ [f]) := by
  classical
  set R₁ := rootList (P₁.map (Polynomial.map φ₁))
  set R₂ := rootList (P₁.map (Polynomial.map φ₂))
  have hR₁ : R₁.Pairwise (· < ·) := rootList_pairwise_lt _
  have hR₂ : R₂.Pairwise (· < ·) := rootList_pairwise_lt _
  set f₁ := f.map φ₁
  set f₂ := f.map φ₂
  have hf₂_lc : φ₂ f.leadingCoeff ≠ 0 := fun h => hf_nz (hlead_f.2.mpr h)
  have hf₁_ne : f₁ ≠ 0 := by
    intro h0
    have hlc : f₁.leadingCoeff = φ₁ f.leadingCoeff := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ₁ hf_nz
    rw [h0, Polynomial.leadingCoeff_zero] at hlc
    exact hf_nz hlc.symm
  have hf₂_ne : f₂ ≠ 0 := by
    intro h0
    have hlc : f₂.leadingCoeff = φ₂ f.leadingCoeff := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ₂ hf₂_lc
    rw [h0, Polynomial.leadingCoeff_zero] at hlc
    exact hf₂_lc hlc.symm
  have hf₁_deg : f₁.natDegree = f.natDegree := Polynomial.natDegree_map_of_leadingCoeff_ne_zero φ₁ hf_nz
  have hf₂_deg : f₂.natDegree = f.natDegree := Polynomial.natDegree_map_of_leadingCoeff_ne_zero φ₂ hf₂_lc
  have hf₁_lc : f₁.leadingCoeff = φ₁ f.leadingCoeff := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ₁ hf_nz
  have hf₂_lc_eq : f₂.leadingCoeff = φ₂ f.leadingCoeff := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ₂ hf₂_lc
  have hf_at_R : ∀ (i : ℕ) (h₁ : i < R₁.length) (h₂ : i < R₂.length),
      sameSign (f₁.eval R₁[i]) (f₂.eval R₂[i]) := by
    intro i hi₁ hi₂
    have hmem : R₁[i] ∈ R₁ := List.getElem_mem hi₁
    rw [mem_rootList] at hmem
    obtain ⟨pK, hpK, hpK0, hpKx⟩ := hmem
    rw [List.mem_map] at hpK
    obtain ⟨g, hgP, rfl⟩ := hpK
    have hgb₁ : φ₁ g.leadingCoeff ≠ 0 := (hP₁_nz g hgP).2
    have hgb₂ : φ₂ g.leadingCoeff ≠ 0 := fun h => hgb₁ ((hlead_P g hgP).2.mpr h)
    have hgx₂ : (g.map φ₂).eval R₂[i] = 0 := (hST.2.1 i hi₁ hi₂ g hgP).2.mp hpKx
    have h1 := prem_sameSign (f := f) φ₁ hgb₁ hpKx
    have h2 := hprem g hgP i hi₁ hi₂ hpKx
    have h3 := prem_sameSign (f := f) φ₂ hgb₂ hgx₂
    exact sameSign_trans (sameSign_symm h1) (sameSign_trans h2 h3)
  have hderiv₁ : ∀ j ≤ R₁.length, ∀ x : K₁, inCell R₁ j x → f₁.derivative.eval x ≠ 0 := by
    intro j _ x hx h0
    have hfd_ne : f.derivative.map φ₁ ≠ 0 := by
      intro hz
      have hfd_mem := List.mem_map_of_mem (f := Polynomial.map φ₁) hf_deriv
      have hfd_lc : φ₁ f.derivative.leadingCoeff ≠ 0 := (hP₁_nz f.derivative hf_deriv).2
      have := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ₁ hfd_lc
      rw [hz, Polynomial.leadingCoeff_zero] at this
      exact hfd_lc this.symm
    have hx_mem : x ∈ R₁ := mem_rootList.mpr ⟨f.derivative.map φ₁, List.mem_map_of_mem hf_deriv, hfd_ne, by
      simpa [f₁, Polynomial.derivative_map] using h0⟩
    exact inCell_not_mem hx hx_mem
  have hderiv₂ : ∀ j ≤ R₂.length, ∀ x : K₂, inCell R₂ j x → f₂.derivative.eval x ≠ 0 := by
    intro j _ x hx h0
    have hfd_lc₁ : φ₁ f.derivative.leadingCoeff ≠ 0 := (hP₁_nz f.derivative hf_deriv).2
    have hfd_lc₂ : φ₂ f.derivative.leadingCoeff ≠ 0 := fun h => hfd_lc₁ ((hlead_P f.derivative hf_deriv).2.mpr h)
    have hfd_ne : f.derivative.map φ₂ ≠ 0 := by
      intro hz
      have := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ₂ hfd_lc₂
      rw [hz, Polynomial.leadingCoeff_zero] at this
      exact hfd_lc₂ this.symm
    have hx_mem : x ∈ R₂ := mem_rootList.mpr ⟨f.derivative.map φ₂, List.mem_map_of_mem hf_deriv, hfd_ne, by
      simpa [f₂, Polynomial.derivative_map] using h0⟩
    exact inCell_not_mem hx hx_mem
  have hL_ss : ∀ j ≤ R₁.length, sameSign (cellLeftVal f₁ R₁ j) (cellLeftVal f₂ R₂ j) := by
    intro j hj
    dsimp [cellLeftVal]
    by_cases hcond : 0 < j ∧ j - 1 < R₁.length
    · have hcond2 : 0 < j ∧ j - 1 < R₂.length := ⟨hcond.1, hST.1 ▸ hcond.2⟩
      simp only [dif_pos hcond, dif_pos hcond2]
      exact hf_at_R (j - 1) hcond.2 hcond2.2
    · have hcond2 : ¬ (0 < j ∧ j - 1 < R₂.length) := by rwa [← hST.1]
      simp only [dif_neg hcond, dif_neg hcond2, hf₁_deg, hf₂_deg, hf₁_lc, hf₂_lc_eq]
      exact sameSign_mul (sameSign_neg_one_pow f.natDegree) hlead_f
  have hR_ss : ∀ j ≤ R₁.length, sameSign (cellRightVal f₁ R₁ j) (cellRightVal f₂ R₂ j) := by
    intro j hj
    dsimp [cellRightVal]
    by_cases hcond : j < R₁.length
    · have hcond2 : j < R₂.length := hST.1 ▸ hcond
      simp only [dif_pos hcond, dif_pos hcond2]
      exact hf_at_R j hcond hcond2
    · have hcond2 : ¬ j < R₂.length := by rwa [← hST.1]
      simp only [dif_neg hcond, dif_neg hcond2, hf₁_lc, hf₂_lc_eq]
      exact hlead_f
  have hca₁ : ∀ j ≤ R₁.length, _ := fun j hj => cell_root_analysis hIVT₁ hMVT₁ hAsymp₁ f₁ hf₁_ne R₁ hR₁ j hj (hderiv₁ j hj)
  have hca₂ : ∀ j ≤ R₂.length, _ := fun j hj => cell_root_analysis hIVT₂ hMVT₂ hAsymp₂ f₂ hf₂_ne R₂ hR₂ j hj (hderiv₂ j hj)
  have hroot_iff : ∀ j ≤ R₁.length,
      (∃ r : K₁, inCell R₁ j r ∧ f₁.eval r = 0) ↔ (∃ r : K₂, inCell R₂ j r ∧ f₂.eval r = 0) := by
    intro j hj
    rw [(hca₁ j hj).2.1, (hca₂ j (hST.1 ▸ hj)).2.1]
    exact (sameSign_mul (hL_ss j hj) (hR_ss j hj)).1
  let opt₁ : ℕ → List K₁ := fun j => if h : ∃ r : K₁, inCell R₁ j r ∧ f₁.eval r = 0 then [Classical.choose h] else []
  let opt₂ : ℕ → List K₂ := fun j => if h : ∃ r : K₂, inCell R₂ j r ∧ f₂.eval r = 0 then [Classical.choose h] else []
  have hopt₁_in : ∀ j ≤ R₁.length, ∀ x ∈ opt₁ j, inCell R₁ j x := by
    intro j _ x hx
    dsimp [opt₁] at hx
    split_ifs at hx with h
    · simp only [List.mem_singleton] at hx
      subst hx
      exact (Classical.choose_spec h).1
    · simp at hx
  have hopt₂_in : ∀ j ≤ R₂.length, ∀ x ∈ opt₂ j, inCell R₂ j x := by
    intro j _ x hx
    dsimp [opt₂] at hx
    split_ifs at hx with h
    · simp only [List.mem_singleton] at hx
      subst hx
      exact (Classical.choose_spec h).1
    · simp at hx
  have hopt₁_pw : ∀ j ≤ R₁.length, (opt₁ j).Pairwise (· < ·) := by
    intro j _
    dsimp [opt₁]
    split_ifs <;> simp
  have hopt₂_pw : ∀ j ≤ R₂.length, (opt₂ j).Pairwise (· < ·) := by
    intro j _
    dsimp [opt₂]
    split_ifs <;> simp
  set RF₁ := rootList ((P₁ ++ [f]).map (Polynomial.map φ₁))
  set RF₂ := rootList ((P₁ ++ [f]).map (Polynomial.map φ₂))
  have hmc₁ := mergeCells_mem_and_pairwise R₁ hR₁ opt₁ hopt₁_in hopt₁_pw 0 (Nat.zero_le _)
  have hmc₂ := mergeCells_mem_and_pairwise R₂ hR₂ opt₂ hopt₂_in hopt₂_pw 0 (Nat.zero_le _)
  have hRF₁_eq : RF₁ = mergeCells R₁ opt₁ 0 := by
    refine list_eq_of_pairwise_lt_of_mem_iff (rootList_pairwise_lt _) hmc₁.1 (fun x => ?_)
    rw [hmc₁.2.2 x, mem_rootList]
    simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨q, hq | rfl, hq0, hqx⟩
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_rootList.mpr ⟨q, hq, hq0, hqx⟩)
        exact Or.inl ⟨i, hi, Nat.zero_le _, rfl⟩
      · by_cases hxR : x ∈ R₁
        · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hxR
          exact Or.inl ⟨i, hi, Nat.zero_le _, rfl⟩
        · obtain ⟨j, hj_le, hjx⟩ := exists_inCell_of_not_mem hR₁ hxR
          have hex : ∃ r : K₁, inCell R₁ j r ∧ f₁.eval r = 0 := ⟨x, hjx, hqx⟩
          have hchoose := Classical.choose_spec hex
          have hxeq : x = Classical.choose hex := (hca₁ j hj_le).2.2.1 x _ hjx hchoose.1 hqx hchoose.2
          refine Or.inr ⟨j, Nat.zero_le _, hj_le, ?_⟩
          dsimp [opt₁]
          rw [dif_pos hex, List.mem_singleton]
          exact hxeq
    · rintro (⟨i, hi, _, rfl⟩ | ⟨k, _, hk, hxk⟩)
      · obtain ⟨q, hq, hq0, hqx⟩ := mem_rootList.mp (List.getElem_mem hi)
        exact ⟨q, Or.inl hq, hq0, hqx⟩
      · refine ⟨f₁, Or.inr rfl, hf₁_ne, ?_⟩
        dsimp [opt₁] at hxk
        split_ifs at hxk with h
        · simp only [List.mem_singleton] at hxk
          subst hxk
          exact (Classical.choose_spec h).2
        · simp at hxk
  have hRF₂_eq : RF₂ = mergeCells R₂ opt₂ 0 := by
    refine list_eq_of_pairwise_lt_of_mem_iff (rootList_pairwise_lt _) hmc₂.1 (fun x => ?_)
    rw [hmc₂.2.2 x, mem_rootList]
    simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨q, hq | rfl, hq0, hqx⟩
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_rootList.mpr ⟨q, hq, hq0, hqx⟩)
        exact Or.inl ⟨i, hi, Nat.zero_le _, rfl⟩
      · by_cases hxR : x ∈ R₂
        · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hxR
          exact Or.inl ⟨i, hi, Nat.zero_le _, rfl⟩
        · obtain ⟨j, hj_le, hjx⟩ := exists_inCell_of_not_mem hR₂ hxR
          have hex : ∃ r : K₂, inCell R₂ j r ∧ f₂.eval r = 0 := ⟨x, hjx, hqx⟩
          have hchoose := Classical.choose_spec hex
          have hxeq : x = Classical.choose hex := (hca₂ j hj_le).2.2.1 x _ hjx hchoose.1 hqx hchoose.2
          refine Or.inr ⟨j, Nat.zero_le _, hj_le, ?_⟩
          dsimp [opt₂]
          rw [dif_pos hex, List.mem_singleton]
          exact hxeq
    · rintro (⟨i, hi, _, rfl⟩ | ⟨k, _, hk, hxk⟩)
      · obtain ⟨q, hq, hq0, hqx⟩ := mem_rootList.mp (List.getElem_mem hi)
        exact ⟨q, Or.inl hq, hq0, hqx⟩
      · refine ⟨f₂, Or.inr rfl, hf₂_ne, ?_⟩
        dsimp [opt₂] at hxk
        split_ifs at hxk with h
        · simp only [List.mem_singleton] at hxk
          subst hxk
          exact (Classical.choose_spec h).2
        · simp at hxk
  let rel : K₁ → K₂ → Prop := fun r₁ r₂ =>
    (r₁ ∈ R₁ ↔ r₂ ∈ R₂) ∧
    (∀ p ∈ P₁ ++ [f], sameSign ((p.map φ₁).eval r₁) ((p.map φ₂).eval r₂))
  have hF_mc : List.Forall₂ rel (mergeCells R₁ opt₁ 0) (mergeCells R₂ opt₂ 0) := by
    refine mergeCells_forall₂ R₁ R₂ hST.1 opt₁ opt₂ rel ?_ ?_ 0 (Nat.zero_le _)
    · intro j hj₁ hj₂
      refine ⟨⟨fun _ => List.getElem_mem hj₂, fun _ => List.getElem_mem hj₁⟩, fun p hp => ?_⟩
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hST.2.1 j hj₁ hj₂ p hp
      · exact hf_at_R j hj₁ hj₂
    · intro j hj
      dsimp [opt₁, opt₂]
      by_cases h1 : ∃ r : K₁, inCell R₁ j r ∧ f₁.eval r = 0
      · have h2 : ∃ r : K₂, inCell R₂ j r ∧ f₂.eval r = 0 := (hroot_iff j hj).mp h1
        rw [dif_pos h1, dif_pos h2]
        refine List.Forall₂.cons ⟨?_, fun p hp => ?_⟩ List.Forall₂.nil
        · constructor
          · intro hm; exact absurd hm (inCell_not_mem (Classical.choose_spec h1).1)
          · intro hm; exact absurd hm (inCell_not_mem (Classical.choose_spec h2).1)
        · simp only [List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · exact hST.2.2 j _ _ hj (Classical.choose_spec h1).1 (Classical.choose_spec h2).1 p hp
          · rw [(Classical.choose_spec h1).2, (Classical.choose_spec h2).2]
            exact sameSign_zero
      · have h2 : ¬ ∃ r : K₂, inCell R₂ j r ∧ f₂.eval r = 0 := fun hx => h1 ((hroot_iff j hj).mpr hx)
        rw [dif_neg h1, dif_neg h2]
        exact List.Forall₂.nil
  rw [← hRF₁_eq, ← hRF₂_eq] at hF_mc
  refine ⟨(List.forall₂_iff_get.mp hF_mc).1, fun i hi₁ hi₂ p hp => (forall₂_getElem hF_mc i hi₁ hi₂).2 p hp, ?_⟩
  intro i x₁ x₂ hi_le hx₁ hx₂ q hq
  have hx₁_nR : x₁ ∉ R₁ := fun hm => by
    have hxRF : x₁ ∈ RF₁ := by
      obtain ⟨p', hp', hp0, hpx⟩ := mem_rootList.mp hm
      exact mem_rootList.mpr ⟨p', by simp [hp'], hp0, hpx⟩
    exact inCell_not_mem hx₁ hxRF
  have hx₂_nR : x₂ ∉ R₂ := fun hm => by
    have hxRF : x₂ ∈ RF₂ := by
      obtain ⟨p', hp', hp0, hpx⟩ := mem_rootList.mp hm
      exact mem_rootList.mpr ⟨p', by simp [hp'], hp0, hpx⟩
    exact inCell_not_mem hx₂ hxRF
  obtain ⟨j₁, hj₁_le, hj₁_in⟩ := exists_inCell_of_not_mem hR₁ hx₁_nR
  obtain ⟨j₂, hj₂_le, hj₂_in⟩ := exists_inCell_of_not_mem hR₂ hx₂_nR
  have hRF₁_pw : RF₁.Pairwise (· < ·) := rootList_pairwise_lt _
  have hRF₂_pw : RF₂.Pairwise (· < ·) := rootList_pairwise_lt _
  have hsub₁ : ∀ r, r ∈ R₁ → r ∈ RF₁ := fun r hr => by
    obtain ⟨p', hp', hp0, hpx⟩ := mem_rootList.mp hr
    exact mem_rootList.mpr ⟨p', by simp [hp'], hp0, hpx⟩
  have hsub₂ : ∀ r, r ∈ R₂ → r ∈ RF₂ := fun r hr => by
    obtain ⟨p', hp', hp0, hpx⟩ := mem_rootList.mp hr
    exact mem_rootList.mpr ⟨p', by simp [hp'], hp0, hpx⟩
  have hRF_len : RF₁.length = RF₂.length := (List.forall₂_iff_get.mp hF_mc).1
  have hj₁_eq := countP_take_lt_of_iff hRF₁_pw hR₁ hsub₁ hi_le
    (fun k hk _ => ⟨fun hki => hx₁.1 k hk hki, fun hkx => by
      by_contra hge
      exact lt_irrefl _ (lt_trans hkx (hx₁.2 k hk (not_lt.mp hge)))⟩)
    hj₁_le hj₁_in
  have hj₂_eq := countP_take_lt_of_iff hRF₂_pw hR₂ hsub₂ (hRF_len ▸ hi_le)
    (fun k hk _ => ⟨fun hki => hx₂.1 k hk hki, fun hkx => by
      by_contra hge
      exact lt_irrefl _ (lt_trans hkx (hx₂.2 k hk (not_lt.mp hge)))⟩)
    hj₂_le hj₂_in
  have htake_eq : (RF₁.take i).countP (fun r => decide (r ∈ R₁)) = (RF₂.take i).countP (fun r => decide (r ∈ R₂)) := by
    refine countP_eq_of_forall₂ _ _ (forall₂_of_getElem (by simp [hRF_len]) (fun k hk₁ hk₂ => ?_))
    have hki : k < i := by
      have : k < (RF₁.take i).length := hk₁
      rw [List.length_take] at this
      exact (lt_min_iff.mp this).1
    have hk_RF₁ : k < RF₁.length := lt_of_lt_of_le hki hi_le
    have hk_RF₂ : k < RF₂.length := hRF_len ▸ hk_RF₁
    change decide ((RF₁.take i)[k] ∈ R₁) = decide ((RF₂.take i)[k] ∈ R₂)
    rw [List.getElem_take, List.getElem_take]
    simpa [decide_eq_true_eq] using (forall₂_getElem hF_mc k hk_RF₁ hk_RF₂).1
  have hj_eq : j₁ = j₂ := by omega
  subst hj_eq
  simp only [List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | rfl
  · exact hST.2.2 j₁ x₁ x₂ hj₁_le hj₁_in hj₂_in q hq
  · by_cases hopt : ∃ r : K₁, inCell R₁ j₁ r ∧ f₁.eval r = 0
    · have hopt2 : ∃ r : K₂, inCell R₂ j₁ r ∧ f₂.eval r = 0 := (hroot_iff j₁ hj₁_le).mp hopt
      set r₁ := Classical.choose hopt
      set r₂ := Classical.choose hopt2
      have hr₁_spec := Classical.choose_spec hopt
      have hr₂_spec := Classical.choose_spec hopt2
      have hr₁_RF : r₁ ∈ RF₁ := mem_rootList.mpr ⟨f₁, by simp [f₁], hf₁_ne, hr₁_spec.2⟩
      obtain ⟨idx, hidx₁, hidx_eq⟩ := List.mem_iff_getElem.mp hr₁_RF
      have hidx_eq' : RF₁[idx] = Classical.choose hopt := hidx_eq
      have hidx₂ : idx < RF₂.length := hRF_len ▸ hidx₁
      have hr₂'_nR : RF₂[idx] ∉ R₂ := fun hm => by
        have hmem1 : RF₁[idx] ∈ R₁ := (forall₂_getElem hF_mc idx hidx₁ hidx₂).1.mpr hm
        exact inCell_not_mem hr₁_spec.1 (hidx_eq' ▸ hmem1)
      have hr₂'_f : f₂.eval RF₂[idx] = 0 := by
        have := (forall₂_getElem hF_mc idx hidx₁ hidx₂).2 q (by simp)
        change sameSign (f₁.eval RF₁[idx]) (f₂.eval RF₂[idx]) at this
        rw [hidx_eq', hr₁_spec.2] at this
        exact this.2.mp rfl
      have hr₂'_in : inCell R₂ j₁ RF₂[idx] := by
        obtain ⟨j', hj'_le, hj'_in⟩ := exists_inCell_of_not_mem hR₂ hr₂'_nR
        have hj'_eq_j₁ : j' = j₁ := by
          have hc1 : j₁ = (RF₁.take idx).countP (fun r => decide (r ∈ R₁)) := by
            refine countP_take_lt_of_iff hRF₁_pw hR₁ hsub₁ hidx₁.le (fun k hk hkR => ?_) hj₁_le hr₁_spec.1
            have hk_ne : k ≠ idx := fun he => by
              have : RF₁[idx] ∈ R₁ := he ▸ hkR
              exact inCell_not_mem hr₁_spec.1 (hidx_eq' ▸ this)
            constructor
            · intro hki
              rw [← hidx_eq']
              exact List.pairwise_iff_getElem.mp hRF₁_pw k idx hk hidx₁ hki
            · intro hlt
              rw [← hidx_eq'] at hlt
              by_contra hge
              rcases eq_or_lt_of_le (not_lt.mp hge) with rfl | hgt
              · exact hk_ne rfl
              · exact lt_irrefl _ (lt_trans hlt (List.pairwise_iff_getElem.mp hRF₁_pw idx k hidx₁ hk hgt))
          have hc2 : j' = (RF₂.take idx).countP (fun r => decide (r ∈ R₂)) := by
            refine countP_take_lt_of_iff hRF₂_pw hR₂ hsub₂ hidx₂.le (fun k hk hkR => ?_) hj'_le hj'_in
            have hk_ne : k ≠ idx := fun he => hr₂'_nR (he ▸ hkR)
            constructor
            · intro hki
              exact List.pairwise_iff_getElem.mp hRF₂_pw k idx hk hidx₂ hki
            · intro hlt
              by_contra hge
              rcases eq_or_lt_of_le (not_lt.mp hge) with rfl | hgt
              · exact hk_ne rfl
              · exact lt_irrefl _ (lt_trans hlt (List.pairwise_iff_getElem.mp hRF₂_pw idx k hidx₂ hk hgt))
          have htake_idx : (RF₁.take idx).countP (fun r => decide (r ∈ R₁)) = (RF₂.take idx).countP (fun r => decide (r ∈ R₂)) := by
            refine countP_eq_of_forall₂ _ _ (forall₂_of_getElem (by simp [hRF_len]) (fun k hk₁ hk₂ => ?_))
            have hki : k < idx := by
              have : k < (RF₁.take idx).length := hk₁
              rw [List.length_take] at this
              exact (lt_min_iff.mp this).1
            have hk_RF₁ : k < RF₁.length := lt_of_lt_of_le hki hidx₁.le
            have hk_RF₂ : k < RF₂.length := hRF_len ▸ hk_RF₁
            change decide ((RF₁.take idx)[k] ∈ R₁) = decide ((RF₂.take idx)[k] ∈ R₂)
            rw [List.getElem_take, List.getElem_take]
            simpa [decide_eq_true_eq] using (forall₂_getElem hF_mc k hk_RF₁ hk_RF₂).1
          omega
        subst hj'_eq_j₁
        exact hj'_in
      have hr₂_eq : RF₂[idx] = r₂ := (hca₂ j₁ (hST.1 ▸ hj₁_le)).2.2.1 (RF₂[idx]) r₂ hr₂'_in hr₂_spec.1 hr₂'_f hr₂_spec.2
      rcases lt_or_ge idx i with hidx_lt | hidx_ge
      · have hr₁_lt : r₁ < x₁ := by rw [← hidx_eq]; exact hx₁.1 idx hidx₁ hidx_lt
        have hr₂_lt : r₂ < x₂ := by rw [← hr₂_eq]; exact hx₂.1 idx hidx₂ hidx_lt
        have h1 := ((hca₁ j₁ hj₁_le).2.2.2.2 r₁ hr₁_spec.1 hr₁_spec.2 x₁ hj₁_in).2 hr₁_lt
        have h2 := ((hca₂ j₁ (hST.1 ▸ hj₁_le)).2.2.2.2 r₂ hr₂_spec.1 hr₂_spec.2 x₂ hj₂_in).2 hr₂_lt
        exact sameSign_trans h1.2 (sameSign_trans (hR_ss j₁ hj₁_le) (sameSign_symm h2.2))
      · have hx₁_lt : x₁ < r₁ := by rw [← hidx_eq]; exact hx₁.2 idx hidx₁ hidx_ge
        have hx₂_lt : x₂ < r₂ := by rw [← hr₂_eq]; exact hx₂.2 idx hidx₂ hidx_ge
        have h1 := ((hca₁ j₁ hj₁_le).2.2.2.2 r₁ hr₁_spec.1 hr₁_spec.2 x₁ hj₁_in).1 hx₁_lt
        have h2 := ((hca₂ j₁ (hST.1 ▸ hj₁_le)).2.2.2.2 r₂ hr₂_spec.1 hr₂_spec.2 x₂ hj₂_in).1 hx₂_lt
        exact sameSign_trans h1.2 (sameSign_trans (hL_ss j₁ hj₁_le) (sameSign_symm h2.2))
    · have hopt2 : ¬ ∃ r : K₂, inCell R₂ j₁ r ∧ f₂.eval r = 0 := fun h => hopt ((hroot_iff j₁ hj₁_le).mpr h)
      have hnbz := (hca₁ j₁ hj₁_le).1
      by_cases hlv₁ : cellLeftVal f₁ R₁ j₁ = 0
      · have hrv₁ : cellRightVal f₁ R₁ j₁ ≠ 0 := fun h => hnbz ⟨hlv₁, h⟩
        have hrv₂ : cellRightVal f₂ R₂ j₁ ≠ 0 := fun h => hrv₁ ((hR_ss j₁ hj₁_le).2.mpr h)
        have h1 := ((hca₁ j₁ hj₁_le).2.2.2.1 hopt x₁ hj₁_in).2 hrv₁
        have h2 := ((hca₂ j₁ (hST.1 ▸ hj₁_le)).2.2.2.1 hopt2 x₂ hj₂_in).2 hrv₂
        exact sameSign_trans h1 (sameSign_trans (hR_ss j₁ hj₁_le) (sameSign_symm h2))
      · have hlv₂ : cellLeftVal f₂ R₂ j₁ ≠ 0 := fun h => hlv₁ ((hL_ss j₁ hj₁_le).2.mpr h)
        have h1 := ((hca₁ j₁ hj₁_le).2.2.2.1 hopt x₁ hj₁_in).1 hlv₁
        have h2 := ((hca₂ j₁ (hST.1 ▸ hj₁_le)).2.2.2.1 hopt2 x₂ hj₂_in).1 hlv₂
        exact sameSign_trans h1 (sameSign_trans (hL_ss j₁ hj₁_le) (sameSign_symm h2))

end CellRootAnalysis

section MainInduction

lemma signTableMatch_exists {A K₁ K₂ : Type} [CommRing A]
    [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂]
    (hIVT₁ : ∀ (p : Polynomial K₁) {a b : K₁}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₁, a < c ∧ c < b ∧ p.eval c = 0)
    (hIVT₂ : ∀ (p : Polynomial K₂) {a b : K₂}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₂, a < c ∧ c < b ∧ p.eval c = 0)
    (hMVT₁ : ∀ (p : Polynomial K₁) {u v : K₁}, u < v →
      ∃ c : K₁, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c)
    (hMVT₂ : ∀ (p : Polynomial K₂) {u v : K₂}, u < v →
      ∃ c : K₂, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c)
    (hAsymp₁ : ∀ (p : Polynomial K₁), p ≠ 0 →
      ∃ M : K₁, ∀ x : K₁, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))
    (hAsymp₂ : ∀ (p : Polynomial K₂), p ≠ 0 →
      ∃ M : K₂, ∀ x : K₂, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))
    (φ₁ : A →+* K₁) :
    ∀ (d c : ℕ) (P : List (Polynomial A)),
      (∀ p ∈ P, p ≠ 0 ∧ φ₁ p.leadingCoeff ≠ 0) →
      (∀ p ∈ P, p.natDegree ≤ d) →
      P.countP (fun p => decide (p.natDegree = d)) ≤ c →
      ∃ Q : List A, ∀ (φ₂ : A →+* K₂),
        (∀ r ∈ Q, sameSign (φ₁ r) (φ₂ r)) →
        SignTableMatch φ₁ φ₂ P := by
  classical
  intro d
  induction d with
  | zero =>
    intro c P hvalid hdeg _
    refine ⟨P.map Polynomial.leadingCoeff, fun φ₂ hQ => ?_⟩
    have hR₁_nil : rootList (P.map (Polynomial.map φ₁)) = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro x hx
      rw [mem_rootList] at hx
      obtain ⟨pK, hpK, hpK0, hpKx⟩ := hx
      rw [List.mem_map] at hpK
      obtain ⟨p, hpP, rfl⟩ := hpK
      have hp0 : p.natDegree = 0 := Nat.le_zero.mp (hdeg p hpP)
      have hpC : p = Polynomial.C p.leadingCoeff := by
        simpa [Polynomial.leadingCoeff, hp0] using Polynomial.eq_C_of_natDegree_eq_zero hp0
      rw [hpC, Polynomial.map_C, Polynomial.eval_C] at hpKx
      exact (hvalid p hpP).2 hpKx
    have hR₂_nil : rootList (P.map (Polynomial.map φ₂)) = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro x hx
      rw [mem_rootList] at hx
      obtain ⟨pK, hpK, hpK0, hpKx⟩ := hx
      rw [List.mem_map] at hpK
      obtain ⟨p, hpP, rfl⟩ := hpK
      have hp0 : p.natDegree = 0 := Nat.le_zero.mp (hdeg p hpP)
      have hpC : p = Polynomial.C p.leadingCoeff := by
        simpa [Polynomial.leadingCoeff, hp0] using Polynomial.eq_C_of_natDegree_eq_zero hp0
      rw [hpC, Polynomial.map_C, Polynomial.eval_C] at hpKx
      have hss := hQ p.leadingCoeff (List.mem_map_of_mem hpP)
      exact (hvalid p hpP).2 (hss.2.mpr hpKx)
    refine ⟨by simp [hR₁_nil, hR₂_nil], fun i hi₁ => by rw [hR₁_nil] at hi₁; simp at hi₁, ?_⟩
    intro j x₁ x₂ _ _ _ p hpP
    have hp0 : p.natDegree = 0 := Nat.le_zero.mp (hdeg p hpP)
    have hpC : p = Polynomial.C p.leadingCoeff := by
      simpa [Polynomial.leadingCoeff, hp0] using Polynomial.eq_C_of_natDegree_eq_zero hp0
    rw [hpC, Polynomial.map_C, Polynomial.eval_C, Polynomial.map_C, Polynomial.eval_C]
    exact hQ p.leadingCoeff (List.mem_map_of_mem hpP)
  | succ d ih_d =>
    intro c
    induction c with
    | zero =>
      intro P hvalid hdeg hcnt
      have hdeg' : ∀ p ∈ P, p.natDegree ≤ d := by
        intro p hp
        have hle := hdeg p hp
        have hne : p.natDegree ≠ d + 1 := by
          intro heq
          have hpos : 0 < P.countP (fun q => decide (q.natDegree = d + 1)) :=
            List.countP_pos_iff.mpr ⟨p, hp, by simp [heq]⟩
          omega
        omega
      exact ih_d P.length P hvalid hdeg' (List.countP_le_length)
    | succ c ih_c =>
      intro P hvalid hdeg hcnt
      by_cases hle_c : P.countP (fun p => decide (p.natDegree = d + 1)) ≤ c
      · exact ih_c P hvalid hdeg hle_c
      · have hpos_cnt : 0 < P.countP (fun p => decide (p.natDegree = d + 1)) := by omega
        obtain ⟨f, hfP, hfd⟩ := List.countP_pos_iff.mp hpos_cnt
        simp only [decide_eq_true_eq] at hfd
        obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hfP
        set P_rest := L₁ ++ L₂
        have hf_valid := hvalid f (by simp)
        have hderiv_coeff : f.derivative.coeff d = f.leadingCoeff * ((d + 1 : ℕ) : A) := by
          rw [Polynomial.coeff_derivative, Polynomial.leadingCoeff, hfd]
          push_cast
          ring
        have hderiv_phi_coeff : φ₁ (f.derivative.coeff d) ≠ 0 := by
          rw [hderiv_coeff, map_mul, map_natCast]
          exact mul_ne_zero hf_valid.2 (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d))
        have hderiv_le : f.derivative.natDegree ≤ d := by
          have := Polynomial.natDegree_derivative_le f
          omega
        have hderiv_deg : f.derivative.natDegree = d :=
          le_antisymm hderiv_le (Polynomial.le_natDegree_of_ne_zero (fun hc => hderiv_phi_coeff (by simp [hc])))
        have hderiv_ne : f.derivative ≠ 0 := fun h0 => hderiv_phi_coeff (by simp [h0])
        have hderiv_lc : φ₁ f.derivative.leadingCoeff ≠ 0 := by
          rwa [Polynomial.leadingCoeff, hderiv_deg]
        set P₁ := P_rest ++ [f.derivative]
        have hP₁_valid : ∀ g ∈ P₁, g ≠ 0 ∧ φ₁ g.leadingCoeff ≠ 0 := by
          intro g hg
          simp only [P₁, List.mem_append, List.mem_singleton] at hg
          rcases hg with hg | rfl
          · have : g ∈ L₁ ++ f :: L₂ := by
              simp only [P_rest, List.mem_append] at hg
              rcases hg with h1 | h2
              · exact List.mem_append_left _ h1
              · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
            exact hvalid g this
          · exact ⟨hderiv_ne, hderiv_lc⟩
        set P_rem := P₁.map (prem f)
        set sr := stripList φ₁ P_rem
        set P_rem' := sr.1
        set Q_rem := sr.2
        have hsr := stripList_spec (K₂ := K₂) φ₁ P_rem
        set P_sub := P₁ ++ P_rem'
        have hP_rem_deg : ∀ r ∈ P_rem, r.natDegree ≤ d := by
          intro r hr
          rw [List.mem_map] at hr
          obtain ⟨g, hgP₁, rfl⟩ := hr
          rcases prem_deg (f := f) (hP₁_valid g hgP₁).1 with h0 | hlt
          · rw [h0, Polynomial.natDegree_zero]; exact Nat.zero_le d
          · have hg_le : g.natDegree ≤ d + 1 := by
              simp only [P₁, List.mem_append, List.mem_singleton] at hgP₁
              rcases hgP₁ with hg | rfl
              · exact hdeg g (by
                  simp only [P_rest, List.mem_append] at hg
                  rcases hg with h1 | h2
                  · exact List.mem_append_left _ h1
                  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2))
              · omega
            omega
        have hP_rem'_deg : ∀ r ∈ P_rem', r.natDegree ≤ d := hsr.2.1 d hP_rem_deg
        have hP_sub_valid : ∀ p ∈ P_sub, p ≠ 0 ∧ φ₁ p.leadingCoeff ≠ 0 := by
          intro p hp
          simp only [P_sub, List.mem_append] at hp
          rcases hp with hp | hp
          · exact hP₁_valid p hp
          · have := hsr.1 p hp
            exact ⟨this.1, this.2.1⟩
        have hP_sub_deg : ∀ p ∈ P_sub, p.natDegree ≤ d + 1 := by
          intro p hp
          simp only [P_sub, List.mem_append] at hp
          rcases hp with hp | hp
          · simp only [P₁, List.mem_append, List.mem_singleton] at hp
            rcases hp with hp | rfl
            · exact hdeg p (by
                simp only [P_rest, List.mem_append] at hp
                rcases hp with h1 | h2
                · exact List.mem_append_left _ h1
                · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2))
            · omega
          · exact Nat.le_succ_of_le (hP_rem'_deg p hp)
        have hP_sub_cnt : P_sub.countP (fun p => decide (p.natDegree = d + 1)) ≤ c := by
          have hP_rem'_cnt : P_rem'.countP (fun p => decide (p.natDegree = d + 1)) = 0 := by
            rw [List.countP_eq_zero]
            intro p hp
            have := hP_rem'_deg p hp
            simp only [decide_eq_true_eq]
            omega
          have hP_rest_cnt : P_rest.countP (fun p => decide (p.natDegree = d + 1)) ≤ c := by
            have htot : (L₁ ++ f :: L₂).countP (fun p => decide (p.natDegree = d + 1)) =
                P_rest.countP (fun p => decide (p.natDegree = d + 1)) + 1 := by
              simp only [P_rest, List.countP_append, List.countP_cons, hfd, decide_true, ↓reduceIte]
              omega
            omega
          have hP₁_cnt : P₁.countP (fun p => decide (p.natDegree = d + 1)) =
              P_rest.countP (fun p => decide (p.natDegree = d + 1)) := by
            simp only [P₁, List.countP_append, List.countP_cons, List.countP_nil, hderiv_deg]
            simp
          rw [List.countP_append, hP₁_cnt, hP_rem'_cnt, add_zero]
          exact hP_rest_cnt
        obtain ⟨Q_sub, hQ_sub⟩ := ih_c P_sub hP_sub_valid hP_sub_deg hP_sub_cnt
        refine ⟨f.leadingCoeff :: P₁.map Polynomial.leadingCoeff ++ Q_rem ++ Q_sub, fun φ₂ hQ => ?_⟩
        have hQ_sub_ok : ∀ r ∈ Q_sub, sameSign (φ₁ r) (φ₂ r) :=
          fun r hr => hQ r (by simp [hr])
        have hQ_rem_ok : ∀ r ∈ Q_rem, φ₁ r = 0 ↔ φ₂ r = 0 :=
          fun r hr => (hQ r (by simp [hr])).2
        have hST_sub : SignTableMatch φ₁ φ₂ P_sub := hQ_sub φ₂ hQ_sub_ok
        obtain ⟨hST₁, hR₁_extra⟩ := filterSignTable_extra hIVT₁ hIVT₂
          (P := P₁) (P' := P_sub) (fun p hp => List.mem_append_left _ hp) hST_sub
        have hlead_f : sameSign (φ₁ f.leadingCoeff) (φ₂ f.leadingCoeff) := hQ f.leadingCoeff (by simp)
        have hlead_P₁ : ∀ g ∈ P₁, sameSign (φ₁ g.leadingCoeff) (φ₂ g.leadingCoeff) :=
          fun g hg => hQ g.leadingCoeff (by simp [List.mem_map_of_mem hg])
        have hprem_ok : ∀ g ∈ P₁, ∀ (i : ℕ) (h₁ : i < (rootList (P₁.map (Polynomial.map φ₁))).length)
            (h₂ : i < (rootList (P₁.map (Polynomial.map φ₂))).length),
            (g.map φ₁).eval (rootList (P₁.map (Polynomial.map φ₁)))[i] = 0 →
            sameSign (((prem f g).map φ₁).eval (rootList (P₁.map (Polynomial.map φ₁)))[i])
                     (((prem f g).map φ₂).eval (rootList (P₁.map (Polynomial.map φ₂)))[i]) := by
          intro g hg i hi₁ hi₂ _
          have hmem : prem f g ∈ P_rem := List.mem_map_of_mem hg
          rcases hsr.2.2.2 φ₂ hQ_rem_ok (prem f g) hmem with ⟨hz1, hz2⟩ | ⟨r', hr', hm1, hm2⟩
          · rw [hz1, hz2, Polynomial.eval_zero, Polynomial.eval_zero]
            exact sameSign_zero
          · rw [← hm1, ← hm2]
            exact hR₁_extra i hi₁ hi₂ r' (List.mem_append_right _ hr')
        have hST_full : SignTableMatch φ₁ φ₂ (P₁ ++ [f]) :=
          addPolySignTable hIVT₁ hIVT₂ hMVT₁ hMVT₂ hAsymp₁ hAsymp₂
            hf_valid.2 (by simp [P₁]) hP₁_valid hlead_f hlead_P₁ hST₁ hprem_ok
        refine (filterSignTable_extra hIVT₁ hIVT₂ (P := L₁ ++ f :: L₂) (P' := P₁ ++ [f]) ?_ hST_full).1
        intro p hp
        simp only [P₁, P_rest, List.mem_append, List.mem_singleton] at hp ⊢
        rcases hp with hp | hp
        · exact Or.inl (Or.inl (Or.inl hp))
        · rcases List.mem_cons.mp hp with rfl | hp
          · exact Or.inr rfl
          · exact Or.inl (Or.inl (Or.inr hp))

end MainInduction

end Hilbert17H3Proof

theorem OMA.solution : OMA.R_Hilbert17_hilbert_17th_problem_R1_H3_R1.H3 := by
  intro A K₁ K₂ _ _ _ _ _ _ _ hIVT₁ hIVT₂ hMVT₁ hMVT₂ hAsymp₁ hAsymp₂ φ₁ P
  set sr := Hilbert17H3Proof.stripList φ₁ P
  set P' := sr.1
  set Q₀ := sr.2
  have hsr := Hilbert17H3Proof.stripList_spec (K₂ := K₂) φ₁ P
  set d := P'.foldl (fun acc p => max acc p.natDegree) 0
  have hdeg : ∀ p ∈ P', p.natDegree ≤ d := by
    have hfold : ∀ (l : List (Polynomial A)) (init : ℕ),
        (∀ p ∈ l, p.natDegree ≤ l.foldl (fun acc p => max acc p.natDegree) init) ∧
        init ≤ l.foldl (fun acc p => max acc p.natDegree) init := by
      intro l
      induction l with
      | nil => intro init; exact ⟨fun _ h => by simp at h, le_rfl⟩
      | cons a t ih =>
        intro init
        rw [List.foldl_cons]
        obtain ⟨ih1, ih2⟩ := ih (max init a.natDegree)
        refine ⟨fun p hp => ?_, le_trans (le_max_left _ _) ih2⟩
        rcases List.mem_cons.mp hp with rfl | hpt
        · exact le_trans (le_max_right _ _) ih2
        · exact ih1 p hpt
    exact (hfold P' 0).1
  have hvalid : ∀ p ∈ P', p ≠ 0 ∧ φ₁ p.leadingCoeff ≠ 0 :=
    fun p hp => ⟨(hsr.1 p hp).1, (hsr.1 p hp).2.1⟩
  obtain ⟨Q₁, hQ₁⟩ := Hilbert17H3Proof.signTableMatch_exists
    hIVT₁ hIVT₂ hMVT₁ hMVT₂ hAsymp₁ hAsymp₂ φ₁ d P'.length P' hvalid hdeg List.countP_le_length
  refine ⟨Q₀ ++ Q₁, fun φ₂ hQ t₁ => ?_⟩
  have hQ₀_ok : ∀ r ∈ Q₀, φ₁ r = 0 ↔ φ₂ r = 0 :=
    fun r hr => (hQ r (List.mem_append_left _ hr)).2
  have hQ₁_ok : ∀ r ∈ Q₁, Hilbert17H3Proof.sameSign (φ₁ r) (φ₂ r) :=
    fun r hr => hQ r (List.mem_append_right _ hr)
  have hST : Hilbert17H3Proof.SignTableMatch φ₁ φ₂ P' := hQ₁ φ₂ hQ₁_ok
  set R₁ := Hilbert17H3Proof.rootList (P'.map (Polynomial.map φ₁))
  set R₂ := Hilbert17H3Proof.rootList (P'.map (Polynomial.map φ₂))
  have hR₁ : R₁.Pairwise (· < ·) := Hilbert17H3Proof.rootList_pairwise_lt _
  have hR₂ : R₂.Pairwise (· < ·) := Hilbert17H3Proof.rootList_pairwise_lt _
  by_cases ht₁ : t₁ ∈ R₁
  · obtain ⟨i, hi₁, rfl⟩ := List.mem_iff_getElem.mp ht₁
    have hi₂ : i < R₂.length := hST.1 ▸ hi₁
    refine ⟨R₂[i], fun p hp => ?_⟩
    rcases hsr.2.2.2 φ₂ hQ₀_ok p hp with ⟨hz1, hz2⟩ | ⟨p', hp', hm1, hm2⟩
    · rw [hz1, hz2, Polynomial.eval_zero, Polynomial.eval_zero]
      exact ⟨by simp, by simp⟩
    · rw [← hm1, ← hm2]
      exact hST.2.1 i hi₁ hi₂ p' hp'
  · obtain ⟨j, hj₁, hj_in⟩ := Hilbert17H3Proof.exists_inCell_of_not_mem hR₁ ht₁
    have hj₂ : j ≤ R₂.length := hST.1 ▸ hj₁
    obtain ⟨t₂, ht₂⟩ := Hilbert17H3Proof.exists_point_inCell hR₂ hj₂
    refine ⟨t₂, fun p hp => ?_⟩
    rcases hsr.2.2.2 φ₂ hQ₀_ok p hp with ⟨hz1, hz2⟩ | ⟨p', hp', hm1, hm2⟩
    · rw [hz1, hz2, Polynomial.eval_zero, Polynomial.eval_zero]
      exact ⟨by simp, by simp⟩
    · rw [← hm1, ← hm2]
      exact hST.2.2 j t₁ t₂ hj₁ hj_in ht₂ p' hp'

