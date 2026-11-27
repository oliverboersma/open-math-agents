import OMAStatements.S_mo_202165
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Proof of transitivity of balanced mass transport on the integer line
Source: https://mathoverflow.net/q/202165 (James Propp, 2015).
Credit: @LDJAI with OpenAI Codex.
-/

namespace OMA.S_mo_202165
open Finset
noncomputable section

/-- Weight each complete row before reading out the resulting column. -/
def pick {r : ℤ} {p : Profile} (P : Rows r p) (f : ℤ → ℝ) (x : ℤ) : ℝ :=
  ∑ i ∈ Icc (x-r) x, f i * P.val i x

def gate (t i : ℤ) : ℝ := if i ≤ t then 1 else 0

def pref {r : ℤ} {p : Profile} (P : Rows r p) (t : ℤ) : Profile :=
  pick P (gate t)

theorem pick_full {r : ℤ} {p : Profile} (P : Rows r p) (f : ℤ → ℝ) (x : ℤ)
    (hf : ∀ i ∈ Icc (x-r) x, f i = 1) : pick P f x = p x := by
  rw [← P.col x]
  exact sum_congr rfl fun i hi => by rw [hf i hi, one_mul]

theorem pick_empty {r : ℤ} {p : Profile} (P : Rows r p) (f : ℤ → ℝ) (x : ℤ)
    (hf : ∀ i ∈ Icc (x-r) x, f i = 0) : pick P f x = 0 :=
  sum_eq_zero fun i hi => by rw [hf i hi, zero_mul]

theorem pick_mono {r : ℤ} {p : Profile} (P : Rows r p) {f g : ℤ → ℝ}
    (hf : ∀ i, f i ≤ g i) (x : ℤ) : pick P f x ≤ pick P g x :=
  sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hf i) (P.pos i x)

theorem pick_sub {r : ℤ} {p : Profile} (P : Rows r p) (f g : ℤ → ℝ) (x : ℤ) :
    pick P (fun i => f i - g i) x = pick P f x - pick P g x := by
  simp only [pick, sub_mul, sum_sub_distrib]

theorem pref_full {r : ℤ} {p : Profile} (P : Rows r p) {t x : ℤ} (hx : x ≤ t) :
    pref P t x = p x := pick_full P _ x fun i hi => by
  have := (mem_Icc.mp hi).2
  simp [gate, show i ≤ t by omega]

theorem pref_empty {r : ℤ} {p : Profile} (P : Rows r p) {t x : ℤ} (hx : t+r < x) :
    pref P t x = 0 := pick_empty P _ x fun i hi => by
  have := (mem_Icc.mp hi).1
  simp [gate, show ¬ i ≤ t by omega]

theorem pref_bounds {r : ℤ} {p : Profile} (P : Rows r p) (t x : ℤ) :
    0 ≤ pref P t x ∧ pref P t x ≤ p x := by
  constructor
  · unfold pref pick
    apply sum_nonneg
    exact fun i _ => mul_nonneg (by unfold gate; split <;> norm_num) (P.pos i x)
  · rw [← P.col x]
    unfold pref pick
    apply sum_le_sum
    intro i _
    simpa using mul_le_mul_of_nonneg_right (show gate t i ≤ 1 by
      unfold gate; split <;> norm_num) (P.pos i x)

/-- The sum of a summand supported in both finite sets can be read over either one. -/
theorem same_sum (S T : Finset ℤ) (f : ℤ → ℝ)
    (hs : ∀ x ∈ S, x ∉ T → f x = 0) (ht : ∀ x ∈ T, x ∉ S → f x = 0) :
    ∑ x ∈ S, f x = ∑ x ∈ T, f x := by
  classical
  have eS : ∑ x ∈ S ∩ T, f x = ∑ x ∈ S, f x := by
    apply sum_subset inter_subset_left
    intro x h h'
    apply hs x h
    exact fun hT => h' (mem_inter.mpr ⟨h,hT⟩)
  have eT : ∑ x ∈ S ∩ T, f x = ∑ x ∈ T, f x := by
    apply sum_subset inter_subset_right
    intro x h h'
    apply ht x h
    exact fun hS => h' (mem_inter.mpr ⟨hS,h⟩)
  exact eS.symm.trans eT

theorem tally_sub (l u : ℤ) (q : Bool) (f g : Profile) :
    tally l u q (fun x => f x - g x) = tally l u q f - tally l u q g := by
  simp only [tally, mul_sub, sum_sub_distrib]

theorem tally_extend (l u l' u' : ℤ) (q : Bool) (f : Profile)
    (hl : l' ≤ l) (hu : u ≤ u') (hf : ∀ x, f x ≠ 0 → l ≤ x ∧ x ≤ u) :
    tally l' u' q f = tally l u q f := by
  apply same_sum
  · intro x _ hx
    have hfx : f x = 0 := by
      by_contra hn
      exact hx (mem_Icc.mpr (hf x hn))
    simp [hfx]
  · intro x hx hn
    obtain ⟨a,b⟩ := mem_Icc.mp hx
    exact False.elim (hn (mem_Icc.mpr ⟨by omega,by omega⟩))

theorem tally_pick {r : ℤ} {p : Profile} (P : Rows r p) (l v u : ℤ) (q : Bool)
    (f : ℤ → ℝ) (hf : ∀ i, f i ≠ 0 → l ≤ i ∧ i ≤ v) (hu : v+r ≤ u) :
    tally l u q (pick P f) = ∑ i ∈ Icc l v, f i * tally i (i+r) q (P.val i) := by
  have swap (x : ℤ) : pick P f x = ∑ i ∈ Icc l v, f i * P.val i x := by
    apply same_sum
    · intro i _ hn
      by_cases e : f i = 0
      · simp [e]
      · exact False.elim (hn (mem_Icc.mpr (hf i e)))
    · intro i _ hn
      by_cases e : P.val i x = 0
      · simp [e]
      · obtain ⟨a,b⟩ := P.loc i x e
        exact False.elim (hn (mem_Icc.mpr ⟨by omega,by omega⟩))
  unfold tally
  simp_rw [swap, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  obtain ⟨il,iv⟩ := mem_Icc.mp hi
  have extn := tally_extend i (i+r) l u q (P.val i) il (by omega) (P.loc i)
  rw [← mul_sum]
  change _ = f i * tally i (i+r) q (P.val i)
  rw [← extn]
  unfold tally
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  ring

end
end OMA.S_mo_202165

namespace OMA.S_mo_202165
open Finset
noncomputable section

structure Blend where
  a : ℝ
  b : ℝ
  d : ℝ
  ha : 0 ≤ a
  hb : 0 ≤ b
  hd : 0 ≤ d
  total : a+b+d=1

def Blend.mix (w : Blend) (x y z : ℝ) : ℝ := w.a*x + w.b*y + w.d*z

theorem Blend.bounds (w : Blend) {x y z : ℝ} (hx : 0 ≤ x ∧ x ≤ 1)
    (hy : 0 ≤ y ∧ y ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    0 ≤ w.mix x y z ∧ w.mix x y z ≤ 1 := by
  unfold Blend.mix
  have a := mul_le_mul_of_nonneg_left hx.2 w.ha
  have b := mul_le_mul_of_nonneg_left hy.2 w.hb
  have d := mul_le_mul_of_nonneg_left hz.2 w.hd
  constructor
  · exact add_nonneg (add_nonneg (mul_nonneg w.ha hx.1) (mul_nonneg w.hb hy.1)) (mul_nonneg w.hd hz.1)
  · linarith [w.total]

/-- Moment bounds for nonnegative mass lying in a given strip. -/
theorem strip_moments (l u a b : ℤ) (f : Profile) (hp : ∀ x, 0 ≤ f x)
    (hl : ∀ x, f x ≠ 0 → a ≤ x ∧ x ≤ b) :
    0 ≤ tally l u false f ∧
    (a:ℝ)*tally l u false f ≤ tally l u true f ∧
    tally l u true f ≤ (b:ℝ)*tally l u false f := by
  simp only [tally, moment, Bool.false_eq_true, if_false, one_mul, if_true, mul_sum]
  refine ⟨sum_nonneg fun x _ => hp x, sum_le_sum ?_, sum_le_sum ?_⟩
  · intro x _
    by_cases he : f x = 0
    · simp [he]
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast (hl x he).1) (hp x)
  · intro x _
    by_cases he : f x = 0
    · simp [he]
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast (hl x he).2) (hp x)

theorem det_pos {m n a b v w : ℝ} (hm : 0<m) (hn : 0<n) (hv : v ≤ a*m)
    (hw : b*n ≤ w) (hab : a<b) : 0 < m*w - n*v := by
  have t : v/m < w/n :=
    lt_of_le_of_lt ((div_le_iff₀ hm).mpr hv) (lt_of_lt_of_le hab ((le_div_iff₀ hn).mpr hw))
  have e := (div_lt_div_iff₀ hm hn).mp t
  linarith

/-- The signed minors of the two-by-three moment matrix give convex cut weights. -/
theorem ordered_blend {m n k v w z a b c d e f : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hk : 0 ≤ k)
    (hv : a*m ≤ v ∧ v ≤ b*m) (hw : c*n ≤ w ∧ w ≤ d*n)
    (hz : e*k ≤ z ∧ z ≤ f*k) (hbc : b<c) (hde : d<e) (hbe : b<e) :
    ∃ W : Blend, W.mix m (-n) k = 0 ∧ W.mix v (-w) z = 0 := by
  by_cases hm0 : m=0
  · have ev : v=0 := le_antisymm (by simpa [hm0] using hv.2) (by simpa [hm0] using hv.1)
    exact ⟨⟨1,0,0,by norm_num,by norm_num,by norm_num,by norm_num⟩,
      by simp [Blend.mix,hm0],by simp [Blend.mix,ev]⟩
  by_cases hn0 : n=0
  · have ew : w=0 := by simpa [hn0] using le_antisymm (show w ≤ 0 by simpa [hn0] using hw.2)
                                              (show 0 ≤ w by simpa [hn0] using hw.1)
    exact ⟨⟨0,1,0,by norm_num,by norm_num,by norm_num,by norm_num⟩,
      by simp [Blend.mix,hn0],by simp [Blend.mix,ew]⟩
  by_cases hk0 : k=0
  · have ez : z=0 := le_antisymm (by simpa [hk0] using hz.2) (by simpa [hk0] using hz.1)
    exact ⟨⟨0,0,1,by norm_num,by norm_num,by norm_num,by norm_num⟩,
      by simp [Blend.mix,hk0],by simp [Blend.mix,ez]⟩
  have pm := lt_of_le_of_ne hm (Ne.symm hm0)
  have pn := lt_of_le_of_ne hn (Ne.symm hn0)
  have pk := lt_of_le_of_ne hk (Ne.symm hk0)
  let A := n*z-k*w
  let B := m*z-k*v
  let D := m*w-n*v
  have pA : 0<A := det_pos pn pk hw.2 hz.1 hde
  have pB : 0<B := det_pos pm pk hv.2 hz.1 hbe
  have pD : 0<D := det_pos pm pn hv.2 hw.1 hbc
  let T := A+B+D
  have pt : 0<T := add_pos (add_pos pA pB) pD
  refine ⟨⟨A/T,B/T,D/T, (div_pos pA pt).le, (div_pos pB pt).le, (div_pos pD pt).le, ?_⟩, ?_, ?_⟩
  · rw [← add_div, ← add_div, div_self pt.ne']
  · change A/T*m+B/T*(-n)+D/T*k=0
    field_simp [pt.ne']
    dsimp [A,B,D]
    ring
  · change A/T*v+B/T*(-w)+D/T*z=0
    field_simp [pt.ne']
    dsimp [A,B,D]
    ring

end
end OMA.S_mo_202165

namespace OMA.S_mo_202165
open Finset
noncomputable section

def gap {r s : ℤ} {p : Profile} (P : Rows r p) (Q : Rows s p) (t h : ℤ) : Profile :=
  fun x => pref P (t+h) x - pref Q t x

theorem gap_pos {r s : ℤ} {p : Profile} (P : Rows r p) (Q : Rows s p) {t h : ℤ}
    (hs : s<h) (x : ℤ) : 0 ≤ gap P Q t h x := by
  unfold gap
  by_cases hx : x ≤ t+h
  · rw [pref_full P hx]
    exact sub_nonneg.mpr (pref_bounds Q t x).2
  · rw [pref_empty Q (by omega), sub_zero]
    exact (pref_bounds P (t+h) x).1

theorem gap_loc {r s : ℤ} {p : Profile} (P : Rows r p) (Q : Rows s p) {t h : ℤ}
    (hh : 0<h) (hr : r<h) (hs : s<h) (x : ℤ) (hx : gap P Q t h x ≠ 0) :
    t+1 ≤ x ∧ x ≤ t+2*h-1 := by
  unfold gap at hx
  constructor
  · by_contra hn
    rw [pref_full P (by omega),pref_full Q (by omega),sub_self] at hx
    contradiction
  · by_contra hn
    rw [pref_empty P (by omega),pref_empty Q (by omega),sub_self] at hx
    contradiction

/-- Left and right thresholds alternate which family extends farther into the strip. -/
def mask (w : Blend) (side : Bool) (c h i : ℤ) : ℝ :=
  if side then w.mix (gate (c+h) i) (gate (c+2*h) i) (gate (c+4*h+h) i)
  else w.mix (gate c i) (gate (c+2*h+h) i) (gate (c+4*h) i)

def border {r s : ℤ} {p : Profile} (P : Rows r p) (Q : Rows s p)
    (w : Blend) (c h : ℤ) : Profile :=
  fun x => pick P (mask w true c h) x - pick Q (mask w false c h) x

theorem gate_bounds (t i : ℤ) : 0 ≤ gate t i ∧ gate t i ≤ 1 := by
  unfold gate; split <;> norm_num

theorem mask_bounds (w : Blend) (side : Bool) (c h i : ℤ) :
    0 ≤ mask w side c h i ∧ mask w side c h i ≤ 1 := by
  cases side <;> exact w.bounds (gate_bounds _ _) (gate_bounds _ _) (gate_bounds _ _)

theorem mask_full (w : Blend) (side : Bool) {c h i : ℤ} (hh : 0<h) (hi : i≤c) :
    mask w side c h i = 1 := by
  cases side <;> simp [mask,gate,Blend.mix,hi, show i≤c+h by omega, show i≤c+2*h by omega,
    show i≤c+4*h+h by omega, show i≤c+2*h+h by omega, show i≤c+4*h by omega,w.total]

theorem mask_empty (w : Blend) (side : Bool) {c h i : ℤ} (hh : 0<h) (hi : c+5*h<i) :
    mask w side c h i = 0 := by
  cases side <;> simp [mask,gate,Blend.mix, show ¬i≤c by omega,show ¬i≤c+h by omega,
    show ¬i≤c+2*h by omega,show ¬i≤c+4*h+h by omega,show ¬i≤c+2*h+h by omega,
    show ¬i≤c+4*h by omega]

theorem cut_full {r : ℤ} {p : Profile} (P : Rows r p) (w : Blend) (side : Bool)
    {c h x : ℤ} (hh : 0<h) (hx : x≤c) : pick P (mask w side c h) x = p x :=
  pick_full P _ x fun _i hi => mask_full w side hh (le_trans (mem_Icc.mp hi).2 hx)

theorem cut_empty {r : ℤ} {p : Profile} (P : Rows r p) (w : Blend) (side : Bool)
    {c h x : ℤ} (hh : 0<h) (hr : r<h) (hx : c+6*h≤x) :
    pick P (mask w side c h) x = 0 := by
  apply pick_empty
  intro i hi
  have il := (mem_Icc.mp hi).1
  exact mask_empty w side hh (by omega)

theorem border_loc {r s : ℤ} {p : Profile} (P : Rows r p) (Q : Rows s p)
    (w : Blend) {c h : ℤ} (hh : 0<h) (hr : r<h) (hs : s<h) (x : ℤ)
    (hx : border P Q w c h x ≠ 0) : c ≤ x ∧ x ≤ c+6*h := by
  unfold border at hx
  constructor
  · by_contra hn
    rw [cut_full P w true hh (by omega),cut_full Q w false hh (by omega), sub_self] at hx
    contradiction
  · by_contra hn
    rw [cut_empty P w true hh hr (by omega),cut_empty Q w false hh hs (by omega),sub_self] at hx
    contradiction

theorem pick_mix {r : ℤ} {p : Profile} (P : Rows r p) (w : Blend) (f g k : ℤ → ℝ) (x : ℤ) :
    pick P (fun i => w.mix (f i) (g i) (k i)) x =
    w.mix (pick P f x) (pick P g x) (pick P k x) := by
  simp only [pick,Blend.mix,add_mul,sum_add_distrib,mul_assoc,mul_sum]

theorem tally_mix (l u : ℤ) (q : Bool) (w : Blend) (f g k : Profile) :
    tally l u q (fun x => w.mix (f x) (-(g x)) (k x)) =
    w.mix (tally l u q f) (-(tally l u q g)) (tally l u q k) := by
  simp only [tally,Blend.mix,mul_add,mul_neg,sum_add_distrib,sum_neg_distrib,mul_sum]
  have term (a : ℝ) (b : Profile) :
      (∑ x ∈ Icc l u, moment q x * (a * b x)) = ∑ x ∈ Icc l u, a * (moment q x * b x) :=
    sum_congr rfl fun _ _ => by ring
  rw [term,term,term]

theorem border_gaps {r s : ℤ} {p : Profile} (P : Rows r p) (Q : Rows s p)
    (w : Blend) (c h : ℤ) :
    border P Q w c h = fun x => w.mix (gap P Q c h x) (-(gap Q P (c+2*h) h x))
      (gap P Q (c+4*h) h x) := by
  funext x
  change pick P (fun i => w.mix (gate (c+h) i) (gate (c+2*h) i) (gate (c+4*h+h) i)) x -
    pick Q (fun i => w.mix (gate c i) (gate (c+2*h+h) i) (gate (c+4*h) i)) x = _
  rw [pick_mix,pick_mix]
  simp only [gap,pref,Blend.mix]
  ring

theorem exists_cut {r s : ℤ} {p : Profile} (P : Rows r p) (Q : Rows s p)
    (c h : ℤ) (hh : 0<h) (hr : r<h) (hs : s<h) :
    ∃ w : Blend, ∀ q, tally c (c+6*h) q (border P Q w c h) = 0 := by
  let T := tally c (c+6*h)
  let F := gap P Q c h
  let G := gap Q P (c+2*h) h
  let H := gap P Q (c+4*h) h
  obtain ⟨pF,lF,uF⟩ := strip_moments c (c+6*h) _ _ F (gap_pos P Q hs) (gap_loc P Q hh hr hs)
  obtain ⟨pG,lG,uG⟩ := strip_moments c (c+6*h) _ _ G (gap_pos Q P hr) (gap_loc Q P hh hs hr)
  obtain ⟨pH,lH,uH⟩ := strip_moments c (c+6*h) _ _ H (gap_pos P Q hs) (gap_loc P Q hh hr hs)
  obtain ⟨w,mass,first⟩ := ordered_blend pF pG pH ⟨lF,uF⟩ ⟨lG,uG⟩ ⟨lH,uH⟩
    (by exact_mod_cast (show c+2*h-1 < c+2*h+1 by omega))
    (by exact_mod_cast (show c+2*h+2*h-1 < c+4*h+1 by omega))
    (by exact_mod_cast (show c+2*h-1 < c+4*h+1 by omega))
  refine ⟨w, fun q => ?_⟩
  rw [border_gaps,tally_mix]
  cases q
  · exact mass
  · exact first

end
end OMA.S_mo_202165

namespace OMA.S_mo_202165
open Finset
noncomputable section

theorem sum_translate (a b d : ℤ) (f : ℤ → ℝ) :
    ∑ k ∈ Icc a b, f (k+d) = ∑ k ∈ Icc (a+d) (b+d), f k := by
  apply sum_bij' (fun i _ => i+d) (fun i _ => i-d)
  · intro i hi
    obtain ⟨_,_⟩ := mem_Icc.mp hi
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro i hi
    obtain ⟨_,_⟩ := mem_Icc.mp hi
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intros; omega
  · intros; omega
  · intros; rfl

theorem sum_split (a b d : ℤ) (f : ℤ → ℝ) (h₁ : a≤b) (h₂ : b≤d) :
    ∑ k ∈ Icc a d, f k = (∑ k ∈ Icc a b, f k) + ∑ k ∈ Icc (b+1) d, f k := by
  have e : Icc a d = Icc a b ∪ Icc (b+1) d := by
    ext x; simp only [mem_union,mem_Icc]; omega
  rw [e,sum_union]
  apply disjoint_left.mpr
  intro x hx hx'
  obtain ⟨_,_⟩ := mem_Icc.mp hx
  obtain ⟨_,_⟩ := mem_Icc.mp hx'
  omega

/-- Averaging the L translated block decompositions avoids a choice of grid origin. -/
theorem boundary_sum (x L : ℤ) (hL : 0<L) (m : ℝ) (f : ℤ → ℝ)
    (zero : ∀ c, c≤x-L → f c=0) (full : ∀ c, x≤c → f c=m) :
    ∑ c ∈ Icc (x-2*L) x, (f (c+L) - f c) = (L:ℝ)*m := by
  rw [sum_sub_distrib,sum_translate]
  rw [show x-2*L+L=x-L by omega]
  rw [sum_split (x-L) x (x+L) f (by omega) (by omega)]
  have low : ∑ i ∈ Icc (x-2*L) (x-L-1), f i = 0 :=
    sum_eq_zero fun i hi => zero i (by have := (mem_Icc.mp hi).2; omega)
  rw [sum_split (x-2*L) (x-L-1) x f (by omega) (by omega),low,zero_add]
  rw [show x-L-1+1=x-L by omega]
  have high : (∑ i ∈ Icc (x+1) (x+L), f i) = (L:ℝ)*m := by
    calc
      _ = ∑ i ∈ Icc (x+1) (x+L), m :=
        sum_congr rfl fun i hi => full i (by have := (mem_Icc.mp hi).1; omega)
      _ = _ := by
        rw [sum_const,nsmul_eq_mul,Int.card_Icc]
        congr 1
        norm_cast
        omega
  rw [high]
  ring

end
end OMA.S_mo_202165

namespace OMA.S_mo_202165
open Finset
noncomputable section

/-- The row weights in the difference between two consecutive mixed prefixes. -/
def delta (W : ℤ → Blend) (side : Bool) (c h i : ℤ) : ℝ :=
  mask (W (c+6*h)) side (c+6*h) h i - mask (W c) side c h i

theorem delta_pos (W : ℤ → Blend) (side : Bool) {c h : ℤ} (hh : 0<h) (i : ℤ) :
    0 ≤ delta W side c h i := by
  unfold delta
  by_cases hi : i ≤ c+6*h
  · rw [mask_full _ side hh hi]
    exact sub_nonneg.mpr (mask_bounds _ side _ _ _).2
  · rw [mask_empty (W c) side hh (by omega),sub_zero]
    exact (mask_bounds _ side _ _ _).1

theorem delta_loc (W : ℤ → Blend) (side : Bool) {c h : ℤ} (hh : 0<h) (i : ℤ)
    (hi : delta W side c h i ≠ 0) : c ≤ i ∧ i ≤ c+11*h := by
  unfold delta at hi
  constructor
  · by_contra hn
    rw [mask_full _ side hh (by omega), mask_full _ side hh (by omega), sub_self] at hi
    contradiction
  · by_contra hn
    rw [mask_empty _ side hh (by omega),mask_empty _ side hh (by omega),sub_self] at hi
    contradiction

def layer {r : ℤ} {p : Profile} (P : Rows r p) (W : ℤ → Blend) (side : Bool) (c h : ℤ) :
    Profile := pick P (delta W side c h)

theorem layer_eq {r : ℤ} {p : Profile} (P : Rows r p) (W : ℤ → Blend) (side : Bool) (c h x : ℤ) :
    layer P W side c h x =
    pick P (mask (W (c+6*h)) side (c+6*h) h) x - pick P (mask (W c) side c h) x :=
  pick_sub P _ _ x

theorem layer_transfer {r : ℤ} {p q : Profile} (A : Rows r p) (B : Rows r q)
    (bal : ∀ i j, tally i (i+r) j (A.val i) = tally i (i+r) j (B.val i))
    (W : ℤ → Blend) (side : Bool) (c h : ℤ) (j : Bool) (hh : 0<h) (hr : r<h) :
    tally c (c+12*h) j (layer A W side c h) = tally c (c+12*h) j (layer B W side c h) := by
  unfold layer
  rw [tally_pick A c (c+11*h) (c+12*h) j _ (delta_loc W side hh) (by omega),
    tally_pick B c (c+11*h) (c+12*h) j _ (delta_loc W side hh) (by omega)]
  exact sum_congr rfl fun i _ => by rw [bal i j]

theorem layer_bridge {r s : ℤ} {p : Profile} (B : Rows r p) (C : Rows s p)
    (W : ℤ → Blend) (h : ℤ) (hh : 0<h) (hr : r<h) (hs : s<h)
    (good : ∀ c j, tally c (c+6*h) j (border B C (W c) c h) = 0)
    (c : ℤ) (j : Bool) :
    tally c (c+12*h) j (layer B W true c h) = tally c (c+12*h) j (layer C W false c h) := by
  have zero (k : ℤ) (lo : c≤k) (hi : k+6*h≤c+12*h) :
      tally c (c+12*h) j (border B C (W k) k h) = 0 :=
    (tally_extend k (k+6*h) c (c+12*h) j _ lo hi (border_loc B C _ hh hr hs)).trans (good k j)
  have ends : (fun x => layer B W true c h x - layer C W false c h x) =
      fun x => border B C (W (c+6*h)) (c+6*h) h x - border B C (W c) c h x := by
    funext x
    rw [layer_eq,layer_eq]
    unfold border
    ring
  apply sub_eq_zero.mp
  rw [← tally_sub,ends,tally_sub,zero (c+6*h) (by omega) (by omega),zero c (by omega) (by omega),sub_zero]

theorem tally_scale (l u : ℤ) (j : Bool) (f : Profile) (v : ℝ) :
    tally l u j (fun x => f x / v) = tally l u j f / v := by
  simp only [tally, div_eq_mul_inv,← mul_assoc,sum_mul]

/-- Use all integer translates of the length-6h grid and divide by the number of translates. -/
def packets {r : ℤ} {p : Profile} (P : Rows r p) (W : ℤ → Blend) (side : Bool)
    (h : ℤ) (hh : 0<h) (hr : r<h) : Rows (12*h) p where
  val c x := layer P W side c h x / (↑(6*h) : ℝ)
  pos c x := by
    apply div_nonneg _ (by exact_mod_cast (show (0:ℤ)≤6*h by omega))
    unfold layer pick
    exact sum_nonneg fun i _ => mul_nonneg (delta_pos W side hh i) (P.pos i x)
  loc c x hn := by
    have hz (e : layer P W side c h x = 0) : False := hn (by simp [e])
    constructor
    · by_contra hx
      apply hz
      rw [layer_eq,cut_full P _ side hh (by omega),cut_full P _ side hh (by omega),sub_self]
    · by_contra hx
      apply hz
      rw [layer_eq,cut_empty P _ side hh hr (by omega),cut_empty P _ side hh hr (by omega),sub_self]
  col x := by
    let L := 6*h
    have hL : 0<L := by dsimp [L]; omega
    have ec : x - 12*h = x-2*L := by dsimp [L]; omega
    let f : ℤ → ℝ := fun k => pick P (mask (W k) side k h) x
    have sz := boundary_sum x L hL (p x) f
      (fun k hk => cut_empty P _ side hh hr (by dsimp [L] at hk; omega))
      (fun k hk => cut_full P _ side hh hk)
    simp only [div_eq_mul_inv,← sum_mul,ec]
    have ev : (∑ i ∈ Icc (x-2*L) x, layer P W side i h x) = (L:ℝ) * p x := by
      calc
        _ = ∑ i ∈ Icc (x-2*L) x, (f (i+L)-f i) := sum_congr rfl fun i _ => layer_eq P W side i h x
        _ = _ := sz
    rw [ev]
    change (L:ℝ) * p x / (L:ℝ) = p x
    exact mul_div_cancel_left₀ _ (by exact_mod_cast hL.ne')

/-- Quantitative composition for given input diameters. -/
theorem compose_rows {p q s : Profile} {r t : ℤ} (hr : 0≤r) (ht : 0≤t)
    (A : Rows r p) (B : Rows r q) (C : Rows t q) (D : Rows t s)
    (hAB : ∀ i j, tally i (i+r) j (A.val i) = tally i (i+r) j (B.val i))
    (hCD : ∀ i j, tally i (i+t) j (C.val i) = tally i (i+t) j (D.val i)) :
    ∃ (U : Rows (12*(max r t + 1)) p) (V : Rows (12*(max r t + 1)) s), ∀ i j,
      tally i (i+12*(max r t + 1)) j (U.val i) = tally i (i+12*(max r t + 1)) j (V.val i) := by
  let h := max r t + 1
  have hh : 0<h := by dsimp [h]; omega
  have rh : r<h := by dsimp [h]; omega
  have th : t<h := by dsimp [h]; omega
  choose W good using fun c => exists_cut B C c h hh rh th
  refine ⟨packets A W true h hh rh,packets D W false h hh th, fun c j => ?_⟩
  change tally c (c+12*h) j (fun x => layer A W true c h x / _) =
    tally c (c+12*h) j (fun x => layer D W false c h x / _)
  rw [tally_scale,tally_scale,layer_transfer A B hAB W true c h j hh rh,
    layer_bridge B C W h hh rh th good c j,layer_transfer C D hCD W false c h j hh th]

end
end OMA.S_mo_202165

open OMA.S_mo_202165 in
theorem OMA.solution : type_of% @OMA.S_mo_202165.main := by
  rintro p q s ⟨r,hr,A,B,hAB⟩ ⟨t,ht,C,D,hCD⟩
  exact ⟨12*(max r t + 1), by omega, compose_rows hr ht A B C D hAB hCD⟩
