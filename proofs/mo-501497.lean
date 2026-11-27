import OMAStatements.S_mo_501497
import Mathlib

/-!
For the terminal recurrence, compare to the path starting at one. Its early
states lie between 1 and 1/(1-a), where a is the current coefficient. The ratio
of two updated states is a convex combination of their ratio and its reciprocal.
This contracts relative errors through the early part of the path, sufficiently
to absorb the original fourth-root initial value. Logarithms of benchmark
terminal values are Cauchy. The final update gives the lower bound by AM–GM.
-/
namespace TerminalLimit
noncomputable section

def f (a x : ℝ) := a*x+1/x
def A (c : ℝ) (m : ℕ) := c / Real.sqrt m
def U (a : ℝ) := 1/(1-a)
def near (e x y : ℝ) : Prop := x≤(1+e)*y ∧ y≤(1+e)*x

lemma apos {c : ℝ} (hc : 0<c) {m : ℕ} (hm : 0 < m) : 0<A c m := by
  unfold A
  positivity

lemma antiA {c : ℝ} (hc : 0<c) {m n : ℕ} (hm : 0 < m) (hle : m≤n) : A c n ≤ A c m := by
  apply div_le_div_of_nonneg_left hc.le (by positivity)
  exact Real.sqrt_le_sqrt (by exact_mod_cast hle)

lemma fpos {a x : ℝ} (ha : 0<a) (hx : 0<x) : 0<f a x := by
  unfold f
  positivity

lemma monoU {a b : ℝ} (hab : a≤b) (hb : b<1) : U a≤U b := by
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma oneU {a : ℝ} (ha : 0≤a) (hb : a<1) : 1≤U a := by
  unfold U
  apply (le_div_iff₀ (by linarith)).mpr
  linarith

lemma trap {a y : ℝ} (ha : 0≤a) (hb : a<1) (hy : 1≤y) (hy' : y≤U a) :
    1≤f a y ∧ f a y≤U a := by
  have yp : 0<y := by linarith
  have ap : 0<1-a := by linarith
  have up := (le_div_iff₀ ap).mp hy'
  have one : 1/y ≤ 1 := (div_le_iff₀ yp).mpr (by linarith)
  have low : 1-a ≤ 1/y := (le_div_iff₀ yp).mpr (by nlinarith)
  constructor
  · unfold f
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hy)]
  · apply (le_div_iff₀ ap).mpr
    unfold f
    nlinarith [mul_le_mul_of_nonneg_left up ha, mul_le_mul_of_nonneg_right one ap.le]

private lemma mix {w p q e b : ℝ} (hw : 0≤w) (hw' : w≤1) (he : 0≤e)
    (hb : b≤w) (hb' : b≤1-w) (hp : p≤1+e) (hq : q≤1+e) (h : p≤1 ∨ q≤1) :
    w*p+(1-w)*q ≤ 1+(1-b)*e := by
  rcases h with h|h
  · nlinarith [mul_le_mul_of_nonneg_left h hw,
      mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hw'),mul_nonneg (sub_nonneg.mpr hb) he]
  · nlinarith [mul_le_mul_of_nonneg_left hp hw,
      mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hw'),mul_nonneg (sub_nonneg.mpr hb') he]

lemma contract {a x y e b : ℝ} (ha : 0<a) (hx : 0<x) (hy : 0<y) (he : 0≤e)
    (h : near e x y) (hl : b ≤ a*y^2/(1+a*y^2)) (hr : b ≤ 1-a*y^2/(1+a*y^2)) :
    near ((1-b)*e) (f a x) (f a y) := by
  set w := a*y^2/(1+a*y^2) with hw
  have den : 0<1+a*y^2 := by positivity
  have wp : 0≤w := by dsimp [w]; positivity
  have wle : w≤1 := (div_le_iff₀ den).mpr (by linarith)
  have hp := (div_le_iff₀ hy).mpr h.1
  have hq := (div_le_iff₀ hx).mpr h.2
  have o : x/y≤1 ∨ y/x≤1 := by
    rcases le_total x y with h|h
    · left; exact (div_le_iff₀ hy).mpr (by linarith)
    · right; exact (div_le_iff₀ hx).mpr (by linarith)
  have left := mix wp wle he hl hr hp hq o
  have right := mix wp wle he hl hr hq hp o.symm
  have fx := fpos ha hx
  have fy := fpos ha hy
  have eq : f a x / f a y = w*(x/y)+(1-w)*(y/x) := by
    dsimp [f,w]; field_simp; ring
  have jensen : f a y / f a x ≤ w*(y/x)+(1-w)*(x/y) := by
    apply (div_le_iff₀ fx).mpr
    dsimp [f,w]
    have p : 0<(1+a*y^2)*x^2*y := by positivity
    field_simp
    nlinarith [mul_nonneg ha.le (sq_nonneg (x^2-y^2))]
  exact ⟨(div_le_iff₀ fy).mp (eq.trans_le left),
    (div_le_iff₀ fx).mp (jensen.trans right)⟩

lemma nonexpand {a x y e : ℝ} (ha : 0<a) (hx : 0<x) (hy : 0<y) (he : 0≤e)
    (h : near e x y) : near e (f a x) (f a y) := by
  have D : 0<1+a*y^2 := by positivity
  have upper : a*y^2/(1+a*y^2)≤1 := (div_le_iff₀ D).mpr (by linarith)
  simpa using contract ha hx hy he h (b:=0) (by positivity) (by linarith)

lemma usual {a y : ℝ} (ha : 0<a) (ha' : a≤1/4) (hy : 1≤y) (hy' : y≤U a) :
    a/2 ≤ a*y^2/(1+a*y^2) ∧ a/2 ≤ 1-a*y^2/(1+a*y^2) := by
  have yp : 0<y := by linarith
  have yp2 : 1≤y^2 := by nlinarith [sq_nonneg (y-1)]
  have ht : U a≤2 := (div_le_iff₀ (by linarith : 0<1-a)).mpr (by linarith)
  have y2 : y^2≤4 := by nlinarith [mul_nonneg (show 0≤2+y by linarith) (show 0≤2-y by linarith)]
  have ay : a*y^2≤1 := by nlinarith [mul_le_mul_of_nonneg_left y2 ha.le]
  have den : 0<1+a*y^2 := by positivity
  constructor
  · apply (le_div_iff₀ den).mpr
    nlinarith [mul_le_mul_of_nonneg_left ay ha.le,mul_le_mul_of_nonneg_left yp2 ha.le]
  · have h : a*y^2/(1+a*y^2)≤1/2 := (div_le_iff₀ den).mpr (by linarith)
    linarith

end
end TerminalLimit

namespace TerminalLimit
noncomputable section

def F (c : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | m+1, x => F c m (f (A c (m+1)) x)

lemma Fpos {c : ℝ} (hc : 0<c) (n : ℕ) {x : ℝ} (hx : 0<x) : 0<F c n x := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih => exact ih (fpos (apos hc (by omega)) hx)

lemma stable {c e : ℝ} (hc : 0<c) (he : 0≤e) (n : ℕ) {x y : ℝ}
    (hx : 0<x) (hy : 0<y) (h : near e x y) : near e (F c n x) (F c n y) := by
  induction n generalizing x y with
  | zero => exact h
  | succ n ih =>
    have ha : 0<A c (n+1) := apos hc (by omega)
    exact ih (fpos ha hx) (fpos ha hy) (nonexpand ha hx hy he h)

lemma U_next {c : ℝ} (hc : 0<c) (m k : ℕ) (ha : A c (m+1)≤1/4) :
    U (A c (m+k+2)) ≤ U (A c (m+k+1)) := by
  have le := antiA hc (m:=m+1) (n:=m+k+1) (by omega) (by omega)
  exact monoU (antiA hc (by omega) (by omega)) (by linarith)

lemma bridge {c : ℝ} (hc : 0<c) (m k : ℕ) (ha : A c (m+1)≤1/4)
    {y : ℝ} (hy : 1≤y) (hy' : y≤U (A c (m+k+1))) :
    ∃ z, 1≤z ∧ z≤U (A c (m+1)) ∧ F c (m+k) y = F c m z := by
  induction k generalizing y with
  | zero => exact ⟨y,hy,hy',rfl⟩
  | succ k ih =>
    have p := apos hc (m:=m+k+1) (by omega)
    have le := antiA hc (m:=m+1) (n:=m+k+1) (by omega) (by omega)
    have hz := trap p.le (by linarith) hy (hy'.trans (U_next hc m k ha))
    exact ih hz.1 hz.2

lemma decay {c r : ℝ} (hc : 0<c) (m k : ℕ) (ha : A c (m+1)≤1/4)
    (hr : 0≤r) (hr' : r≤A c (m+k+1)/2)
    {x y e : ℝ} (hx : 0<x) (hy : 1≤y) (hy' : y≤U (A c (m+k+1)))
    (he : 0≤e) (h : near e x y) :
    near ((1-r)^k*e) (F c (m+k) x) (F c (m+k) y) := by
  induction k generalizing x y e with
  | zero => simpa using stable hc he m hx (by linarith) h
  | succ k ih =>
    let a := A c (m+k+1)
    have p : 0<a := apos hc (by omega)
    have le : a ≤ 1/4 := (antiA hc (m:=m+1) (by omega) (by omega)).trans ha
    have ra : r≤a/2 := by
      have := antiA hc (m:=m+k+1) (n:=m+(k+1)+1) (by omega) (by omega)
      dsimp [a]; linarith
    have yU : y≤U a := hy'.trans (U_next hc m k ha)
    have hz := trap p.le (by linarith) hy yU
    have w := usual p le hy yU
    have next := contract p hx (by linarith : 0<y) he h (ra.trans w.1) (ra.trans w.2)
    have ans := ih ra (fpos p hx) hz.1 hz.2
      (mul_nonneg (by linarith : 0≤1-r) he) next
    change near ((1-r)^(k+1)*e) (F c (m+k) (f a x)) (F c (m+k) (f a y))
    simpa only [pow_succ,mul_assoc] using ans

lemma near_log {x y e : ℝ} (hx : 0<x) (hy : 0<y) (h : near e x y) :
    dist (Real.log x) (Real.log y) ≤ e := by
  have hp := (div_le_iff₀ hy).mpr h.1
  have hq := (div_le_iff₀ hx).mpr h.2
  have a := Real.log_le_sub_one_of_pos (div_pos hx hy)
  have b := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hx.ne' hy.ne'] at a
  rw [Real.log_div hy.ne' hx.ne'] at b
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

lemma geometric (k : ℕ) {r : ℝ} (hr : 0≤r) (hr' : r≤1) :
    (1-r)^k ≤ 1/(1+k*r) := by
  apply (le_div_iff₀ (by positivity : 0<1+(k:ℝ)*r)).mpr
  have hb := one_add_mul_le_pow (by linarith : -2≤r) k
  calc (1-r)^k * (1+k*r) ≤ (1-r)^k * (1+r)^k :=
         mul_le_mul_of_nonneg_left hb (pow_nonneg (by linarith) k)
       _ = ((1-r)*(1+r))^k := (mul_pow _ _ _).symm
       _ ≤ 1 := pow_le_one₀ (mul_nonneg (by linarith) (by linarith)) (by nlinarith [sq_nonneg r])

end
end TerminalLimit

namespace TerminalLimit
noncomputable section
open Filter
open scoped Topology

def root4 (n : ℕ) : ℝ := Real.sqrt (Real.sqrt (n+1:ℕ))

lemma root_infty : Tendsto root4 atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))

lemma coef_zero (c : ℝ) : Tendsto (fun n : ℕ => A c (n+1)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))

lemma bench_cauchy {c : ℝ} (hc : 0<c) : CauchySeq (fun n => Real.log (F c n 1)) := by
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  have ev := (coef_zero c).eventually_lt_const (show (0:ℝ) < min (1/4) (ε/3) by positivity)
  obtain ⟨m,hm⟩ := ev.exists
  have small := lt_min_iff.mp hm
  refine ⟨m,?_⟩
  intro n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  have hle := antiA hc (m:=m+1) (n:=m+k+1) (by omega) (by omega)
  have p := apos hc (m:=m+k+1) (by omega)
  obtain ⟨z,hz,hz',eq⟩ := bridge hc m k small.1.le (by norm_num : (1:ℝ)≤1)
    (oneU p.le (by linarith [small.1]))
  have r := apos hc (m:=m+1) (by omega)
  have UU : U (A c (m+1))≤1+2*A c (m+1) := by
    apply (div_le_iff₀ (by linarith [small.1] : 0<1-A c (m+1))).mpr
    nlinarith [mul_nonneg r.le (show 0≤1-2*A c (m+1) by linarith [small.1])]
  have start : near (2*A c (m+1)) z 1 := by
    constructor
    · simpa using hz'.trans UU
    · nlinarith [mul_nonneg r.le (show 0≤z by linarith)]
  have nearEnd := stable hc (by positivity : 0≤2*A c (m+1)) m (by linarith) (by norm_num) start
  rw [eq]
  exact (near_log (Fpos hc _ (by linarith)) (Fpos hc _ (by norm_num)) nearEnd).trans_lt (by linarith [small.2])

lemma rate_bound (c d : ℝ) (hc : 0<c) (hd : 0<d) {m k : ℕ}
    (h : m+1≤2*k) :
    (d*root4 (m+k))/(1+(k:ℝ)*(A c (m+k+1)/2)) ≤
      (6*d/c)/root4 (m+k) := by
  let N : ℝ := ((m+k+1:ℕ):ℝ)
  let s := Real.sqrt N
  let t := Real.sqrt s
  have hN : 0<N := by dsimp [N]; positivity
  have hs : 0<s := Real.sqrt_pos.mpr hN
  have ht : 0<t := Real.sqrt_pos.mpr hs
  have hs2 : s^2=N := Real.sq_sqrt hN.le
  have ht2 : t^2=s := Real.sq_sqrt hs.le
  have hk : N≤3*(k:ℝ) := by
    dsimp [N]; push_cast; exact_mod_cast (by omega : m+k+1≤3*k)
  have ha : 0<c/s := div_pos hc hs
  change d*t/(1+(k:ℝ)*(c/s/2)) ≤ (6*d/c)/t
  have den : 0<1+(k:ℝ)*(c/s/2) := by positivity
  apply (div_le_div_iff₀ den ht).mpr
  field_simp
  rw [ht2]
  have key : s*c*s = c*N := by rw [← hs2]; ring
  nlinarith only [key, mul_le_mul_of_nonneg_left hk hc.le, hs]


lemma actual_close {c d : ℝ} (hc : 0<c) (hd : 0<d) :
    Tendsto (fun n => dist (Real.log (F c n (d*root4 n))) (Real.log (F c n 1))) atTop (𝓝 0) := by
  have small := (coef_zero c).eventually_lt_const (by norm_num : (0:ℝ)<1/4)
  obtain ⟨m,hm⟩ := small.exists
  have large := (root_infty.const_mul_atTop hd).eventually_ge_atTop 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun n => (6*d/c)/root4 n) atTop (𝓝 0) from tendsto_const_nhds.div_atTop root_infty)
    (Eventually.of_forall fun _ => dist_nonneg)
  filter_upwards [large,eventually_ge_atTop (3*m+3)] with n hbig hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (by omega : m≤n)
  let a := A c (m+k+1)
  have ha : 0<a := apos hc (by omega)
  have hu : a ≤ 1/4 := (antiA hc (m:=m+1) (by omega) (by omega)).trans hm.le
  let x := d*root4 (m+k)
  have hx : 1≤x := hbig
  have H : near x x 1 := by constructor <;> nlinarith [sq_nonneg x]
  have D := decay hc m k hm.le (r:=a/2) (by positivity) (le_refl _)
    (x:=x) (y:=1) (by linarith) (by norm_num) (oneU ha.le (by linarith)) (by linarith) H
  have endDist := near_log (Fpos hc _ (by linarith)) (Fpos hc _ (by norm_num)) D
  refine endDist.trans ((mul_le_mul_of_nonneg_right (geometric k (r:=a/2) (by positivity)
    (by linarith)) (show 0≤x by linarith)).trans ?_)
  simpa only [a,x,one_div,div_eq_inv_mul,mul_one] using rate_bound c d hc hd (m:=m) (k:=k) (by omega)

lemma converges {c d : ℝ} (hc : 0<c) (hd : 0<d) :
    ∃ u, Tendsto (fun n => F c n (d*root4 n)) atTop (𝓝 u) := by
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete (bench_cauchy hc)
  have ds : Tendsto (fun n => dist (Real.log (F c n 1)) (Real.log (F c n (d*root4 n)))) atTop (𝓝 0) :=
    (actual_close hc hd).congr (fun n => dist_comm _ _)
  have h := hv.congr_dist ds
  refine ⟨Real.exp v,?_⟩
  have hp (n : ℕ) : 0< F c n (d*root4 n) := Fpos hc _ (by unfold root4; positivity)
  simpa only [Function.comp_def,Real.exp_log (hp _)] using Real.continuous_exp.continuousAt.tendsto.comp h

end
end TerminalLimit

namespace TerminalLimit
noncomputable section
open Filter
open scoped Topology
open OMA.S_mo_501497

private lemma agree (c : ℝ) (n : ℕ) (x : ℝ) : F c n x = finish c n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [F, finish, ih, f, A, Nat.cast_add, Nat.cast_one]

private lemma lower {c : ℝ} (hc : 0<c) (n : ℕ) (x : ℝ) (hx : 0<x) :
    2*Real.sqrt c ≤ F c (n+1) x := by
  induction n generalizing x with
  | zero =>
    change 2*Real.sqrt c ≤ f (A c 1) x
    simp only [f,A,Nat.cast_one,Real.sqrt_one,div_one]
    have eq : (Real.sqrt c*x)^2 = c*x^2 := by rw [mul_pow,Real.sq_sqrt hc.le]
    apply (le_of_mul_le_mul_right (a:=x) _ hx)
    field_simp
    nlinarith [sq_nonneg (Real.sqrt c*x-1)]
  | succ n ih => exact ih _ (fpos (apos hc (by omega)) hx)

theorem result (R L : ℝ) (hR : 0<R) (hL : 0<L) :
    ∃ u : ℝ, 2 * Real.sqrt (R/L) ≤ u ∧ Tendsto (terminal R L) atTop (𝓝 u) := by
  let c := R/L
  let d := Real.sqrt (L/R)/2
  have hc : 0<c := div_pos hR hL
  have hd : 0<d := by dsimp [d]; positivity
  obtain ⟨u,H⟩ := converges hc hd
  have shifted (n : ℕ) : terminal R L (n+1) = F c n (d*root4 n) := by
    simp only [terminal,Nat.add_sub_cancel,agree,root4,c,d]
  have hu : Tendsto (terminal R L) atTop (𝓝 u) := (tendsto_add_atTop_iff_nat 1).mp (by
    simpa only [shifted] using H)
  refine ⟨u,ge_of_tendsto H ?_,hu⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  exact lower hc _ _ (by unfold root4; positivity)

end
end TerminalLimit

theorem OMA.solution : type_of% @OMA.S_mo_501497.main := TerminalLimit.result
