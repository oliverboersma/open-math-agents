import FormalConjectures.ErdosProblems.«829»

/-! # Stewart's lower bound for natural sums of two cubes

C. L. Stewart, *Cubic Thue equations with many solutions* (IMRN, 2008),
and N. D. Elkies and N. F. Rogers, *Elliptic curves x³+y³=k of high rank*,
arXiv:math/0403116, §5, supply the rank-eleven construction. We use
the eleven points listed on p. 10 of Elkies–Rogers, on the integral short
model Y²=X³+16k² with k=13293998056584952174157235.

Each point satisfies the curve equation. Eleven explicit good reductions
give a nonsingular parity matrix; together with absence of rational
two-torsion this proves independence. Balanced projective addition bounds
the coordinate heights in a whole N-by-…-by-N box. An explicit degree-three
map and a cover by rational translates retain a positive proportion of
distinct representations with NONNEGATIVE coordinates, as required for
natural cubes. Clearing a common denominator proves the exponent 11/13. -/

/- A finite translation cover of y²=the scaled rank-eleven curve. No real uniformization is needed
to turn points of controlled height into positive rational cube pairs. -/
namespace OMA.StewMap829

abbrev Pair := ℚ × ℚ
def k : ℕ := 13293998056584952174157235
def M : ℕ := 170829273
def delta : ℚ := 27*(k:ℚ)^2/(4*(M:ℚ)^6)
def a₁ : ℚ := 186947444570606201329/14124398008634928036
def b₁ : ℚ := 2529513158175975931208754745967/53082934154310554533538352216
def a₂ : ℚ := 8127471096051103790569/1882747235382419456964
def b₂ : ℚ := 465319221889540295783669355640547/81693598731637202574810586421688
def On (p : Pair) : Prop := p.2^2 = p.1^3-delta
def slope (a b : ℚ) (p : Pair) := (p.2-b)/(p.1-a)
def chord (a b : ℚ) (p : Pair) : Pair :=
  let m := slope a b p
  let u := m^2-p.1-a
  (u, m*(a-u)-b)

private theorem chord_data {a b : ℚ} {p : Pair} (E : On p) (F : b^2=a^3-delta)
    (ne : p.1≠a) :
    let m := slope a b p
    let q := chord a b p
    m*(p.1-a) = p.2-b ∧
      2*b*m = (a-q.1)*(p.1-a)+3*a^2 ∧ On q := by
  rcases p with ⟨x,y⟩
  change y^2=x^3-delta at E
  change x≠a at ne
  let m := (y-b)/(x-a)
  let u := m^2-x-a
  change m*(x-a) = y-b ∧ 2*b*m=(a-u)*(x-a)+3*a^2 ∧ (m*(a-u)-b)^2=u^3-delta
  have L : m*(x-a)=y-b := div_mul_cancel₀ _ (sub_ne_zero.mpr ne)
  have K : m^2*(x-a)+2*b*m=x^2+a*x+a^2 := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr ne)
    linear_combination (m*(x-a)+b+y)*L + E - F
  have T : 2*b*m=(a-u)*(x-a)+3*a^2 := by dsimp [u]; linear_combination K
  refine ⟨L,T,?_⟩
  dsimp [u]
  linear_combination (m^2-x-2*a)*K + F

theorem chord_on {a b : ℚ} {p : Pair} (E : On p) (F : b^2=a^3-delta)
    (ne : p.1≠a) : On (chord a b p) := (chord_data E F ne).2.2

/-- Translation by a fixed point is injective where the affine slope is defined. -/
theorem chord_inj {a b : ℚ} (F : b^2=a^3-delta) (bn : b ≠ 0) {p r : Pair}
    (hp : On p) (hr : On r) (pne : p.1≠a) (rne : r.1≠a)
    (eqn : chord a b p=chord a b r) : p=r := by
  let u := (chord a b p).1
  obtain ⟨lp,tp,_⟩ := chord_data hp F pne
  obtain ⟨lr,tr,_⟩ := chord_data hr F rne
  have fx := congrArg Prod.fst eqn
  have fy := congrArg Prod.snd eqn
  change slope a b p*(a-(chord a b p).1)-b=slope a b r*(a-(chord a b r).1)-b at fy
  rw [← fx] at fy tr
  have same : slope a b p=slope a b r := by
    by_cases h : (chord a b p).1=a
    · rw [h, sub_self, zero_mul, zero_add] at tp tr
      exact mul_left_cancel₀ (mul_ne_zero (by norm_num) bn) (tp.trans tr.symm)
    · exact mul_right_cancel₀ (sub_ne_zero.mpr (Ne.symm h)) (sub_left_inj.mp fy)
  change (slope a b p)^2-p.1-a=(slope a b r)^2-r.1-a at fx
  rw [same] at fx lp
  have px : p.1 = r.1 := by linarith
  rw [px] at lp
  exact Prod.ext px (by linarith)


theorem root₁ : b₁^2 = a₁^3-delta := by norm_num [a₁,b₁,delta,M,k]
theorem root₂ : b₂^2 = a₂^3-delta := by norm_num [a₂,b₂,delta,M,k]

private def deficit (a x : ℚ) := (a-11/2)*x^2+(a^2+11*a)*x-2*delta-(11/2)*a^2

private theorem from_deficit {a b x y : ℚ} (E : y^2=x^3-delta) (F : b^2=a^3-delta)
    (h : deficit a x ≤ 2*b*y) (ne : x≠a) : (chord a b (x,y)).1 ≤ 11/2 := by
  change ((y-b)/(x-a))^2-x-a ≤ 11/2
  rw [div_pow,sub_le_iff_le_add,sub_le_iff_le_add,div_le_iff₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr ne))]
  unfold deficit at h
  nlinarith only [E,F,h]

theorem middle {x y : ℚ} (E : y^2=x^3-delta) (yn : 0≤y) (low : 11/2≤x) (hi : x≤12) :
    (chord a₁ b₁ (x,y)).1 ≤ 11/2 := by
  apply from_deficit E root₁
  · have lo : 0≤x-11/2 := by linarith
    have up : 0≤12-x := by linarith
    have cert : 0≤(2*b₁)^2*(x^3-delta)-(deficit a₁ x)^2 := by
      calc
        0 ≤ (223512298243928830855110406567391924515862739542669476383773237882352275376753802083266961574144428152454430787/2057741143390509705788066400115834464259415243341327909437285218944308433908838945732842651147055595002834992:ℚ)*(x-11/2)^0*(12-x)^4
        +(1360314387076008234457153916012522604623132910510181795676163626923828986883323735956029964632634204523851300003/2057741143390509705788066400115834464259415243341327909437285218944308433908838945732842651147055595002834992:ℚ)*(x-11/2)^1*(12-x)^3
        +(1899915663424151459314426382712912592660218625759756484903693420377683957579698186222502489072458863101023658688043/2987840140203020092804272412968191642104670933331608124502938137907135846035634149204087529465524723944116408384:ℚ)*(x-11/2)^2*(12-x)^2
        +(230546519681632659182957242191129600505620637082930346603014261696957718896441703376980022175259436223408921536739/1493920070101510046402136206484095821052335466665804062251469068953567923017817074602043764732762361972058204192:ℚ)*(x-11/2)^3*(12-x)^1
        +(33014741065740309522863841375572105864374626910715938144136552458219811007491821871074750699676535250149393775223/2987840140203020092804272412968191642104670933331608124502938137907135846035634149204087529465524723944116408384:ℚ)*(x-11/2)^4*(12-x)^0 := by positivity
        _ = _ := by unfold deficit a₁ b₁ delta M k; ring
    by_contra! bad
    have pos : 0 ≤ 2*b₁*y := mul_nonneg (by norm_num [b₁]) yn
    nlinarith only [cert, mul_self_lt_mul_self pos bad, congrArg (fun z : ℚ => (2*b₁)^2*z) E]
  · have : 12 < a₁ := by norm_num [a₁]
    linarith

theorem outer {x y : ℚ} (E : y^2=x^3-delta) (yn : 0≤y) (low : 12≤x) :
    (chord a₂ b₂ (x,y)).1 ≤ 11/2 := by
  apply from_deficit E root₂
  · have h : 0≤x-12 := by linarith
    have w : 0 ≤ (x^3-delta)-(4*x-8)^2 := by
      calc
        0 ≤ (x-12)^3 + 20*(x-12)^2+112*(x-12)+(128-delta) :=
          by
            have : (0:ℚ) ≤ 128-delta := by norm_num [delta,M,k]
            positivity
        _ = _ := by ring
    have ly : 4*x-8 ≤ y := by
      by_contra! bad
      nlinarith only [w,E,mul_self_lt_mul_self yn bad]
    have poly : 0≤2*b₂*(4*x-8)-deficit a₂ x := by
      calc
        0 ≤ (715032819831585553682804025853190235007303609215110074593899/22987731118295394607626284394739973189566106379801906008352:ℚ)*(x-12)^0
        +(27804410302884803303744638020424767226757843/3544737152340143575564589630144640648097296:ℚ)*(x-12)^1
        +(2227638698552203222733/1882747235382419456964:ℚ)*(x-12)^2 := by positivity
        _ = _ := by unfold deficit a₂ b₂ delta M k; ring
    linarith only [poly, mul_le_mul_of_nonneg_left ly (by norm_num [b₂] : 0 ≤ 2*b₂)]
  · have : a₂ < 12 := by norm_num [a₂]
    linarith

end OMA.StewMap829

/- Injectivity on the six sign-and-translation classes of the finite cover. -/

namespace OMA.StewSelect829

open OMA.StewMap829

def normal (p : Pair) : Pair := (p.1, |p.2|)
def band (x : ℚ) : Fin 3 := if x ≤ 11/2 then 0 else if x ≤ 12 then 1 else 2
def shift (t : Fin 3) (p : Pair) : Pair :=
  if t=0 then p else if t=1 then chord a₁ b₁ p else chord a₂ b₂ p
def recenter (p : Pair) := shift (band p.1) (normal p)
def A : ℚ := 9*(k:ℚ)
def V : ℚ := 2*(M:ℚ)^3
def U : ℚ := 6*(M:ℚ)^2
def cubesOf (p : Pair) : Pair := ((A+V*p.2)/(U*p.1),(A-V*p.2)/(U*p.1))
def output (p : Pair) := cubesOf (recenter p)
def tag (p : Pair) : Bool × Fin 3 := (decide (0≤p.2),band p.1)

private theorem positive_x {p : Pair} (E : On p) : 0<p.1 := by
  by_contra! h
  have nonpos : p.1^3 ≤ 0 := by
    rw [pow_succ]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h
  change p.2^2 = p.1^3-delta at E
  have : 0 < delta := by norm_num [delta,M,k]
  linarith [sq_nonneg p.2]

private theorem normal_on {p : Pair} (E : On p) : On (normal p) := by
  simpa [On, normal, sq_abs] using E

theorem cover {p : Pair} (E : On p) : On (recenter p) ∧ (recenter p).1 ≤ 11/2 := by
  have h := normal_on E
  by_cases l : p.1≤11/2
  · simpa [recenter,band,shift,l,normal] using And.intro h l
  by_cases u : p.1≤12
  · have ne : (normal p).1 ≠ a₁ := by
      change p.1≠a₁
      have z : (12:ℚ)<a₁ := by norm_num [a₁]
      linarith
    have on := (chord_on (a:=a₁) (b:=b₁) h root₁ ne)
    have le := middle h (abs_nonneg p.2) (le_of_not_ge l) u
    simpa [recenter,band,shift,l,u,normal] using And.intro on le
  · have ne : (normal p).1 ≠ a₂ := by
      change p.1≠a₂
      have z : a₂ < (12:ℚ) := by norm_num [a₂]
      linarith
    have on := (chord_on (a:=a₂) (b:=b₂) h root₂ ne)
    have le := outer h (abs_nonneg p.2) (le_of_not_ge u)
    simpa [recenter,band,shift,l,u,normal] using And.intro on le

private theorem cubes_pos {p : Pair} (E : On p) (small : p.1≤11/2) :
    0≤(cubesOf p).1 ∧ 0≤(cubesOf p).2 ∧
      (cubesOf p).1^3+(cubesOf p).2^3=(k:ℚ) := by
  have h := positive_x E
  have bound := pow_le_pow_left₀ h.le small 3
  change p.2^2=p.1^3-delta at E
  have near : (48:ℚ) ≤ delta := by norm_num [delta,k,M]
  have low : -12≤p.2 := by nlinarith [sq_nonneg (p.2+12)]
  have hi : p.2≤12 := by nlinarith [sq_nonneg (p.2-12)]
  have va : 12*V ≤ A := by norm_num [V,A,k,M]
  have vpos : 0≤V := by norm_num [V,M]
  have upos : 0<U := by norm_num [U,M]
  have one := mul_le_mul_of_nonneg_left low vpos
  have two := mul_le_mul_of_nonneg_left hi vpos
  refine ⟨div_nonneg (by linarith) (by positivity),div_nonneg (by linarith) (by positivity),?_⟩
  change ((A+V*p.2)/(U*p.1))^3+((A-V*p.2)/(U*p.1))^3=(k:ℚ)
  field_simp [h.ne',upos.ne']
  unfold U V A delta M k at *
  linear_combination (6*(9*(13293998056584952174157235:ℚ))*(2*170829273^3)^2)*E

theorem output_correct {p : Pair} (E : On p) :
    0≤(output p).1 ∧ 0≤(output p).2 ∧ (output p).1^3+(output p).2^3=(k:ℚ) :=
  cubes_pos (cover E).1 (cover E).2

private theorem cubes_inj {p r : Pair} (hp : On p) (hr : On r)
    (eqn : cubesOf p = cubesOf r) : p=r := by
  have hp' := (positive_x hp).ne'
  have hr' := (positive_x hr).ne'
  have a := congrArg Prod.fst eqn
  have b := congrArg Prod.snd eqn
  change (A+V*p.2)/(U*p.1)=(A+V*r.2)/(U*r.1) at a
  change (A-V*p.2)/(U*p.1)=(A-V*r.2)/(U*r.1) at b
  have uz : U≠0 := by norm_num [U,M]
  field_simp [hp',hr',uz] at a b
  norm_num [A,V,U,k,M] at a b
  have px : p.1=r.1 := by linarith
  rw [px] at a
  exact Prod.ext px (by apply mul_right_cancel₀ hr'; linarith)

private theorem normal_inj {p r : Pair} (sg : decide (0≤p.2) = decide (0≤r.2))
    (eqn : normal p=normal r) : p=r := by
  have y : |p.2|=|r.2| := congrArg Prod.snd eqn
  have x : (normal p).1 = (normal r).1 := congrArg Prod.fst eqn
  refine Prod.ext x ?_
  by_cases hp : 0≤p.2 <;> by_cases hr : 0≤r.2 <;> simp_all [abs_of_nonneg,abs_of_neg]

private theorem range_middle {x : ℚ} (s : band x=1) : x≤12 := by
  by_contra! h
  simp [band,show ¬x≤11/2 by linarith,not_le.mpr h] at s

private theorem range_outer {x : ℚ} (s : band x=2) : 12<x := by
  by_contra! h
  by_cases hh : x≤11/2 <;> simp [band,hh,h] at s

theorem unique {p r : Pair} (hp : On p) (hr : On r)
    (st : tag p = tag r) (eqn : output p=output r) : p=r := by
  have s : band p.1 = band r.1 := congrArg Prod.snd st
  have sg : decide (0≤p.2) = decide (0≤r.2) := congrArg Prod.fst st
  have sh := cubes_inj (cover hp).1 (cover hr).1 eqn
  change shift (band p.1) (normal p) = shift (band r.1) (normal r) at sh
  apply normal_inj sg
  have cases : band p.1=0 ∨ band p.1=1 ∨ band p.1=2 := by omega
  rcases cases with h|h|h
  · simpa [h,s.symm,shift] using sh
  · apply chord_inj (a:=a₁) (b:=b₁) root₁ (by norm_num [b₁]) (normal_on hp) (normal_on hr)
    · change p.1≠a₁
      have z : (12:ℚ)<a₁ := by norm_num [a₁]
      linarith [range_middle h]
    · change r.1≠a₁
      have z : (12:ℚ)<a₁ := by norm_num [a₁]
      linarith [range_middle (s.symm.trans h)]
    · simpa [h,s.symm,shift] using sh
  · apply chord_inj (a:=a₂) (b:=b₂) root₂ (by norm_num [b₂]) (normal_on hp) (normal_on hr)
    · change p.1≠a₂
      have z : a₂ < (12:ℚ) := by norm_num [a₂]
      linarith [range_outer h]
    · change r.1≠a₂
      have z : a₂ < (12:ℚ) := by norm_num [a₂]
      linarith [range_outer (s.symm.trans h)]
    · simpa [h,s.symm,shift] using sh

end OMA.StewSelect829

/- Rational height bounds for fixed rational expressions. Heights are the
maximum of the reduced denominator and the absolute reduced numerator. -/
namespace OMA.HeightArith829

abbrev H (q : ℚ) := max q.num.natAbs q.den
abbrev Bdd (T d : ℕ) (q : ℚ) := H q ≤ T^d

lemma mulH (q r : ℚ) : H (q*r) ≤ H q * H r := by
  have h := Height.mulHeight₁_mul_le q r
  simp only [Rat.mulHeight₁_eq_max] at h
  exact_mod_cast h

lemma addH (q r : ℚ) : H (q+r) ≤ 2 * H q * H r := by
  have h := Height.mulHeight₁_add_le q r
  have wt : Height.totalWeight ℚ = 1 := by simp [NumberField.totalWeight_eq_finrank]
  simp only [wt, pow_one, Rat.mulHeight₁_eq_max] at h
  exact_mod_cast h

lemma subH (q r : ℚ) : H (q-r) ≤ 2 * H q * H r := by
  have h := Height.mulHeight₁_sub_le q r
  have wt : Height.totalWeight ℚ = 1 := by simp [NumberField.totalWeight_eq_finrank]
  simp only [wt, pow_one, Rat.mulHeight₁_eq_max] at h
  exact_mod_cast h

lemma invH (q : ℚ) : H q⁻¹ = H q := by
  have h := Height.mulHeight₁_inv q
  simp only [Rat.mulHeight₁_eq_max] at h
  exact_mod_cast h

lemma bmul {T d e : ℕ} {q r : ℚ} (hq : Bdd T d q) (hr : Bdd T e r) :
    Bdd T (d+e) (q*r) := by
  simpa only [Bdd, pow_add] using (mulH q r).trans (Nat.mul_le_mul hq hr)

lemma bdiv {T d e : ℕ} {q r : ℚ} (hq : Bdd T d q) (hr : Bdd T e r) :
    Bdd T (d+e) (q/r) := by
  rw [div_eq_mul_inv]
  apply bmul hq
  simpa only [Bdd, invH] using hr

lemma bsum {T d e : ℕ} {q r : ℚ} (hT : 2 ≤ T)
    (hq : Bdd T d q) (hr : Bdd T e r) :
    Bdd T (1+d+e) (q+r) ∧ Bdd T (1+d+e) (q-r) := by
  have h := Nat.mul_le_mul (Nat.mul_le_mul hT hq) hr
  simpa only [Bdd, pow_add, pow_one] using And.intro ((addH q r).trans h) ((subH q r).trans h)

lemma widen {T d e : ℕ} {q : ℚ} (hT : 2 ≤ T) (h : Bdd T d q) (he : d ≤ e) :
    Bdd T e q := h.trans (Nat.pow_le_pow_right (by omega) he)


lemma bpow {T d n:ℕ} {q:ℚ} (h : Bdd T d q) : Bdd T (d*n) (q^n) := by
  induction n with
  | zero => simp [H,Bdd]
  | succ n ih => simpa only [pow_succ,Nat.mul_succ] using bmul ih h

lemma bneg {T d:ℕ} {q:ℚ} (h:Bdd T d q) : Bdd T d (-q) := by simpa [Bdd,H] using h
lemma babs {T d:ℕ} {q:ℚ} (h:Bdd T d q) : Bdd T d |q| := by
  rcases abs_choice q with e|e
  · simpa [e] using h
  · simpa [e] using bneg h

lemma const {T d:ℕ} {q:ℚ} (hT:2≤T) (h:H q≤2^d) : Bdd T d q :=
  h.trans (Nat.pow_le_pow_left hT d)

end OMA.HeightArith829

/- The rational 3-isogeny on the positive sextic twist, followed by a fixed
change of scale. The two points with X=0 are discarded. A single output has
at most three possible abscissae, each with at most two ordinates. -/
namespace OMA.Isogeny829
open OMA.StewMap829

def Source (p:Pair) : Prop := p.2^2=p.1^3+16*(k:ℚ)^2

def phi (p:Pair) : Pair :=
  ((p.1^3+64*(k:ℚ)^2)/((4*(M:ℚ)^2)*p.1^2),
    p.2*(p.1^3-128*(k:ℚ)^2)/((8*(M:ℚ)^3)*p.1^3))

theorem on {p:Pair} (hs:Source p) (nz:p.1≠0) : On (phi p) := by
  obtain ⟨x,y⟩ := p
  change y^2=x^3+16*(k:ℚ)^2 at hs
  change x≠0 at nz
  have m : (M:ℚ)≠0 := by norm_num [M]
  unfold On phi delta
  dsimp only
  rw [div_pow,mul_pow,hs]
  field_simp
  ring

private theorem vertical (S:Finset Pair) (hs:∀p∈S,Source p) (x:ℚ) :
    (S.filter (fun p => p.1=x)).card ≤ 2 := by
  classical
  let T:=S.filter (fun p => p.1=x)
  change T.card ≤ 2
  rcases T.eq_empty_or_nonempty with e|⟨a,ha⟩
  · simp [e]
  have am := Finset.mem_filter.mp ha
  apply (Finset.card_le_card (t:={(x,a.2),(x,-a.2)}) ?_).trans Finset.card_le_two
  intro b hb
  have bm := Finset.mem_filter.mp hb
  have ae := hs a am.1
  have be := hs b bm.1
  unfold Source at ae be
  rw [am.2] at ae
  rw [bm.2] at be
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (be.trans ae.symm) with eql|eql
  · exact Finset.mem_insert.mpr (Or.inl (Prod.ext bm.2 eql))
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (Prod.ext bm.2 eql))

private noncomputable def cubic (t:ℚ) : Polynomial ℚ :=
  Polynomial.X^3 - Polynomial.C (4*(M:ℚ)^2*t) * Polynomial.X^2 + Polynomial.C (64*(k:ℚ)^2)

private theorem abscissae (S:Finset Pair) (q:Pair)
    (nn:∀p∈S,p.1≠0) (same:∀p∈S,phi p=q) : (S.image Prod.fst).card≤3 := by
  classical
  let g := cubic q.1
  have dg : g.natDegree=3 := by unfold g cubic;compute_degree!
  have ng : g ≠ 0 := fun z => by simp [z] at dg
  have inclusion : S.image Prod.fst ⊆ g.roots.toFinset := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    have eq := congrArg Prod.fst (same p hp)
    change (p.1^3+64*(k:ℚ)^2)/((4*(M:ℚ)^2)*p.1^2)=q.1 at eq
    have m : (M:ℚ)≠0 := by norm_num [M]
    have den : (4*(M:ℚ)^2)*p.1^2 ≠ 0 := by have := nn p hp; positivity
    have h := (div_eq_iff den).mp eq
    rw [Multiset.mem_toFinset,Polynomial.mem_roots ng,Polynomial.IsRoot]
    simp [g,cubic]
    linear_combination h
  exact (Finset.card_le_card inclusion).trans
    ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans_eq dg))

/-- At most two exceptional points, then at most six inputs per output. -/
theorem image_bound (S:Finset Pair) (hs:∀p∈S,Source p) :
    S.card ≤ 2+6*((S.filter (fun p => p.1≠0)).image phi).card := by
  classical
  let good:=S.filter fun p => p.1≠0
  have lost := vertical S hs 0
  have rest : S.card=(S.filter (fun p => p.1=0)).card+good.card := by
    exact (Finset.card_filter_add_card_filter_not ..).symm
  have all : good.card≤6*(good.image phi).card := by
    apply Finset.card_le_mul_card_image
    intro q _
    let T:=good.filter fun p => phi p=q
    have mem (p) (hp:p∈T) : p∈S ∧ p.1≠0 ∧ phi p=q := by
      have h:=Finset.mem_filter.mp hp
      have h':=Finset.mem_filter.mp h.1
      exact ⟨h'.1,h'.2,h.2⟩
    have xs := abscissae T q (fun p h => (mem p h).2.1) (fun p h => (mem p h).2.2)
    have h := Finset.card_le_mul_card_image (f:=Prod.fst) T 2 fun x _ =>
      vertical T (fun p hp => hs p (mem p hp).1) x
    change T.card≤6
    omega
  exact rest.le.trans (Nat.add_le_add lost all)

open OMA.HeightArith829 in
/-- Both output coordinates have height at most T^512 when both input
coordinates have height at most T. -/
theorem height {T:ℕ} (hT:2≤T) {p:Pair} (hx:H p.1≤T) (hy:H p.2≤T) :
    H (phi p).1≤T^512 ∧ H (phi p).2≤T^512 := by
  have x : Bdd T 1 p.1 := by simpa [Bdd] using hx
  have y : Bdd T 1 p.2 := by simpa [Bdd] using hy
  have x2 := bpow (n:=2) x
  have x3 := bpow (n:=3) x
  have A : Bdd T 200 (64*(k:ℚ)^2) := const hT (by norm_num [k,H])
  have B : Bdd T 200 (128*(k:ℚ)^2) := const hT (by norm_num [k,H])
  have C : Bdd T 200 (4*(M:ℚ)^2) := const hT (by norm_num [M,H])
  have D : Bdd T 200 (8*(M:ℚ)^3) := const hT (by norm_num [M,H])
  exact ⟨widen hT (bdiv (bsum hT x3 A).1 (bmul C x2)) (by decide),
    widen hT (bdiv (bmul y (bsum hT x3 B).2) (bmul D x3)) (by decide)⟩

end OMA.Isogeny829

/- Clearing all denominators of a rank-eleven family: N^11 pairs of height bounded
by B^(N²) give N^11 integral cube representations with log n bounded by a multiple of N^13. -/

namespace OMA.CountStewart829
open Filter AdditiveCombinatorics OMA.StewMap829

private theorem clear {D : ℕ} (a : ℚ) (ha : 0 ≤ a) (hd : a.den ∣ D) :
    ∃ u : ℕ, (u : ℚ) = D * a := by
  obtain ⟨e, rfl⟩ := hd
  refine ⟨a.num.toNat * e, ?_⟩
  have hz : ((a.num.toNat : ℕ) : ℚ) = (a.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr ha)
  have hn := (div_eq_iff (by exact_mod_cast a.den_ne_zero : (a.den : ℚ) ≠ 0)).mp a.num_div_den
  push_cast
  rw [hz, hn]
  ring

private theorem reps {K D : ℕ} (hD : 0 < D) (p : Fin K → ℚ × ℚ) (hp : Function.Injective p)
    (h : ∀ i, 0 ≤ (p i).1 ∧ 0 ≤ (p i).2 ∧ (p i).1^3 + (p i).2^3 = (k:ℚ) ∧
      (p i).1.den ∣ D ∧ (p i).2.den ∣ D) :
    K ≤ sumRep Erdos829.cubes (k * D^3) := by
  classical
  choose u hu using fun i => clear (p i).1 (h i).1 (h i).2.2.2.1
  choose v hv using fun i => clear (p i).2 (h i).2.1 (h i).2.2.2.2
  let f (i : Fin K) : ℕ × ℕ := ((u i)^3,(v i)^3)
  have fsum (i : Fin K) : (f i).1 + (f i).2 = k * D^3 := by
    change (u i)^3 + (v i)^3 = k * D^3
    have hh : (u i : ℚ)^3 + (v i : ℚ)^3 = (k:ℚ) * (D : ℚ)^3 := by
      rw [hu, hv, mul_pow, mul_pow, ← mul_add, (h i).2.2.1, mul_comm]
    exact_mod_cast hh
  have inj : Function.Injective f := by
    intro i j hij
    have h₁ : (u i)^3 = (u j)^3 := congrArg Prod.fst hij
    have h₂ : (v i)^3 = (v j)^3 := congrArg Prod.snd hij
    have h₁' : (u i : ℚ) = (u j : ℚ) := by exact_mod_cast (Nat.pow_left_injective (by decide : 3 ≠ 0) h₁)
    have h₂' : (v i : ℚ) = (v j : ℚ) := by exact_mod_cast (Nat.pow_left_injective (by decide : 3 ≠ 0) h₂)
    rw [hu, hu] at h₁'
    rw [hv, hv] at h₂'
    have nz : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    exact hp (Prod.ext (mul_left_cancel₀ nz h₁') (mul_left_cancel₀ nz h₂'))
  rw [sumRep_def]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    (Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin K))) f
      (t := (Finset.HasAntidiagonal.antidiagonal (k * D^3)).filter fun q =>
        q.1 ∈ Erdos829.cubes ∧ q.2 ∈ Erdos829.cubes)
      (fun i _ => Finset.mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (fsum i),
        ⟨u i, rfl⟩, ⟨v i, rfl⟩⟩) (fun _ _ _ _ hh => inj hh))

private theorem find {N B : ℕ} (hn : 0 < N) (hb : 2 ≤ B)
    (p : Fin (N^11) → ℚ × ℚ) (hp : Function.Injective p)
    (h : ∀ i, 0 ≤ (p i).1 ∧ 0 ≤ (p i).2 ∧ (p i).1^3 + (p i).2^3 = (k:ℚ) ∧
      (p i).1.den ≤ B^(N^2) ∧ (p i).2.den ≤ B^(N^2)) :
    ∃ n : ℕ, N ≤ n ∧ n ≤ B^(109*N^13) ∧ N^11 ≤ sumRep Erdos829.cubes n := by
  let H := B^(N^2)
  let m (i : Fin (N^11)) := (p i).1.den * (p i).2.den
  let D := H * ∏ i, m i
  have hH : 0 < H := pow_pos (by omega : 0 < B) _
  have hprod : 0 < ∏ i, m i := Finset.prod_pos fun i _ => Nat.mul_pos (p i).1.den_pos (p i).2.den_pos
  have hD : 0 < D := Nat.mul_pos hH hprod
  have nH : N ≤ H := calc
    N ≤ 2^N := N.lt_two_pow_self.le
    _ ≤ B^N := Nat.pow_le_pow_left hb _
    _ ≤ H := Nat.pow_le_pow_right (by omega) (Nat.le_self_pow (by decide : 2 ≠ 0) N)
  have nD : N ≤ D := nH.trans (Nat.le_mul_of_pos_right _ hprod)
  refine ⟨k*D^3, ?_, ?_, reps hD p hp ?_⟩
  · exact nD.trans ((Nat.le_self_pow (by decide : 3 ≠ 0) D).trans
      (Nat.le_mul_of_pos_left _ (by decide : 0 < k)))
  · have hh : ∏ i, m i ≤ (H*H)^(N^11) := by
      simpa using (Finset.prod_le_prod' (s := (Finset.univ : Finset (Fin (N^11))))
        (g := fun _ => H*H) (fun i _ => Nat.mul_le_mul (h i).2.2.2.1 (h i).2.2.2.2))
    have hk : k ≤ B^100 := le_trans (by decide : k ≤ 2^100) (Nat.pow_le_pow_left hb _)
    calc
      k * D^3 ≤ B^100 * (H*(H*H)^(N^11))^3 :=
        Nat.mul_le_mul hk (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hh) _)
      _ = B^(100+(N^2)*(1+2*(N^11))*3) := by
        dsimp [H]
        simp only [pow_add, pow_one, pow_mul, pow_two]
      _ ≤ B^(109*N^13) := by
        apply Nat.pow_le_pow_right (by omega)
        have h13 : 1 ≤ N^13 := Nat.one_le_pow _ _ hn
        have h2 : N^2 ≤ N^13 := Nat.pow_le_pow_right hn (by decide)
        nlinarith
  · intro i
    have hd : m i ∣ D := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) H
    exact ⟨(h i).1, (h i).2.1, (h i).2.2.1,
      dvd_trans (dvd_mul_right ..) hd, dvd_trans (dvd_mul_left ..) hd⟩

theorem lower (B : ℕ) (hB : 2 ≤ B)
    (pts : ∀ N : ℕ, 0 < N → ∃ p : Fin (N^11) → ℚ × ℚ, Function.Injective p ∧
      ∀ i, 0 ≤ (p i).1 ∧ 0 ≤ (p i).2 ∧ (p i).1^3 + (p i).2^3 = (k:ℚ) ∧
        (p i).1.den ≤ B^(N^2) ∧ (p i).2.den ≤ B^(N^2)) :
    type_of% @Erdos829.variants.stewart := by
  have hlog : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  let L : ℝ := 109 * Real.log B
  have hL : 0 < L := mul_pos (by norm_num) hlog
  refine ⟨(L^(11/13 : ℝ))⁻¹, by positivity, frequently_atTop.2 ?_⟩
  intro t
  let N := t+1
  have hN : 0 < N := Nat.succ_pos _
  obtain ⟨p, hp, h⟩ := pts N hN
  obtain ⟨n, hNn, hb, hr⟩ := find hN hB p hp h
  refine ⟨n, by omega, ?_⟩
  have hn : (0:ℝ) < n := by exact_mod_cast (hN.trans_le hNn)
  have hl := Real.log_le_log hn (show (n:ℝ) ≤ (B:ℝ)^(109*N^13) by exact_mod_cast hb)
  rw [Real.log_pow] at hl
  have hl' : Real.log n ≤ L*(N:ℝ)^13 := by
    push_cast at hl
    dsimp [L]
    linarith
  have hroot := Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
    hl' (by norm_num : (0:ℝ) ≤ 11/13)
  rw [Real.mul_rpow hL.le (by positivity), ← Real.rpow_natCast_mul (by positivity : 0 ≤ (N:ℝ))] at hroot
  norm_num at hroot
  calc
    (L^(11/13 : ℝ))⁻¹ * (Real.log n)^(11/13 : ℝ) ≤ (N:ℝ)^11 := by
      rw [inv_mul_eq_div]
      exact (div_le_iff₀ (Real.rpow_pos_of_pos hL _)).2 (by simpa [mul_comm] using hroot)
    _ ≤ (sumRep Erdos829.cubes n : ℝ) := by exact_mod_cast hr

end OMA.CountStewart829

/- Bounds for the height increase in the finite real-translation cover and
the final rational change of variables to the cubic sum. -/
namespace OMA.StewHeightMap829
open StewMap829 StewSelect829 HeightArith829

private theorem chord_bound {T:ℕ} (hT:2≤T) {x y a b:ℚ}
    (hx:Bdd T 1 x) (hy:Bdd T 1 y) (ha:Bdd T 128 a) (hb:Bdd T 128 b) :
    Bdd T 651 (chord a b (x,y)).1 ∧ Bdd T 1169 (chord a b (x,y)).2 := by
  let m:=(y-b)/(x-a)
  let u:=m^2-x-a
  have hm : Bdd T 260 m := bdiv (bsum hT hy hb).2 (bsum hT hx ha).2
  have hu : Bdd T 651 u := (bsum hT (bsum hT (bpow (n:=2) hm) hx).2 ha).2
  exact ⟨hu,(bsum hT (bmul hm (bsum hT ha hu).2) hb).2⟩

/-- A uniform bound on the reduced denominators of the final cube pair. -/
theorem bound {T:ℕ} (hT:2≤T) {p:Pair} (hx:H p.1≤T) (hy:H p.2≤T) :
    (output p).1.den ≤ T^2304 ∧ (output p).2.den ≤ T^2304 := by
  have x : Bdd T 1 p.1 := by simpa [Bdd] using hx
  have y : Bdd T 1 |p.2| := babs (by simpa [Bdd] using hy)
  have bounds : Bdd T 651 (recenter p).1 ∧ Bdd T 1169 (recenter p).2 := by
    unfold recenter shift
    split
    · exact ⟨widen hT x (by decide),widen hT y (by decide)⟩
    split
    · exact chord_bound hT x y (const hT (by norm_num [a₁,H])) (const hT (by norm_num [b₁,H]))
    · exact chord_bound hT x y (const hT (by norm_num [a₂,H])) (const hT (by norm_num [b₂,H]))
  have a : Bdd T 128 A := const hT (by norm_num [A,k,H])
  have u : Bdd T 128 U := const hT (by norm_num [U,M,H])
  have v : Bdd T 128 V := const hT (by norm_num [V,M,H])
  obtain ⟨hp,hm⟩ := bsum hT a (bmul v bounds.2)
  have d := bmul u bounds.1
  exact ⟨(le_max_right ..).trans (widen hT (bdiv hp d) (by decide)),
    (le_max_right ..).trans (widen hT (bdiv hm d) (by decide))⟩

end OMA.StewHeightMap829

/- A quadratic logarithmic height bound for a finite box of rational points
on an integral Weierstrass curve. The two projective addition laws are quartic.
Halving all coefficients at once applies one quartic bound at each binary scale. -/
namespace OMA.StewartHeight829

open WeierstrassCurve Projective
open scoped WeierstrassCurve.Projective

abbrev Vec (K : Type*) := Fin 3 → K
abbrev liftCurve (K : Type*) [CommRing K] (W : WeierstrassCurve.Projective ℤ) :=
  W.map (Int.castRingHom K)
def castV (K : Type*) [CommRing K] (p : Vec ℤ) : Vec K := fun i => p i

private theorem cast_dbl (K : Type*) [CommRing K] (W : WeierstrassCurve.Projective ℤ) (v : Vec ℤ) :
    castV K (W.dblXYZ v)=(liftCurve K W).dblXYZ (castV K v) :=
  (map_dblXYZ (Int.castRingHom K) v).symm

private theorem cast_add (K : Type*) [CommRing K] (W : WeierstrassCurve.Projective ℤ) (v w : Vec ℤ) :
    castV K (W.addXYZ v w)=(liftCurve K W).addXYZ (castV K v) (castV K w) :=
  (map_addXYZ (Int.castRingHom K) v w).symm

private theorem quartic {V:Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
    (f:V→Vec ℝ) (hc:Continuous f) (hom:∀s:ℝ,∀p:V,f (s • p)=s^4 • f p) :
    ∃M:ℕ,∀r:ℝ,0<r → ∀p:V,‖p‖≤r → ‖f p‖≤(M:ℝ)*r^4 := by
  obtain ⟨K,hK⟩ := (isCompact_closedBall (0:V) 1).bddAbove_image hc.norm.continuousOn
  obtain ⟨M,hM⟩ := exists_nat_gt K
  refine ⟨M,?_⟩
  intro r hr p hp
  have ins : r⁻¹ • p ∈ Metric.closedBall (0:V) 1 := by
    rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    simpa [hr.ne'] using mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hr.le)
  have bb := (hK (Set.mem_image_of_mem _ ins)).trans hM.le
  have eq : f p=r^4 • f (r⁻¹ • p) := by rw [←hom,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  rw [eq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),mul_comm]
  exact mul_le_mul_of_nonneg_right bb (by positivity)


set_option maxHeartbeats 3000000 in
private theorem continuous_dbl (W : WeierstrassCurve.Projective ℝ) : Continuous W.dblXYZ := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [dblXYZ,dblX,dblY,negDblY,dblZ,negY,
    Matrix.cons_val_two] <;> fun_prop

set_option maxHeartbeats 3000000 in
private theorem continuous_add (W : WeierstrassCurve.Projective ℝ) :
    Continuous (fun p:Vec ℝ×Vec ℝ => W.addXYZ p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [addXYZ,addX,addY,negAddY,addZ,negY,
    Matrix.cons_val_two] <;> fun_prop

private theorem coord_le (p:Vec ℤ) (L:ℕ) :
    (∀i,(p i).natAbs≤L) ↔ ‖castV ℝ p‖≤L := by
  rw [pi_norm_le_iff_of_nonneg (Nat.cast_nonneg L)]
  constructor <;> intro h i <;> specialize h i
  · change |(p i:ℝ)| ≤ (L:ℝ)
    rw [←Int.cast_abs,←Nat.cast_natAbs]
    exact_mod_cast h
  · change |(p i:ℝ)| ≤ (L:ℝ) at h
    rw [←Int.cast_abs,←Nat.cast_natAbs] at h
    exact_mod_cast h


def Represents {W:WeierstrassCurve.Projective ℤ} (A:(liftCurve ℚ W).Point) (p:Vec ℤ) : Prop :=
  A.point=⟦castV ℚ p⟧

private theorem integral_rep {W:WeierstrassCurve.Projective ℤ} (A:(liftCurve ℚ W).Point) :
    ∃p:Vec ℤ,Represents A p := by
  obtain ⟨v,eq⟩ := Quotient.exists_rep A.point
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) v
  choose p hp using hd
  refine ⟨p,?_⟩
  have eq' : castV ℚ p=((d.val:ℤ):ℚ) • v := by
    ext i
    exact (hp i).trans (by simp [Algebra.smul_def])
  rw [Represents,eq',smul_eq v]
  · exact eq.symm
  · apply isUnit_iff_ne_zero.mpr
    exact_mod_cast (nonZeroDivisors.ne_zero d.property)

/-- Uniform height cost for a single addition, including doubling. -/
private theorem quartet (W : WeierstrassCurve.Projective ℤ) :
    ∃C:ℕ,0<C ∧ ∀ H:ℕ,0<H → ∀ {A D:(liftCurve ℚ W).Point} {p q:Vec ℤ},
      Represents A p → Represents D q → (∀i,(p i).natAbs≤H) → (∀i,(q i).natAbs≤H) →
        ∃v:Vec ℤ,Represents (A+D) v ∧ ∀i,(v i).natAbs≤C*H^4 := by
  obtain ⟨M,md⟩ := quartic _ (continuous_dbl (liftCurve ℝ W)) fun s p => dblXYZ_smul p s
  obtain ⟨N,ma⟩ := quartic _ (continuous_add (liftCurve ℝ W)) (fun s p => by
    change (liftCurve ℝ W).addXYZ (s • p.1) (s • p.2)=s^4 • (liftCurve ℝ W).addXYZ p.1 p.2
    rw [addXYZ_smul]
    congr 1
    ring)
  refine ⟨1+M+N,by omega,?_⟩
  intro H hH A D p q ap dq pb qb
  have pp := (coord_le p H).mp pb
  have qq := (coord_le q H).mp qb
  have hR : (0:ℝ)<H := by exact_mod_cast hH
  by_cases h : castV ℚ p ≈ castV ℚ q
  · refine ⟨W.dblXYZ p,?_,?_⟩
    · unfold Represents at *
      rw [Point.add_point,ap,dq,addMap_eq,add_of_equiv h,cast_dbl]
    · apply (coord_le _ _).mpr
      rw [cast_dbl]
      push_cast
      exact (md H hR (castV ℝ p) pp).trans (mul_le_mul_of_nonneg_right
        (by exact_mod_cast (show M≤1+M+N by omega)) (by positivity))
  · refine ⟨W.addXYZ p q,?_,?_⟩
    · unfold Represents at *
      rw [Point.add_point,ap,dq,addMap_eq,add_of_not_equiv h,cast_add]
    · apply (coord_le _ _).mpr
      rw [cast_add]
      push_cast
      exact (ma H hR (castV ℝ p,castV ℝ q) (max_le pp qq)).trans (mul_le_mul_of_nonneg_right
        (by exact_mod_cast (show N≤1+M+N by omega)) (by positivity))

private theorem reduced {a d:ℤ} (nz:d≠0) :
    max (((a:ℚ)/d).num.natAbs) (((a:ℚ)/d).den) ≤ max a.natAbs d.natAbs := by
  obtain ⟨k,ka,kd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den a nz
  have kn : k≠0 := by intro h;rw [h,zero_mul] at kd;exact nz kd
  have kp : 1≤k.natAbs := Int.natAbs_pos.mpr kn
  have na := congrArg Int.natAbs ka
  have nd := congrArg Int.natAbs kd
  rw [Int.natAbs_mul] at na nd
  rw [Int.natAbs_natCast] at nd
  apply max_le_max
  · calc _ = 1*(((a:ℚ)/d).num.natAbs) := (one_mul _).symm
         _ ≤ _ := (Nat.mul_le_mul_right _ kp).trans_eq na.symm
  · calc _ = 1*(((a:ℚ)/d).den) := (one_mul _).symm
         _ ≤ _ := (Nat.mul_le_mul_right _ kp).trans_eq nd.symm


/-- Bounds integral projective coordinates for all nonnegative combinations
of a fixed finite family with coefficients at most N. -/
theorem box {r:ℕ} (W:WeierstrassCurve.Projective ℤ) (P:Fin r→(liftCurve ℚ W).Point) :
    ∃B:ℕ,1<B ∧ ∀ N:ℕ,0<N → ∀ n:Fin r→ℕ,(∀i,n i≤N) →
      ∃p:Vec ℤ,Represents (∑i,n i • P i) p ∧ ∀j,(p j).natAbs ≤ B^(N^2) := by
  classical
  obtain ⟨C,hC,add⟩ := quartet W
  choose v hv using fun b:Fin r→Fin 2 => integral_rep (∑i,(b i).val • P i)
  let U : ℕ := Finset.univ.sup fun b:Fin r→Fin 2 => Finset.univ.sup fun i => (v b i).natAbs
  let D := 2+C+U
  have hD : 1<D := by dsimp [D];omega
  have cv : C≤D := by dsimp [D];omega
  have base (b : Fin r→Fin 2) (i) : (v b i).natAbs ≤ D := by
    have p := Finset.le_sup (f:=fun j => (v b j).natAbs) (Finset.mem_univ i)
    have q : Finset.univ.sup (fun j => (v b j).natAbs) ≤ U :=
      Finset.le_sup (f:=fun b:Fin r→Fin 2 => Finset.univ.sup fun j => (v b j).natAbs)
        (Finset.mem_univ b)
    exact (p.trans q).trans (by dsimp [D];omega)
  have dyadic (k:ℕ) (n:Fin r→ℕ) (hn:∀i,n i≤2^k) :
      ∃p:Vec ℤ,Represents (∑i,n i • P i) p ∧ ∀j,(p j).natAbs ≤ D^(2*4^k-1) := by
    induction k generalizing n with
    | zero =>
      let b (i:Fin r) : Fin 2 := ⟨n i,by have := hn i;simp only [pow_zero] at this;omega⟩
      exact ⟨v b,hv b,fun j => by simpa using base b j⟩
    | succ k ih =>
      let a (i:Fin r):=n i/2
      let b (i:Fin r):=(n i+1)/2
      have hav (i) : a i ≤ 2^k := by
        have h:=hn i;rw [pow_succ] at h;dsimp [a];omega
      have hbv (i) : b i ≤ 2^k := by
        have h:=hn i;rw [pow_succ] at h;dsimp [b];omega
      obtain ⟨p,hp,pb⟩ := ih a hav
      obtain ⟨q,hq,qb⟩ := ih b hbv
      obtain ⟨v,rep,bound⟩ := add _ (Nat.pow_pos (by omega)) hp hq pb qb
      have split : (∑i,a i • P i)+(∑i,b i • P i)=∑i,n i • P i := by
        rw [←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [←add_nsmul,show a i+b i=n i by dsimp [a,b];omega]
      rw [split] at rep
      refine ⟨v,rep,fun j => (bound j).trans ?_⟩
      apply (Nat.mul_le_mul_right _ cv).trans
      rw [←pow_mul,←pow_succ']
      apply Nat.pow_le_pow_right hD.le
      have pos : 0<4^k := by positivity
      rw [pow_succ]
      omega
  refine ⟨D^8,one_lt_pow₀ hD (by decide),?_⟩
  intro N hN n hn
  obtain ⟨p,hp,pb⟩ := dyadic (N.log2+1) n fun i => (hn i).trans Nat.lt_log2_self.le
  refine ⟨p,hp,fun j => (pb j).trans ?_⟩
  rw [←pow_mul]
  apply Nat.pow_le_pow_right hD.le
  have h := Nat.pow_le_pow_left (Nat.log2_self_le hN.ne') 2
  have pw : 4^N.log2 = (2^N.log2)^2 := by rw [←pow_mul, mul_comm, pow_mul];rfl
  rw [pow_succ,pw]
  omega

/-- For an affine member of the box, divide by its nonzero projective Z. -/
theorem affine {W:WeierstrassCurve.Projective ℤ} {A:(liftCurve ℚ W).Point}
    {p:Vec ℤ} (rep:Represents A p) (ne:A≠0) {H:ℕ} (bound:∀j,(p j).natAbs ≤ H) :
    ∃x y:ℚ,A.point=⟦![x,y,1]⟧ ∧ max x.num.natAbs x.den≤H ∧ max y.num.natAbs y.den≤H := by
  have valid : (liftCurve ℚ W).Nonsingular (castV ℚ p) :=
    (nonsingularLift_iff _).mp (rep ▸ A.nonsingular)
  have nz : castV ℚ p 2≠0 := by
    intro eq
    apply ne
    apply Point.ext
    rw [Point.zero_point,rep]
    exact Quotient.sound (equiv_zero_of_Z_eq_zero valid eq)
  have iz : p 2 ≠ 0 := by simpa [castV] using nz
  exact ⟨_,_,rep.trans (Quotient.sound (equiv_some_of_Z_ne_zero nz)),
    (reduced (a:=p 0) iz).trans (max_le (bound 0) (bound 2)),
    (reduced (a:=p 1) iz).trans (max_le (bound 1) (bound 2))⟩

/-- An independent positive-rank family yields N^r distinct affine points
with the same quadratic exponent, taking coefficient vectors in [1,N]^r. -/
theorem points {r:ℕ} (hr:0<r) (W:WeierstrassCurve.Projective ℤ)
    (P:Fin r→(liftCurve ℚ W).Point)
    (indep:Function.Injective (fun n:Fin r→ℕ => ∑i,n i • P i)) :
    ∃ B:ℕ,1<B ∧ ∀ N:ℕ,0<N → ∃ f:(Fin r→Fin N)→ℚ×ℚ,Function.Injective f ∧
      ∀ a,(liftCurve ℚ W).toAffine.Equation (f a).1 (f a).2 ∧
        max (f a).1.num.natAbs (f a).1.den≤B^(N^2) ∧
        max (f a).2.num.natAbs (f a).2.den≤B^(N^2) := by
  classical
  obtain ⟨B,hB,H⟩ := box W P
  refine ⟨B,hB,?_⟩
  intro N hN
  let coeff (a:Fin r→Fin N) (i:Fin r):=(a i).val+1
  let A (a:Fin r→Fin N):=∑i,coeff a i • P i
  have total (a:Fin r→Fin N) : ∃x y:ℚ,(A a).point=⟦![x,y,1]⟧ ∧
      max x.num.natAbs x.den≤B^(N^2) ∧ max y.num.natAbs y.den≤B^(N^2) := by
    obtain ⟨p,rep,b⟩ := H N hN (coeff a) fun i => (a i).isLt
    apply affine rep _ b
    intro hz
    have eq : coeff a=(fun _:Fin r => 0) := indep (by simpa using hz)
    have z := congrFun eq (⟨0,hr⟩:Fin r)
    simp [coeff] at z
  choose x y eq hx hy using total
  refine ⟨fun a => (x a,y a),?_,?_⟩
  · intro a b e
    have xy : x a=x b := congrArg Prod.fst e
    have yy : y a=y b := congrArg Prod.snd e
    have ab : A a=A b := Point.ext (by rw [eq a,eq b,xy,yy])
    have cc : coeff a=coeff b := indep ab
    funext i
    exact Fin.ext (Nat.succ.inj (congrFun cc i))
  · intro a
    have ns := (A a).nonsingular
    rw [eq a,nonsingularLift_iff,nonsingular_some] at ns
    exact ⟨ns.1,hx a,hy a⟩

end OMA.StewartHeight829

/- A shared integral representative suffices to compare rational and finite-field sums.
Two auxiliary translations remove the exceptional case of equal specializations. -/
namespace OMA.Red829
open WeierstrassCurve Projective
open scoped WeierstrassCurve.Projective

abbrev Vec (F : Type*) := Fin 3 → F
abbrev pt (W : Projective ℤ) (F : Type*) [Field F] := (W.map (Int.castRingHom F)).Point
abbrev image (F : Type*) [Field F] (v : Vec ℤ) : Vec F := Int.castRingHom F ∘ v

variable {W : Projective ℤ} {F : Type*} [Field F]

def Red (P : pt W ℚ) (A : pt W F) : Prop :=
  ∃ v : Vec ℤ, P.point = ⟦image ℚ v⟧ ∧ A.point = ⟦image F v⟧

private lemma residue_equiv {v w : Vec ℤ}
    (hv : (W.map (Int.castRingHom F)).Nonsingular (image F v))
    (hw : (W.map (Int.castRingHom F)).Nonsingular (image F w))
    (h : image ℚ v ≈ image ℚ w) : image F v ≈ image F w := by
  have eqx := X_eq_of_equiv h
  have eqy := Y_eq_of_equiv h
  change (v 0 : ℚ) * w 2 = (w 0 : ℚ) * v 2 at eqx
  change (v 1 : ℚ) * w 2 = (w 1 : ℚ) * v 2 at eqy
  have ex : v 0 * w 2 = w 0 * v 2 := by exact_mod_cast eqx
  have ey : v 1 * w 2 = w 1 * v 2 := by exact_mod_cast eqy
  have fx : image F v 0 * image F w 2 = image F w 0 * image F v 2 := by
    simpa only [image, Function.comp_apply, map_mul] using congrArg (Int.castRingHom F) ex
  have fy : image F v 1 * image F w 2 = image F w 1 * image F v 2 := by
    simpa only [image, Function.comp_apply, map_mul] using congrArg (Int.castRingHom F) ey
  by_cases av : image F v 2 = 0
  · have hy := Y_ne_zero_of_Z_eq_zero hv av
    have zw : image F w 2 = 0 := (mul_eq_zero.mp (by simpa only [av, mul_zero] using fy)).resolve_left hy
    exact equiv_of_Z_eq_zero hv hw av zw
  · have bw : image F w 2 ≠ 0 := by
      intro no
      have hy := Y_ne_zero_of_Z_eq_zero hw no
      exact av ((mul_eq_zero.mp (by simpa only [no, mul_zero] using fy.symm)).resolve_left hy)
    exact equiv_of_X_eq_of_Y_eq av bw fx fy

theorem unique {P : pt W ℚ} {A B : pt W F} (hA : Red P A) (hB : Red P B) : A = B := by
  obtain ⟨v, hv, av⟩ := hA
  obtain ⟨w, hw, bw⟩ := hB
  apply Point.ext
  rw [av, bw, Quotient.eq]
  exact residue_equiv ((nonsingularLift_iff _).mp (av ▸ A.nonsingular))
    ((nonsingularLift_iff _).mp (bw ▸ B.nonsingular)) (Quotient.eq.mp (hv.symm.trans hw))

theorem zero : Red (0 : pt W ℚ) (0 : pt W F) := by
  refine ⟨![0,1,0], ?_, ?_⟩ <;> rw [Point.zero_point] <;> apply congrArg Quotient.mk''
  all_goals funext i; fin_cases i <;> simp [image]

theorem neg {P : pt W ℚ} {A : pt W F} (h : Red P A) : Red (-P) (-A) := by
  obtain ⟨v, pv, av⟩ := h
  refine ⟨W.neg v, ?_, ?_⟩
  · rw [Point.neg_point, pv, negMap_eq, Projective.map_neg]
  · rw [Point.neg_point, av, negMap_eq, Projective.map_neg]

theorem add_ne {P Q : pt W ℚ} {A B : pt W F}
    (hp : Red P A) (hq : Red Q B) (ne : A ≠ B) : Red (P+Q) (A+B) := by
  have ratne : P ≠ Q := by rintro rfl; exact ne (unique hp hq)
  obtain ⟨v, pv, av⟩ := hp
  obtain ⟨w, qw, bw⟩ := hq
  have r : ¬ image ℚ v ≈ image ℚ w := by
    intro h
    exact ratne (Point.ext (pv.trans ((Quotient.sound h).trans qw.symm)))
  have f : ¬ image F v ≈ image F w := by
    intro h
    exact ne (Point.ext (av.trans ((Quotient.sound h).trans bw.symm)))
  refine ⟨W.addXYZ v w, ?_, ?_⟩
  · rw [Point.add_point, pv, qw, addMap_eq, add_of_not_equiv r, map_addXYZ]
  · rw [Point.add_point, av, bw, addMap_eq, add_of_not_equiv f, map_addXYZ]

/-- Two liftable points that are distinct up to sign and are not their own negatives
suffice to compare the group law on all points for which a common representative is known. -/
structure Offsets (W : Projective ℤ) (F : Type*) [Field F] where
  p : pt W ℚ
  q : pt W ℚ
  a : pt W F
  b : pt W F
  ra : Red p a
  rb : Red q b
  a_ne : a ≠ -a
  b_ne : b ≠ -b
  diff : a ≠ b
  opp : a ≠ -b

private theorem offset (o : Offsets W F) (A : pt W F) :
    ∃ (t : pt W ℚ) (s : pt W F), Red t s ∧ A ≠ s ∧ A ≠ -s ∧ s ≠ -s := by
  by_cases h : A = o.a ∨ A = -o.a
  · refine ⟨o.q,o.b,o.rb,?_,?_,o.b_ne⟩
    · rcases h with rfl|rfl
      · exact o.diff
      · exact fun h => o.opp (neg_eq_iff_eq_neg.mp h)
    · rcases h with rfl|rfl
      · exact o.opp
      · exact fun h => o.diff (neg_inj.mp h)
  · exact ⟨o.p,o.a,o.ra,fun e => h (.inl e),fun e => h (.inr e),o.a_ne⟩

theorem add (o : Offsets W F) {P Q : pt W ℚ} {A B : pt W F}
    (hp : Red P A) (hq : Red Q B) : Red (P+Q) (A+B) := by
  by_cases h : A = B
  · subst B
    obtain ⟨t,s,ht,h₁,h₂,h₃⟩ := offset o A
    have r := add_ne (add_ne hp ht h₁) (add_ne hq (neg ht) h₂)
      (fun e => h₃ (add_left_cancel e))
    convert r using 1 <;> abel
  · exact add_ne hp hq h

theorem smul (o : Offsets W F) {P : pt W ℚ} {A : pt W F} (hp : Red P A) (n : ℤ) :
    Red (n • P) (n • A) := by
  have nat (m : ℕ) : Red (m • P) (m • A) := by
    induction m with
    | zero => simpa using (zero (W:=W) (F:=F))
    | succ m ih => simpa only [succ_nsmul] using add o ih hp
  cases n with
  | ofNat n => simpa using nat n
  | negSucc n => simpa using neg (nat (n+1))

theorem total (o : Offsets W F) {ι : Type*} [Fintype ι] (P : ι → pt W ℚ) (A : ι → pt W F)
    (red : ∀ i, Red (P i) (A i)) (m : ι → ℤ) (eqn : ∑ i,m i • P i = 0) :
    ∑ i,m i • A i = 0 := by
  classical
  have go (s : Finset ι) : Red (∑ i ∈ s,m i • P i) (∑ i ∈ s,m i • A i) := by
    induction s using Finset.induction_on with
    | empty => simpa using (zero (W:=W) (F:=F))
    | insert a s ha ih => simpa [Finset.sum_insert,ha] using add o (smul o (red a) (m a)) ih
  exact unique (eqn ▸ go Finset.univ) zero

end OMA.Red829

/- A finite, kernel-computable scalar-multiplication chart for projective curve points. -/
namespace OMA.ECBin829
open WeierstrassCurve Projective
open scoped WeierstrassCurve.Projective

abbrev Code (F : Type*) := Option (F × F)
variable {F : Type*} [Field F]

def xyz : Code F → (Fin 3 → F)
  | none => ![0,1,0]
  | some (x,y) => ![x,y,1]

def chart [DecidableEq F] (v : Fin 3 → F) : Code F :=
  if v 2 = 0 then none else some (v 0/v 2, v 1/v 2)

theorem chart_eq [DecidableEq F] {W : Projective F} {v : Fin 3 → F} (h : W.Nonsingular v) :
    v ≈ xyz (chart v) := by
  unfold chart
  split
  next eqn => exact equiv_zero_of_Z_eq_zero h eqn
  next ne => exact equiv_some_of_Z_ne_zero ne

theorem code_inj {c d : Code F} (h : xyz c ≈ xyz d) : c = d := by
  rcases c with _ | ⟨x,y⟩ <;> rcases d with _ | ⟨u,v⟩
  · rfl
  · exact False.elim (not_equiv_of_Z_eq_zero_left (P:=xyz none) (Q:=xyz (some (u,v))) rfl one_ne_zero h)
  · exact False.elim (not_equiv_of_Z_eq_zero_right (P:=xyz (some (x,y))) (Q:=xyz none) one_ne_zero rfl h)
  · have h' := (equiv_iff_eq_of_Z_eq (P:=xyz (some (x,y))) (Q:=xyz (some (u,v))) rfl one_ne_zero).mp h
    exact congrArg some (Prod.ext (congrFun h' 0) (congrFun h' 1))

def Rep {W : Projective F} (P : W.Point) (c : Code F) := P.point = ⟦xyz c⟧

theorem rep_zero (W : Projective F) : Rep (0 : W.Point) none := rfl

theorem rep_chart [DecidableEq F] {W : Projective F} {P : W.Point} {v : Fin 3 → F}
    (h : P.point = ⟦v⟧) : Rep P (chart v) :=
  h.trans (Quotient.sound (chart_eq ((nonsingularLift_iff _).mp (h ▸ P.nonsingular))))

theorem rep_neg [DecidableEq F] {W : Projective F} {P : W.Point} {c : Code F}
    (hp : Rep P c) : Rep (-P) (chart (W.neg (xyz c))) := by
  apply rep_chart
  rw [Point.neg_point,hp,negMap_eq]

lemma rep_inj {W : Projective F} {P Q : W.Point} {c d : Code F}
    (hp : Rep P c) (hq : Rep Q d) : P = Q ↔ c = d := by
  constructor
  · rintro rfl; exact code_inj (Quotient.eq.mp (hp.symm.trans hq))
  · rintro rfl; exact Point.ext (hp.trans hq.symm)

noncomputable def step [DecidableEq F] (W : Projective F) (c d : Code F) : Code F :=
  chart (if c=d then W.dblXYZ (xyz c) else W.addXYZ (xyz c) (xyz d))

theorem rep_step [DecidableEq F] {W : Projective F} {P Q : W.Point} {c d : Code F}
    (hp : Rep P c) (hq : Rep Q d) : Rep (P+Q) (step W c d) := by
  let v := if c=d then W.dblXYZ (xyz c) else W.addXYZ (xyz c) (xyz d)
  have hh : (P+Q).point = ⟦v⟧ := by
    rw [Point.add_point,hp,hq,addMap_eq]
    by_cases e : c=d
    · subst d
      simp only [v,if_true]; rw [add_self]
    · simp only [v,if_neg e]
      rw [add_of_not_equiv (fun eqn => e (code_inj eqn))]
  have ns := (nonsingularLift_iff _).mp (hh ▸ (P+Q).nonsingular)
  exact hh.trans (Quotient.sound (chart_eq ns))

def number : List Bool → ℕ
  | [] => 0
  | b::l => 2 * number l + if b then 1 else 0

noncomputable def times [DecidableEq F] (W : Projective F) (c : Code F) : List Bool → Code F
  | [] => none
  | b::l =>
    let u := times W c l
    let v := step W u u
    if b then step W v c else v

theorem rep_times [DecidableEq F] {W : Projective F} {P : W.Point} {c : Code F}
    (hp : Rep P c) (l : List Bool) : Rep (number l • P) (times W c l) := by
  induction l with
  | nil => simp only [number,times,zero_nsmul]; rfl
  | cons b l ih =>
    cases b
    · simpa only [number,times,Bool.false_eq_true,if_false,add_zero,mul_nsmul,two_nsmul,nsmul_add] using rep_step ih ih
    · simpa only [number,times,if_true,add_nsmul,one_nsmul,mul_nsmul,two_nsmul,nsmul_add] using rep_step (rep_step ih ih) hp

end OMA.ECBin829

/- The eleven rational points of Elkies and Rogers (arXiv:math/0403116, page 10),
on the short model X=4x, Y=8y+4. The primes and parity tests below were computed independently. -/
namespace OMA.Elkies829
open WeierstrassCurve Projective Red829 ECBin829
open scoped WeierstrassCurve.Projective

def k : ℤ := 13293998056584952174157235
def W : Projective ℤ := ⟨0,0,0,0,16*k^2⟩
abbrev Wf (F : Type*) [Field F] := W.map (Int.castRingHom F)
def v : Fin 11 → Fin 3 → ℤ := ![
  ![-120624009114599280,32750397449019677848206540,1],
  ![45456348408270240,54051934980578901525010740,1],
  ![-83343155086767576,47421280049901405707809932,1],
  ![4537059682279957560,9664253486630600945771824140,1],
  ![35630260838764707336,212680913069246095125328519284,1],
  ![447396799544485336,303941396839211550156567284,1],
  ![46899494086672080,54137274773077725376275660,1],
  ![-138658831412368575,12719819443574268333325815,1],
  ![663884243606088960,543534311011222532617111860,1],
  ![3979072871187960,53176584602621297951728140,1],
  ![1065792702118872450,576457310785324883248677855,8]]
def prime : Fin 11 → ℕ := ![29,41,47,53,71,83,89,101,107,131,149]
instance (j : Fin 11) : Fact (prime j).Prime := ⟨by fin_cases j <;> decide⟩
abbrev K (j : Fin 11) := ZMod (prime j)
def root : Fin 11 → ℕ := ![22,31,33,25,52,79,34,33,95,6,80]
def bits : Fin 11 → List Bool := ![[true,true,true,true], [true,false,true,false,true], [false,false,false,true,true], [true,true,false,true,true], [false,false,true,false,false,true], [false,true,false,true,false,true], [true,false,true,true,false,true], [true,true,false,false,true,true], [false,true,true,false,true,true], [false,true,false,false,false,false,true], [true,true,false,true,false,false,true]]
def entry : Fin 11 → Fin 11 → Bool := ![
  ![true,true,true,true,false,false,true,false,true,false,false],
  ![true,true,true,false,false,false,false,false,true,true,false],
  ![false,false,false,false,true,false,true,true,false,false,true],
  ![true,false,true,false,false,false,true,true,false,false,false],
  ![true,true,true,true,true,true,true,true,false,false,false],
  ![false,false,false,false,false,true,true,false,true,true,false],
  ![true,false,true,false,false,false,false,false,true,false,false],
  ![true,false,false,true,true,false,true,false,false,true,true],
  ![false,false,false,true,true,true,true,false,true,false,false],
  ![true,false,true,false,false,false,true,true,false,false,true],
  ![true,false,false,true,false,true,false,true,true,true,true]]

abbrev Valid {F : Type*} [Field F] (w : Fin 3 → F) :=
  w 1^2 * w 2 = w 0^3 + ((16*k^2:ℤ):F)*w 2^3 ∧ (3*w 0^2 ≠ 0 ∨ 2*w 1*w 2 ≠ 0)

theorem valid_ns {F : Type*} [Field F] {w : Fin 3 → F} (h : Valid w) : (Wf F).Nonsingular w := by
  rw [nonsingular_iff, equation_iff]
  simp [Valid,Wf,W,WeierstrassCurve.map,sub_eq_zero] at *
  exact ⟨h.1, h.2.imp_right Or.inl⟩

theorem goodQ : ∀ i : Fin 11, Valid (image ℚ (v i)) := by decide +kernel
theorem goodK : ∀ (j i : Fin 11), Valid (image (K j) (v i)) := by decide

def points (i : Fin 11) : (Wf ℚ).Point :=
  ⟨(nonsingularLift_iff _).mpr (valid_ns (goodQ i))⟩

def localPt (j i : Fin 11) : (Wf (K j)).Point :=
  ⟨(nonsingularLift_iff _).mpr (valid_ns (goodK j i))⟩

theorem red (j i : Fin 11) : Red (points i) (localPt j i) := ⟨v i, rfl, rfl⟩

def code (j i : Fin 11) : Code (K j) := chart (image (K j) (v i))
theorem rep (j i : Fin 11) : Rep (localPt j i) (code j i) := rep_chart rfl

def tcode (j : Fin 11) : Code (K j) := some (root j,0)
private theorem goodT : ∀ j : Fin 11, Valid (xyz (tcode j)) := by decide
def tors (j : Fin 11) : (Wf (K j)).Point :=
  ⟨(nonsingularLift_iff _).mpr (valid_ns (goodT j))⟩
theorem trep (j : Fin 11) : Rep (tors j) (tcode j) := rfl

private def other (j : Fin 11) : Fin 11 := if j=2 then 3 else 1

private theorem offsetChecks : ∀ j : Fin 11,
    code j 0 ≠ chart ((Wf (K j)).neg (xyz (code j 0))) ∧
    code j (other j) ≠ chart ((Wf (K j)).neg (xyz (code j (other j)))) ∧
    code j 0 ≠ code j (other j) ∧
    code j 0 ≠ chart ((Wf (K j)).neg (xyz (code j (other j)))) := by decide +kernel

def offsets (j : Fin 11) : Offsets W (K j) where
  p := points 0
  q := points (other j)
  a := localPt j 0
  b := localPt j (other j)
  ra := red j 0
  rb := red j (other j)
  a_ne := fun eqn => (offsetChecks j).1 ((rep_inj (rep j 0) (rep_neg (rep j 0))).mp eqn)
  b_ne := fun eqn => (offsetChecks j).2.1 ((rep_inj (rep j _) (rep_neg (rep j _))).mp eqn)
  diff := fun eqn => (offsetChecks j).2.2.1 ((rep_inj (rep j _) (rep j _)).mp eqn)
  opp := fun eqn => (offsetChecks j).2.2.2 ((rep_inj (rep j _) (rep_neg (rep j _))).mp eqn)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 5000000 in
private theorem table (j : Fin 11) : ∀ i : Fin 11,
    times (Wf (K j)) (code j i) (bits j) = if entry j i then tcode j else none := by
  fin_cases j <;> decide +kernel

private theorem mod_two (j i : Fin 11) :
    number (bits j) • localPt j i = if entry j i then tors j else 0 := by
  have h := table j i
  cases b : entry j i <;> simp only [b, Bool.false_eq_true, if_false, if_true] at h ⊢
  · exact (rep_inj (rep_times (rep j i) _) (rep_zero _)).mpr h
  · exact (rep_inj (rep_times (rep j i) _) (trep j)).mpr h

theorem twice_zero (j : Fin 11) : tors j + tors j = 0 := by
  have h : ∀ j : Fin 11, step (Wf (K j)) (tcode j) (tcode j) = none := by decide +kernel
  exact (rep_inj (rep_step (trep j) (trep j)) (rep_zero _)).mpr (h j)

theorem tors_ne_zero (j : Fin 11) : tors j ≠ 0 := fun e =>
  Option.some_ne_none _ ((rep_inj (trep j) (rep_zero _)).mp e)

private theorem even_mult {G : Type*} [AddCommGroup G] (T : G) (ne : T ≠ 0)
    (two : T+T=0) {z : ℤ} (h : z • T = 0) : Even z := by
  by_contra hn
  rw [Int.even_iff] at hn
  have eqn : z = 2*(z/2)+1 := by omega
  rw [eqn, add_zsmul, mul_zsmul, two_zsmul, one_zsmul, ← smul_add, two, smul_zero, zero_add] at h
  exact ne h

theorem row_even (m : Fin 11 → ℤ) (h : ∑ i,m i • points i = 0) (j : Fin 11) :
    Even (∑ i, if entry j i then m i else 0) := by
  apply even_mult (tors j) (tors_ne_zero j) (twice_zero j)
  have hr := Red829.total (offsets j) points (localPt j) (red j) m h
  calc
    _ = ∑ i,(if entry j i then m i else 0) • tors j := Finset.sum_smul ..
    _ = ∑ i,m i • number (bits j) • localPt j i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mod_two]
      cases b : entry j i <;> simp only [Bool.false_eq_true,if_true,if_false,zero_zsmul,zsmul_zero]
    _ = ∑ i,number (bits j) • (m i • localPt j i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← natCast_zsmul, ← natCast_zsmul]
      exact smul_comm ..
    _ = 0 := by rw [← Finset.smul_sum,hr,smul_zero]

end OMA.Elkies829

/- The explicit inverse of the matrix of the eleven local parity characters over 𝔽₂. -/
namespace OMA.Elkies829
open Matrix
open scoped Matrix
private def M : Matrix (Fin 11) (Fin 11) (ZMod 2) := fun j i => if entry j i then 1 else 0
private def N : Matrix (Fin 11) (Fin 11) (ZMod 2) := ![
  ![1,0,0,1,1,1,0,0,1,1,1],
  ![1,1,1,1,1,1,1,0,0,1,0],
  ![1,1,1,1,0,0,0,1,0,0,0],
  ![1,1,1,1,0,1,0,1,0,1,1],
  ![0,1,0,0,1,1,0,1,1,0,1],
  ![0,1,0,1,1,1,1,0,1,0,0],
  ![1,0,0,0,1,0,0,1,0,0,1],
  ![1,1,1,1,0,1,0,0,1,1,0],
  ![0,1,1,0,1,1,1,1,1,1,1],
  ![1,0,1,1,1,1,0,0,0,1,0],
  ![0,0,0,1,0,0,0,0,0,1,0]]

set_option maxHeartbeats 2000000 in
private theorem left_inverse : N * M = 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem parity (m : Fin 11 → ℤ) (h : ∑ i,m i • points i = 0) : ∀ i, Even (m i) := by
  let z : Fin 11 → ZMod 2 := fun i => (m i : ZMod 2)
  have hz : M *ᵥ z = 0 := by
    funext j
    have hr := (row_even m h j).intCast_zmod_two
    push_cast at hr
    change (∑ i, M j i * z i) = 0
    convert hr using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [M,z]
    split <;> simp_all
  have hz' : z = 0 := calc
    z = (N*M) *ᵥ z := by rw [left_inverse,one_mulVec]
    _ = N *ᵥ (M *ᵥ z) := (mulVec_mulVec ..).symm
    _ = 0 := by rw [hz,mulVec_zero]
  intro i
  exact ZMod.intCast_eq_zero_iff_even.mp (congrFun hz' i)

end OMA.Elkies829

/- Descent on one nonzero coefficient detects integer independence from parity. -/
namespace OMA.Parity829

theorem independent {ι G : Type*} [Fintype ι] [AddCommGroup G] (P : ι → G)
    (noTwo : ∀ z : G, (2:ℤ) • z = 0 → z=0)
    (par : ∀ m : ι → ℤ, (∑ i, m i • P i) = 0 → ∀ i, Even (m i)) :
    Function.Injective (fun n : ι → ℕ => ∑ i,n i • P i) := by
  classical
  have vanish (j : ι) (n : ℕ) : ∀ m : ι → ℤ, (m j).natAbs = n →
      (∑ i,m i • P i) = 0 → m j = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m size rel
      by_contra nz
      choose w hw using par m rel
      have hw' (i : ι) : m i=2*w i := by linarith [hw i]
      have rr : (2:ℤ) • (∑ i,w i • P i) = 0 := by
        rw [Finset.smul_sum]
        simpa only [hw',mul_smul] using rel
      have lt : (w j).natAbs < n := by
        rw [←size,hw',Int.natAbs_mul]
        have : w j ≠ 0 := fun e => nz (by rw [hw', e, mul_zero])
        have := Int.natAbs_pos.mpr this
        change (w j).natAbs < 2*(w j).natAbs
        omega
      have zero := ih (w j).natAbs lt w rfl (noTwo _ rr)
      exact nz (by rw [hw',zero,mul_zero])
  intro a b eqn
  let m (i : ι) : ℤ := (a i : ℤ)-b i
  have rel : (∑ i,m i • P i)=0 := by
    simp [m,sub_smul,Finset.sum_sub_distrib,eqn]
  funext i
  have hv := vanish i (m i).natAbs m rfl rel
  dsimp only [m] at hv
  omega

end OMA.Parity829

/- A point of order two on the short Elkies–Rogers model would have Y=0.
For odd k, the 2-adic valuation of 16k² is four, so its negative is not a rational cube. -/
namespace OMA.NoTwo829
open WeierstrassCurve Projective

abbrev model (c:ℕ) : Projective ℤ := ⟨0,0,0,0,16*(c:ℤ)^2⟩
abbrev Q (c:ℕ) := (model c).map (Int.castRingHom ℚ)

private theorem not_cube {c:ℕ} (odd:¬2 ∣ c) (x:ℚ) : x^3 ≠ -(16*(c:ℚ)^2) := by
  intro eq
  have cn : c≠0 := fun h => odd (h ▸ dvd_zero 2)
  have cq : (c:ℚ)≠0 := by exact_mod_cast cn
  have v0 : padicValRat 2 (c:ℚ)=0 := by rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd odd];rfl
  have v1 : padicValRat 2 (2:ℚ)=1 := padicValRat.self (by decide : 1<2)
  have v := congrArg (padicValRat 2) eq
  rw [padicValRat.pow,padicValRat.neg,padicValRat.mul (by norm_num) (pow_ne_zero _ cq),
    show (16:ℚ)=2^4 by norm_num,padicValRat.pow,padicValRat.pow,v0,v1] at v
  omega

private theorem affine {c:ℕ} (hc:¬2 ∣ c) (z:(Q c).toAffine.Point)
    (hz:(2:ℤ) • z=0) : z=0 := by
  cases z with
  | zero => rfl
  | some x y h =>
    have eq : (Affine.Point.some x y h) = -(Affine.Point.some x y h) :=
      eq_neg_of_add_eq_zero_left (by simpa only [two_zsmul] using hz)
    rw [Affine.Point.neg_some,Affine.Point.some.injEq] at eq
    have yy := eq.2
    simp [Affine.negY,Q,model,WeierstrassCurve.map] at yy
    have e := (Affine.equation_iff' ..).mp h.1
    simp [Q,model,WeierstrassCurve.map] at e
    rw [show y=0 by linarith only [yy]] at e
    exact ((not_cube hc x) (by linear_combination -e)).elim

theorem no_two {c:ℕ} (hc:¬2 ∣ c) (z:(Q c).Point) (hz:(2:ℤ) • z=0) : z=0 := by
  let e := Projective.Point.toAffineAddEquiv (Q c)
  apply e.injective
  rw [map_zero]
  exact affine hc (e z) (by rw [←map_zsmul,hz,map_zero])

theorem elkies (z:(Q StewMap829.k).Point) (hz:(2:ℤ) • z=0) : z=0 :=
  no_two (by decide) z hz

end OMA.NoTwo829

/- Independence of the eleven explicit points on the Elkies–Rogers model. -/
namespace OMA.Elkies829

theorem independent : Function.Injective (fun n : Fin 11 → ℕ => ∑ i,n i • points i) :=
  Parity829.independent points NoTwo829.elkies parity

end OMA.Elkies829

/- A rank-eleven box on the short integral curve supplies enough distinct
nonnegative rational cube pairs even after both finite-to-one maps. -/
namespace OMA.StewBridge829
open StewMap829 StewSelect829 Isogeny829 HeightArith829

theorem finish (d : ℕ) (dpos : 0<d)
    (source : ∃ B : ℕ, 2 ≤ B ∧ ∀ N : ℕ, 0<N →
      ∃ p : (Fin 11 → Fin N) → Pair, Function.Injective p ∧
        ∀ i, Source (p i) ∧ H (p i).1 ≤ B^(N^2) ∧ H (p i).2 ≤ B^(N^2))
    (bounds : ∀ {T : ℕ}, 2≤T → ∀ {p : Pair}, H p.1≤T → H p.2≤T →
      (output p).1.den≤T^d ∧ (output p).2.den≤T^d) :
    type_of% @Erdos829.variants.stewart := by
  classical
  obtain ⟨B,b,src⟩ := source
  refine CountStewart829.lower (B^(4*512*d)) ((Nat.le_pow (by positivity)).trans' b) ?_
  intro N hN
  obtain ⟨p,inj,P⟩ := src (2*N) (by omega)
  let S := Finset.univ.image p
  have ss : S.card=(2*N)^11 := by
    rw [show S=Finset.univ.image p by rfl, Finset.card_image_of_injective _ inj]
    simp
  have pts (t) (ht : t∈S) : Source t ∧ H t.1≤B^((2*N)^2) ∧ H t.2≤B^((2*N)^2) := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
    exact P i
  let mid := (S.filter (fun t => t.1≠0)).image phi
  have midCount : S.card≤2+6*mid.card := image_bound S (fun t h => (pts t h).1)
  have mdata (z) (hz : z∈mid) : On z ∧ H z.1≤(B^((2*N)^2))^512 ∧ H z.2≤(B^((2*N)^2))^512 := by
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ts,hx⟩ := Finset.mem_filter.mp ht
    have good := pts t ts
    exact ⟨on good.1 hx,height ((Nat.le_pow (by positivity)).trans' b) good.2.1 good.2.2⟩
  let vals := mid.image output
  let f (i : ↥mid) : (Bool × Fin 3) × ↥vals :=
    (tag i.val,⟨output i.val,Finset.mem_image_of_mem _ i.property⟩)
  have fi : Function.Injective f := by
    intro i j eqn
    apply Subtype.ext
    exact unique (mdata _ i.property).1 (mdata _ j.property).1
      (congrArg Prod.fst eqn) (congrArg (fun v : (Bool × Fin 3) × ↥vals => v.2.val) eqn)
  have bound := Fintype.card_le_of_injective f fi
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Fintype.card_coe] at bound
  have enough : N^11 ≤ Fintype.card ↥vals := by
    rw [Fintype.card_coe]
    rw [ss,mul_pow] at midCount
    norm_num1 at midCount
    have pos : 0<N^11 := by positivity
    omega
  let e : Fin (N^11) ↪ ↥vals := (Fin.castLEEmb enough).trans (Fintype.equivFin ↥vals).symm.toEmbedding
  refine ⟨fun i => (e i).val,Subtype.val_injective.comp e.injective,?_⟩
  intro i
  obtain ⟨z,hz,eqn⟩ := Finset.mem_image.mp (e i).property
  change output z=(e i).val at eqn
  dsimp only
  rw [←eqn]
  have data := mdata z hz
  have hc := output_correct data.1
  have bt : 2 ≤ B^((2*N)^2) := (Nat.le_pow (by positivity)).trans' b
  have bt' : 2 ≤ (B^((2*N)^2))^512 := (Nat.le_pow (by norm_num)).trans' bt
  have hh := bounds bt' data.2.1 data.2.2
  have poweq : ((B^((2*N)^2))^512)^d = (B^(4*512*d))^(N^2) := by
    simp only [←pow_mul]; congr 1; ring
  rw [poweq] at hh
  exact ⟨hc.1,hc.2.1,hc.2.2,hh⟩

end OMA.StewBridge829

/- Assemble the eleven independent points, the rational height estimate, the
positive real-locus covering, and denominator scaling. -/
namespace OMA

theorem stewart829 : type_of% @Erdos829.variants.stewart := by
  refine StewBridge829.finish 2304 (by decide) ?_ (by
    intro T hT p hx hy
    exact StewHeightMap829.bound hT hx hy)
  obtain ⟨B,b,s⟩ := StewartHeight829.points (by decide : 0<11) Elkies829.W
    Elkies829.points Elkies829.independent
  refine ⟨B,b,?_⟩
  intro N hN
  obtain ⟨p,inj,data⟩ := s N hN
  refine ⟨p,inj,fun i => ⟨?_,(data i).2⟩⟩
  have eqn := (WeierstrassCurve.Affine.equation_iff' ..).mp (data i).1
  norm_num [StewartHeight829.liftCurve,Elkies829.W,Elkies829.k,
    WeierstrassCurve.map] at eqn
  unfold Isogeny829.Source StewMap829.k
  norm_num
  linarith

end OMA

theorem OMA.solution : type_of% @Erdos829.variants.stewart := OMA.stewart829
