import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H1_R2

/-!
For a prime power p^a the ratio of the ordinary to the unitary divisor sum is
(p^(a+1)-1)/((p-1)*(p^a+1)). The product of four such ratios would have to be
two. The limiting ratios force the first prime to be 3, the second 5 or 7,
and the third below 37. A finite tree of rational intervals then separates
the product from two, including the unbounded fourth prime and all exponent
tails. Each split covers its parent interval and the kernel checks each leaf.

The unitary-product argument and the one-prime rational estimates build on the
reductions of PanPapag and desenyon.
-/
open OeisA63880
open scoped ArithmeticFunction.sigma
open OMA.R_OeisA63880_mod_216_of_a_R1_H1_R2 (odd_triple_exclusion)

namespace FourPrimeRatios

private def ratio (p : ℕ) (x : ℚ) : ℚ :=
  ((p:ℚ)*x-1)/(((p:ℚ)-1)*(x+1))

private def value (p a : ℕ) := ratio p ((p:ℚ)^a)
private def limit (p : ℕ) : ℚ := p / ((p:ℚ)-1)

private theorem ratio_mono {p : ℕ} (hp : 2 ≤ p) {x y : ℚ}
    (hx : 0 ≤ x) (hxy : x ≤ y) : ratio p x ≤ ratio p y := by
  have h : (2:ℚ) ≤ p := by exact_mod_cast hp
  have hy : 0 ≤ y := hx.trans hxy
  unfold ratio
  apply (div_le_div_iff₀ (mul_pos (by linarith) (by linarith))
    (mul_pos (by linarith) (by linarith))).2
  nlinarith only [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ (p:ℚ)^2-1 by nlinarith)]

private theorem ratio_upper {p : ℕ} (hp : 2 ≤ p) {x : ℚ} (hx : 0 ≤ x) :
    ratio p x ≤ (p:ℚ)/(p-1) := by
  have h : (2:ℚ) ≤ p := by exact_mod_cast hp
  unfold ratio
  apply (div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) (by linarith)).2
  nlinarith

private theorem ratio_sigma {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ratio p ((p:ℚ)^a) = (σ 1 (p^a) : ℚ)/((p:ℚ)^a+1) := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  change p = k+1 at hk
  have hg := geom_sum_mul_add k (a+1)
  rw [← hk, ← ArithmeticFunction.sigma_one_apply_prime_pow hp, pow_succ] at hg
  have he : (σ 1 (p^a):ℚ) * k + 1 = (p:ℚ)^a*p := by exact_mod_cast hg
  have hl : (2:ℚ) ≤ p := by exact_mod_cast hp.two_le
  have hk' : (p:ℚ) = k+1 := by exact_mod_cast hk
  have hx : 0 < (p:ℚ)^a+1 := by positivity
  unfold ratio
  rw [div_mul_eq_div_div, div_left_inj' hx.ne']
  apply (div_eq_iff (by linarith : (p:ℚ)-1 ≠ 0)).2
  have hk2 : (p:ℚ)-1 = k := by linarith
  rw [hk2]
  linarith


private theorem value_mono {p a b : ℕ} (hp : 2 ≤ p) (hab : a ≤ b) :
    value p a ≤ value p b := by
  apply ratio_mono hp (by positivity)
  apply pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ p by omega)) hab

private theorem value_limit {p : ℕ} (hp : 2 ≤ p) (a : ℕ) : value p a ≤ limit p :=
  ratio_upper hp (by positivity)

private theorem value_nonneg {p : ℕ} (hp : 2 ≤ p) (a : ℕ) : 0 ≤ value p a := by
  have h : 2 ≤ (p:ℚ) := by exact_mod_cast hp
  have hx : 1 ≤ (p:ℚ)^a := one_le_pow₀ (by linarith)
  unfold value ratio
  apply div_nonneg _ (mul_nonneg (by linarith) (by positivity))
  nlinarith only [h,hx,mul_nonneg (show 0≤(p:ℚ)-1 by linarith) (show 0≤(p:ℚ)^a-1 by linarith)]

private theorem one_le_value {p a : ℕ} (hp : 2 ≤ p) (ha : 1 ≤ a) : 1 ≤ value p a := by
  have h : 2 ≤ (p:ℚ) := by exact_mod_cast hp
  have he : value p 1 = 1 := by
    unfold value ratio
    rw [pow_one,div_eq_iff (mul_ne_zero (by linarith) (by linarith))]
    ring
  exact he ▸ value_mono hp ha

private theorem limit_anti {j p : ℕ} (hj : 2 ≤ j) (hjp : j ≤ p) : limit p ≤ limit j := by
  have hj' : 2 ≤ (j:ℚ) := by exact_mod_cast hj
  have hp' : (j:ℚ) ≤ p := by exact_mod_cast hjp
  unfold limit
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  linarith

private theorem exponent_two_lower {s a u : ℕ} (hs : 2 ≤ s) (hu : s ≤ u) (ha : 2 ≤ a) :
    ((u:ℚ)+2)/(u+1) ≤ value s a := by
  apply le_trans _ (value_mono hs ha)
  have hs' : 2 ≤ (s:ℚ) := by exact_mod_cast hs
  have hu' : (s:ℚ) ≤ u := by exact_mod_cast hu
  have mono : ((u:ℚ)+2)/(u+1) ≤ ((s:ℚ)+2)/(s+1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).2
    linarith
  apply mono.trans
  unfold value ratio
  apply (div_le_div_iff₀ (by linarith) (mul_pos (by linarith) (by positivity))).2
  nlinarith only [sq_nonneg ((s:ℚ)-1)]

/-- An upper endpoint of zero denotes an unbounded interval. -/
private structure Interval where
  lo : ℕ
  hi : ℕ

private def Interval.contains (b : Interval) (x : ℕ) : Prop :=
  b.lo ≤ x ∧ (b.hi = 0 ∨ x ≤ b.hi)

private def Interval.exact (b : Interval) : Prop := b.lo=b.hi ∧ b.hi≠0
private instance (b : Interval) : Decidable b.exact := by unfold Interval.exact; infer_instance

private def lower (p : ℕ) (b : Interval) : ℚ := value p b.lo
private def upper (p : ℕ) (b : Interval) : ℚ := if b.hi=0 then limit p else value p b.hi

private theorem bounds {p a : ℕ} {b : Interval} (hp : 2≤p) (h : b.contains a) :
    lower p b ≤ value p a ∧ value p a ≤ upper p b := by
  refine ⟨value_mono hp h.1,?_⟩
  by_cases hh : b.hi=0
  · simpa [upper,hh] using value_limit hp a
  · simpa [upper,hh] using value_mono hp (h.2.resolve_left hh)

private inductive Axis
  | a | b | c | d | s

private structure Box where
  a : Interval
  b : Interval
  c : Interval
  d : Interval
  s : Interval

private def Box.get (B : Box) : Axis → Interval
  | .a => B.a | .b => B.b | .c => B.c | .d => B.d | .s => B.s

private def Box.put (B : Box) (i : Axis) (v : Interval) : Box := match i with
  | .a => {B with a := v} | .b => {B with b := v} | .c => {B with c := v}
  | .d => {B with d := v} | .s => {B with s := v}

private def Inside (B : Box) (v : Axis → ℕ) := ∀ i, (B.get i).contains (v i)

private theorem inside_put {B : Box} {v : Axis → ℕ} (h : Inside B v) (i : Axis) (b : Interval)
    (hb : b.contains (v i)) : Inside (B.put i b) v := by
  intro j
  have hj := h j
  cases i <;> cases j <;> first | exact hb | exact hj

private def slow (B : Box) : ℚ :=
  if B.s.exact then lower B.s.lo B.d
  else if 2 ≤ B.d.lo ∧ B.s.hi ≠ 0 then ((B.s.hi:ℚ)+2)/(B.s.hi+1) else 1

private def shigh (B : Box) : ℚ :=
  if B.s.exact then upper B.s.lo B.d else limit (max 2 B.s.lo)

private theorem last_bounds {B : Box} {v : Axis → ℕ} (h : Inside B v)
    (hp : (v .s).Prime) (hd : 1 ≤ v .d) :
    slow B ≤ value (v .s) (v .d) ∧ value (v .s) (v .d) ≤ shigh B := by
  obtain ⟨sl,sh⟩ := h .s
  change B.s.lo ≤ v .s at sl
  change B.s.hi=0 ∨ v .s ≤ B.s.hi at sh
  by_cases eqn : B.s.exact
  · obtain ⟨e,hn⟩ := eqn
    have he : B.s.lo=v .s := by have := sh.resolve_left hn; omega
    simpa [slow,shigh,Interval.exact,e,hn,← he] using
      (bounds hp.two_le (h .d) : lower (v .s) B.d ≤ _ ∧ _ ≤ upper (v .s) B.d)
  · unfold slow shigh
    rw [if_neg eqn,if_neg eqn]
    refine ⟨?_,(value_limit hp.two_le _).trans (limit_anti (le_max_left _ _) (max_le hp.two_le sl))⟩
    split
    · rename_i tail
      exact exponent_two_lower hp.two_le (sh.resolve_left tail.2) (tail.1.trans (h .d).1)
    · exact one_le_value hp.two_le hd

private def cell (q r : ℕ) (B : Box) : Bool :=
  decide (B.s.exact ∧ ¬ B.s.lo.Prime) ||
  decide (2 < lower 3 B.a * lower q B.b * lower r B.c * slow B ∨
    upper 3 B.a * upper q B.b * upper r B.c * shigh B < 2)

private theorem cell_sound {q r : ℕ} (hq : 2 ≤ q) (hr : 2 ≤ r)
    {B : Box} {v : Axis → ℕ} (h : Inside B v) (hp : (v .s).Prime) (hd : 1 ≤ v .d)
    (yes : cell q r B = true) :
    value 3 (v .a) * value q (v .b) * value r (v .c) * value (v .s) (v .d) ≠ 2 := by
  intro eqn
  have ha := bounds (by decide : 2≤3) (h .a)
  have hb := bounds hq (h .b)
  have hc := bounds hr (h .c)
  have hs := last_bounds h hp hd
  have xa := value_nonneg (by decide : 2≤3) (v .a)
  have xb := value_nonneg hq (v .b)
  have xc := value_nonneg hr (v .c)
  have xs := value_nonneg hp.two_le (v .d)
  have la : 0≤lower 3 B.a := value_nonneg (by decide) _
  have lb : 0≤lower q B.b := value_nonneg hq _
  have lc : 0≤lower r B.c := value_nonneg hr _
  have ls : 0 ≤ slow B := by
    unfold slow
    split
    · rename_i ex
      obtain ⟨ll,hh⟩ := h .s
      change B.s.lo ≤ v .s at ll
      change B.s.hi=0 ∨ v .s ≤ B.s.hi at hh
      have he : B.s.lo=v .s := by have := hh.resolve_left ex.2; have := ex.1; omega
      exact value_nonneg (he ▸ hp.two_le) _
    · split <;> positivity
  rcases Bool.or_eq_true_iff.mp yes with noPrime|outside
  · obtain ⟨exactS,np⟩ := of_decide_eq_true noPrime
    have lo := (h .s).1
    have hi := (h .s).2.resolve_left exactS.2
    change B.s.lo ≤ v .s at lo
    change v .s ≤ B.s.hi at hi
    have e := exactS.1
    have he : B.s.lo=v .s := by omega
    exact np (he ▸ hp)
  · rcases of_decide_eq_true outside with low|high
    · have lowprod := mul_le_mul (mul_le_mul (mul_le_mul ha.1 hb.1 lb xa) hc.1 lc (mul_nonneg xa xb)) hs.1 ls (mul_nonneg (mul_nonneg xa xb) xc)
      exact (not_lt_of_ge (eqn ▸ lowprod)) low
    · have pa := xa.trans ha.2
      have pb := xb.trans hb.2
      have pc := xc.trans hc.2
      have hiprod := mul_le_mul (mul_le_mul (mul_le_mul ha.2 hb.2 xb pa) hc.2 xc (mul_nonneg pa pb)) hs.2 xs (mul_nonneg (mul_nonneg pa pb) pc)
      exact (not_lt_of_ge (eqn ▸ hiprod)) high

/-- The certificate checker compares unreduced fractions by cross multiplication. -/
private structure Fraction where
  num : ℕ
  den : ℕ

private def Fraction.val (f : Fraction) : ℚ := f.num / (f.den : ℚ)
private def Fraction.mul (f g : Fraction) : Fraction := ⟨f.num*g.num,f.den*g.den⟩
private def Represents (f : Fraction) (x : ℚ) : Prop := 0 < f.den ∧ f.val=x

private theorem Represents.mul {f g : Fraction} {x y : ℚ}
    (hx : Represents f x) (hy : Represents g y) : Represents (f.mul g) (x*y) := by
  refine ⟨Nat.mul_pos hx.1 hy.1,?_⟩
  rw [← hx.2,← hy.2]
  simp only [Fraction.val,Fraction.mul,Nat.cast_mul]
  ring

private def powFraction (p a : ℕ) : Fraction :=
  let x := p^a
  ⟨p*x-1,(p-1)*(x+1)⟩

private def limFraction (p : ℕ) : Fraction := ⟨p,p-1⟩

private theorem pow_rep {p : ℕ} (hp : 2 ≤ p) (a : ℕ) : Represents (powFraction p a) (value p a) := by
  have pp : 0 < p := by omega
  have hh := Nat.mul_pos pp (Nat.pow_pos pp (n:=a))
  refine ⟨Nat.mul_pos (by omega) (Nat.succ_pos _),?_⟩
  simp [powFraction,Fraction.val,value,ratio,Nat.cast_sub (show 1 ≤ p*p^a by omega),
    Nat.cast_sub (show 1 ≤ p by omega)]

private theorem lim_rep {p : ℕ} (hp : 2 ≤ p) : Represents (limFraction p) (limit p) := by
  refine ⟨by change 0 < p-1; omega,?_⟩
  simp [limFraction,Fraction.val,limit,Nat.cast_sub (show 1 ≤ p by omega)]

private def loFr (p : ℕ) (b : Interval) := powFraction p b.lo
private def hiFr (p : ℕ) (b : Interval) := if b.hi=0 then limFraction p else powFraction p b.hi

private theorem hi_rep {p : ℕ} (hp : 2≤p) (b : Interval) : Represents (hiFr p b) (upper p b) := by
  by_cases h : b.hi=0
  · simpa [hiFr,upper,h] using lim_rep hp
  · simpa [hiFr,upper,h] using pow_rep hp b.hi

private def slFr (B : Box) : Fraction :=
  if B.s.exact then loFr B.s.lo B.d
  else if 2 ≤ B.d.lo ∧ B.s.hi ≠ 0 then ⟨B.s.hi+2,B.s.hi+1⟩ else ⟨1,1⟩
private def shFr (B : Box) : Fraction :=
  if B.s.exact then hiFr B.s.lo B.d else limFraction (max 2 B.s.lo)

private theorem last_reps {B : Box} {v : Axis → ℕ} (h : Inside B v) (hp : (v .s).Prime) :
    Represents (slFr B) (slow B) ∧ Represents (shFr B) (shigh B) := by
  by_cases ex : B.s.exact
  · have ll := (h .s).1
    have hh := (h .s).2.resolve_left ex.2
    change B.s.lo ≤ v .s at ll
    change v .s ≤ B.s.hi at hh
    have e := ex.1
    have h2 : 2 ≤ B.s.lo := by have := hp.two_le; omega
    simp only [slFr,shFr,slow,shigh,if_pos ex]
    exact ⟨pow_rep h2 B.d.lo,hi_rep h2 B.d⟩
  · simp only [slFr,shFr,slow,shigh,if_neg ex]
    refine ⟨?_,lim_rep (le_max_left _ _)⟩
    split
    · exact ⟨Nat.succ_pos _,by simp [Fraction.val]⟩
    · exact ⟨by decide,by norm_num [Fraction.val]⟩

private def integerCell (q r : ℕ) (B : Box) : Bool :=
  let L := (((loFr 3 B.a).mul (loFr q B.b)).mul (loFr r B.c)).mul (slFr B)
  let U := (((hiFr 3 B.a).mul (hiFr q B.b)).mul (hiFr r B.c)).mul (shFr B)
  decide (2*L.den < L.num ∨ U.num < 2*U.den)

private theorem integer_sound {q r : ℕ} (hq : 2≤q) (hr : 2≤r)
    {B : Box} {v : Axis → ℕ} (h : Inside B v) (hp : (v .s).Prime)
    (yes : integerCell q r B=true) : cell q r B=true := by
  obtain ⟨sl,sh⟩ := last_reps h hp
  have L := (((pow_rep (by decide : 2≤3) B.a.lo).mul (pow_rep hq B.b.lo)).mul (pow_rep hr B.c.lo)).mul sl
  have U := (((hi_rep (by decide : 2≤3) B.a).mul (hi_rep hq B.b)).mul (hi_rep hr B.c)).mul sh
  apply Bool.or_eq_true_iff.mpr
  right
  apply decide_eq_true
  rcases of_decide_eq_true yes with hl|hu
  · left
    unfold lower
    rw [← L.2]
    apply (lt_div_iff₀ (by exact_mod_cast L.1)).2
    exact_mod_cast hl
  · right
    rw [← U.2]
    apply (div_lt_iff₀ (by exact_mod_cast U.1)).2
    exact_mod_cast hu

private inductive Tree
  | leaf
  | composite (factor : ℕ)
  | cut (i : Axis) (k : ℕ) (left right : Tree)

private def check (q r : ℕ) : Tree → Box → Bool
  | .leaf, B => integerCell q r B
  | .composite f, B => decide (B.s.exact ∧ 1 < f ∧ f < B.s.lo ∧ f ∣ B.s.lo)
  | .cut i k l t, B =>
    check q r l (B.put i ⟨(B.get i).lo,k⟩) &&
    check q r t (B.put i ⟨k+1,(B.get i).hi⟩)

private theorem check_sound {q r : ℕ} (hq : 2≤q) (hr : 2≤r) (t : Tree)
    (B : Box) (v : Axis → ℕ) (h : Inside B v) (hp : (v .s).Prime) (hd : 1≤v .d)
    (yes : check q r t B=true) :
    value 3 (v .a) * value q (v .b) * value r (v .c) * value (v .s) (v .d) ≠ 2 := by
  induction t generalizing B with
  | leaf => exact cell_sound hq hr h hp hd (integer_sound hq hr h hp yes)
  | composite f =>
    obtain ⟨ex,one,lt,dvd⟩ := of_decide_eq_true yes
    have ll := (h .s).1
    have hh := (h .s).2.resolve_left ex.2
    change B.s.lo ≤ v .s at ll
    change v .s ≤ B.s.hi at hh
    have e := ex.1
    have he : B.s.lo=v .s := by omega
    rw [he] at dvd lt
    rcases (Nat.dvd_prime hp).mp dvd with h1|heq <;> omega
  | cut i k l t il it =>
    obtain ⟨hl,ht⟩ := Bool.and_eq_true_iff.mp yes
    by_cases atLeft : v i ≤ k
    · exact il _ (inside_put h i ⟨(B.get i).lo,k⟩ ⟨(h i).1,Or.inr atLeft⟩) hl
    · exact it _ (inside_put h i ⟨k+1,(B.get i).hi⟩ ⟨by change k+1 ≤ v i; omega,(h i).2⟩) ht


private def initial (r : ℕ) : Box :=
  ⟨⟨1,0⟩, ⟨1,0⟩, ⟨1,0⟩, ⟨2,0⟩, ⟨r+1,0⟩⟩

private def tree_5_7_0 : Tree :=
  .cut .s 10 (.cut .a 3 (.cut .b 2 .leaf (.cut .s 8 (.composite 2) (.cut .s 9 (.composite 3) (.composite 2)))) (.cut .b 2 (.cut .s 8 (.composite 2) (.cut .s 9 (.composite 3) (.composite 2))) (.cut .s 8 (.composite 2) (.cut .s 9 (.composite 3) (.composite 2))))) (.cut .a 3 .leaf (.cut .b 2 .leaf (.cut .s 13 (.cut .s 11 (.cut .a 4 (.cut .b 3 (.cut .d 2 .leaf .leaf) .leaf) .leaf) (.cut .s 12 (.composite 2) (.cut .a 4 .leaf (.cut .b 3 (.cut .d 2 .leaf (.cut .a 5 (.cut .d 3 .leaf .leaf) .leaf)) .leaf)))) (.cut .s 14 (.composite 2) (.cut .a 4 .leaf (.cut .s 15 (.composite 3) (.composite 2)))))))

private def tree_5_7_1 : Tree :=
  .cut .s 16 (.cut .s 10 (.cut .b 2 (.cut .s 8 (.composite 2) (.cut .s 9 (.composite 3) (.composite 2))) .leaf) (.cut .b 2 .leaf (.cut .s 13 (.cut .s 11 .leaf (.cut .c 2 (.cut .s 12 (.composite 2) (.cut .b 3 .leaf (.cut .d 2 .leaf .leaf))) .leaf)) (.cut .c 2 .leaf (.cut .s 14 (.composite 2) (.cut .s 15 (.composite 3) (.composite 2))))))) (.cut .s 34 (.cut .b 2 .leaf (.cut .s 22 (.cut .c 2 .leaf (.cut .s 19 (.cut .s 17 (.cut .b 3 .leaf (.cut .d 2 (.cut .c 3 (.cut .b 4 .leaf (.cut .b 5 .leaf .leaf)) .leaf) .leaf)) (.cut .b 3 .leaf (.cut .s 18 (.composite 2) (.cut .c 3 .leaf (.cut .d 2 .leaf (.cut .b 4 .leaf (.cut .c 4 (.cut .b 5 .leaf (.cut .d 3 .leaf .leaf)) (.cut .b 5 (.cut .d 3 (.cut .c 5 .leaf .leaf) .leaf) .leaf)))))))) .leaf)) .leaf)) .leaf)

private def tree_5_7_2 : Tree :=
  .cut .s 142 (.cut .s 94 .leaf (.cut .s 113 (.cut .c 3 (.cut .s 103 (.cut .s 98 .leaf (.cut .s 100 .leaf (.cut .s 101 .leaf (.cut .s 102 (.composite 2) .leaf)))) .leaf) .leaf) (.cut .c 3 .leaf .leaf))) (.cut .s 286 (.cut .s 190 (.cut .c 3 .leaf (.cut .s 163 (.cut .s 152 (.cut .s 147 (.cut .c 4 (.cut .s 144 (.cut .s 143 (.composite 11) (.composite 2)) (.cut .s 145 (.composite 5) .leaf)) .leaf) (.cut .c 4 .leaf .leaf)) (.cut .s 157 (.cut .c 4 .leaf (.cut .s 154 (.cut .s 153 (.composite 3) (.composite 2)) (.cut .s 155 (.composite 5) (.cut .s 156 (.composite 2) .leaf)))) .leaf)) .leaf)) .leaf) .leaf)

private def tree_5_7_3 : Tree :=
  .cut .b 1 (.cut .c 1 .leaf (.cut .a 2 .leaf (.cut .s 16 (.cut .s 10 (.cut .a 3 .leaf (.cut .s 8 (.composite 2) .leaf)) .leaf) .leaf))) (.cut .c 1 (.cut .a 2 .leaf (.cut .s 16 tree_5_7_0 .leaf)) (.cut .a 2 tree_5_7_1 (.cut .s 16 .leaf (.cut .s 34 (.cut .a 3 (.cut .b 2 (.cut .s 22 .leaf (.cut .c 2 (.cut .s 27 .leaf (.cut .s 30 .leaf (.cut .s 32 .leaf (.cut .s 33 (.composite 3) (.composite 2))))) .leaf)) .leaf) .leaf) (.cut .a 3 (.cut .b 2 (.cut .s 70 (.cut .c 2 .leaf .leaf) (.cut .c 2 .leaf tree_5_7_2)) .leaf) .leaf)))))

private def tree_5_7 : Tree :=
  .cut .a 1 .leaf tree_5_7_3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem accepted_5_7 : check 5 7 tree_5_7 (initial 7) = true := by decide +kernel

private def tree_5_11_0 : Tree :=
  .cut .s 40 (.cut .b 3 (.cut .c 2 .leaf (.cut .s 36 (.cut .s 34 (.composite 2) (.cut .s 35 (.composite 5) (.composite 2))) .leaf)) (.cut .c 2 (.cut .s 36 (.cut .s 34 (.composite 2) (.cut .s 35 (.composite 5) (.composite 2))) (.cut .s 38 (.cut .s 37 (.cut .b 4 .leaf (.cut .d 2 .leaf (.cut .b 5 (.cut .d 3 .leaf .leaf) .leaf))) (.composite 2)) .leaf)) .leaf)) (.cut .b 3 .leaf (.cut .c 2 .leaf (.cut .s 45 .leaf (.cut .s 47 (.cut .b 4 (.cut .s 46 (.composite 2) .leaf) .leaf) (.cut .b 4 (.cut .s 48 (.composite 2) (.cut .s 49 (.composite 7) (.composite 2))) .leaf)))))

private def tree_5_11_1 : Tree :=
  .cut .s 50 (.cut .s 33 (.cut .s 28 (.cut .b 3 (.cut .c 2 (.cut .s 26 (.cut .s 25 (.composite 5) (.composite 2)) (.cut .s 27 (.composite 3) (.composite 2))) .leaf) .leaf) (.cut .b 3 (.cut .c 2 .leaf .leaf) .leaf)) tree_5_11_0) (.cut .s 102 (.cut .s 68 (.cut .b 3 .leaf (.cut .c 2 .leaf (.cut .s 58 (.cut .s 54 (.cut .b 4 .leaf (.cut .s 52 (.cut .s 51 (.composite 3) (.composite 2)) (.cut .s 53 (.cut .c 3 (.cut .b 5 .leaf (.cut .d 2 .leaf .leaf)) .leaf) (.composite 2)))) (.cut .b 4 .leaf (.cut .s 56 (.cut .s 55 (.composite 5) (.composite 2)) .leaf))) .leaf))) .leaf) .leaf)

private def tree_5_11_2 : Tree :=
  .cut .s 40 (.cut .c 2 (.cut .s 36 (.cut .a 5 .leaf (.cut .s 34 (.composite 2) (.cut .s 35 (.composite 5) (.composite 2)))) (.cut .a 5 .leaf (.cut .s 38 (.cut .s 37 (.cut .a 6 (.cut .d 2 .leaf .leaf) .leaf) (.composite 2)) (.cut .s 39 (.composite 3) (.composite 2))))) .leaf) (.cut .c 2 .leaf (.cut .a 5 (.cut .s 45 (.cut .s 42 .leaf (.cut .s 43 .leaf (.cut .s 44 (.composite 2) (.composite 3)))) (.cut .s 47 (.cut .s 46 (.composite 2) .leaf) .leaf)) .leaf))

private def tree_5_11_3 : Tree :=
  .cut .s 58 (.cut .s 54 (.cut .a 6 (.cut .s 52 (.cut .s 51 (.composite 3) (.composite 2)) (.cut .s 53 (.cut .c 3 .leaf .leaf) (.composite 2))) .leaf) (.cut .a 6 (.cut .s 56 (.cut .s 55 (.composite 5) (.composite 2)) .leaf) (.cut .s 56 (.cut .s 55 (.composite 5) (.composite 2)) (.cut .s 57 (.composite 3) (.composite 2))))) (.cut .s 63 (.cut .a 6 .leaf (.cut .s 60 (.cut .s 59 (.cut .c 3 .leaf (.cut .a 7 (.cut .d 2 .leaf (.cut .c 4 .leaf (.cut .c 5 .leaf (.cut .d 3 .leaf .leaf)))) .leaf)) (.composite 2)) (.cut .s 61 (.cut .c 3 .leaf (.cut .a 7 .leaf (.cut .d 2 .leaf (.cut .a 8 .leaf (.cut .c 4 .leaf (.cut .a 9 .leaf .leaf)))))) .leaf))) .leaf)

private def tree_5_11_4 : Tree :=
  .cut .b 2 (.cut .s 50 (.cut .s 33 (.cut .a 4 (.cut .s 28 (.cut .c 2 .leaf .leaf) (.cut .c 2 .leaf (.cut .s 30 (.cut .s 29 .leaf (.composite 2)) .leaf))) (.cut .s 28 .leaf (.cut .c 2 (.cut .s 30 .leaf (.cut .a 5 (.cut .s 31 .leaf (.cut .s 32 (.composite 2) (.composite 3))) .leaf)) .leaf))) (.cut .a 4 .leaf tree_5_11_2)) (.cut .s 102 (.cut .a 4 .leaf (.cut .s 68 (.cut .c 2 .leaf (.cut .a 5 .leaf tree_5_11_3)) .leaf)) .leaf)) (.cut .s 50 .leaf (.cut .s 102 .leaf (.cut .a 4 (.cut .s 206 .leaf (.cut .b 3 (.cut .c 2 (.cut .s 414 (.cut .s 276 (.cut .s 236 .leaf (.cut .s 255 (.cut .s 245 (.cut .s 240 (.cut .s 238 .leaf (.cut .s 239 .leaf (.composite 2))) .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf) .leaf)) .leaf)))

private def tree_5_11_5 : Tree :=
  .cut .s 24 (.cut .a 3 (.cut .s 16 (.cut .b 2 (.cut .s 13 (.cut .s 12 (.composite 2) (.cut .c 2 (.cut .d 2 .leaf .leaf) .leaf)) (.cut .s 14 (.composite 2) (.cut .s 15 (.composite 3) (.composite 2)))) .leaf) (.cut .b 2 .leaf .leaf)) (.cut .s 16 .leaf (.cut .b 2 (.cut .s 19 .leaf (.cut .a 4 (.cut .s 21 .leaf (.cut .c 2 (.cut .s 22 (.composite 2) (.cut .s 23 .leaf (.composite 2))) .leaf)) .leaf)) .leaf))) (.cut .a 3 (.cut .b 2 .leaf tree_5_11_1) tree_5_11_4)

private def tree_5_11 : Tree :=
  .cut .a 1 .leaf (.cut .b 1 .leaf (.cut .a 2 .leaf (.cut .c 1 (.cut .s 24 (.cut .a 3 .leaf (.cut .s 16 (.cut .b 2 .leaf (.cut .s 13 (.cut .s 12 (.composite 2) (.cut .a 4 .leaf (.cut .b 3 (.cut .d 2 .leaf (.cut .a 5 (.cut .d 3 .leaf .leaf) .leaf)) .leaf))) (.cut .s 14 (.composite 2) (.cut .a 4 .leaf (.cut .s 15 (.composite 3) (.composite 2)))))) .leaf)) .leaf) tree_5_11_5)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem accepted_5_11 : check 5 11 tree_5_11 (initial 11) = true := by decide +kernel

private def tree_5_13_0 : Tree :=
  .cut .b 2 .leaf (.cut .s 18 .leaf (.cut .s 22 (.cut .s 20 (.cut .b 3 (.cut .s 19 .leaf (.composite 2)) .leaf) (.cut .b 3 (.cut .c 2 .leaf (.cut .s 21 (.composite 3) (.composite 2))) .leaf)) (.cut .s 25 (.cut .b 3 (.cut .s 23 (.cut .c 2 .leaf (.cut .d 2 .leaf .leaf)) .leaf) (.cut .s 23 .leaf (.cut .c 2 (.cut .s 24 (.composite 2) (.composite 5)) .leaf))) (.cut .b 3 .leaf (.cut .c 2 .leaf (.cut .s 26 (.composite 2) (.cut .s 27 (.composite 3) (.composite 2))))))))

private def tree_5_13_1 : Tree :=
  .cut .s 22 (.cut .a 4 (.cut .s 20 (.cut .s 19 (.cut .c 2 .leaf .leaf) (.composite 2)) (.cut .c 2 .leaf (.cut .s 21 (.composite 3) (.composite 2)))) (.cut .s 20 .leaf (.cut .c 2 (.cut .s 21 (.composite 3) (.composite 2)) .leaf))) (.cut .a 4 .leaf (.cut .s 25 (.cut .s 23 (.cut .c 2 (.cut .a 5 (.cut .d 2 .leaf .leaf) .leaf) .leaf) (.cut .c 2 (.cut .a 5 .leaf (.cut .s 24 (.composite 2) (.composite 5))) .leaf)) (.cut .c 2 (.cut .a 5 .leaf (.cut .s 26 (.composite 2) .leaf)) (.cut .a 5 (.cut .s 26 (.composite 2) (.cut .s 27 (.composite 3) (.composite 2))) (.cut .s 26 (.composite 2) (.cut .s 27 (.composite 3) (.composite 2)))))))

private def tree_5_13_2 : Tree :=
  .cut .s 78 (.cut .c 2 (.cut .s 67 (.cut .s 62 (.cut .s 60 (.cut .s 59 (.cut .d 2 .leaf .leaf) (.composite 2)) .leaf) .leaf) .leaf) .leaf) (.cut .c 2 .leaf (.cut .s 94 (.cut .s 85 .leaf (.cut .s 89 .leaf (.cut .s 91 (.cut .c 3 (.cut .s 90 (.composite 2) (.composite 7)) .leaf) (.cut .c 3 .leaf (.cut .s 92 (.composite 2) (.cut .s 93 (.composite 3) (.composite 2))))))) (.cut .s 105 (.cut .s 99 (.cut .s 96 (.cut .c 3 .leaf (.cut .s 95 (.composite 5) (.composite 2))) .leaf) .leaf) .leaf)))

private def tree_5_13_3 : Tree :=
  .cut .s 158 (.cut .s 135 (.cut .b 4 .leaf (.cut .s 126 .leaf (.cut .s 130 (.cut .b 5 (.cut .s 128 .leaf (.cut .s 129 (.composite 3) (.composite 2))) .leaf) (.cut .b 5 (.cut .s 132 (.cut .s 131 (.cut .d 2 .leaf .leaf) (.composite 2)) .leaf) .leaf)))) (.cut .b 4 .leaf (.cut .s 146 (.cut .s 140 (.cut .b 5 .leaf (.cut .s 137 (.cut .s 136 (.composite 2) (.cut .b 6 (.cut .d 2 .leaf .leaf) .leaf)) (.cut .s 138 (.composite 2) .leaf))) .leaf) .leaf))) .leaf

private def tree_5_13_4 : Tree :=
  .cut .s 318 (.cut .b 4 (.cut .s 272 .leaf (.cut .s 293 .leaf (.cut .c 3 (.cut .s 305 (.cut .s 299 .leaf (.cut .s 302 (.cut .s 300 (.composite 2) (.cut .s 301 (.composite 7) (.composite 2))) (.cut .s 303 (.composite 3) .leaf))) .leaf) .leaf))) .leaf) (.cut .b 4 (.cut .s 382 (.cut .s 347 (.cut .c 3 .leaf .leaf) (.cut .c 3 .leaf (.cut .s 364 (.cut .s 355 (.cut .s 351 (.cut .s 349 .leaf (.cut .c 4 (.cut .s 350 (.composite 2) (.composite 3)) .leaf)) (.cut .s 353 (.cut .c 4 .leaf .leaf) (.cut .c 4 .leaf (.cut .s 354 (.composite 2) (.composite 5))))) (.cut .s 359 (.cut .s 357 (.cut .c 4 .leaf (.cut .s 356 (.composite 2) (.composite 3))) .leaf) .leaf)) .leaf))) .leaf) .leaf)

private def tree_5_13_5 : Tree :=
  .cut .s 729 (.cut .b 6 .leaf (.cut .s 712 .leaf (.cut .s 720 (.cut .s 716 (.cut .b 7 (.cut .s 714 .leaf (.cut .s 715 (.composite 5) (.composite 2))) .leaf) (.cut .b 7 (.cut .s 718 (.cut .s 717 (.composite 3) (.composite 2)) .leaf) .leaf)) (.cut .s 724 (.cut .b 7 .leaf (.cut .s 722 (.cut .s 721 (.composite 7) (.composite 2)) (.cut .s 723 (.composite 3) (.composite 2)))) (.cut .b 7 .leaf (.cut .s 726 (.cut .s 725 (.composite 5) (.composite 2)) .leaf)))))) .leaf

private def tree_5_13_6 : Tree :=
  .cut .c 3 (.cut .b 5 .leaf (.cut .s 696 (.cut .s 666 .leaf (.cut .b 6 (.cut .s 681 .leaf (.cut .s 688 (.cut .s 684 .leaf (.cut .s 686 (.cut .s 685 (.composite 5) (.composite 2)) (.cut .s 687 (.composite 3) (.composite 2)))) .leaf)) .leaf)) tree_5_13_5)) (.cut .b 5 (.cut .s 696 .leaf (.cut .s 729 .leaf (.cut .s 747 .leaf (.cut .c 4 (.cut .s 756 .leaf (.cut .s 761 .leaf (.cut .s 763 (.cut .s 762 (.composite 2) (.composite 7)) .leaf))) .leaf)))) .leaf)

private def tree_5_13_7 : Tree :=
  .cut .s 638 (.cut .s 547 .leaf (.cut .c 3 (.cut .b 5 (.cut .s 589 (.cut .s 567 (.cut .s 557 .leaf (.cut .s 562 .leaf (.cut .s 564 .leaf (.cut .s 565 (.composite 5) (.cut .s 566 (.composite 2) (.composite 3)))))) .leaf) .leaf) .leaf) .leaf)) (.cut .s 766 tree_5_13_6 (.cut .c 3 .leaf (.cut .b 5 (.cut .s 851 (.cut .s 806 (.cut .s 786 (.cut .c 4 .leaf (.cut .s 776 .leaf (.cut .s 781 .leaf (.cut .s 783 (.cut .s 782 (.composite 2) (.composite 3)) (.cut .s 784 (.composite 2) (.cut .s 785 (.composite 5) (.composite 2))))))) .leaf) .leaf) .leaf) .leaf)))

private def tree_5_13_8 : Tree :=
  .cut .c 4 (.cut .s 1076 (.cut .s 1066 (.cut .b 7 (.cut .s 1061 (.cut .s 1059 .leaf (.cut .s 1060 (.composite 2) (.cut .d 2 .leaf .leaf))) .leaf) .leaf) (.cut .b 7 .leaf (.cut .s 1071 .leaf (.cut .s 1073 .leaf (.cut .s 1074 (.composite 2) (.cut .b 8 (.cut .s 1075 (.composite 5) (.composite 2)) .leaf)))))) (.cut .s 1085 (.cut .b 7 .leaf (.cut .s 1080 (.cut .s 1078 (.cut .b 8 .leaf (.cut .s 1077 (.composite 3) (.composite 2))) .leaf) .leaf)) .leaf)) .leaf

private def tree_5_13_9 : Tree :=
  .cut .s 1022 (.cut .b 6 (.cut .s 989 .leaf (.cut .c 4 (.cut .s 1005 (.cut .s 997 (.cut .s 993 .leaf (.cut .s 995 (.cut .s 994 (.composite 2) (.composite 5)) (.cut .s 996 (.composite 2) .leaf))) .leaf) .leaf) .leaf)) .leaf) (.cut .b 6 (.cut .s 1057 (.cut .c 4 .leaf (.cut .s 1039 (.cut .s 1030 .leaf (.cut .s 1034 (.cut .s 1032 (.cut .c 5 (.cut .s 1031 .leaf (.composite 2)) .leaf) (.cut .c 5 .leaf (.cut .s 1033 .leaf (.composite 2)))) (.cut .s 1036 (.cut .c 5 .leaf (.cut .s 1035 (.composite 3) (.composite 2))) .leaf))) .leaf)) .leaf) (.cut .s 1057 .leaf tree_5_13_8))

private def tree_5_13_10 : Tree :=
  .cut .s 1120 (.cut .s 1117 (.cut .b 8 (.cut .c 5 (.cut .s 1116 (.composite 2) (.cut .d 2 .leaf .leaf)) .leaf) .leaf) (.cut .s 1118 (.composite 2) (.cut .b 8 (.cut .c 5 .leaf (.cut .s 1119 (.composite 3) (.composite 2))) (.cut .c 5 (.cut .s 1119 (.composite 3) (.composite 2)) .leaf)))) (.cut .s 1122 (.cut .b 8 .leaf (.cut .c 5 .leaf (.cut .s 1121 (.composite 19) (.composite 2)))) (.cut .s 1123 (.cut .b 8 .leaf (.cut .c 5 .leaf (.cut .d 2 (.cut .b 9 .leaf .leaf) .leaf))) (.cut .b 8 .leaf (.cut .c 5 .leaf (.cut .s 1124 (.composite 2) (.composite 3))))))

private def tree_5_13_11 : Tree :=
  .cut .s 1136 (.cut .c 4 .leaf (.cut .s 1115 (.cut .s 1105 (.cut .b 7 (.cut .s 1100 (.cut .s 1097 .leaf (.cut .s 1098 (.composite 2) (.cut .c 5 (.cut .s 1099 (.composite 7) (.composite 2)) .leaf))) (.cut .s 1102 (.cut .c 5 (.cut .s 1101 (.composite 3) (.composite 2)) .leaf) (.cut .s 1103 (.cut .c 5 .leaf .leaf) (.cut .c 5 .leaf (.cut .s 1104 (.composite 2) (.composite 5)))))) .leaf) (.cut .b 7 .leaf .leaf)) (.cut .s 1125 (.cut .b 7 .leaf tree_5_13_10) .leaf))) .leaf

private def tree_5_13_12 : Tree :=
  .cut .a 7 (.cut .s 1278 (.cut .s 1095 (.cut .s 1022 (.cut .s 989 (.cut .s 973 (.cut .s 965 .leaf (.cut .s 969 .leaf (.cut .s 971 (.cut .s 970 (.composite 2) (.cut .d 2 .leaf .leaf)) .leaf))) .leaf) .leaf) .leaf) .leaf) .leaf) (.cut .s 1278 .leaf (.cut .s 1534 .leaf (.cut .a 8 (.cut .s 1705 (.cut .s 1615 (.cut .s 1573 .leaf (.cut .s 1594 .leaf (.cut .s 1604 (.cut .s 1599 .leaf (.cut .s 1601 .leaf (.cut .s 1602 (.composite 2) (.cut .s 1603 (.composite 7) (.composite 2))))) .leaf))) .leaf) .leaf) .leaf)))

private def tree_5_13_13 : Tree :=
  .cut .s 2273 (.cut .a 10 (.cut .s 2232 .leaf (.cut .s 2252 .leaf (.cut .s 2262 (.cut .s 2257 (.cut .s 2254 .leaf (.cut .s 2255 (.composite 5) (.cut .s 2256 (.composite 2) (.composite 37)))) (.cut .s 2259 (.cut .s 2258 (.composite 2) (.composite 3)) .leaf)) .leaf))) .leaf) (.cut .a 10 .leaf (.cut .s 2316 .leaf (.cut .s 2338 (.cut .a 11 (.cut .s 2327 .leaf (.cut .s 2332 .leaf (.cut .s 2335 .leaf (.cut .s 2336 (.composite 2) (.cut .s 2337 (.composite 3) (.composite 2)))))) .leaf) (.cut .a 11 .leaf .leaf))))

private def tree_5_13_14 : Tree :=
  .cut .s 2372 (.cut .a 12 (.cut .s 2366 (.cut .s 2363 .leaf (.cut .s 2364 (.composite 2) (.cut .s 2365 (.composite 5) (.composite 2)))) .leaf) .leaf) (.cut .a 12 .leaf (.cut .s 2378 (.cut .s 2375 (.cut .a 13 (.cut .s 2373 (.composite 3) (.cut .s 2374 (.composite 2) (.composite 5))) .leaf) (.cut .a 13 .leaf (.cut .s 2376 (.composite 2) (.cut .s 2377 .leaf (.composite 2))))) (.cut .s 2381 (.cut .a 13 .leaf (.cut .s 2379 (.composite 3) (.cut .s 2380 (.composite 2) .leaf))) .leaf)))

private def tree_5_13_15 : Tree :=
  .cut .s 2558 (.cut .a 8 .leaf (.cut .s 2192 (.cut .a 9 (.cut .s 2046 .leaf (.cut .s 2117 (.cut .s 2081 (.cut .s 2063 (.cut .s 2054 (.cut .s 2050 (.cut .s 2048 (.cut .s 2047 (.composite 23) (.composite 2)) (.cut .s 2049 (.composite 3) (.composite 2))) .leaf) .leaf) .leaf) .leaf) .leaf)) .leaf) (.cut .a 9 .leaf (.cut .s 2361 tree_5_13_13 (.cut .s 2456 (.cut .a 10 .leaf (.cut .s 2408 (.cut .s 2384 (.cut .a 11 .leaf tree_5_13_14) .leaf) .leaf)) .leaf))))) .leaf

private def tree_5_13_16 : Tree :=
  .cut .s 15358 .leaf (.cut .s 30718 (.cut .s 20478 .leaf (.cut .s 24574 .leaf (.cut .s 27305 .leaf (.cut .s 28911 (.cut .s 28085 .leaf (.cut .s 28492 .leaf (.cut .s 28700 .leaf (.cut .s 28805 (.cut .s 28752 (.cut .s 28726 .leaf (.cut .s 28739 (.cut .s 28732 (.cut .s 28729 (.cut .s 28727 (.composite 23) (.cut .s 28728 (.composite 2) .leaf)) (.cut .s 28730 (.composite 2) (.cut .s 28731 (.composite 3) (.composite 2)))) .leaf) .leaf)) .leaf) .leaf)))) .leaf)))) .leaf)

private def tree_5_13_17 : Tree :=
  .cut .c 2 (.cut .a 5 .leaf (.cut .s 478 (.cut .s 318 .leaf (.cut .a 6 (.cut .s 382 .leaf (.cut .s 425 .leaf (.cut .s 450 (.cut .s 437 .leaf (.cut .s 443 .leaf (.cut .s 446 (.cut .s 444 (.composite 2) (.cut .s 445 (.composite 5) (.composite 2))) .leaf))) .leaf))) .leaf)) (.cut .s 958 (.cut .a 6 .leaf .leaf) (.cut .a 6 .leaf (.cut .s 1918 tree_5_13_12 (.cut .a 7 .leaf (.cut .s 3838 tree_5_13_15 .leaf))))))) (.cut .a 5 (.cut .s 478 .leaf (.cut .s 958 .leaf (.cut .s 1918 .leaf (.cut .s 3838 .leaf (.cut .c 3 (.cut .s 7678 .leaf tree_5_13_16) .leaf))))) .leaf)

private def tree_5_13_18 : Tree :=
  .cut .a 4 (.cut .b 3 .leaf (.cut .s 238 (.cut .c 2 tree_5_13_3 .leaf) (.cut .c 2 .leaf (.cut .s 478 tree_5_13_4 (.cut .s 958 (.cut .b 4 .leaf tree_5_13_7) (.cut .b 4 .leaf (.cut .s 1918 (.cut .s 1278 (.cut .c 3 .leaf (.cut .b 5 .leaf (.cut .s 1095 tree_5_13_9 (.cut .s 1180 (.cut .b 6 .leaf tree_5_13_11) .leaf)))) .leaf) .leaf))))))) (.cut .b 3 (.cut .s 238 (.cut .c 2 (.cut .a 5 (.cut .s 158 .leaf (.cut .s 190 (.cut .s 173 (.cut .s 165 .leaf (.cut .s 169 (.cut .s 167 .leaf (.cut .s 168 (.composite 2) (.composite 13))) (.cut .s 171 (.cut .s 170 (.composite 2) (.composite 3)) .leaf))) .leaf) .leaf)) .leaf) .leaf) tree_5_13_17) .leaf)

private def tree_5_13_19 : Tree :=
  .cut .s 58 (.cut .s 38 .leaf (.cut .a 4 (.cut .b 3 (.cut .s 46 .leaf (.cut .c 2 (.cut .s 51 .leaf (.cut .s 54 .leaf (.cut .s 56 .leaf (.cut .s 57 (.composite 3) (.composite 2))))) .leaf)) .leaf) .leaf)) (.cut .s 118 (.cut .a 4 (.cut .b 3 tree_5_13_2 (.cut .s 78 .leaf (.cut .c 2 (.cut .s 94 .leaf (.cut .s 105 .leaf (.cut .b 4 (.cut .s 111 (.cut .s 108 (.cut .s 106 (.composite 2) (.cut .s 107 .leaf (.composite 2))) (.cut .s 109 (.cut .d 2 .leaf .leaf) .leaf)) .leaf) .leaf))) .leaf))) .leaf) tree_5_13_18)

private def tree_5_13_20 : Tree :=
  .cut .a 3 (.cut .b 2 .leaf (.cut .s 58 (.cut .s 38 (.cut .s 32 (.cut .b 3 .leaf (.cut .c 2 .leaf (.cut .s 30 (.cut .s 29 (.cut .b 4 .leaf (.cut .d 2 (.cut .c 3 (.cut .b 5 .leaf .leaf) .leaf) .leaf)) (.composite 2)) .leaf))) .leaf) .leaf) .leaf)) (.cut .b 2 (.cut .s 58 (.cut .s 38 (.cut .a 4 .leaf (.cut .s 32 (.cut .c 2 .leaf (.cut .a 5 .leaf (.cut .s 30 (.cut .s 29 (.cut .a 6 (.cut .d 2 (.cut .c 3 .leaf .leaf) .leaf) .leaf) (.composite 2)) (.cut .s 31 (.cut .a 6 .leaf (.cut .d 2 .leaf (.cut .a 7 (.cut .c 3 .leaf .leaf) .leaf))) (.composite 2))))) .leaf)) .leaf) .leaf) tree_5_13_19)

private def tree_5_13 : Tree :=
  .cut .a 1 .leaf (.cut .b 1 .leaf (.cut .a 2 .leaf (.cut .c 1 (.cut .s 28 (.cut .a 3 .leaf (.cut .b 2 .leaf (.cut .s 18 (.cut .s 15 (.cut .a 4 .leaf (.cut .s 14 (.composite 2) (.composite 3))) (.cut .a 4 .leaf (.cut .s 16 (.composite 2) .leaf))) .leaf))) .leaf) (.cut .s 28 (.cut .a 3 tree_5_13_0 (.cut .b 2 (.cut .s 18 (.cut .s 15 .leaf (.cut .a 4 (.cut .s 16 (.composite 2) (.cut .s 17 .leaf (.composite 2))) .leaf)) tree_5_13_1) .leaf)) tree_5_13_20))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem accepted_5_13 : check 5 13 tree_5_13 (initial 13) = true := by decide +kernel

private def tree_5_17_0 : Tree :=
  .cut .b 2 (.cut .s 24 (.cut .s 20 (.cut .a 4 .leaf (.cut .s 18 (.composite 2) (.cut .s 19 (.cut .a 5 .leaf (.cut .c 2 .leaf (.cut .d 2 .leaf .leaf))) (.composite 2)))) .leaf) .leaf) (.cut .s 24 .leaf (.cut .a 4 (.cut .s 29 (.cut .b 3 (.cut .s 26 .leaf (.cut .s 27 (.composite 3) (.cut .c 2 (.cut .s 28 (.composite 2) .leaf) .leaf))) .leaf) (.cut .b 3 (.cut .s 32 (.cut .s 30 (.composite 2) (.cut .c 2 .leaf (.cut .s 31 .leaf (.composite 2)))) (.cut .s 34 (.cut .c 2 .leaf (.cut .s 33 (.composite 3) (.composite 2))) .leaf)) .leaf)) .leaf))

private def tree_5_17_1 : Tree :=
  .cut .s 42 (.cut .s 39 (.cut .c 2 (.cut .s 37 .leaf (.cut .s 38 (.composite 2) (.composite 3))) .leaf) (.cut .c 2 (.cut .s 40 (.composite 2) (.cut .b 4 .leaf (.cut .s 41 (.cut .d 2 (.cut .b 5 .leaf .leaf) .leaf) (.composite 2)))) .leaf)) (.cut .s 45 (.cut .c 2 .leaf (.cut .s 43 .leaf (.cut .b 4 (.cut .s 44 (.composite 2) (.composite 3)) .leaf))) (.cut .c 2 .leaf (.cut .s 47 (.cut .b 4 .leaf (.cut .s 46 (.composite 2) .leaf)) (.cut .b 4 .leaf (.cut .s 48 (.composite 2) (.composite 7))))))

private def tree_5_17_2 : Tree :=
  .cut .a 5 (.cut .s 54 (.cut .c 2 .leaf (.cut .s 51 (.cut .s 50 (.composite 2) (.composite 3)) (.cut .s 52 (.composite 2) (.cut .s 53 (.cut .d 2 .leaf (.cut .c 3 .leaf .leaf)) (.composite 2))))) .leaf) (.cut .s 54 (.cut .c 2 (.cut .s 51 .leaf (.cut .a 6 (.cut .s 52 (.composite 2) (.cut .s 53 (.cut .d 2 .leaf .leaf) (.composite 2))) .leaf)) .leaf) (.cut .c 2 (.cut .a 6 .leaf (.cut .s 56 (.cut .s 55 (.composite 5) (.composite 2)) (.cut .s 57 (.composite 3) (.cut .s 58 (.composite 2) .leaf)))) .leaf))

private def tree_5_17_3 : Tree :=
  .cut .s 66 (.cut .s 62 .leaf (.cut .a 6 (.cut .s 64 (.cut .s 63 (.composite 3) (.composite 2)) (.cut .s 65 (.composite 5) (.composite 2))) .leaf)) (.cut .a 6 .leaf (.cut .s 70 (.cut .s 68 .leaf (.cut .s 69 (.composite 3) (.composite 2))) (.cut .s 72 (.cut .a 7 (.cut .s 71 (.cut .c 3 .leaf (.cut .d 2 .leaf .leaf)) (.composite 2)) (.cut .s 71 .leaf (.composite 2))) (.cut .a 7 .leaf (.cut .s 73 (.cut .c 3 (.cut .a 8 .leaf (.cut .d 2 .leaf .leaf)) (.cut .a 8 (.cut .d 2 .leaf .leaf) .leaf)) (.composite 2))))))

private def tree_5_17_4 : Tree :=
  .cut .s 49 (.cut .b 3 (.cut .s 42 .leaf (.cut .a 5 (.cut .s 45 (.cut .c 2 (.cut .s 43 .leaf (.cut .s 44 (.composite 2) (.composite 3))) .leaf) (.cut .c 2 .leaf .leaf)) .leaf)) .leaf) (.cut .b 3 (.cut .s 59 tree_5_17_2 (.cut .a 5 .leaf (.cut .c 2 .leaf tree_5_17_3))) (.cut .s 59 .leaf (.cut .a 5 (.cut .c 2 (.cut .s 66 (.cut .s 62 .leaf (.cut .b 4 (.cut .s 64 .leaf (.cut .s 65 (.composite 5) (.composite 2))) .leaf)) (.cut .b 4 (.cut .s 70 (.cut .s 68 (.cut .s 67 (.cut .d 2 .leaf .leaf) (.composite 2)) .leaf) .leaf) (.cut .s 70 .leaf (.cut .s 72 .leaf (.cut .s 73 .leaf (.composite 2)))))) .leaf) .leaf)))

private def tree_5_17_5 : Tree :=
  .cut .a 5 (.cut .c 2 (.cut .s 85 (.cut .b 4 .leaf (.cut .s 79 (.cut .s 76 (.cut .s 75 (.composite 3) (.composite 2)) (.cut .s 77 (.composite 7) .leaf)) .leaf)) .leaf) (.cut .s 85 .leaf (.cut .b 4 (.cut .s 92 (.cut .s 88 (.cut .s 86 (.composite 2) (.cut .s 87 (.composite 3) (.composite 2))) .leaf) .leaf) (.cut .s 92 .leaf (.cut .s 96 .leaf (.cut .s 98 .leaf (.cut .b 5 (.cut .s 99 (.composite 3) (.composite 2)) .leaf))))))) (.cut .c 2 (.cut .s 85 .leaf (.cut .b 4 (.cut .s 92 (.cut .a 6 (.cut .s 88 (.cut .s 86 (.composite 2) (.cut .s 87 (.composite 3) (.composite 2))) .leaf) .leaf) (.cut .a 6 .leaf (.cut .s 96 .leaf (.cut .a 7 (.cut .s 98 (.cut .s 97 .leaf (.composite 2)) (.cut .s 99 (.composite 3) (.composite 2))) .leaf)))) .leaf)) .leaf)

private def tree_5_17_6 : Tree :=
  .cut .a 6 (.cut .s 109 (.cut .s 104 (.cut .s 102 (.cut .b 5 (.cut .s 101 .leaf (.composite 2)) .leaf) (.cut .b 5 .leaf .leaf)) (.cut .s 106 (.cut .b 5 .leaf (.cut .s 105 (.composite 3) (.composite 2))) .leaf)) .leaf) (.cut .s 109 .leaf (.cut .s 114 .leaf (.cut .a 7 (.cut .s 117 (.cut .b 5 (.cut .s 115 (.composite 5) (.cut .s 116 (.composite 2) (.composite 3))) .leaf) (.cut .b 5 .leaf (.cut .s 118 (.composite 2) (.cut .s 119 (.composite 7) (.composite 2))))) .leaf)))

private def tree_5_17_7 : Tree :=
  .cut .s 129 (.cut .b 5 .leaf (.cut .s 127 (.cut .a 8 (.cut .b 6 (.cut .d 2 .leaf .leaf) .leaf) .leaf) (.cut .a 8 (.cut .s 128 (.composite 2) (.composite 3)) (.cut .s 128 (.composite 2) (.composite 3))))) (.cut .b 5 .leaf (.cut .s 131 (.cut .a 8 .leaf (.cut .s 130 (.composite 2) (.cut .b 6 (.cut .a 9 .leaf (.cut .d 2 .leaf (.cut .a 10 .leaf .leaf))) (.cut .a 9 (.cut .d 2 .leaf .leaf) (.cut .d 2 (.cut .a 10 (.cut .b 7 .leaf .leaf) .leaf) .leaf))))) (.cut .a 8 .leaf (.cut .s 132 (.composite 2) (.composite 7)))))

private def tree_5_17_8 : Tree :=
  .cut .s 126 (.cut .a 7 (.cut .s 123 (.cut .b 5 .leaf (.cut .s 121 (.composite 11) (.cut .s 122 (.composite 2) (.composite 3)))) .leaf) (.cut .s 123 (.cut .b 5 (.cut .s 121 (.composite 11) (.cut .a 8 (.cut .s 122 (.composite 2) (.composite 3)) .leaf)) .leaf) (.cut .b 5 (.cut .s 124 (.composite 2) (.cut .a 8 .leaf (.cut .s 125 (.composite 5) (.composite 2)))) (.cut .s 124 (.composite 2) (.cut .a 8 (.cut .s 125 (.composite 5) (.composite 2)) .leaf))))) (.cut .a 7 .leaf tree_5_17_7)

private def tree_5_17_9 : Tree :=
  .cut .a 6 (.cut .s 133 (.cut .s 126 (.cut .s 123 .leaf (.cut .s 124 (.composite 2) (.cut .c 3 (.cut .s 125 (.composite 5) (.composite 2)) .leaf))) (.cut .s 129 (.cut .s 127 (.cut .c 3 (.cut .d 2 .leaf .leaf) .leaf) (.cut .c 3 .leaf (.cut .s 128 (.composite 2) (.composite 3)))) (.cut .s 131 (.cut .c 3 .leaf (.cut .s 130 (.composite 2) (.cut .d 2 .leaf (.cut .c 4 .leaf .leaf)))) .leaf))) .leaf) (.cut .s 133 .leaf (.cut .s 141 .leaf (.cut .a 7 (.cut .s 145 .leaf (.cut .s 147 .leaf (.cut .c 3 (.cut .s 148 (.composite 2) (.cut .s 149 .leaf (.composite 2))) .leaf))) .leaf)))

private def tree_5_17_10 : Tree :=
  .cut .a 5 (.cut .c 2 .leaf (.cut .s 120 (.cut .b 4 .leaf (.cut .s 109 (.cut .s 104 (.cut .s 102 (.cut .b 5 (.cut .s 101 (.cut .c 3 .leaf .leaf) (.composite 2)) (.cut .s 101 .leaf (.composite 2))) (.cut .b 5 .leaf (.cut .s 103 (.cut .c 3 (.cut .d 2 (.cut .b 6 .leaf .leaf) .leaf) .leaf) (.composite 2)))) (.cut .s 106 (.cut .b 5 .leaf (.cut .s 105 (.composite 3) (.composite 2))) .leaf)) .leaf)) .leaf)) (.cut .c 2 (.cut .s 120 (.cut .b 4 (.cut .a 6 .leaf (.cut .s 109 (.cut .s 104 (.cut .a 7 .leaf (.cut .s 102 (.cut .s 101 .leaf (.composite 2)) (.cut .s 103 (.cut .a 8 (.cut .d 2 .leaf .leaf) .leaf) (.composite 2)))) (.cut .a 7 .leaf (.cut .s 106 (.cut .s 105 (.composite 3) (.composite 2)) .leaf))) .leaf)) tree_5_17_6) (.cut .b 4 .leaf (.cut .a 6 .leaf (.cut .s 133 tree_5_17_8 .leaf)))) (.cut .s 120 .leaf (.cut .b 4 tree_5_17_9 .leaf)))

private def tree_5_17_11 : Tree :=
  .cut .s 166 (.cut .s 163 (.cut .c 3 (.cut .a 8 .leaf (.cut .s 161 (.composite 7) (.cut .s 162 (.composite 2) .leaf))) .leaf) (.cut .c 3 (.cut .a 8 .leaf (.cut .s 164 (.composite 2) (.cut .s 165 (.composite 3) (.composite 2)))) (.cut .a 8 (.cut .s 164 (.composite 2) (.cut .s 165 (.composite 3) (.composite 2))) .leaf))) (.cut .s 169 (.cut .c 3 .leaf (.cut .a 8 .leaf (.cut .s 167 .leaf (.cut .s 168 (.composite 2) (.composite 13))))) (.cut .c 3 .leaf (.cut .a 8 .leaf (.cut .s 170 (.composite 2) (.cut .s 171 (.composite 3) (.composite 2))))))

private def tree_5_17_12 : Tree :=
  .cut .s 166 (.cut .b 5 (.cut .s 163 (.cut .c 3 .leaf (.cut .s 161 (.composite 7) (.cut .s 162 (.composite 2) (.cut .d 2 .leaf .leaf)))) .leaf) (.cut .s 163 .leaf (.cut .c 3 (.cut .s 164 (.composite 2) (.cut .s 165 (.composite 3) (.composite 2))) .leaf))) (.cut .b 5 .leaf (.cut .s 169 (.cut .c 3 (.cut .s 167 (.cut .b 6 .leaf (.cut .d 2 (.cut .b 7 .leaf .leaf) .leaf)) (.cut .s 168 (.composite 2) (.composite 13))) .leaf) (.cut .c 3 .leaf (.cut .s 170 (.composite 2) (.cut .s 171 (.composite 3) (.composite 2))))))

private def tree_5_17_13 : Tree :=
  .cut .a 6 (.cut .s 172 (.cut .s 160 (.cut .s 155 .leaf (.cut .b 5 (.cut .s 157 (.cut .c 3 (.cut .s 156 (.composite 2) .leaf) .leaf) (.cut .c 3 (.cut .s 158 (.composite 2) .leaf) .leaf)) .leaf)) tree_5_17_12) (.cut .s 185 (.cut .s 178 (.cut .b 5 .leaf (.cut .s 175 (.cut .c 3 .leaf (.cut .s 173 (.cut .b 6 .leaf (.cut .d 2 (.cut .b 7 (.cut .c 4 .leaf .leaf) .leaf) .leaf)) (.cut .s 174 (.composite 2) (.composite 5)))) .leaf)) .leaf) .leaf)) (.cut .s 172 .leaf (.cut .s 185 .leaf (.cut .a 7 (.cut .s 193 .leaf (.cut .b 5 (.cut .s 197 (.cut .c 3 (.cut .s 195 (.cut .s 194 (.composite 2) (.composite 3)) .leaf) .leaf) (.cut .c 3 .leaf .leaf)) .leaf)) .leaf)))

private def tree_5_17_14 : Tree :=
  .cut .s 210 (.cut .b 5 (.cut .s 205 (.cut .c 3 .leaf (.cut .s 203 (.cut .s 202 (.composite 2) (.composite 7)) (.cut .s 204 (.composite 2) (.composite 5)))) .leaf) (.cut .s 205 .leaf (.cut .c 3 (.cut .s 207 (.cut .b 6 (.cut .s 206 (.composite 2) (.composite 3)) .leaf) (.cut .s 208 (.composite 2) (.cut .b 6 .leaf (.cut .s 209 (.composite 11) (.composite 2))))) .leaf))) (.cut .b 5 .leaf (.cut .s 215 (.cut .c 3 (.cut .s 212 (.cut .b 6 .leaf (.cut .s 211 (.cut .d 2 .leaf (.cut .b 7 .leaf .leaf)) (.composite 2))) .leaf) .leaf) (.cut .c 3 .leaf (.cut .s 217 (.cut .b 6 (.cut .s 216 (.composite 2) (.composite 7)) .leaf) (.cut .s 218 (.composite 2) (.cut .b 6 .leaf (.cut .s 219 (.composite 3) (.composite 2))))))))

private def tree_5_17_15 : Tree :=
  .cut .s 225 (.cut .c 3 (.cut .a 8 .leaf (.cut .s 222 (.cut .a 9 .leaf (.cut .s 221 (.composite 13) (.composite 2))) .leaf)) (.cut .a 8 (.cut .s 222 (.cut .s 221 (.composite 13) (.composite 2)) .leaf) .leaf)) (.cut .c 3 .leaf (.cut .a 8 .leaf (.cut .s 228 (.cut .s 226 (.composite 2) (.cut .a 9 (.cut .s 227 .leaf (.composite 2)) .leaf)) (.cut .s 229 (.cut .a 9 (.cut .d 2 .leaf (.cut .c 4 .leaf .leaf)) .leaf) (.cut .a 9 .leaf (.cut .s 230 (.composite 2) (.composite 3)))))))

private def tree_5_17_16 : Tree :=
  .cut .s 236 (.cut .a 8 .leaf (.cut .s 233 (.cut .b 6 (.cut .a 9 (.cut .s 232 (.composite 2) .leaf) .leaf) .leaf) (.cut .b 6 (.cut .s 234 (.composite 2) (.cut .a 9 .leaf (.cut .s 235 (.composite 5) (.composite 2)))) (.cut .s 234 (.composite 2) (.cut .a 9 (.cut .s 235 (.composite 5) (.composite 2)) .leaf))))) (.cut .a 8 .leaf (.cut .s 239 (.cut .b 6 (.cut .s 237 (.composite 3) (.cut .a 9 .leaf (.cut .s 238 (.composite 2) .leaf))) (.cut .s 237 (.composite 3) (.cut .a 9 (.cut .s 238 (.composite 2) .leaf) (.cut .s 238 (.composite 2) .leaf)))) (.cut .b 6 .leaf (.cut .s 240 (.composite 2) (.cut .a 9 .leaf (.cut .s 241 (.cut .a 10 (.cut .d 2 .leaf (.cut .b 7 .leaf .leaf)) (.cut .d 2 (.cut .b 7 .leaf .leaf) .leaf)) (.composite 2)))))))

private def tree_5_17_17 : Tree :=
  .cut .b 5 (.cut .c 3 .leaf (.cut .s 236 (.cut .a 8 .leaf (.cut .s 233 (.cut .a 9 .leaf (.cut .s 232 (.composite 2) (.cut .a 10 .leaf (.cut .d 2 .leaf (.cut .c 4 .leaf (.cut .a 11 .leaf (.cut .a 12 (.cut .c 5 .leaf .leaf) .leaf))))))) .leaf)) .leaf)) (.cut .c 3 tree_5_17_16 (.cut .s 236 .leaf (.cut .a 8 (.cut .s 239 (.cut .b 6 (.cut .s 237 (.composite 3) (.cut .s 238 (.composite 2) .leaf)) .leaf) (.cut .b 6 .leaf (.cut .s 240 (.composite 2) (.cut .s 241 (.cut .d 2 (.cut .b 7 (.cut .c 4 .leaf .leaf) .leaf) .leaf) (.composite 2))))) .leaf)))

private def tree_5_17_18 : Tree :=
  .cut .a 7 (.cut .s 231 (.cut .b 5 .leaf (.cut .s 225 (.cut .c 3 .leaf (.cut .s 222 (.cut .b 6 .leaf (.cut .s 221 (.composite 13) (.composite 2))) .leaf)) .leaf)) .leaf) (.cut .s 231 (.cut .b 5 tree_5_17_15 (.cut .s 225 .leaf (.cut .c 3 (.cut .a 8 (.cut .s 228 (.cut .s 226 (.composite 2) (.cut .b 6 (.cut .s 227 (.cut .d 2 .leaf .leaf) (.composite 2)) .leaf)) (.cut .b 6 .leaf (.cut .s 229 .leaf (.cut .s 230 (.composite 2) (.composite 3))))) .leaf) .leaf))) tree_5_17_17)

private def tree_5_17_19 : Tree :=
  .cut .s 251 (.cut .b 6 (.cut .a 9 .leaf (.cut .s 249 (.composite 3) (.cut .s 250 (.composite 2) (.cut .a 10 .leaf (.cut .d 2 .leaf (.cut .c 4 .leaf (.cut .a 11 .leaf (.cut .a 12 .leaf (.cut .a 13 (.cut .c 5 .leaf .leaf) .leaf))))))))) (.cut .a 9 (.cut .s 249 (.composite 3) (.cut .s 250 (.composite 2) (.cut .d 2 .leaf (.cut .b 7 .leaf (.cut .c 4 .leaf .leaf))))) (.cut .s 249 (.composite 3) (.cut .s 250 (.composite 2) .leaf)))) (.cut .s 253 (.cut .b 6 .leaf (.cut .a 9 .leaf (.cut .s 252 (.composite 2) (.composite 11)))) (.cut .b 6 .leaf (.cut .a 9 .leaf (.cut .s 254 (.composite 2) (.composite 3)))))

private def tree_5_17_20 : Tree :=
  .cut .s 248 (.cut .c 3 .leaf (.cut .a 8 (.cut .s 245 (.cut .b 6 .leaf (.cut .s 243 (.composite 3) .leaf)) .leaf) (.cut .s 245 (.cut .b 6 (.cut .a 9 (.cut .s 243 (.composite 3) (.cut .s 244 (.composite 2) (.composite 5))) .leaf) .leaf) (.cut .b 6 (.cut .a 9 (.cut .s 246 (.composite 2) .leaf) (.cut .s 246 (.composite 2) (.cut .s 247 (.composite 13) (.composite 2)))) (.cut .a 9 (.cut .s 246 (.composite 2) (.cut .s 247 (.composite 13) (.composite 2))) .leaf))))) (.cut .c 3 .leaf (.cut .a 8 .leaf tree_5_17_19))

private def tree_5_17_21 : Tree :=
  .cut .s 242 (.cut .s 220 (.cut .a 7 tree_5_17_14 (.cut .s 210 .leaf (.cut .b 5 (.cut .s 215 (.cut .c 3 (.cut .a 8 (.cut .s 212 (.cut .s 211 .leaf (.composite 2)) .leaf) .leaf) .leaf) (.cut .c 3 (.cut .a 8 .leaf (.cut .s 217 (.cut .a 9 (.cut .s 216 (.composite 2) (.composite 7)) .leaf) (.cut .s 218 (.composite 2) (.cut .a 9 .leaf (.cut .s 219 (.composite 3) (.composite 2)))))) .leaf)) .leaf))) tree_5_17_18) (.cut .s 269 (.cut .a 7 .leaf (.cut .s 255 (.cut .b 5 .leaf tree_5_17_20) (.cut .b 5 .leaf (.cut .s 262 (.cut .c 3 .leaf (.cut .a 8 .leaf (.cut .s 258 (.cut .b 6 .leaf (.cut .a 9 .leaf (.cut .s 256 (.composite 2) .leaf))) .leaf))) .leaf)))) .leaf)

private def tree_5_17_22 : Tree :=
  .cut .s 201 (.cut .b 4 (.cut .a 6 .leaf (.cut .s 172 (.cut .s 160 (.cut .a 7 (.cut .s 155 (.cut .s 152 (.cut .c 3 .leaf .leaf) (.cut .c 3 .leaf (.cut .s 153 (.composite 3) (.cut .s 154 (.composite 2) (.composite 5))))) .leaf) (.cut .s 155 .leaf (.cut .s 157 .leaf (.cut .c 3 (.cut .a 8 (.cut .s 158 (.composite 2) (.cut .s 159 (.composite 3) (.composite 2))) .leaf) .leaf)))) (.cut .a 7 .leaf tree_5_17_11)) .leaf)) tree_5_17_13) (.cut .b 4 .leaf (.cut .a 6 .leaf tree_5_17_21))

private def tree_5_17_23 : Tree :=
  .cut .s 36 (.cut .a 3 (.cut .b 2 .leaf (.cut .s 24 (.cut .s 20 (.cut .s 18 (.composite 2) (.cut .b 3 .leaf (.cut .s 19 (.cut .c 2 .leaf (.cut .d 2 .leaf (.cut .b 4 .leaf .leaf))) (.composite 2)))) .leaf) .leaf)) tree_5_17_0) (.cut .a 3 .leaf (.cut .b 2 .leaf (.cut .s 74 (.cut .a 4 (.cut .s 49 (.cut .b 3 .leaf tree_5_17_1) .leaf) tree_5_17_4) (.cut .a 4 .leaf (.cut .s 150 (.cut .b 3 .leaf (.cut .s 100 tree_5_17_5 tree_5_17_10)) (.cut .b 3 .leaf (.cut .s 302 (.cut .a 5 .leaf (.cut .c 2 .leaf tree_5_17_22)) .leaf)))))))

private def tree_5_17 : Tree :=
  .cut .a 1 .leaf (.cut .b 1 .leaf (.cut .a 2 .leaf (.cut .c 1 .leaf tree_5_17_23)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem accepted_5_17 : check 5 17 tree_5_17 (initial 17) = true := by decide +kernel

private def tree_5_19_0 : Tree :=
  .cut .s 32 (.cut .b 3 (.cut .s 29 (.cut .s 27 (.composite 3) .leaf) .leaf) (.cut .s 29 .leaf (.cut .s 30 (.composite 2) (.cut .s 31 .leaf (.composite 2))))) (.cut .b 3 .leaf (.cut .s 36 (.cut .s 34 (.cut .c 2 (.cut .s 33 (.composite 3) (.composite 2)) (.cut .s 33 (.composite 3) (.composite 2))) (.cut .c 2 .leaf (.cut .s 35 (.composite 5) (.composite 2)))) (.cut .s 38 (.cut .c 2 .leaf (.cut .s 37 (.cut .b 4 .leaf (.cut .d 2 .leaf (.cut .b 5 (.cut .c 3 .leaf .leaf) .leaf))) (.composite 2))) .leaf)))

private def tree_5_19_1 : Tree :=
  .cut .s 26 (.cut .a 4 (.cut .s 22 .leaf (.cut .b 3 (.cut .s 24 (.cut .s 23 .leaf (.composite 2)) (.cut .s 25 (.composite 5) (.composite 2))) .leaf)) .leaf) (.cut .a 4 tree_5_19_0 (.cut .s 32 .leaf (.cut .b 3 (.cut .s 36 (.cut .a 5 (.cut .s 34 (.cut .c 2 (.cut .s 33 (.composite 3) (.composite 2)) .leaf) (.cut .c 2 (.cut .s 35 (.composite 5) (.composite 2)) .leaf)) .leaf) (.cut .a 5 (.cut .s 38 (.cut .c 2 .leaf (.cut .s 37 .leaf (.composite 2))) (.cut .c 2 .leaf (.cut .s 39 (.composite 3) (.composite 2)))) (.cut .s 38 .leaf (.cut .c 2 (.cut .s 39 (.composite 3) (.composite 2)) .leaf)))) .leaf)))

private def tree_5_19_2 : Tree :=
  .cut .s 46 (.cut .a 5 .leaf (.cut .s 43 (.cut .c 2 (.cut .s 41 (.cut .a 6 .leaf .leaf) (.cut .a 6 .leaf (.cut .s 42 (.composite 2) (.cut .a 7 .leaf (.cut .d 2 (.cut .a 8 .leaf (.cut .a 9 .leaf .leaf)) .leaf))))) .leaf) (.cut .c 2 (.cut .s 44 (.composite 2) .leaf) (.cut .s 44 (.composite 2) (.cut .a 6 (.cut .s 45 (.composite 3) (.composite 2)) .leaf))))) (.cut .a 5 .leaf (.cut .s 50 (.cut .c 2 .leaf (.cut .s 48 (.cut .a 6 .leaf (.cut .s 47 .leaf (.composite 2))) (.cut .a 6 .leaf (.cut .s 49 (.composite 7) (.composite 2))))) .leaf))

private def tree_5_19_3 : Tree :=
  .cut .a 5 (.cut .s 59 (.cut .c 2 .leaf (.cut .b 4 (.cut .s 56 (.cut .s 55 (.composite 5) (.composite 2)) .leaf) .leaf)) (.cut .c 2 .leaf (.cut .b 4 .leaf (.cut .s 62 (.cut .s 60 (.composite 2) (.cut .s 61 (.cut .b 5 (.cut .d 2 .leaf .leaf) .leaf) (.composite 2))) (.cut .s 63 (.composite 3) .leaf))))) (.cut .s 59 (.cut .c 2 (.cut .b 4 (.cut .a 6 (.cut .s 56 .leaf (.cut .s 57 (.composite 3) (.cut .s 58 (.composite 2) .leaf))) .leaf) .leaf) .leaf) (.cut .c 2 (.cut .b 4 (.cut .a 6 .leaf (.cut .s 62 (.cut .s 60 (.composite 2) (.cut .s 61 .leaf (.composite 2))) (.cut .s 63 (.composite 3) (.cut .s 64 (.composite 2) (.composite 5))))) (.cut .a 6 (.cut .s 62 .leaf (.cut .s 63 (.composite 3) (.cut .s 64 (.composite 2) (.composite 5)))) .leaf)) .leaf))

private def tree_5_19_4 : Tree :=
  .cut .s 69 (.cut .a 6 (.cut .s 67 (.cut .s 66 (.composite 2) .leaf) .leaf) (.cut .s 67 .leaf (.cut .s 68 (.composite 2) (.composite 3)))) (.cut .a 6 .leaf (.cut .s 71 (.cut .a 7 (.cut .s 70 (.composite 2) (.cut .b 5 .leaf (.cut .d 2 .leaf .leaf))) (.cut .s 70 (.composite 2) .leaf)) (.cut .a 7 .leaf (.cut .s 72 (.composite 2) (.cut .b 5 (.cut .a 8 .leaf (.cut .d 2 .leaf (.cut .a 9 .leaf .leaf))) (.cut .a 8 (.cut .d 2 (.cut .b 6 .leaf .leaf) .leaf) .leaf))))))

private def tree_5_19_5 : Tree :=
  .cut .a 6 .leaf (.cut .s 77 (.cut .s 75 (.cut .a 7 (.cut .s 74 (.composite 2) (.composite 3)) .leaf) (.cut .a 7 (.cut .s 76 (.composite 2) (.composite 7)) (.cut .s 76 (.composite 2) (.composite 7)))) (.cut .s 79 (.cut .a 7 .leaf (.cut .s 78 (.composite 2) (.cut .a 8 (.cut .d 2 .leaf (.cut .c 3 .leaf .leaf)) (.cut .d 2 (.cut .c 3 (.cut .a 9 .leaf .leaf) .leaf) .leaf)))) (.cut .a 7 .leaf (.cut .s 80 (.composite 2) (.cut .s 81 (.composite 3) (.composite 2))))))

private def tree_5_19_6 : Tree :=
  .cut .s 73 (.cut .c 2 (.cut .b 4 .leaf tree_5_19_4) (.cut .b 4 (.cut .s 69 (.cut .a 6 (.cut .s 67 .leaf (.cut .s 68 (.composite 2) (.composite 3))) .leaf) (.cut .a 6 (.cut .s 71 (.cut .s 70 (.composite 2) .leaf) .leaf) .leaf)) .leaf)) (.cut .c 2 (.cut .b 4 .leaf (.cut .a 6 .leaf (.cut .s 77 (.cut .s 75 (.cut .a 7 .leaf (.cut .s 74 (.composite 2) (.composite 3))) .leaf) .leaf))) (.cut .b 4 tree_5_19_5 (.cut .a 6 (.cut .s 77 (.cut .s 75 .leaf (.cut .s 76 (.composite 2) (.composite 7))) (.cut .s 79 (.cut .s 78 (.composite 2) (.cut .b 5 (.cut .d 2 .leaf (.cut .c 3 .leaf .leaf)) .leaf)) (.cut .s 80 (.composite 2) (.cut .s 81 (.composite 3) (.composite 2))))) .leaf)))

private def tree_5_19_7 : Tree :=
  .cut .s 54 (.cut .b 3 tree_5_19_2 (.cut .s 46 .leaf (.cut .a 5 (.cut .s 50 (.cut .c 2 (.cut .s 48 (.cut .b 4 (.cut .s 47 .leaf (.composite 2)) .leaf) (.cut .b 4 .leaf .leaf)) .leaf) (.cut .c 2 (.cut .b 4 .leaf (.cut .s 52 (.cut .s 51 (.composite 3) (.composite 2)) (.cut .s 53 (.cut .b 5 .leaf (.cut .d 2 .leaf .leaf)) (.composite 2)))) (.cut .b 4 (.cut .s 52 .leaf (.cut .s 53 .leaf (.composite 2))) .leaf))) .leaf))) (.cut .b 3 .leaf (.cut .s 65 tree_5_19_3 (.cut .a 5 .leaf tree_5_19_6)))

private def tree_5_19_8 : Tree :=
  .cut .s 91 (.cut .a 7 (.cut .s 89 (.cut .b 5 .leaf (.cut .c 3 (.cut .d 2 .leaf (.cut .b 6 .leaf .leaf)) .leaf)) (.cut .b 5 .leaf (.cut .s 90 (.composite 2) (.composite 7)))) (.cut .s 89 (.cut .b 5 (.cut .a 8 (.cut .c 3 (.cut .d 2 .leaf .leaf) .leaf) .leaf) .leaf) (.cut .b 5 (.cut .s 90 (.composite 2) (.composite 7)) (.cut .s 90 (.composite 2) (.composite 7))))) (.cut .a 7 .leaf (.cut .s 92 (.composite 2) (.cut .b 5 .leaf (.cut .s 93 (.composite 3) (.composite 2)))))

private def tree_5_19_9 : Tree :=
  .cut .s 94 (.cut .c 2 .leaf (.cut .b 4 .leaf (.cut .a 6 .leaf (.cut .s 88 (.cut .s 85 (.cut .a 7 (.cut .s 83 .leaf (.cut .s 84 (.composite 2) (.composite 5))) .leaf) (.cut .a 7 (.cut .s 86 (.composite 2) (.cut .s 87 (.composite 3) (.composite 2))) (.cut .s 86 (.composite 2) (.cut .s 87 (.composite 3) (.composite 2))))) tree_5_19_8)))) (.cut .c 2 .leaf (.cut .b 4 .leaf (.cut .a 6 .leaf (.cut .s 101 (.cut .s 97 (.cut .a 7 .leaf (.cut .s 95 (.composite 5) (.cut .b 5 .leaf (.cut .s 96 (.composite 2) .leaf)))) .leaf) .leaf))))

private def tree_5_19 : Tree :=
  .cut .a 1 .leaf (.cut .b 1 .leaf (.cut .a 2 .leaf (.cut .c 1 .leaf (.cut .s 40 (.cut .a 3 .leaf (.cut .b 2 .leaf tree_5_19_1)) (.cut .a 3 .leaf (.cut .b 2 .leaf (.cut .s 82 (.cut .a 4 .leaf tree_5_19_7) (.cut .a 4 .leaf (.cut .s 166 (.cut .b 3 .leaf (.cut .s 110 (.cut .a 5 .leaf tree_5_19_9) .leaf)) .leaf)))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem accepted_5_19 : check 5 19 tree_5_19 (initial 19) = true := by decide +kernel

private def tree_5_23_0 : Tree :=
  .cut .a 4 (.cut .s 27 (.cut .b 3 .leaf (.cut .s 25 (.cut .s 24 (.composite 2) (.composite 5)) (.cut .s 26 (.composite 2) (.composite 3)))) .leaf) (.cut .s 27 (.cut .b 3 (.cut .s 25 .leaf (.cut .a 5 (.cut .s 26 (.composite 2) (.composite 3)) .leaf)) .leaf) (.cut .b 3 (.cut .s 29 (.cut .a 5 (.cut .s 28 (.composite 2) .leaf) (.cut .s 28 (.composite 2) .leaf)) (.cut .a 5 .leaf (.cut .s 30 (.composite 2) (.cut .s 31 (.cut .c 2 (.cut .a 6 .leaf (.cut .d 2 (.cut .a 7 .leaf (.cut .a 8 .leaf .leaf)) .leaf)) .leaf) (.composite 2))))) .leaf))

private def tree_5_23_1 : Tree :=
  .cut .s 41 (.cut .c 2 (.cut .b 4 (.cut .a 6 .leaf (.cut .s 40 (.composite 2) (.cut .a 7 (.cut .d 2 .leaf .leaf) (.cut .d 2 (.cut .a 8 .leaf .leaf) .leaf)))) (.cut .a 6 (.cut .s 40 (.composite 2) (.cut .d 2 (.cut .b 5 .leaf .leaf) .leaf)) .leaf)) (.cut .b 4 (.cut .a 6 (.cut .s 40 (.composite 2) .leaf) .leaf) .leaf)) (.cut .c 2 (.cut .b 4 (.cut .a 6 .leaf (.cut .s 42 (.composite 2) .leaf)) (.cut .a 6 (.cut .s 42 (.composite 2) .leaf) (.cut .s 42 (.composite 2) (.cut .a 7 (.cut .d 2 (.cut .b 5 .leaf .leaf) .leaf) .leaf)))) (.cut .b 4 (.cut .a 6 (.cut .s 42 (.composite 2) .leaf) (.cut .s 42 (.composite 2) .leaf)) .leaf))

private def tree_5_23_2 : Tree :=
  .cut .s 43 tree_5_23_1 (.cut .s 45 (.cut .c 2 (.cut .b 4 .leaf (.cut .a 6 .leaf (.cut .s 44 (.composite 2) (.composite 3)))) (.cut .b 4 (.cut .a 6 .leaf (.cut .s 44 (.composite 2) (.composite 3))) (.cut .a 6 (.cut .s 44 (.composite 2) (.composite 3)) .leaf))) (.cut .c 2 .leaf (.cut .b 4 .leaf (.cut .a 6 (.cut .s 46 (.composite 2) .leaf) (.cut .s 46 (.composite 2) (.cut .s 47 (.cut .a 7 (.cut .d 2 (.cut .b 5 .leaf .leaf) .leaf) .leaf) (.composite 2)))))))

private def tree_5_23_3 : Tree :=
  .cut .s 39 (.cut .b 3 (.cut .s 35 (.cut .a 5 .leaf (.cut .s 33 (.composite 3) (.cut .s 34 (.composite 2) (.composite 5)))) .leaf) (.cut .s 35 (.cut .a 5 (.cut .s 33 (.composite 3) (.cut .s 34 (.composite 2) (.composite 5))) .leaf) (.cut .a 5 (.cut .s 37 (.cut .s 36 (.composite 2) (.cut .c 2 .leaf (.cut .b 4 .leaf .leaf))) (.cut .s 38 (.composite 2) (.composite 3))) (.cut .s 37 .leaf (.cut .s 38 (.composite 2) (.composite 3)))))) (.cut .b 3 .leaf (.cut .a 5 .leaf tree_5_23_2))

private def tree_5_23 : Tree :=
  .cut .a 1 .leaf (.cut .b 1 .leaf (.cut .a 2 .leaf (.cut .a 3 .leaf (.cut .b 2 .leaf (.cut .c 1 .leaf (.cut .s 48 (.cut .s 32 tree_5_23_0 (.cut .a 4 .leaf tree_5_23_3)) (.cut .s 98 (.cut .a 4 .leaf (.cut .s 65 (.cut .b 3 .leaf (.cut .s 55 (.cut .a 5 .leaf (.cut .s 51 (.cut .c 2 .leaf (.cut .b 4 .leaf (.cut .a 6 .leaf (.cut .s 49 (.composite 7) (.cut .s 50 (.composite 2) (.composite 3)))))) .leaf)) .leaf)) .leaf)) .leaf)))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem accepted_5_23 : check 5 23 tree_5_23 (initial 23) = true := by decide +kernel

private def tree_5_29_0 : Tree :=
  .cut .s 60 (.cut .s 40 (.cut .a 4 .leaf (.cut .s 34 (.cut .b 3 .leaf (.cut .s 31 (.cut .a 5 .leaf (.cut .s 30 (.composite 2) (.cut .b 4 (.cut .a 6 .leaf (.cut .c 2 (.cut .d 2 .leaf (.cut .a 7 .leaf (.cut .a 8 .leaf .leaf))) (.cut .d 2 (.cut .a 7 .leaf .leaf) .leaf))) (.cut .a 6 (.cut .c 2 (.cut .d 2 .leaf (.cut .b 5 .leaf .leaf)) .leaf) .leaf)))) (.cut .a 5 .leaf (.cut .s 32 (.composite 2) (.cut .s 33 (.composite 3) (.composite 2)))))) .leaf)) .leaf) .leaf

private def tree_5_29 : Tree :=
  .cut .a 1 .leaf (.cut .b 1 .leaf (.cut .a 2 .leaf (.cut .a 3 .leaf (.cut .b 2 .leaf (.cut .c 1 .leaf tree_5_29_0)))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem accepted_5_29 : check 5 29 tree_5_29 (initial 29) = true := by decide +kernel

private def tree_5_31 : Tree :=
  .cut .a 1 .leaf (.cut .b 1 .leaf (.cut .a 2 .leaf (.cut .a 3 .leaf (.cut .b 2 .leaf (.cut .c 1 .leaf (.cut .s 64 (.cut .s 42 (.cut .a 4 .leaf (.cut .b 3 .leaf (.cut .s 36 (.cut .a 5 .leaf (.cut .s 33 (.cut .s 32 (.composite 2) (.composite 3)) .leaf)) .leaf))) .leaf) .leaf))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem accepted_5_31 : check 5 31 tree_5_31 (initial 31) = true := by decide +kernel

private def tree_7_11_0 : Tree :=
  .cut .s 19 (.cut .a 4 (.cut .s 17 (.cut .c 2 .leaf (.cut .d 2 (.cut .b 3 .leaf .leaf) .leaf)) (.cut .c 2 .leaf (.cut .s 18 (.composite 2) .leaf))) (.cut .s 17 .leaf (.cut .c 2 (.cut .s 18 (.composite 2) (.cut .a 5 (.cut .b 3 .leaf (.cut .d 2 .leaf .leaf)) (.cut .b 3 (.cut .d 2 (.cut .a 6 .leaf .leaf) .leaf) .leaf))) .leaf))) (.cut .a 4 .leaf (.cut .s 21 (.cut .c 2 (.cut .s 20 (.composite 2) (.composite 3)) (.cut .s 20 (.composite 2) (.composite 3))) (.cut .c 2 .leaf (.cut .s 22 (.composite 2) (.cut .a 5 (.cut .s 23 (.cut .b 3 .leaf (.cut .d 2 .leaf (.cut .c 3 .leaf .leaf))) (.composite 2)) (.cut .s 23 (.cut .b 3 (.cut .d 2 (.cut .a 6 .leaf (.cut .c 3 (.cut .a 7 .leaf (.cut .a 8 .leaf .leaf)) .leaf)) .leaf) .leaf) (.composite 2)))))))

private def tree_7_11_1 : Tree :=
  .cut .a 3 (.cut .s 16 (.cut .s 13 (.cut .b 2 .leaf (.cut .s 12 (.composite 2) .leaf)) .leaf) .leaf) (.cut .s 16 (.cut .s 13 (.cut .b 2 (.cut .s 12 (.composite 2) (.cut .a 4 (.cut .c 2 .leaf (.cut .d 2 .leaf .leaf)) (.cut .c 2 (.cut .d 2 (.cut .a 5 .leaf .leaf) .leaf) .leaf))) .leaf) (.cut .b 2 (.cut .s 14 (.composite 2) (.cut .a 4 .leaf (.cut .s 15 (.composite 3) (.composite 2)))) (.cut .s 14 (.composite 2) (.cut .a 4 (.cut .s 15 (.composite 3) (.composite 2)) .leaf)))) (.cut .b 2 .leaf tree_7_11_0))

private def tree_7_11 : Tree :=
  .cut .a 1 .leaf (.cut .b 1 .leaf (.cut .a 2 .leaf (.cut .c 1 .leaf (.cut .s 24 tree_7_11_1 (.cut .a 3 .leaf (.cut .s 50 (.cut .b 2 .leaf (.cut .s 33 (.cut .a 4 .leaf (.cut .s 28 (.cut .c 2 .leaf (.cut .s 26 (.cut .a 5 .leaf (.cut .s 25 (.composite 5) (.composite 2))) .leaf)) .leaf)) .leaf)) .leaf))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem accepted_7_11 : check 7 11 tree_7_11 (initial 11) = true := by decide +kernel

private def tree_7_13_0 : Tree :=
  .cut .s 15 (.cut .a 4 (.cut .s 14 (.composite 2) (.composite 3)) (.cut .s 14 (.composite 2) (.composite 3))) (.cut .a 4 .leaf (.cut .s 16 (.composite 2) (.cut .s 17 (.cut .c 2 (.cut .a 5 .leaf (.cut .d 2 .leaf (.cut .b 3 .leaf (.cut .a 6 .leaf (.cut .a 7 (.cut .b 4 .leaf (.cut .d 3 .leaf .leaf)) (.cut .b 4 (.cut .d 3 (.cut .a 8 .leaf .leaf) .leaf) .leaf)))))) (.cut .a 5 (.cut .d 2 .leaf (.cut .b 3 .leaf .leaf)) (.cut .d 2 (.cut .b 3 (.cut .a 6 .leaf (.cut .a 7 .leaf (.cut .c 3 .leaf (.cut .a 8 .leaf .leaf)))) .leaf) .leaf))) (.composite 2))))

private def tree_7_13_1 : Tree :=
  .cut .s 18 (.cut .b 2 .leaf tree_7_13_0) (.cut .b 2 .leaf (.cut .s 22 (.cut .a 4 .leaf (.cut .s 20 (.cut .s 19 (.cut .c 2 .leaf (.cut .a 5 .leaf (.cut .b 3 .leaf (.cut .d 2 .leaf (.cut .a 6 .leaf (.cut .a 7 .leaf (.cut .c 3 (.cut .b 4 .leaf (.cut .a 8 .leaf (.cut .d 3 .leaf (.cut .b 5 (.cut .a 9 .leaf (.cut .a 10 .leaf .leaf)) .leaf)))) (.cut .b 4 (.cut .a 8 .leaf (.cut .d 3 .leaf (.cut .a 9 (.cut .c 4 .leaf .leaf) .leaf))) .leaf)))))))) (.composite 2)) .leaf)) .leaf))

private def tree_7_13 : Tree :=
  .cut .a 1 .leaf (.cut .b 1 .leaf (.cut .a 2 .leaf (.cut .c 1 .leaf (.cut .s 28 (.cut .a 3 .leaf tree_7_13_1) .leaf))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem accepted_7_13 : check 7 13 tree_7_13 (initial 13) = true := by decide +kernel

private def tree_7_17 : Tree := .leaf

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem accepted_7_17 : check 7 17 tree_7_17 (initial 17) = true := by decide +kernel

private def tree_7_19 : Tree := .leaf

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem accepted_7_19 : check 7 19 tree_7_19 (initial 19) = true := by decide +kernel

private def tree_7_23 : Tree := .leaf

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem accepted_7_23 : check 7 23 tree_7_23 (initial 23) = true := by decide +kernel

private def tree_7_29 : Tree := .leaf

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem accepted_7_29 : check 7 29 tree_7_29 (initial 29) = true := by decide +kernel

private def tree_7_31 : Tree := .leaf

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem accepted_7_31 : check 7 31 tree_7_31 (initial 31) = true := by decide +kernel

/- The prime-power decomposition here follows PanPapag and desenyon in the parent reductions. -/
private theorem splitUnitary {m q : ℕ} (hm : 0 < m) (hq : IsPrimePow q)
    (hc : q.Coprime m) :
    unitaryDivisors (m*q) = unitaryDivisors m ∪ (unitaryDivisors m).image (· * q) := by
  have hq0 := hq.pos
  ext d
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hd, -⟩, hcd⟩
    obtain ⟨t, ht⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_mul_pos_right (ht ▸ Nat.mul_pos hm hq0)
    rw [ht, Nat.mul_div_cancel_left _ hd0] at hcd
    have hqt : q ∣ d*t := ht ▸ dvd_mul_left q m
    rcases (hcd.isPrimePow_dvd_mul hq).1 hqt with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have he : m = b*t := Nat.eq_of_mul_eq_mul_right hq0 (by linear_combination ht)
      subst m
      have hb : 0 < b := Nat.pos_of_mul_pos_left hd0
      exact Or.inr ⟨b, ⟨⟨dvd_mul_right _ _, hm.ne'⟩, by
        simpa [Nat.mul_div_cancel_left _ hb] using (Nat.coprime_mul_iff_left.1 hcd).2⟩, mul_comm ..⟩
    · have he : m = d*b := Nat.eq_of_mul_eq_mul_right hq0 (by linear_combination ht)
      subst m
      exact Or.inl ⟨⟨dvd_mul_right _ _, hm.ne'⟩, by
        simpa [Nat.mul_div_cancel_left _ hd0] using (Nat.coprime_mul_iff_right.1 hcd).2⟩
  · rintro (⟨⟨⟨t, rfl⟩, -⟩, hcd⟩ | ⟨b, ⟨⟨⟨t, rfl⟩, -⟩, hcd⟩, rfl⟩)
    · have hd := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd] at hcd
      refine ⟨⟨dvd_mul_of_dvd_left (dvd_mul_right d t) q, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_assoc, Nat.mul_div_cancel_left _ hd]
      exact hcd.mul_right (Nat.coprime_mul_iff_right.1 hc).1.symm
    · have hb := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hb] at hcd
      refine ⟨⟨mul_dvd_mul (dvd_mul_right b t) dvd_rfl, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_right_comm b t q, Nat.mul_div_cancel_left _ (Nat.mul_pos hb hq0)]
      exact hcd.mul_left (Nat.coprime_mul_iff_right.1 hc).2

private theorem unitarySum {m q : ℕ} (hm : 0 < m) (hq : IsPrimePow q)
    (hc : q.Coprime m) : usigma (m*q) = usigma m * (q+1) := by
  have dis : Disjoint (unitaryDivisors m) ((unitaryDivisors m).image (· * q)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hd'
    have dvd : b*q ∣ m := (Nat.mem_divisors.1 (Finset.mem_filter.1 hd).1).1
    exact hq.ne_one (hc.eq_one_of_dvd ((dvd_mul_left q b).trans dvd))
  unfold usigma
  rw [splitUnitary hm hq hc, Finset.sum_union dis,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hq.pos h),
    ← Finset.sum_mul, mul_add, mul_one, add_comm]


private theorem equality4 {p q r s a b c d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : A (p^a*q^b*r^c*s^d)) :
    value p a * value q b * value r c * value s d = 2 := by
  have cop {i j : ℕ} (hi : i.Prime) (hj : j.Prime) (hij : i < j) (u v : ℕ) :
      (i^u).Coprime (j^v) := ((Nat.coprime_primes hi hj).2 hij.ne).pow u v
  have pq := cop hp hq hpq a b
  have pqr := (cop hp hr (hpq.trans hqr) a c).mul_left (cop hq hr hqr b c)
  have pqrs := ((cop hp hs ((hpq.trans hqr).trans hrs) a d).mul_left
    (cop hq hs (hqr.trans hrs) b d)).mul_left (cop hr hs hrs c d)
  have primePower {i t : ℕ} (hi : i.Prime) (ht : 0 < t) : IsPrimePow (i^t) :=
    (isPrimePow_nat_iff _).2 ⟨i,t,hi,ht,rfl⟩
  have U := unitarySum (m:=1) (q:=p^a) (by decide) (primePower hp ha) (Nat.coprime_one_right _)
  have unit : usigma 1 = 1 := by decide
  simp only [one_mul,unit] at U
  have ppos := hp.pos
  have qpos := hq.pos
  have rpos := hr.pos
  have hn := h.2
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime pqrs,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime pqr,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime pq,
      unitarySum (by positivity) (primePower hs hd) pqrs.symm,
      unitarySum (by positivity) (primePower hr hc) pqr.symm,
      unitarySum (pow_pos hp.pos a) (primePower hq hb) pq.symm,U] at hn
  unfold value
  rw [ratio_sigma hp,ratio_sigma hq,ratio_sigma hr,ratio_sigma hs]
  field_simp
  rw [Nat.mul_comm 2 _] at hn
  exact_mod_cast hn

private theorem cap4 {p q r s a b c d P Q R S : ℕ}
    (hP : 2 ≤ P) (hQ : 2 ≤ Q) (hR : 2 ≤ R) (hS : 2 ≤ S)
    (pi : P ≤ p) (qi : Q ≤ q) (ri : R ≤ r) (si : S ≤ s)
    (h : value p a * value q b * value r c * value s d=2) :
    2 ≤ limit P * limit Q * limit R * limit S := by
  have bd {v k i : ℕ} (hk : 2 ≤ k) (le : k ≤ v) : value v i ≤ limit k :=
    (value_limit (hk.trans le) i).trans (limit_anti hk le)
  have vp := value_nonneg (hP.trans pi) a
  have vq := value_nonneg (hQ.trans qi) b
  have vr := value_nonneg (hR.trans ri) c
  have vs := value_nonneg (hS.trans si) d
  have ap := bd (i:=a) hP pi
  have aq := bd (i:=b) hQ qi
  have ar := bd (i:=c) hR ri
  have as' := bd (i:=d) hS si
  rw [← h]
  exact mul_le_mul (mul_le_mul (mul_le_mul ap aq vq (vp.trans ap)) ar vr
    (mul_nonneg (vp.trans ap) (vq.trans aq))) as' vs
    (mul_nonneg (mul_nonneg (vp.trans ap) (vq.trans aq)) (vr.trans ar))

private theorem support {p q r s a b c d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hs : s.Prime) (p3 : 3 ≤ p) (pq : p < q) (qr : q < r) (rs : r < s)
    (eqn : value p a * value q b * value r c * value s d=2) :
    p=3 ∧ (q=5 ∨ q=7) ∧ r < 37 := by
  have gap {u v : ℕ} (hu : u.Prime) (hv : v.Prime) (hh : 3 ≤ u) (lt : u < v) : u+2 ≤ v := by
    obtain ⟨i,hi⟩ := hu.odd_of_ne_two (by omega)
    obtain ⟨j,hj⟩ := hv.odd_of_ne_two (by omega)
    omega
  have gq := gap hp hq p3 pq
  have gr := gap hq hr (by omega) qr
  have gs := gap hr hs (by omega) rs
  have p5 : p < 5 := by
    by_contra! big
    have bad := cap4 (P:=5) (Q:=7) (R:=9) (S:=11) (by decide) (by decide) (by decide) (by decide) big
      (by omega) (by omega) (by omega) eqn
    norm_num [limit] at bad
  have ep : p=3 := by interval_cases p <;> norm_num at *
  have q11 : q < 11 := by
    by_contra! big
    have bad := cap4 (P:=3) (Q:=11) (R:=11) (S:=11) (by decide) (by decide) (by decide) (by decide) p3
      big (by omega) (by omega) eqn
    norm_num [limit] at bad
  have q5 : 5 ≤ q := by omega
  have eq : q=5 ∨ q=7 := by interval_cases q <;> norm_num at *
  have r37 : r < 37 := by
    by_contra! big
    have bad := cap4 (P:=3) (Q:=5) (R:=37) (S:=37) (by decide) (by decide) (by decide) (by decide) p3
      (by omega) big (by omega) eqn
    norm_num [limit] at bad
  exact ⟨ep,eq,r37⟩

private theorem exclude_ordered {p q r s a b c d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hp3 : 3 ≤ p) (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ¬ A (p^a*q^b*r^c*s^d) := by
  intro H
  have eqn := equality4 hp hq hr hs hpq hqr hrs ha hb hc hd H
  have hd2 : 2 ≤ d := by
    by_contra! small
    have one : d=1 := by omega
    rw [one,pow_one] at H
    have cop {u e : ℕ} (hu : u.Prime) (lt : u < s) : s.Coprime (u^e) :=
      ((Nat.coprime_primes hs hu).2 lt.ne.symm).pow_right e
    have copall : s.Coprime (p^a*q^b*r^c) :=
      ((cop hp ((hpq.trans hqr).trans hrs)).mul_right (cop hq (hqr.trans hrs))).mul_right (cop hr hrs)
    have pos : 0 < p^a*q^b*r^c :=
      Nat.mul_pos (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)) (pow_pos hr.pos _)
    exact odd_triple_exclusion hp hq hr hp3 hpq hqr ha hb hc
      (A_of_mul_prime pos H hs (hs.coprime_iff_not_dvd.mp copall))
  obtain ⟨rfl,eq,rbound⟩ := support hp hq hr hs hp3 hpq hqr hrs eqn
  let v : Axis → ℕ
    | .a => a | .b => b | .c => c | .d => d | .s => s
  have inside : Inside (initial r) v := by
    intro i
    cases i <;> simp [initial,Box.get,Interval.contains,v] <;> omega
  have finish (t : Tree) (cert : check q r t (initial r)=true) : False :=
    check_sound hq.two_le hr.two_le t _ v inside hs hd cert eqn
  rcases eq with rfl|rfl
  · have choices : ∀ t : Fin 37, t.val.Prime → 5 < t.val → t.val=7 ∨ t.val=11 ∨ t.val=13 ∨ t.val=17 ∨ t.val=19 ∨ t.val=23 ∨ t.val=29 ∨ t.val=31 := by decide
    rcases choices ⟨r,rbound⟩ hr hqr with h|h|h|h|h|h|h|h
    · change r=7 at h
      subst r
      exact finish _ accepted_5_7
    · change r=11 at h
      subst r
      exact finish _ accepted_5_11
    · change r=13 at h
      subst r
      exact finish _ accepted_5_13
    · change r=17 at h
      subst r
      exact finish _ accepted_5_17
    · change r=19 at h
      subst r
      exact finish _ accepted_5_19
    · change r=23 at h
      subst r
      exact finish _ accepted_5_23
    · change r=29 at h
      subst r
      exact finish _ accepted_5_29
    · change r=31 at h
      subst r
      exact finish _ accepted_5_31
  · have choices : ∀ t : Fin 37, t.val.Prime → 7 < t.val → t.val=11 ∨ t.val=13 ∨ t.val=17 ∨ t.val=19 ∨ t.val=23 ∨ t.val=29 ∨ t.val=31 := by decide
    rcases choices ⟨r,rbound⟩ hr hqr with h|h|h|h|h|h|h
    · change r=11 at h
      subst r
      exact finish _ accepted_7_11
    · change r=13 at h
      subst r
      exact finish _ accepted_7_13
    · change r=17 at h
      subst r
      exact finish _ accepted_7_17
    · change r=19 at h
      subst r
      exact finish _ accepted_7_19
    · change r=23 at h
      subst r
      exact finish _ accepted_7_23
    · change r=29 at h
      subst r
      exact finish _ accepted_7_29
    · change r=31 at h
      subst r
      exact finish _ accepted_7_31

end FourPrimeRatios

open FourPrimeRatios in
theorem OMA.solution : OMA.R_OeisA63880_mod_216_of_a_R1_H1_R2.H1 := by
  classical
  intro n ho card H
  let P := n.primeFactors
  let e : Fin 4 ≃o P := P.orderIsoOfFin card
  let p (i : Fin 4) : ℕ := e i
  let a (i : Fin 4) := n.factorization (p i)
  have info (i : Fin 4) : (p i).Prime ∧ 3 ≤ p i ∧ 0 < a i := by
    have mem : p i ∈ n.primeFactors := (e i).property
    obtain ⟨hp,hd,hn⟩ := Nat.mem_primeFactors.mp mem
    refine ⟨hp,?_,hp.factorization_pos_of_dvd hn hd⟩
    have ll := hp.two_le
    obtain ⟨u,hu⟩ := ho
    by_contra! small
    have he : p i=2 := by omega
    rw [he] at hd
    omega
  have inc : StrictMono p := e.strictMono
  have fac : p 0^a 0 * p 1^a 1 * p 2^a 2 * p 3^a 3 = n := by
    calc _ = ∏ i : Fin 4, p i^a i := by simp [Fin.prod_univ_succ]; ring
         _ = ∏ i : P, (i:ℕ)^n.factorization i :=
              Fintype.prod_equiv e.toEquiv _ _ (fun _ => rfl)
         _ = ∏ i∈P, i^n.factorization i := Finset.prod_coe_sort P (fun i => i^n.factorization i)
         _ = n := (Nat.prod_primeFactors_pow_factorization H.1.ne').symm
  exact exclude_ordered (info 0).1 (info 1).1 (info 2).1 (info 3).1 (info 0).2.1
    (inc (show (0:Fin 4)<1 by decide)) (inc (show (1:Fin 4)<2 by decide))
    (inc (show (2:Fin 4)<3 by decide)) (info 0).2.2 (info 1).2.2 (info 2).2.2 (info 3).2.2
    (fac ▸ H)
