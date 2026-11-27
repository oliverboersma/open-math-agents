import OMAReductions.R_Erdos97_erdos_97_variants_three_unit_distance_cut_min_R1

/-! Exact interval arithmetic for the Fishburn–Reeds twenty-point cut construction. -/

open Finset EuclideanGeometry
open scoped EuclideanGeometry

namespace FishburnReeds

structure Box where
  lo : ℚ
  hi : ℚ

def Box.Covers (B : Box) (x : ℝ) : Prop := (B.lo : ℝ) ≤ x ∧ x ≤ (B.hi : ℝ)

def Box.constant (q : ℚ) : Box := ⟨q,q⟩

def Box.add (A B : Box) : Box := ⟨A.lo+B.lo,A.hi+B.hi⟩

def Box.neg (A : Box) : Box := ⟨-A.hi,-A.lo⟩

def Box.sub (A B : Box) : Box := A.add B.neg

def Box.mul (A B : Box) : Box :=
  ⟨min (min (A.lo*B.lo) (A.hi*B.lo)) (min (A.lo*B.hi) (A.hi*B.hi)),
   max (max (A.lo*B.lo) (A.hi*B.lo)) (max (A.lo*B.hi) (A.hi*B.hi))⟩

theorem Box.constant_sound (q : ℚ) : (Box.constant q).Covers (q : ℝ) := ⟨le_rfl,le_rfl⟩

theorem Box.add_sound {A B : Box} {x y : ℝ} (hx : A.Covers x) (hy : B.Covers y) :
    (A.add B).Covers (x+y) := by
  unfold Box.Covers Box.add
  push_cast
  exact ⟨add_le_add hx.1 hy.1,add_le_add hx.2 hy.2⟩

theorem Box.neg_sound {A : Box} {x : ℝ} (hx : A.Covers x) : A.neg.Covers (-x) := by
  unfold Box.Covers Box.neg
  push_cast
  exact ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩

theorem Box.sub_sound {A B : Box} {x y : ℝ} (hx : A.Covers x) (hy : B.Covers y) :
    (A.sub B).Covers (x-y) := by
  simpa only [sub_eq_add_neg, Box.sub] using Box.add_sound hx (Box.neg_sound hy)

private theorem mul_corner {a x b : ℝ} (hlo : a ≤ x) (hhi : x ≤ b) (z : ℝ) :
    min (a*z) (b*z) ≤ x*z ∧ x*z ≤ max (a*z) (b*z) := by
  rcases le_or_gt 0 z with hz | hz
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hlo hz),
      (mul_le_mul_of_nonneg_right hhi hz).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hhi hz.le),
      (mul_le_mul_of_nonpos_right hlo hz.le).trans (le_max_left _ _)⟩

theorem Box.mul_sound {A B : Box} {x y : ℝ} (hx : A.Covers x) (hy : B.Covers y) :
    (A.mul B).Covers (x*y) := by
  have h0 := mul_corner hx.1 hx.2 (B.lo : ℝ)
  have h1 := mul_corner hx.1 hx.2 (B.hi : ℝ)
  have h := mul_corner hy.1 hy.2 x
  rw [mul_comm _ x, mul_comm (y) x, mul_comm (B.hi : ℝ) x] at h
  unfold Box.Covers Box.mul
  simp only [Rat.cast_mono.map_min, Rat.cast_mono.map_max, Rat.cast_mul]
  exact ⟨(le_min ((min_le_left _ _).trans h0.1) ((min_le_right _ _).trans h1.1)).trans h.1,
    h.2.trans (max_le (h0.2.trans (le_max_left _ _)) (h1.2.trans (le_max_right _ _)))⟩

abbrev RPoint := ℝ × ℝ
abbrev QPoint := Box × Box

def QPoint.Covers (B : QPoint) (x : RPoint) : Prop := B.1.Covers x.1 ∧ B.2.Covers x.2

def QPoint.constant (x y : ℚ) : QPoint := ⟨Box.constant x,Box.constant y⟩

def sqDist (p q : RPoint) : ℝ := (q.1-p.1)*(q.1-p.1)+(q.2-p.2)*(q.2-p.2)

def sqBox (p q : QPoint) : Box :=
  ((q.1.sub p.1).mul (q.1.sub p.1)).add ((q.2.sub p.2).mul (q.2.sub p.2))

theorem sqBox_sound {P Q : QPoint} {p q : RPoint}
    (hp : P.Covers p) (hq : Q.Covers q) : (sqBox P Q).Covers (sqDist p q) := by
  have hx := Box.sub_sound hq.1 hp.1
  have hy := Box.sub_sound hq.2 hp.2
  exact Box.add_sound (Box.mul_sound hx hx) (Box.mul_sound hy hy)

noncomputable def reflect (p : RPoint) : RPoint := (-p.1,p.2)

noncomputable def leftPointReflected (p q : RPoint) : RPoint :=
  let k := Real.sqrt (1 / sqDist p q - 1/4)
  (-(p.1+q.1)*(1/2) + k*(q.2-p.2), (p.2+q.2)*(1/2) + k*(q.1-p.1))

def leftBoxReflected (p q : QPoint) (k : Box) : QPoint :=
  ((((p.1.add q.1).neg).mul (Box.constant (1/2))).add (k.mul (q.2.sub p.2)),
   (((p.2.add q.2)).mul (Box.constant (1/2))).add (k.mul (q.1.sub p.1)))

def ValidFactor (p q : QPoint) (k : Box) : Prop :=
  let S := sqBox p q
  0 < S.lo ∧ S.hi < 4 ∧ 0 ≤ k.hi ∧
    k.lo^2 ≤ 1/S.hi-1/4 ∧ 1/S.lo-1/4 ≤ k.hi^2

instance (p q : QPoint) (k : Box) : Decidable (ValidFactor p q k) :=
  inferInstanceAs (Decidable (0 < (sqBox p q).lo ∧ (sqBox p q).hi < 4 ∧ 0 ≤ k.hi ∧
    k.lo^2 ≤ 1/(sqBox p q).hi-1/4 ∧ 1/(sqBox p q).lo-1/4 ≤ k.hi^2))

theorem validFactor_sound {P Q : QPoint} {p q : RPoint} {k : Box}
    (hp : P.Covers p) (hq : Q.Covers q) (hv : ValidFactor P Q k) :
    0 < sqDist p q ∧ sqDist p q < 4 ∧
      (leftBoxReflected P Q k).Covers (leftPointReflected p q) := by
  have ⟨hslo,hshi⟩ := sqBox_sound hp hq
  obtain ⟨hpos,hfour,hkhi,hfactlo,hfacthi⟩ := hv
  have hpos' : 0 < ((sqBox P Q).lo : ℝ) := by exact_mod_cast hpos
  have hfour' : ((sqBox P Q).hi : ℝ) < 4 := by exact_mod_cast hfour
  have hdist0 := hpos'.trans_le hslo
  have hdist4 := hshi.trans_lt hfour'
  refine ⟨hdist0,hdist4,?_⟩
  have hkl : (k.lo : ℝ)^2 ≤ 1 / ((sqBox P Q).hi : ℝ) - 1/4 := by
    have h : ((k.lo^2 : ℚ) : ℝ) ≤ ((1/(sqBox P Q).hi-1/4 : ℚ) : ℝ) := Rat.cast_le.mpr hfactlo
    push_cast at h
    exact h
  have hkh : 1 / ((sqBox P Q).lo : ℝ) - 1/4 ≤ (k.hi : ℝ)^2 := by
    have h : ((1/(sqBox P Q).lo-1/4 : ℚ) : ℝ) ≤ ((k.hi^2 : ℚ) : ℝ) := Rat.cast_le.mpr hfacthi
    push_cast at h
    exact h
  have hk : k.Covers (Real.sqrt (1 / sqDist p q - 1/4)) := by
    constructor
    · exact Real.le_sqrt_of_sq_le (hkl.trans ((sub_le_sub_iff_right _).mpr
        (one_div_le_one_div_of_le hdist0 hshi)))
    · exact Real.sqrt_le_iff.mpr ⟨by exact_mod_cast hkhi,
        ((sub_le_sub_iff_right _).mpr (one_div_le_one_div_of_le hpos' hslo)).trans hkh⟩
  have hh : (Box.constant (1/2)).Covers (1/2) := by simpa using Box.constant_sound (1/2)
  refine ⟨?_,?_⟩
  · exact Box.add_sound
      (Box.mul_sound (Box.neg_sound (Box.add_sound hp.1 hq.1)) hh)
      (Box.mul_sound hk (Box.sub_sound hq.2 hp.2))
  · exact Box.add_sound
      (Box.mul_sound (Box.add_sound hp.2 hq.2) hh)
      (Box.mul_sound hk (Box.sub_sound hq.1 hp.1))

theorem leftPointReflected_dist {p q : RPoint} (h₀ : 0 < sqDist p q) (h₄ : sqDist p q < 4) :
    sqDist (reflect (leftPointReflected p q)) p = 1 ∧
      sqDist (reflect (leftPointReflected p q)) q = 1 := by
  let k := Real.sqrt (1 / sqDist p q - 1/4)
  have hk : k^2 = 1 / sqDist p q - 1/4 := Real.sq_sqrt
    (sub_nonneg.mpr (one_div_le_one_div_of_le h₀ h₄.le))
  have hr : sqDist p q * (1/4+k^2) = 1 := by
    rw [hk,show (1/4:ℝ) + (1 / sqDist p q-1/4)=1 / sqDist p q by ring]
    field_simp
  constructor
  · calc
      _ = sqDist p q * (1/4+k^2) := by
        change sqDist (-( -(p.1+q.1)*(1/2) + k*(q.2-p.2)),
          (p.2+q.2)*(1/2)+k*(q.1-p.1)) p = _
        unfold sqDist
        ring
      _ = _ := hr
  · calc
      _ = sqDist p q * (1/4+k^2) := by
        change sqDist (-( -(p.1+q.1)*(1/2) + k*(q.2-p.2)),
          (p.2+q.2)*(1/2)+k*(q.1-p.1)) q = _
        unfold sqDist
        ring
      _ = _ := hr

theorem leftPointReflected_continuousOn {S : Set ℝ} {p q : ℝ → RPoint}
    (hp : ContinuousOn p S) (hq : ContinuousOn q S)
    (hD : ∀ t ∈ S, 0 < sqDist (p t) (q t)) : ContinuousOn (fun t => leftPointReflected (p t) (q t)) S := by
  have hd : ContinuousOn (fun t => sqDist (p t) (q t)) S := by unfold sqDist; fun_prop
  have hi : ContinuousOn (fun t => (1 : ℝ) / sqDist (p t) (q t)) S :=
    continuousOn_const.div hd (fun t ht => (hD t ht).ne')
  have hk : ContinuousOn (fun t => Real.sqrt ((1 : ℝ) / sqDist (p t) (q t) - 1/4)) S :=
    (hi.sub continuousOn_const).sqrt
  exact ((hp.fst.add hq.fst).neg.mul continuousOn_const |>.add
    (hk.mul (hq.snd.sub hp.snd))).prodMk
    ((hp.snd.add hq.snd).mul continuousOn_const |>.add (hk.mul (hq.fst.sub hp.fst)))

end FishburnReeds


namespace FishburnReeds

private def tLower : ℚ := 52099624685 / 10^11
private def tUpper : ℚ := 52099624688 / 10^11
private def parameterBox : Box := ⟨tLower,tUpper⟩
private def brange : Set ℝ := Set.Icc (tLower : ℝ) (tUpper : ℝ)

private noncomputable def p4 (_ : ℝ) : RPoint := (13/25,3/100)
private noncomputable def p5 (t : ℝ) : RPoint := (t,33/1000)
private noncomputable def p6 (_ : ℝ) : RPoint := (261/500,361/10000)

private noncomputable def p7 (t : ℝ) : RPoint := leftPointReflected (p5 t) (p6 t)

private noncomputable def p8 (t : ℝ) : RPoint := leftPointReflected (p4 t) (p6 t)

private noncomputable def p9 (t : ℝ) : RPoint := leftPointReflected (p4 t) (p5 t)

private noncomputable def p1 (t : ℝ) : RPoint := leftPointReflected (p6 t) (p9 t)

private noncomputable def p2 (t : ℝ) : RPoint := leftPointReflected (p5 t) (p8 t)

private noncomputable def p3 (t : ℝ) : RPoint := leftPointReflected (p4 t) (p7 t)

private noncomputable def p10 (t : ℝ) : RPoint := leftPointReflected (p1 t) (p2 t)

private noncomputable def points (t : ℝ) : Fin 10 → RPoint :=
  ![p1 t,p2 t,p3 t,p4 t,p5 t,p6 t,p7 t,p8 t,p9 t,p10 t]

private def box4 (_T : Box) (_F : Fin 7 → Box) : QPoint := QPoint.constant (13/25) (3/100)
private def box5 (T : Box) (_F : Fin 7 → Box) : QPoint := (T,Box.constant (33/1000))
private def box6 (_T : Box) (_F : Fin 7 → Box) : QPoint := QPoint.constant (261/500) (361/10000)

private def box7 (T : Box) (F : Fin 7 → Box) : QPoint :=
  leftBoxReflected (box5 T F) (box6 T F) (F 0)

private def box8 (T : Box) (F : Fin 7 → Box) : QPoint :=
  leftBoxReflected (box4 T F) (box6 T F) (F 1)

private def box9 (T : Box) (F : Fin 7 → Box) : QPoint :=
  leftBoxReflected (box4 T F) (box5 T F) (F 2)

private def box1 (T : Box) (F : Fin 7 → Box) : QPoint :=
  leftBoxReflected (box6 T F) (box9 T F) (F 3)

private def box2 (T : Box) (F : Fin 7 → Box) : QPoint :=
  leftBoxReflected (box5 T F) (box8 T F) (F 4)

private def box3 (T : Box) (F : Fin 7 → Box) : QPoint :=
  leftBoxReflected (box4 T F) (box7 T F) (F 5)

private def box10 (T : Box) (F : Fin 7 → Box) : QPoint :=
  leftBoxReflected (box1 T F) (box2 T F) (F 6)

private def boxPoints (T : Box) (F : Fin 7 → Box) : Fin 10 → QPoint :=
  ![box1 T F,box2 T F,box3 T F,box4 T F,box5 T F,box6 T F,box7 T F,box8 T F,box9 T F,box10 T F]

private def Valid (T : Box) (F : Fin 7 → Box) : Prop :=
    ValidFactor (box5 T F) (box6 T F) (F 0) ∧
    ValidFactor (box4 T F) (box6 T F) (F 1) ∧
    ValidFactor (box4 T F) (box5 T F) (F 2) ∧
    ValidFactor (box6 T F) (box9 T F) (F 3) ∧
    ValidFactor (box5 T F) (box8 T F) (F 4) ∧
    ValidFactor (box4 T F) (box7 T F) (F 5) ∧
    ValidFactor (box1 T F) (box2 T F) (F 6)

private instance (T : Box) (F : Fin 7 → Box) : Decidable (Valid T F) := by
  unfold Valid
  infer_instance

private structure GeometryAt (t : ℝ) : Prop where
  good7 : 0 < sqDist (p5 t) (p6 t) ∧ sqDist (p5 t) (p6 t) < 4
  good8 : 0 < sqDist (p4 t) (p6 t) ∧ sqDist (p4 t) (p6 t) < 4
  good9 : 0 < sqDist (p4 t) (p5 t) ∧ sqDist (p4 t) (p5 t) < 4
  good1 : 0 < sqDist (p6 t) (p9 t) ∧ sqDist (p6 t) (p9 t) < 4
  good2 : 0 < sqDist (p5 t) (p8 t) ∧ sqDist (p5 t) (p8 t) < 4
  good3 : 0 < sqDist (p4 t) (p7 t) ∧ sqDist (p4 t) (p7 t) < 4
  good10 : 0 < sqDist (p1 t) (p2 t) ∧ sqDist (p1 t) (p2 t) < 4

private theorem bounds_pass {T : Box} {F : Fin 7 → Box} (h : Valid T F)
    {t : ℝ} (ht : T.Covers t) :
    (∀ i, (boxPoints T F i).Covers (points t i)) ∧ GeometryAt t := by
  obtain ⟨hc7,hc8,hc9,hc1,hc2,hc3,hc10⟩ := h
  have h4 : (box4 T F).Covers (p4 t) := by
    unfold p4 box4 QPoint.constant QPoint.Covers Box.Covers Box.constant
    norm_num
  have h5 : (box5 T F).Covers (p5 t) := ⟨ht, by norm_num [p5,box5,QPoint.constant,Box.Covers,Box.constant]⟩
  have h6 : (box6 T F).Covers (p6 t) := by
    unfold p6 box6 QPoint.constant QPoint.Covers Box.Covers Box.constant
    norm_num
  obtain ⟨hd7,hmax7,h7⟩ := validFactor_sound h5 h6 hc7
  obtain ⟨hd8,hmax8,h8⟩ := validFactor_sound h4 h6 hc8
  obtain ⟨hd9,hmax9,h9⟩ := validFactor_sound h4 h5 hc9
  obtain ⟨hd1,hmax1,h1⟩ := validFactor_sound h6 h9 hc1
  obtain ⟨hd2,hmax2,h2⟩ := validFactor_sound h5 h8 hc2
  obtain ⟨hd3,hmax3,h3⟩ := validFactor_sound h4 h7 hc3
  obtain ⟨hd10,hmax10,h10⟩ := validFactor_sound h1 h2 hc10
  refine ⟨?_,⟨⟨hd7,hmax7⟩,⟨hd8,hmax8⟩,⟨hd9,hmax9⟩,⟨hd1,hmax1⟩,⟨hd2,hmax2⟩,⟨hd3,hmax3⟩,⟨hd10,hmax10⟩⟩⟩
  intro i
  fin_cases i
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10

private def rangeFactors : Fin 7 → Box :=
  ![⟨306893628373369657128414265780609879122176179544/10^45,306893629243760057252080528891376034616089487152/10^45⟩,
    ⟨155774532146060225288041582201471558596605883931/10^45,155774532146060225288041582201471558596605883932/10^45⟩,
    ⟨316345898843911581808581380220376564543604234540/10^45,316345899790098675862251280627701655376173222667/10^45⟩,
    ⟨3042593446349595111878172929205204093184500235/10^45,3042593550529273212120895188839133994187007360/10^45⟩,
    ⟨3037636475687753676023887249874335000520924640/10^45,3037636475769159803358231831525576787155745641/10^45⟩,
    ⟨3032872844908113938237897180851743754192478164/10^45,3032872944856754749952468624246191421839289103/10^45⟩,
    ⟨285695918069705088296036805744200103261245955563/10^45,285700308150814393822339955257800444271273764675/10^45⟩]

private def leftFactors : Fin 7 → Box :=
  ![⟨306893628373369657128414265780609879122176179544/10^45,306893628373369657128414265780609879122176179545/10^45⟩,
    ⟨155774532146060225288041582201471558596605883931/10^45,155774532146060225288041582201471558596605883932/10^45⟩,
    ⟨316345899790098675862251280627701655376173222666/10^45,316345899790098675862251280627701655376173222667/10^45⟩,
    ⟨3042593541832364679128316643898827340806660523/10^45,3042593541832364679128316643898827340806660554/10^45⟩,
    ⟨3037636475769159803358231831525576787155745610/10^45,3037636475769159803358231831525576787155745641/10^45⟩,
    ⟨3032872852986470094356516797498259643529487338/10^45,3032872852986470094356516797498259643529487383/10^45⟩,
    ⟨285697969212121764855990660574320393874230066270/10^45,285697969212121764855990660574320393874253386034/10^45⟩]

private def rightFactors : Fin 7 → Box :=
  ![⟨306893629243760057252080528891376034616089487151/10^45,306893629243760057252080528891376034616089487152/10^45⟩,
    ⟨155774532146060225288041582201471558596605883931/10^45,155774532146060225288041582201471558596605883932/10^45⟩,
    ⟨316345898843911581808581380220376564543604234540/10^45,316345898843911581808581380220376564543604234541/10^45⟩,
    ⟨3042593455046503382457032051310803281364346344/10^45,3042593455046503382457032051310803281364346390/10^45⟩,
    ⟨3037636475687753676023887249874335000520924640/10^45,3037636475687753676023887249874335000520924671/10^45⟩,
    ⟨3032872936778398363821157867795221421537696774/10^45,3032872936778398363821157867795221421537696805/10^45⟩,
    ⟨285698256986256319344516645897679389733063167373/10^45,285698256986256319344516645897679389733086487207/10^45⟩]

set_option maxRecDepth 18000 in
private theorem range_valid : Valid parameterBox rangeFactors := by decide +kernel

set_option maxRecDepth 18000 in
private theorem left_valid : Valid (Box.constant tLower) leftFactors := by decide +kernel

set_option maxRecDepth 18000 in
private theorem right_valid : Valid (Box.constant tUpper) rightFactors := by decide +kernel

private theorem range_pass {t : ℝ} (ht : t ∈ brange) :
    (∀ i, (boxPoints parameterBox rangeFactors i).Covers (points t i)) ∧ GeometryAt t :=
  bounds_pass range_valid ht

private def defectBox (P Q : QPoint) : Box :=
  let x := P.1.add Q.1
  let y := Q.2.sub P.2
  ((x.mul x).add (y.mul y)).sub (Box.constant 1)

private noncomputable def defect (t : ℝ) : ℝ := sqDist (reflect (p10 t)) (p3 t)-1

private theorem defectBox_sound {P Q : QPoint} {p q : RPoint} (hp : P.Covers p) (hq : Q.Covers q) :
    (defectBox P Q).Covers (sqDist (reflect p) q-1) := by
  have hx := Box.add_sound hp.1 hq.1
  have hy := Box.sub_sound hq.2 hp.2
  have h := Box.sub_sound (Box.add_sound (Box.mul_sound hx hx) (Box.mul_sound hy hy))
    (Box.constant_sound 1)
  push_cast at h
  unfold defectBox sqDist reflect
  convert h using 2; ring

set_option maxRecDepth 18000 in
private theorem left_defect : 0 < defect (tLower : ℝ) := by
  have h := (bounds_pass left_valid (Box.constant_sound tLower)).1
  have ht := defectBox_sound (h 9) (h 2)
  change (defectBox (box10 _ _) (box3 _ _)).Covers (defect (tLower : ℝ)) at ht
  have hk : 0 < (defectBox (box10 (Box.constant tLower) leftFactors)
      (box3 (Box.constant tLower) leftFactors)).lo := by decide +kernel
  exact (Rat.cast_pos.mpr hk).trans_le ht.1

set_option maxRecDepth 18000 in
private theorem right_defect : defect (tUpper : ℝ) < 0 := by
  have h := (bounds_pass right_valid (Box.constant_sound tUpper)).1
  have ht := defectBox_sound (h 9) (h 2)
  change (defectBox (box10 _ _) (box3 _ _)).Covers (defect (tUpper : ℝ)) at ht
  have hk : (defectBox (box10 (Box.constant tUpper) rightFactors)
      (box3 (Box.constant tUpper) rightFactors)).hi < 0 := by decide +kernel
  exact ht.2.trans_lt (Rat.cast_lt_zero.mpr hk)

private theorem pc4 : ContinuousOn p4 brange := by unfold p4; fun_prop

private theorem pc5 : ContinuousOn p5 brange := by unfold p5; fun_prop

private theorem pc6 : ContinuousOn p6 brange := by unfold p6; fun_prop

private theorem pc7 : ContinuousOn p7 brange :=
  leftPointReflected_continuousOn pc5 pc6 (fun _ ht => (range_pass ht).2.good7.1)

private theorem pc8 : ContinuousOn p8 brange :=
  leftPointReflected_continuousOn pc4 pc6 (fun _ ht => (range_pass ht).2.good8.1)

private theorem pc9 : ContinuousOn p9 brange :=
  leftPointReflected_continuousOn pc4 pc5 (fun _ ht => (range_pass ht).2.good9.1)

private theorem pc1 : ContinuousOn p1 brange :=
  leftPointReflected_continuousOn pc6 pc9 (fun _ ht => (range_pass ht).2.good1.1)

private theorem pc2 : ContinuousOn p2 brange :=
  leftPointReflected_continuousOn pc5 pc8 (fun _ ht => (range_pass ht).2.good2.1)

private theorem pc3 : ContinuousOn p3 brange :=
  leftPointReflected_continuousOn pc4 pc7 (fun _ ht => (range_pass ht).2.good3.1)

private theorem pc10 : ContinuousOn p10 brange :=
  leftPointReflected_continuousOn pc1 pc2 (fun _ ht => (range_pass ht).2.good10.1)

private theorem defect_continuousOn : ContinuousOn defect brange := by
  unfold defect sqDist reflect
  have hx : ContinuousOn (fun t => (p3 t).1 - -(p10 t).1) brange :=
    pc3.fst.sub pc10.fst.neg
  have hy : ContinuousOn (fun t => (p3 t).2 - (p10 t).2) brange :=
    pc3.snd.sub pc10.snd
  exact ((hx.mul hx).add (hy.mul hy)).sub continuousOn_const

private theorem exists_root : ∃ t ∈ brange, defect t = 0 := by
  have horder : (tLower : ℝ) ≤ (tUpper : ℝ) := by norm_num [tLower,tUpper]
  have him := intermediate_value_Icc' horder defect_continuousOn
  exact him ⟨right_defect.le,left_defect.le⟩

private def qSlope : Fin 10 → ℚ := ![61/100,588/1000,1/2,36/100,328/1000,0,
  -313/1000,-328/1000,-43/100,-3/5]

private def supportBox (i j : Fin 10) : Box :=
  let B := boxPoints parameterBox rangeFactors j
  B.1.sub ((Box.constant (qSlope i)).mul B.2)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 4000000 in
private theorem support_cert : ∀ i j : Fin 10, i ≠ j →
    (supportBox i j).hi < (supportBox i i).lo := by decide +kernel

set_option maxRecDepth 18000 in
private theorem x_cert : ∀ i : Fin 10, 0 < (boxPoints parameterBox rangeFactors i).1.lo := by
  decide +kernel

private theorem strict_support {t : ℝ} (ht : t ∈ brange) {i j : Fin 10}
    (hij : i ≠ j) :
    (points t j).1 - (qSlope i : ℝ) * (points t j).2 <
      (points t i).1 - (qSlope i : ℝ) * (points t i).2 := by
  have h := (range_pass ht).1
  have hbox (j : Fin 10) := Box.sub_sound (h j).1
    (Box.mul_sound (Box.constant_sound (qSlope i)) (h j).2)
  exact (hbox j).2.trans_lt ((Rat.cast_lt.mpr (support_cert i j hij)).trans_le (hbox i).1)

private theorem x_pos {t : ℝ} (ht : t ∈ brange) (i : Fin 10) : 0 < (points t i).1 :=
  (Rat.cast_pos.mpr (x_cert i)).trans_le ((range_pass ht).1 i).1.1

private def neigh : Fin 10 → Finset (Fin 10) :=
  ![{5, 8, 9},{4, 7, 9},{3, 6, 9},{2, 7, 8},{1, 6, 8},{0, 6, 7},{2, 4, 5},{1, 3, 5},{0, 3, 4},{0, 1, 2}]

private theorem neigh_card : ∀ i : Fin 10, (neigh i).card = 3 := by decide +kernel

private theorem unit_reverse {p q : RPoint} (h : sqDist (reflect p) q = 1) :
    sqDist (reflect q) p = 1 := by
  calc
    _ = sqDist (reflect p) q := by unfold sqDist reflect; ring
    _ = 1 := h

private theorem unit_cert {t : ℝ} (hg : GeometryAt t) (he : defect t = 0)
    (i j : Fin 10) (hj : j ∈ neigh i) :
    sqDist (reflect (points t i)) (points t j) = 1 := by
  have ⟨h7_5, h7_6⟩ := leftPointReflected_dist hg.good7.1 hg.good7.2
  change sqDist (reflect (points t 6)) (points t 4) = 1 at h7_5
  change sqDist (reflect (points t 6)) (points t 5) = 1 at h7_6
  have ⟨h8_4, h8_6⟩ := leftPointReflected_dist hg.good8.1 hg.good8.2
  change sqDist (reflect (points t 7)) (points t 3) = 1 at h8_4
  change sqDist (reflect (points t 7)) (points t 5) = 1 at h8_6
  have ⟨h9_4, h9_5⟩ := leftPointReflected_dist hg.good9.1 hg.good9.2
  change sqDist (reflect (points t 8)) (points t 3) = 1 at h9_4
  change sqDist (reflect (points t 8)) (points t 4) = 1 at h9_5
  have ⟨h1_6, h1_9⟩ := leftPointReflected_dist hg.good1.1 hg.good1.2
  change sqDist (reflect (points t 0)) (points t 5) = 1 at h1_6
  change sqDist (reflect (points t 0)) (points t 8) = 1 at h1_9
  have ⟨h2_5, h2_8⟩ := leftPointReflected_dist hg.good2.1 hg.good2.2
  change sqDist (reflect (points t 1)) (points t 4) = 1 at h2_5
  change sqDist (reflect (points t 1)) (points t 7) = 1 at h2_8
  have ⟨h3_4, h3_7⟩ := leftPointReflected_dist hg.good3.1 hg.good3.2
  change sqDist (reflect (points t 2)) (points t 3) = 1 at h3_4
  change sqDist (reflect (points t 2)) (points t 6) = 1 at h3_7
  have ⟨h10_1, h10_2⟩ := leftPointReflected_dist hg.good10.1 hg.good10.2
  change sqDist (reflect (points t 9)) (points t 0) = 1 at h10_1
  change sqDist (reflect (points t 9)) (points t 1) = 1 at h10_2
  have h10_3 : sqDist (reflect (points t 9)) (points t 2) = 1 := sub_eq_zero.mp he
  fin_cases i
  · change j ∈ ({5, 8, 9} : Finset (Fin 10)) at hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact h1_6
    · exact h1_9
    · exact (unit_reverse h10_1)
  · change j ∈ ({4, 7, 9} : Finset (Fin 10)) at hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact h2_5
    · exact h2_8
    · exact (unit_reverse h10_2)
  · change j ∈ ({3, 6, 9} : Finset (Fin 10)) at hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact h3_4
    · exact h3_7
    · exact (unit_reverse h10_3)
  · change j ∈ ({2, 7, 8} : Finset (Fin 10)) at hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact (unit_reverse h3_4)
    · exact (unit_reverse h8_4)
    · exact (unit_reverse h9_4)
  · change j ∈ ({1, 6, 8} : Finset (Fin 10)) at hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact (unit_reverse h2_5)
    · exact (unit_reverse h7_5)
    · exact (unit_reverse h9_5)
  · change j ∈ ({0, 6, 7} : Finset (Fin 10)) at hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact (unit_reverse h1_6)
    · exact (unit_reverse h7_6)
    · exact (unit_reverse h8_6)
  · change j ∈ ({2, 4, 5} : Finset (Fin 10)) at hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact (unit_reverse h3_7)
    · exact h7_5
    · exact h7_6
  · change j ∈ ({1, 3, 5} : Finset (Fin 10)) at hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact (unit_reverse h2_8)
    · exact h8_4
    · exact h8_6
  · change j ∈ ({0, 3, 4} : Finset (Fin 10)) at hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact (unit_reverse h1_9)
    · exact h9_4
    · exact h9_5
  · change j ∈ ({0, 1, 2} : Finset (Fin 10)) at hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact h10_1
    · exact h10_2
    · exact h10_3

private noncomputable def emb (p : RPoint) : ℝ² := !₂[p.1,p.2]

private theorem dist_sq_emb (p q : RPoint) : dist (emb p) (emb q)^2 = sqDist p q := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  change dist p.1 q.1 ^ 2 + dist p.2 q.2 ^ 2 = _
  simp only [Real.dist_eq, sq_abs]
  unfold sqDist
  ring

private theorem dist_emb_eq_one {p q : RPoint} (h : sqDist p q = 1) :
    dist (emb p) (emb q) = 1 := by
  have hd := dist_sq_emb p q
  rw [h] at hd
  nlinarith [dist_nonneg (x := emb p) (y := emb q)]

private noncomputable def planarCovector (a b : ℝ) : ℝ² →ₗ[ℝ] ℝ :=
  a • EuclideanSpace.projₗ 0 + b • EuclideanSpace.projₗ 1

private theorem halfplane_convex (a b c : ℝ) :
    Convex ℝ {x : ℝ² | a * x 0 + b * x 1 < c} :=
  convex_halfSpace_lt (planarCovector a b).isLinear c

private theorem support_halfplane_convex (a b c : ℝ) :
    Convex ℝ {x : ℝ² | a * x 0 - b * x 1 < c} := by
  convert halfplane_convex a (-b) c using 1
  ext x
  simp only [Set.mem_ofPred_eq, neg_mul, sub_eq_add_neg]

private theorem hull_support {S : Set ℝ²} {a b c : ℝ}
    (h : ∀ x ∈ S, a * x 0 - b * x 1 < c) :
    ∀ x ∈ convexHull ℝ S, a * x 0 - b * x 1 < c :=
  convexHull_min h (support_halfplane_convex a b c)

private theorem at_least_three {a b : Fin 10 → ℝ²} (hb : Function.Injective b)
    (hd : ∀ i j : Fin 10, j ∈ neigh i → dist (a i) (b j) = 1) :
    Erdos97.HasNUnitDistancePointsOn 3 (univ.image b) (univ.image a) := by
  classical
  intro p hp
  obtain ⟨i, _, rfl⟩ := mem_image.mp hp
  change 3 ≤ ((univ.image b).filter fun q => dist (a i) q = 1).card
  rw [← neigh_card i, ← card_image_of_injective (neigh i) hb]
  apply card_le_card
  intro q hq
  obtain ⟨j, hji, rfl⟩ := mem_image.mp hq
  exact mem_filter.mpr ⟨mem_image.mpr ⟨j, mem_univ _, rfl⟩, hd i j hji⟩

open Erdos97

/-- The convex twenty-point configuration of Fishburn and Reeds [FiRe92]. -/
theorem twenty_point_cut :
    ∃ (V : Finset ℝ²) (A B : Finset ℝ²),
      20 = V.card ∧ ConvexIndep V ∧ A.Nonempty ∧ B.Nonempty ∧ IsCut V A B ∧
      HasNUnitDistancePointsOn 3 B A ∧ HasNUnitDistancePointsOn 3 A B := by
  classical
  obtain ⟨t, ht, hroot⟩ := exists_root
  let a : Fin 10 → ℝ² := fun i => emb (reflect (points t i))
  let b : Fin 10 → ℝ² := fun i => emb (points t i)
  let A := univ.image a
  let B := univ.image b
  let V := A ∪ B
  let q : Fin 10 → ℝ := fun i => (qSlope i : ℝ)
  have apos (i : Fin 10) : (a i) 0 < 0 := neg_lt_zero.mpr (x_pos ht i)
  have bpos (i : Fin 10) : 0 < (b i) 0 := x_pos ht i
  have a_support {i j : Fin 10} (hij : i ≠ j) :
      -(a j) 0 - q i * (a j) 1 < -(a i) 0 - q i * (a i) 1 := by
    change -(-(points t j).1) - q i * (points t j).2 <
      -(-(points t i).1) - q i * (points t i).2
    simpa only [neg_neg] using strict_support ht hij
  have b_support {i j : Fin 10} (hij : i ≠ j) :
      (b j) 0 - q i * (b j) 1 < (b i) 0 - q i * (b i) 1 := strict_support ht hij
  have a_inj : Function.Injective a := by
    intro i j he
    by_contra hne
    have hs := a_support hne
    rw [he] at hs
    exact (lt_irrefl _ hs)
  have b_inj : Function.Injective b := by
    intro i j he
    by_contra hne
    have hs := b_support hne
    rw [he] at hs
    exact (lt_irrefl _ hs)
  have crossA (i j : Fin 10) :
      -(b j) 0 - q i * (b j) 1 < -(a i) 0 - q i * (a i) 1 := by
    have h := bpos j
    have he0 : (a j) 0 = -(b j) 0 := rfl
    have he1 : (a j) 1 = (b j) 1 := rfl
    calc
      _ < -(a j) 0 - q i * (a j) 1 := by rw [he0,he1]; linarith
      _ ≤ _ := by
        rcases eq_or_ne i j with rfl | hne
        · exact le_rfl
        · exact (a_support hne).le
  have crossB (i j : Fin 10) :
      (a j) 0 - q i * (a j) 1 < (b i) 0 - q i * (b i) 1 := by
    have h := bpos j
    have he0 : (a j) 0 = -(b j) 0 := rfl
    have he1 : (a j) 1 = (b j) 1 := rfl
    calc
      _ < (b j) 0 - q i * (b j) 1 := by rw [he0,he1]; linarith
      _ ≤ _ := by
        rcases eq_or_ne i j with rfl | hne
        · exact le_rfl
        · exact (b_support hne).le
  have disj : Disjoint A B := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    obtain ⟨j, _, hj⟩ := mem_image.mp hy
    have h := bpos j
    rw [hj] at h
    exact (lt_asymm h (apos i))
  have cvx : ConvexIndep V := by
    intro z hz hzHull
    rcases mem_union.mp hz with hz | hz
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hz
      have hsub : ∀ x ∈ (V : Set ℝ²) \ {a i},
          (-1) * x 0 - q i * x 1 < -(a i) 0 - q i * (a i) 1 := by
        intro x hx
        rcases mem_union.mp hx.1 with hxA | hxB
        · obtain ⟨j, _, rfl⟩ := mem_image.mp hxA
          have hne : i ≠ j := by
            rintro rfl
            exact hx.2 rfl
          simpa only [neg_one_mul] using a_support hne
        · obtain ⟨j, _, rfl⟩ := mem_image.mp hxB
          simpa only [neg_one_mul] using crossA i j
      have hh := hull_support hsub (a i) hzHull
      simp only [neg_one_mul, lt_self_iff_false] at hh
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hz
      have hsub : ∀ x ∈ (V : Set ℝ²) \ {b i},
          (1 : ℝ) * x 0 - q i * x 1 < (b i) 0 - q i * (b i) 1 := by
        intro x hx
        rcases mem_union.mp hx.1 with hxA | hxB
        · obtain ⟨j, _, rfl⟩ := mem_image.mp hxA
          simpa only [one_mul] using crossB i j
        · obtain ⟨j, _, rfl⟩ := mem_image.mp hxB
          have hne : i ≠ j := by
            rintro rfl
            exact hx.2 rfl
          simpa only [one_mul] using b_support hne
      have hh := hull_support hsub (b i) hzHull
      simp only [one_mul, lt_self_iff_false] at hh
  have hullDisj : Disjoint (convexHull ℝ (A : Set ℝ²)) (convexHull ℝ (B : Set ℝ²)) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    have ha : ∀ z ∈ (A : Set ℝ²), (1 : ℝ) * z 0 - 0 * z 1 < 0 := by
      intro z hz
      obtain ⟨i, _, rfl⟩ := mem_image.mp hz
      simpa only [one_mul, zero_mul, sub_zero] using apos i
    have hb : ∀ z ∈ (B : Set ℝ²), (-1 : ℝ) * z 0 - 0 * z 1 < 0 := by
      intro z hz
      obtain ⟨i, _, rfl⟩ := mem_image.mp hz
      simpa only [neg_one_mul, zero_mul, sub_zero, neg_lt_zero] using bpos i
    have hhA := hull_support ha x hxA
    have hhB := hull_support hb x hxB
    linarith
  have hcard : 20 = V.card := by
    change 20 = (A ∪ B).card
    rw [card_union_of_disjoint disj]
    change 20 = (univ.image a).card + (univ.image b).card
    rw [card_image_of_injective _ a_inj, card_image_of_injective _ b_inj,
      card_univ, Fintype.card_fin]
  have an : A.Nonempty := ⟨a 0, mem_image.mpr ⟨0,mem_univ _,rfl⟩⟩
  have bn : B.Nonempty := ⟨b 0, mem_image.mpr ⟨0,mem_univ _,rfl⟩⟩
  have hdist (i j : Fin 10) (hj : j ∈ neigh i) :=
    unit_cert (range_pass ht).2 hroot i j hj
  refine ⟨V, A, B, hcard, cvx, an, bn, ⟨rfl,disj,hullDisj⟩, ?_, ?_⟩
  · exact at_least_three b_inj (fun i j hj => dist_emb_eq_one (hdist i j hj))
  · exact at_least_three a_inj (fun i j hj => (dist_comm _ _).trans
      (dist_emb_eq_one (unit_reverse (hdist i j hj))))

theorem upper :
    sInf {n : ℕ | ∃ (V : Finset ℝ²) (A B : Finset ℝ²),
      n = V.card ∧ ConvexIndep V ∧ A.Nonempty ∧ B.Nonempty ∧ IsCut V A B ∧
      HasNUnitDistancePointsOn 3 B A ∧ HasNUnitDistancePointsOn 3 A B} ≤ 20 :=
  Nat.sInf_le twenty_point_cut

end FishburnReeds

open Erdos97 EuclideanGeometry
open scoped Classical EuclideanGeometry

theorem OMA.solution : OMA.R_Erdos97_erdos_97_variants_three_unit_distance_cut_min_R1.H1 :=
  FishburnReeds.twenty_point_cut