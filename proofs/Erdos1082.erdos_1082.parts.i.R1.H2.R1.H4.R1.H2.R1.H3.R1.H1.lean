import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H3_R1

/-!
# Four-color extension certificates for three-distance bases

Five further points have at most 64 possible triples of squared distances to the first three noncollinear vertices. The Gram and separation equations constrain each profile and each pair. Bezout certificates over the base number field prove that the resulting compatibility graph is four-colorable. Equal profiles give equal points. The scale is the squared reciprocal of the first base distance.
-/

namespace Erdos1082Ten


open EuclideanGeometry

def dsq (p q : ℝ²) := (p 0 - q 0)^2 + (p 1-q 1)^2

lemma dsq_eq (p q : ℝ²) : dsq p q=dist p q^2 := by
  rw [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two]
  simp [dsq,Real.dist_eq]

def cross (o e f : ℝ²) := (e 0-o 0)*(f 1-o 1)-(e 1-o 1)*(f 0-o 0)

lemma collinear_of_cross_zero (o e f : ℝ²) (hoe : o≠e) (he : cross o e f=0) :
    Collinear ℝ ({o,e,f}:Set ℝ²) := by
  apply (collinear_iff_of_mem (k:=ℝ) (Set.mem_insert o ({e,f}:Set ℝ²))).mpr
  refine ⟨e-o,?_⟩
  intro x hx
  rcases hx with h|h|h
  · exact ⟨0,by simp [h]⟩
  · exact ⟨1,by simp [h]⟩
  have hx' : x=f := h
  subst x
  dsimp [cross] at he
  have hev (i : Fin 2) (k : ℝ) : (k • (e-o) +ᵥ o) i=k*(e i-o i)+o i := rfl
  by_cases h₀ : e 0-o 0=0
  · have h₁ : e 1-o 1≠0 := by
      intro he
      apply hoe
      ext i
      fin_cases i <;> dsimp at * <;> linarith
    refine ⟨(f 1-o 1)/(e 1-o 1),?_⟩
    ext i
    rw [hev]
    fin_cases i
    · change f 0=(f 1-o 1)/(e 1-o 1)*(e 0-o 0)+o 0
      rw [h₀,mul_zero,zero_add]
      have hh : f 0-o 0=0 := (mul_eq_zero.mp (by linear_combination -he+ (f 1-o 1)*h₀ : (e 1-o 1)*(f 0-o 0)=0)).resolve_left h₁
      linarith
    · change f 1=(f 1-o 1)/(e 1-o 1)*(e 1-o 1)+o 1
      field_simp; ring
  · refine ⟨(f 0-o 0)/(e 0-o 0),?_⟩
    ext i
    rw [hev]
    fin_cases i
    · change f 0=(f 0-o 0)/(e 0-o 0)*(e 0-o 0)+o 0
      field_simp; ring
    · change f 1=(f 0-o 0)/(e 0-o 0)*(e 1-o 1)+o 1
      field_simp
      linear_combination he

def area (a b c : ℝ) := 4*a*b-(a+b-c)^2

def gram (a b c d₀ d₁ d₂ e₀ e₁ e₂ h : ℝ) : ℝ :=
  let g := a+b-c
  let u := a+d₀-d₁
  let v := b+d₀-d₂
  let w := a+e₀-e₁
  let z := b+e₀-e₂
  2*b*u*w-g*(u*z+v*w)+2*a*v*z-area a b c*(d₀+e₀-h)

lemma area_identity (o e f : ℝ²) (s : ℝ) :
    area (s*dsq o e) (s*dsq o f) (s*dsq e f)=4*(s*cross o e f)^2 := by
  unfold area dsq cross
  ring

lemma area_ne (o e f : ℝ²) (s : ℝ) (hs : s≠0) (hoe : o≠e)
    (hn : ¬Collinear ℝ ({o,e,f}:Set ℝ²)) :
    area (s*dsq o e) (s*dsq o f) (s*dsq e f)≠0 := by
  rw [area_identity]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (mul_ne_zero hs (fun he => hn (collinear_of_cross_zero o e f hoe he))))

lemma gram_identity (o e f x y : ℝ²) (s : ℝ) :
    gram (s*dsq o e) (s*dsq o f) (s*dsq e f)
      (s*dsq o x) (s*dsq e x) (s*dsq f x) (s*dsq o y) (s*dsq e y) (s*dsq f y) (s*dsq x y)=0 := by
  unfold gram area dsq
  ring


abbrev Triple := ℝ×ℝ×ℝ

def dataTriple (s : ℝ) (o e f x : ℝ²) : Triple := (s*dsq o x,s*dsq e x,s*dsq f x)

def locus (a b c : ℝ) (p : Triple) := gram a b c p.1 p.2.1 p.2.2 p.1 p.2.1 p.2.2 0

def sep4 (a b c : ℝ) (p q : Triple) :=
  let u := (p.1-p.2.1)-(q.1-q.2.1)
  let v := (p.1-p.2.2)-(q.1-q.2.2)
  2*b*u*u-2*(a+b-c)*u*v+2*a*v*v

def edge4 (a b c : ℝ) (p q : Triple) (x y t : ℝ) :=
  let d := 2*area a b c
  let l := sep4 a b c p q
  (l-d)*(l-d*x)*(l-d*y)*(l-d*t)

lemma geom_locus (s : ℝ) (o e f x : ℝ²) :
    locus (s*dsq o e) (s*dsq o f) (s*dsq e f) (dataTriple s o e f x)=0 := by
  have h := gram_identity o e f x x s
  simpa [locus,dataTriple,dsq] using h

lemma geom_sep4 (s : ℝ) (o e f x y : ℝ²) :
    sep4 (s*dsq o e) (s*dsq o f) (s*dsq e f) (dataTriple s o e f x) (dataTriple s o e f y)=
    2*area (s*dsq o e) (s*dsq o f) (s*dsq e f)*(s*dsq x y) := by
  unfold sep4 dataTriple dsq area
  ring

lemma geom_edge4 (s : ℝ) (o e f u v : ℝ²) (x y t : ℝ)
    (h : s*dsq u v=1 ∨ s*dsq u v=x ∨ s*dsq u v=y ∨ s*dsq u v=t) :
    edge4 (s*dsq o e) (s*dsq o f) (s*dsq e f) (dataTriple s o e f u) (dataTriple s o e f v) x y t=0 := by
  unfold edge4
  rw [geom_sep4]
  rcases h with h|h|h|h <;> rw [h] <;> ring

lemma geom_injective (s : ℝ) (hs : s≠0) (o e f : ℝ²) (hoe : o≠e)
    (hn : ¬Collinear ℝ ({o,e,f}:Set ℝ²)) : Function.Injective (dataTriple s o e f) := by
  intro x y he
  have hh := geom_sep4 s o e f x y
  rw [he] at hh
  simp [sep4] at hh
  have h0 := area_ne o e f s hs hoe hn
  have hz := (hh.resolve_left h0).resolve_left hs
  rw [dsq_eq] at hz
  exact dist_eq_zero.mp (sq_eq_zero_iff.mp hz)

def palette4 (x y t : ℝ) : Fin 4→ℝ := ![1,x,y,t]

def profile4 (x y t : ℝ) (k : Fin 64) : Triple :=
  (palette4 x y t ⟨k.val/16,by omega⟩,palette4 x y t ⟨k.val/4%4,by omega⟩,palette4 x y t ⟨k.val%4,by omega⟩)

lemma profile4_surjective (x y t : ℝ) (a b c : Fin 4) :
    ∃ k : Fin 64, profile4 x y t k=(palette4 x y t a,palette4 x y t b,palette4 x y t c) := by
  let k : Fin 64 := ⟨16*a.val+4*b.val+c.val,by omega⟩
  have ha : k.val/16=a.val := by dsimp [k]; omega
  have hb : k.val/4%4=b.val := by dsimp [k]; omega
  have hc : k.val%4=c.val := by dsimp [k]; omega
  exact ⟨k, by simp [profile4,ha,hb,hc]⟩

def cell (a b c : ℝ) (p q r : Triple) (x y t : ℝ) :=
  locus a b c p=0 ∧ edge4 a b c p q x y t=0 ∧ edge4 a b c p r x y t=0


open EuclideanGeometry
def colorCode (c : Fin 10→Fin 3) : ℕ := (c 0).val*19683+(c 1).val*6561+(c 2).val*2187+(c 3).val*729+(c 4).val*243+(c 5).val*81+(c 6).val*27+(c 7).val*9+(c 8).val*3+(c 9).val*1
def slot : Fin 5→Fin 5→Fin 10 := ![![0,0,1,2,3],![0,0,4,5,6],![1,4,0,7,8],![2,5,7,0,9],![3,6,8,9,0]]
def permColors (c : Fin 10→Fin 3) (p : Fin 5→Fin 5) (s : Fin 3→Fin 3) : Fin 10→Fin 3 := ![s (c (slot (p 0) (p 1))),s (c (slot (p 0) (p 2))),s (c (slot (p 0) (p 3))),s (c (slot (p 0) (p 4))),s (c (slot (p 1) (p 2))),s (c (slot (p 1) (p 3))),s (c (slot (p 1) (p 4))),s (c (slot (p 2) (p 3))),s (c (slot (p 2) (p 4))),s (c (slot (p 3) (p 4)))]
def minimalColor (c : Fin 10→Fin 3) := ∀ (p : Fin 5→Fin 5) (s : Fin 3→Fin 3), Function.Injective p → Function.Injective s → colorCode c≤colorCode (permColors c p s)
def baseCodes : List ℕ := [0,1,4,5,13,14,31,32,36,37,38,40,41,44,45,46,49,50,53,120,121,122,123,124,125,132,133,151,156,157,364,365,368,377,400,401,761,764,765,766,767,770,773,774,775,776,779,782,792,793,794,796,797,800,822,823,824,825,826,827,834,835,836,849,851,852,853,854,855,857,858,860,861,862,863,879,880,881,882,883,885,886,887,888,889,890,912,913,939,941,942,943,969,970,1062,1064,1070,1071,1072,1073,1075,1076,1079,1100,1106,1124,1125,1126,1127,1129,1130,1152,1153,1155,1157,1158,1159,1185,1212,1213,1395,1396,3048,3050,3072,3074,3075,3194,3195,3197,3203,3206,3231,3233,3234,3236,3237,3399,3437,3440,3801,3961]

lemma slot_symm (i j : Fin 5) : slot i j=slot j i := by decide +revert

lemma perm_slot (c : Fin 10→Fin 3) (p : Fin 5→Fin 5) (s : Fin 3→Fin 3) (i j : Fin 5) (h : i≠j) :
    permColors c p s (slot i j)=s (c (slot (p i) (p j))) := by
  fin_cases i <;> fin_cases j <;> first | exact False.elim (h rfl) | rfl | exact congrArg (fun k => s (c k)) (slot_symm _ _)

lemma lookup_sym (k : Fin 5→Fin 5→Fin 3) (hs : ∀ i j,k i j=k j i) (i j : Fin 5) (h : i≠j) :
    (![k 0 1,k 0 2,k 0 3,k 0 4,k 1 2,k 1 3,k 1 4,k 2 3,k 2 4,k 3 4] : Fin 10→Fin 3) (slot i j)=k i j := by
  fin_cases i <;> fin_cases j <;> first | exact False.elim (h rfl) | rfl | exact hs _ _

def realizes (B : Finset ℝ²) (D : Finset ℝ) (c : Fin 10→Fin 3) :=
  ∃ (v : Fin 5≃B) (r : Fin 3≃D), ∀ i j : Fin 5, i≠j →
    (r (c (slot i j))).1=dist (v i).1 (v j).1

lemma minimal_realization (B : Finset ℝ²) (D : Finset ℝ) (hB : B.card=5) (hD : D.card=3)
    (hBD : ∀ x∈B, ∀ y∈B, x≠y → dist x y∈D) : ∃ c, realizes B D c ∧ minimalColor c := by
  classical
  let V := (B.equivFinOfCardEq hB).symm
  let R := (D.equivFinOfCardEq hD).symm
  let k (i j : Fin 5) := if h : i≠j then R.symm ⟨dist (V i).1 (V j).1,hBD _ (V i).2 _ (V j).2
    (fun he => h (V.injective (Subtype.ext he)))⟩ else 0
  have sym (i j : Fin 5) : k i j=k j i := by
    by_cases he : i=j
    · subst j; rfl
    · have hf : j≠i := Ne.symm he
      simp only [k,dif_pos he,dif_pos hf]
      apply congrArg R.symm
      apply Subtype.ext
      exact dist_comm ..
  let c₀ : Fin 10→Fin 3 := ![k 0 1,k 0 2,k 0 3,k 0 4,k 1 2,k 1 3,k 1 4,k 2 3,k 2 4,k 3 4]
  have hlookup (i j : Fin 5) (hij : i≠j) : c₀ (slot i j)=k i j := by
    apply lookup_sym k sym i j hij
  let L := Finset.univ.filter (realizes B D)
  have h₀ : realizes B D c₀ := by
    refine ⟨V,R,?_⟩
    intro i j hij
    rw [hlookup _ _ hij]
    simp [k,hij]
  have hl : L.Nonempty := ⟨c₀,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h₀⟩⟩
  obtain ⟨c,hc,hm⟩ := Finset.exists_min_image L colorCode hl
  have hreal := (Finset.mem_filter.mp hc).2
  refine ⟨c,hreal,?_⟩
  rintro p s hp hs
  let P : Fin 5≃Fin 5 := Equiv.ofBijective p ⟨hp,Finite.injective_iff_surjective.mp hp⟩
  let S : Fin 3≃Fin 3 := Equiv.ofBijective s ⟨hs,Finite.injective_iff_surjective.mp hs⟩
  apply hm
  apply Finset.mem_filter.mpr
  obtain ⟨v,r,hr⟩ := hreal
  refine ⟨Finset.mem_univ _,P.trans v,S.symm.trans r,?_⟩
  intro i j hij
  rw [perm_slot _ _ _ _ _ hij]
  change (r (S.symm (S (c (slot (p i) (p j)))))).1=dist (v (p i)).1 (v (p j)).1
  rw [S.symm_apply_apply]
  exact hr _ _ (fun he => hij (hp he))

def palette3 (x y : ℝ) : Fin 3→ℝ := ![1,x,y]

def baseD (c : Fin 10→Fin 3) (x y : ℝ) (i j : Fin 5) := palette3 x y (c (slot i j))

def baseT (c : Fin 10→Fin 3) (x y : ℝ) (i : Fin 5) : Triple :=
  (baseD c x y 0 i,baseD c x y 1 i,baseD c x y 2 i)

def threeGram (d : Fin 5→Fin 5→ℝ) (i j : Fin 5) :=
  gram (d 0 1) (d 0 2) (d 1 2) (d 0 i) (d 1 i) (d 2 i) (d 0 j) (d 1 j) (d 2 j) (if i=j then 0 else d i j)

def admissible (c : Fin 10→Fin 3) (x y : ℝ) :=
  let d := baseD c x y
  (x≠0 ∧ y≠0 ∧ x-1≠0 ∧ y-1≠0 ∧ x-y≠0) ∧
    (∀ i j k : Fin 5, i<j → j<k → area (d i j) (d i k) (d j k)≠0) ∧
    threeGram d 3 3=0 ∧ threeGram d 3 4=0 ∧ threeGram d 4 4=0

def hasExtension (c : Fin 10→Fin 3) (x y t : ℝ) :=
  let d := baseD c x y
  ∃ g : Fin 5→Fin 64, Function.Injective g ∧
    (∀ i, cell (d 0 1) (d 0 2) (d 1 2) (profile4 x y t (g i)) (baseT c x y 3) (baseT c x y 4) x y t) ∧
    (∀ i j, i≠j → edge4 (d 0 1) (d 0 2) (d 1 2) (profile4 x y t (g i)) (profile4 x y t (g j)) x y t=0)

lemma build_admissible (c : Fin 10→Fin 3) (x y s : ℝ) (p : Fin 5→ℝ²) (hp : Function.Injective p) (hs : s≠0)
    (hcol : ∀ i j k : Fin 5, i≠j → j≠k → i≠k → ¬Collinear ℝ ({p i,p j,p k}:Set ℝ²))
    (hc : ∀ i j, i≠j → baseD c x y i j=s*dsq (p i) (p j))
    (he : x≠0 ∧ y≠0 ∧ x-1≠0 ∧ y-1≠0 ∧ x-y≠0) : admissible c x y := by
  refine ⟨he,?_,?_,?_,?_⟩
  · intro i j k hij hjk
    rw [hc _ _ hij.ne,hc _ _ (hij.trans hjk).ne,hc _ _ hjk.ne]
    exact area_ne _ _ _ s hs (fun h => hij.ne (hp h)) (hcol _ _ _ hij.ne hjk.ne (hij.trans hjk).ne)
  · have hv := gram_identity (p 0) (p 1) (p 2) (p 3) (p 3) s
    rw [←hc 0 1 (by decide),←hc 0 2 (by decide),←hc 1 2 (by decide),←hc 0 3 (by decide),←hc 1 3 (by decide),←hc 2 3 (by decide)] at hv
    have hzero : dsq (p 3) (p 3)=0 := by simp [dsq]
    rw [hzero,mul_zero] at hv
    exact hv
  · have hv := gram_identity (p 0) (p 1) (p 2) (p 3) (p 4) s
    rw [←hc 0 1 (by decide),←hc 0 2 (by decide),←hc 1 2 (by decide),←hc 0 3 (by decide),←hc 1 3 (by decide),←hc 2 3 (by decide),←hc 0 4 (by decide),←hc 1 4 (by decide),←hc 2 4 (by decide),←hc 3 4 (by decide)] at hv
    exact hv
  · have hv := gram_identity (p 0) (p 1) (p 2) (p 4) (p 4) s
    rw [←hc 0 1 (by decide),←hc 0 2 (by decide),←hc 1 2 (by decide),←hc 0 4 (by decide),←hc 1 4 (by decide),←hc 2 4 (by decide)] at hv
    have hzero : dsq (p 4) (p 4)=0 := by simp [dsq]
    rw [hzero,mul_zero] at hv
    exact hv

lemma palette4_or (x y t : ℝ) (k : Fin 4) :
    palette4 x y t k=1 ∨ palette4 x y t k=x ∨ palette4 x y t k=y ∨ palette4 x y t k=t := by
  fin_cases k <;> simp [palette4]

lemma build_extension (c : Fin 10→Fin 3) (x y t s : ℝ) (p q : Fin 5→ℝ²) (hq : Function.Injective q)
    (hs : s≠0) (hoe : p 0≠p 1) (hn : ¬Collinear ℝ ({p 0,p 1,p 2}:Set ℝ²))
    (hb : ∀ i j, i≠j → baseD c x y i j=s*dsq (p i) (p j))
    (hd : ∀ i j, ∃ k, s*dsq (p i) (q j)=palette4 x y t k)
    (he : ∀ i j, i≠j → ∃ k, s*dsq (q i) (q j)=palette4 x y t k) : hasExtension c x y t := by
  classical
  have hp (j : Fin 5) : ∃ k, profile4 x y t k=dataTriple s (p 0) (p 1) (p 2) (q j) := by
    obtain ⟨a,ha⟩ := hd 0 j
    obtain ⟨b,hb⟩ := hd 1 j
    obtain ⟨k,hk⟩ := hd 2 j
    rw [dataTriple,ha,hb,hk]
    exact profile4_surjective x y t a b k
  let g (i : Fin 5) := (hp i).choose
  have gg (i : Fin 5) : profile4 x y t (g i)=dataTriple s (p 0) (p 1) (p 2) (q i) := (hp i).choose_spec
  have h03 : baseT c x y 3=dataTriple s (p 0) (p 1) (p 2) (p 3) := by
    simp only [baseT,dataTriple,hb 0 3 (by decide),hb 1 3 (by decide),hb 2 3 (by decide)]
  have h04 : baseT c x y 4=dataTriple s (p 0) (p 1) (p 2) (p 4) := by
    simp only [baseT,dataTriple,hb 0 4 (by decide),hb 1 4 (by decide),hb 2 4 (by decide)]
  have hrev (u v : ℝ²) : dsq u v=dsq v u := by rw [dsq_eq,dsq_eq,dist_comm]
  have hpoint (i j : Fin 5) : s*dsq (q i) (p j)=1 ∨ s*dsq (q i) (p j)=x ∨
      s*dsq (q i) (p j)=y ∨ s*dsq (q i) (p j)=t := by
    obtain ⟨k,hk⟩ := hd j i
    rw [hrev,hk]
    exact palette4_or x y t k
  refine ⟨g,?_,?_,?_⟩
  · intro i j hij
    apply hq
    apply geom_injective s hs (p 0) (p 1) (p 2) hoe hn
    rw [←gg,←gg,hij]
  · intro i
    rw [gg,h03,h04,hb 0 1 (by decide),hb 0 2 (by decide),hb 1 2 (by decide)]
    exact ⟨geom_locus ..,geom_edge4 _ _ _ _ _ _ _ _ _ (hpoint i 3),geom_edge4 _ _ _ _ _ _ _ _ _ (hpoint i 4)⟩
  · intro i j hij
    rw [gg,gg,hb 0 1 (by decide),hb 0 2 (by decide),hb 1 2 (by decide)]
    apply geom_edge4
    obtain ⟨k,hk⟩ := he i j hij
    rw [hk]
    exact palette4_or x y t k


def edges5 : Fin 10→Fin 5×Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

lemma match_edges {B : Finset ℝ²} {T : Finset ℝ} (p : Fin 5≃B) (r : Fin 3≃T) (c : Fin 10→Fin 3)
    (h : ∀ k, dist (p (edges5 k).1).1 (p (edges5 k).2).1=(r (c k)).1) :
    ∀ i j : Fin 5, i≠j → (r (c (slot i j))).1=dist (p i).1 (p j).1 := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact (h 0).symm
  · exact (h 1).symm
  · exact (h 2).symm
  · exact (h 3).symm
  · exact (h 0).symm.trans (dist_comm ..)
  · exact False.elim (hij rfl)
  · exact (h 4).symm
  · exact (h 5).symm
  · exact (h 6).symm
  · exact (h 1).symm.trans (dist_comm ..)
  · exact (h 4).symm.trans (dist_comm ..)
  · exact False.elim (hij rfl)
  · exact (h 7).symm
  · exact (h 8).symm
  · exact (h 2).symm.trans (dist_comm ..)
  · exact (h 5).symm.trans (dist_comm ..)
  · exact (h 7).symm.trans (dist_comm ..)
  · exact False.elim (hij rfl)
  · exact (h 9).symm
  · exact (h 3).symm.trans (dist_comm ..)
  · exact (h 6).symm.trans (dist_comm ..)
  · exact (h 8).symm.trans (dist_comm ..)
  · exact (h 9).symm.trans (dist_comm ..)
  · exact False.elim (hij rfl)

lemma unmatch_edges {B : Finset ℝ²} {T : Finset ℝ} (p : Fin 5≃B) (r : Fin 3≃T) (c : Fin 10→Fin 3)
    (h : ∀ i j : Fin 5, i≠j → (r (c (slot i j))).1=dist (p i).1 (p j).1) :
    ∀ k, dist (p (edges5 k).1).1 (p (edges5 k).2).1=(r (c k)).1 := by
  intro k
  fin_cases k
  · exact (h 0 1 (by decide)).symm
  · exact (h 0 2 (by decide)).symm
  · exact (h 0 3 (by decide)).symm
  · exact (h 0 4 (by decide)).symm
  · exact (h 1 2 (by decide)).symm
  · exact (h 1 3 (by decide)).symm
  · exact (h 1 4 (by decide)).symm
  · exact (h 2 3 (by decide)).symm
  · exact (h 2 4 (by decide)).symm
  · exact (h 3 4 (by decide)).symm

lemma scaled_sq_inj {s a b : ℝ} (hs : s≠0) (ha : 0<a) (hb : 0<b) (h : s*a^2=s*b^2) : a=b := by
  have he := mul_left_cancel₀ hs h
  have hsum : 0<a+b := add_pos ha hb
  have hprod : (a-b)*(a+b)=0 := by linear_combination he
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hsum.ne')

lemma distanceSet_pos {A : Finset ℝ²} {d : ℝ} (hd : d∈distanceSet A) : 0<d := by
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hd
  exact dist_pos.mpr (Finset.mem_offDiag.mp hab).2.2

lemma given_colors (B : Finset ℝ²) (hn : NonTrilinear (B:Set ℝ²))
    (p : Fin 5≃B) (r : Fin 3≃distanceSet B) (c : Fin 10→Fin 3)
    (h : ∀ k, dist (p (edges5 k).1).1 (p (edges5 k).2).1=(r (c k)).1) :
    ∃ s x y : ℝ, 0<s ∧ admissible c x y ∧ (∀ i : Fin 3, palette3 x y i=s*(r i).1^2) ∧
      ∀ i j, i≠j → baseD c x y i j=s*dsq (p i).1 (p j).1 := by
  let s := ((r 0).1^2)⁻¹
  let f (d : ℝ) := s*d^2
  let x := f (r 1).1
  let y := f (r 2).1
  have rpos (i : Fin 3) := distanceSet_pos (r i).2
  have hs : 0<s := inv_pos.mpr (sq_pos_of_pos (rpos 0))
  have one : f (r 0).1=1 := by dsimp [f,s]; field_simp [(rpos 0).ne']
  have rmap (i : Fin 3) : palette3 x y i=f (r i).1 := by fin_cases i <;> first | exact one.symm | rfl
  have hr := match_edges p r c h
  have hc (i j : Fin 5) (hij : i≠j) : baseD c x y i j=s*dsq (p i).1 (p j).1 := by
    change palette3 x y (c (slot i j))=_
    rw [rmap,hr i j hij,dsq_eq]
  have vi : Function.Injective (fun i : Fin 3 => f (r i).1) := fun i j e =>
    r.injective (Subtype.ext (scaled_sq_inj hs.ne' (rpos i) (rpos j) e))
  have hpos (i : Fin 3) : 0<f (r i).1 := mul_pos hs (sq_pos_of_pos (rpos i))
  have xy : x≠0 ∧ y≠0 ∧ x-1≠0 ∧ y-1≠0 ∧ x-y≠0 := by
    refine ⟨(hpos 1).ne',(hpos 2).ne',sub_ne_zero.mpr ?_,sub_ne_zero.mpr ?_,sub_ne_zero.mpr ?_⟩
    · intro e; exact (by decide : (1:Fin 3)≠0) (vi (e.trans one.symm))
    · intro e; exact (by decide : (2:Fin 3)≠0) (vi (e.trans one.symm))
    · intro e; exact (by decide : (1:Fin 3)≠2) (vi e)
  have pi : Function.Injective (fun i : Fin 5 => (p i).1) := fun _ _ e => p.injective (Subtype.ext e)
  refine ⟨s,x,y,hs,build_admissible c x y s _ pi hs.ne' ?_ hc xy,rmap,hc⟩
  intro i j k hij hjk hik
  exact hn (p i).2 (p j).2 (p k).2 (fun e => hij (pi e)) (fun e => hjk (pi e)) (fun e => hik (pi e))

lemma given_extension (A B : Finset ℝ²) (M : ℝ) (hM : M∈distanceSet A) (hBA : B⊆A)
    (hA : A.card=10) (hB : B.card=5) (hD : distinctDistances A=4) (hthree : distinctDistances B=3)
    (hn : NonTrilinear (A:Set ℝ²)) (hdiam : ∀ a∈B, ∀ b∈B, dist a b<M)
    (p : Fin 5≃B) (r : Fin 3≃distanceSet B) (c : Fin 10→Fin 3)
    (hc : ∀ k, dist (p (edges5 k).1).1 (p (edges5 k).2).1=(r (c k)).1) :
    ∃ x y t : ℝ, admissible c x y ∧ hasExtension c x y t ∧ t-1≠0 ∧ t-x≠0 ∧ t-y≠0 ∧ t≠0 := by
  classical
  have hnB : NonTrilinear (B:Set ℝ²) := by
    intro a ha b hb d hd ab bd ad
    exact hn (hBA ha) (hBA hb) (hBA hd) ab bd ad
  obtain ⟨s,x,y,hs,had,rmap,hb⟩ := given_colors B hnB p r c hc
  let t := s*M^2
  have rpos (i : Fin 3) := distanceSet_pos (r i).2
  have eqD : distanceSet B=(distanceSet A).erase M := by
    apply Finset.eq_of_subset_of_card_le
    · intro d hd
      refine Finset.mem_erase.mpr ⟨?_,OMA.R_Erdos1082_erdos_1082_parts_i_R1.distanceSet_mono hBA hd⟩
      obtain ⟨⟨u,v⟩,h,rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨hu,hv,_⟩ := Finset.mem_offDiag.mp h
      exact (hdiam u hu v hv).ne
    · rw [Finset.card_erase_of_mem hM]
      change distinctDistances A-1≤distinctDistances B
      omega
  have mt (i : Fin 3) : t≠palette3 x y i := by
    rw [rmap]
    have hh : (r i).1∈(distanceSet A).erase M := (Finset.ext_iff.mp eqD _).mp (r i).2
    exact fun e => (Finset.mem_erase.mp hh).1 (scaled_sq_inj hs.ne' (distanceSet_pos hM) (rpos i) e).symm
  have palette (u v : ℝ²) (hu : u∈A) (hv : v∈A) (hne : u≠v) : ∃ k, s*dsq u v=palette4 x y t k := by
    rw [dsq_eq]
    by_cases h : dist u v=M
    · exact ⟨3,by rw [h]; rfl⟩
    have hd : dist u v∈distanceSet B := by
      rw [eqD]
      exact Finset.mem_erase.mpr ⟨h,OMA.R_Erdos1082_erdos_1082_parts_i_R1.dist_mem hu hv hne⟩
    obtain ⟨k,hk⟩ := r.surjective (⟨dist u v,hd⟩:distanceSet B)
    have ek := congrArg Subtype.val hk
    change (r k).1=dist u v at ek
    rw [←ek,←rmap]
    fin_cases k
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  let T := A\B
  have ht : T.card=5 := by dsimp [T]; rw [Finset.card_sdiff_of_subset hBA,hA,hB]
  let q := (T.equivFinOfCardEq ht).symm
  have qi : Function.Injective (fun i : Fin 5 => (q i).1) := fun _ _ e => q.injective (Subtype.ext e)
  have pi : Function.Injective (fun i : Fin 5 => (p i).1) := fun _ _ e => p.injective (Subtype.ext e)
  have hn3 : ¬Collinear ℝ ({(p 0).1,(p 1).1,(p 2).1}:Set ℝ²) := hnB (p 0).2 (p 1).2 (p 2).2
    (fun e => (by decide : (0:Fin 5)≠1) (pi e)) (fun e => (by decide : (1:Fin 5)≠2) (pi e)) (fun e => (by decide : (0:Fin 5)≠2) (pi e))
  refine ⟨x,y,t,had,?_,sub_ne_zero.mpr (mt 0),sub_ne_zero.mpr (mt 1),sub_ne_zero.mpr (mt 2),
    (mul_pos hs (sq_pos_of_pos (distanceSet_pos hM))).ne'⟩
  apply build_extension c x y t s (fun i => (p i).1) (fun i => (q i).1) qi hs.ne'
    (fun e => (by decide : (0:Fin 5)≠1) (pi e)) hn3 hb
  · intro i j
    obtain ⟨hq,hqb⟩ := Finset.mem_sdiff.mp (q j).2
    exact palette _ _ (hBA (p i).2) hq (fun e => hqb (e ▸ (p i).2))
  · intro i j hij
    exact palette _ _ (Finset.mem_sdiff.mp (q i).2).1 (Finset.mem_sdiff.mp (q j).2).1 (fun e => hij (qi e))


lemma injective_colorCode : Function.Injective colorCode := by
  intro c d h
  unfold colorCode at h
  have a0 := (c 0).isLt
  have b0 := (d 0).isLt
  have a1 := (c 1).isLt
  have b1 := (d 1).isLt
  have a2 := (c 2).isLt
  have b2 := (d 2).isLt
  have a3 := (c 3).isLt
  have b3 := (d 3).isLt
  have a4 := (c 4).isLt
  have b4 := (d 4).isLt
  have a5 := (c 5).isLt
  have b5 := (d 5).isLt
  have a6 := (c 6).isLt
  have b6 := (d 6).isLt
  have a7 := (c 7).isLt
  have b7 := (d 7).isLt
  have a8 := (c 8).isLt
  have b8 := (d 8).isLt
  have a9 := (c 9).isLt
  have b9 := (d 9).isLt
  have h0 : c 0=d 0 := by apply Fin.ext; omega
  rw [h0] at h
  have h1 : c 1=d 1 := by apply Fin.ext; omega
  rw [h1] at h
  have h2 : c 2=d 2 := by apply Fin.ext; omega
  rw [h2] at h
  have h3 : c 3=d 3 := by apply Fin.ext; omega
  rw [h3] at h
  have h4 : c 4=d 4 := by apply Fin.ext; omega
  rw [h4] at h
  have h5 : c 5=d 5 := by apply Fin.ext; omega
  rw [h5] at h
  have h6 : c 6=d 6 := by apply Fin.ext; omega
  rw [h6] at h
  have h7 : c 7=d 7 := by apply Fin.ext; omega
  rw [h7] at h
  have h8 : c 8=d 8 := by apply Fin.ext; omega
  rw [h8] at h
  have h9 : c 9=d 9 := by apply Fin.ext; omega
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
private lemma base_0001010221 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : -x^2 - 2*x*y + 5*x + 2*y^2 - 4*y - (1:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -y^2 + 4*y≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : -x^2 + 4*x*y≠0) : (x - y^3 + 6*y^2 - 9*y + (1:ℝ)=0) ∧ (y^4 - 7*y^3 + 14*y^2 - 8*y + (1:ℝ)=0) := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 + 2*x*y - 5*x - 2*y^2 + 4*y + (1:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x - y^3 + 6*y^2 - 9*y + (1:ℝ)=0 := by linear_combination (x/3 - 1)*h2 + (-x/3 - y + 2)*h3
  have h5 : y^4 - 7*y^3 + 14*y^2 - 8*y + (1:ℝ)=0 := by linear_combination (-x*y/3 + x/3 + y - 2/3)*h2 + (x*y/3 - x/3 + y^2 - 3*y + 5/3)*h3
  have h6 : x - y^3 + 6*y^2 - 9*y + (1:ℝ)=0 := by linear_combination (1)*h4
  have h7 : y^4 - 7*y^3 + 14*y^2 - 8*y + (1:ℝ)=0 := by linear_combination (1)*h5
  exact ⟨h6, h7⟩



private lemma shape_0001010221 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,0,2,2,1] x y) : (x - y^3 + 6*y^2 - 9*y + 1=0) ∧ (y^4 - 7*y^3 + 14*y^2 - 8*y + 1=0) := by
  apply base_0001010221 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x 1 y x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x 1 y x 1 y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma base_0011012210 (x y : ℝ) (g0 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (g1 : -x^2 + 2*x*y - 4*x - y^2 - 2*y + (5:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : 4*x - (1:ℝ)≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : (x - 1/(3:ℝ)=0) ∧ (y - 4/(3:ℝ)=0) := by
  have h1 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 2*x*y + 4*x + y^2 + 2*y - (5:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : 2*x + y - (2:ℝ)=0 := by linear_combination (1/3)*h2 + (-1/3)*h3
  have h5 : 3*y^2 - 4*y=0 := by linear_combination (-2*x/9 + 5*y/9 + 2/9)*h2 + (2*x/9 - 5*y/9 + 10/9)*h3
  have h6 : x + y/2 - (1:ℝ)=0 := by linear_combination (1/2)*h4
  have h8 : y≠0 := by
    intro he
    apply n1
    linear_combination (1)*he
  have h9 : ((y))*(y - 4/3)=0 := by linear_combination (1/3)*h5
  have h7 := (mul_eq_zero.mp h9).resolve_left h8
  have h10 : x - 1/(3:ℝ)=0 := by linear_combination (1)*h6 + (-1/2)*h7
  exact ⟨h10, h7⟩



private lemma shape_0011012210 (x y : ℝ) (ha : admissible ![0,0,1,1,0,1,2,2,1,0] x y) : (x - 1/3=0) ∧ (y - 4/3=0) := by
  apply base_0011012210 x y
  · have hg : gram 1 1 1 x x y x x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x y x y x 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y x x y x 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 1≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma base_0011101122 (x y : ℝ) (g0 : 2*x^3 - 4*x^2 - 4*x + (2:ℝ)=0) (g1 : 3*x^3 - 2*x^2*y - 9*x^2 + 6*x*y + 3*x - 2*y=0) (g2 : 2*x^3 - 4*x^2 - 6*x*y + 2*x + 2*y^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : 4*x - (1:ℝ)≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x*y - y^2≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : 4*x*y - y^2≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 4*x*y≠0) : (x - y/3 - 1/(3:ℝ)=0) ∧ (y^2 - 7*y + (1:ℝ)=0) := by
  have h1 : x^3 - 2*x^2 - 2*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^3 - 2*x^2*y/3 - 3*x^2 + 2*x*y + x - 2*y/(3:ℝ)=0 := by linear_combination (1/3)*g1
  have h3 : x^3 - 2*x^2 - 3*x*y + x + y^2=0 := by linear_combination (1/2)*g2
  have h4 : x^2 - 3*x + (1:ℝ)=0 := by linear_combination (4*x^2/25 - 6*x/5 + 6*y/25 + 1)*h1 + (18*x/25 - 6*y/25 + 9/25)*h2 + (-4*x^2/25 + 12*x/25 - 4/25)*h3
  have h5 : x*y - x - y^2/3 + 1/(3:ℝ)=0 := by linear_combination (1/3)*h1 + (-1/3)*h3
  have h6 : y^3 - 8*y^2 + 8*y - (1:ℝ)=0 := by linear_combination (-18*x^2/5 + 24*x - 32*y/5 - 1)*h1 + (-81*x/5 + 27*y/5 - 108/5)*h2 + (18*x^2/5 - 39*x/5 + y - 22/5)*h3
  have h8 : y - (1:ℝ)≠0 := by
    intro he
    apply n3
    linear_combination (1)*he
  have h9 : ((y - 1))*(x - y/3 - 1/3)=0 := by linear_combination (1)*h5
  have h7 := (mul_eq_zero.mp h9).resolve_left h8
  have h11 : ((y - 1))*(y^2 - 7*y + 1)=0 := by linear_combination (1)*h6
  have h10 := (mul_eq_zero.mp h11).resolve_left h8
  exact ⟨h7, h10⟩



private lemma shape_0011101122 (x y : ℝ) (ha : admissible ![0,0,1,1,1,0,1,1,2,2] x y) : (x - y/3 - 1/3=0) ∧ (y^2 - 7*y + 1=0) := by
  apply base_0011101122 x y
  · have hg : gram 1 1 x x 1 x x 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 x x x y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x x y x x y 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 2 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring

private lemma cell_5_0 (z t : ℝ) (_hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_5_1 (z t : ℝ) (_hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/2)*h0
  norm_num at hh

private lemma cell_5_2 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 6*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^3/5 - 13*z^2/10 + 12*z/5 - 7/5)*h0 + (1 - 2*z/5)*hf
  norm_num at hh

private lemma cell_5_3 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z^3 - 384*z^2 + 448*z - 176) + t^6*(-480*z^3 + 2880*z^2 - 2736*z + 576) + t^5*(1632*z^3 - 10320*z^2 + 8016*z - 1008) + t^4*(-3024*z^3 + 21888*z^2 - 15696*z + 1728) + t^3*(2736*z^3 - 25920*z^2 + 19152*z - 2448) + t^2*(-864*z^3 + 15120*z^2 - 12096*z + 1728) + t*(-3456*z^2 + 3024*z - 432):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(z^3/810 - z^2/405 - z/81 + 1/135) + t^5*(-8*z^3/135 + 38*z^2/135 - 22*z/135) + t^4*(43*z^3/90 - 319*z^2/135 + 46*z/27 - 61/270) + t^3*(-5*z^3/3 + 25*z^2/3 - 109*z/18 + 5/6) + t^2*(124*z^3/45 - 251*z^2/18 + 452*z/45 - 41/30) + t*(-21*z^3/10 + 54*z^2/5 - 233*z/30 + 29/30) + 3*z^3/5 - 47*z^2/15 + 34*z/15 - 7/15)*h0 + (-z^3/6480 + z^2/3240 + z/648 - 1/1080)*h1 + (4*t^7*z^2/405 - 4*t^7*z/405 - 16*t^7/135 - 2*t^6*z^2/27 + 2*t^6*z/27 + 133*t^6/135 + 34*t^5*z^2/135 - t^5*z/3 - 178*t^5/45 - 7*t^4*z^2/15 + 47*t^4*z/45 + 28*t^4/3 + 19*t^3*z^2/45 - 17*t^3*z/9 - 62*t^3/5 - 2*t^2*z^2/15 + 5*t^2*z/3 + 25*t^2/3 - 8*t*z/15 - 11*t/5)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_5_4 (z t : ℝ) (_hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/2)*h0
  norm_num at hh

private lemma cell_5_5 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z^3 + 12*z^2 - 18*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^3/2 - 3*z^2 + 9*z/2 - 2)*h0 + (z^2 - 5*z + 5)*hf
  norm_num at hh

private lemma cell_5_6 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h1 : (t*(1296*z^3 - 6480*z^2 + 9072*z - 1296):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (-z^3/324 + z^2/48 - 25*z/648 + 23/1296)*h1 + (4*t*z^2 - 19*t*z + 24*t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_5_7 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^3 + 12*z^2 - 18*z - 2) + 2*z^3 - 12*z^2 + 18*z - 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 48) + t^6*(-48*z^3 + 736*z^2 - 192*z) + t^5*(-464*z^3 - 2736*z^2 + 3744*z - 288) + t^4*(6352*z^3 - 10640*z^2 + 1760*z - 112) + t^3*(-22000*z^3 + 63024*z^2 - 42320*z + 5264) + t^2*(31280*z^3 - 97536*z^2 + 68736*z - 9056) + t*(-18784*z^3 + 55760*z^2 - 32272*z + 4096) + 4384*z^3 - 13376*z^2 + 8192*z - 1040:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-17*z^3/243 + 13*z^2/27 - 445*z/486 + 203/486) + t^6*(127*z^3/486 - 901*z^2/486 + 199*z/54 - 835/486) + t^5*(10*z^3/27 - 55*z^2/27 + 64*z/27 - 7/9) + t^4*(-997*z^3/486 + 6029*z^2/486 - 8849*z/486 + 1187/162) + t^3*(373*z^3/243 - 1363*z^2/162 + 3587*z/486 - 853/486) + t^2*(37*z^3/54 - 115*z^2/27 + 679*z/54 - 187/27) + t*(-62*z^3/81 + 1123*z^2/486 - 953*z/486 + 148/243) + 143*z^3/486 - 133*z^2/486 - 562*z/243 + 145/81)*h0 + (t*(17*z^3/1944 - 13*z^2/216 + 445*z/3888 - 203/3888) - 73*z^3/3888 + 251*z^2/1944 - 53*z/216 + 109/972)*h1 + (-34*t^8*z^2/243 + 200*t^8*z/243 - 7*t^8/243 + 263*t^7*z^2/243 - 842*t^7*z/81 + 1054*t^7/243 + 820*t^6*z^2/243 + 1025*t^6*z/27 - 8428*t^6/243 - 16792*t^5*z^2/243 + 14120*t^5*z/243 + 10463*t^5/243 + 77474*t^4*z^2/243 - 20197*t^4*z/27 + 75913*t^4/243 - 167258*t^3*z^2/243 + 476222*t^3*z/243 - 87619*t^3/81 + 2246*t^2*z^2/3 - 179573*t^2*z/81 + 32756*t^2/27 - 31501*t*z^2/81 + 90142*t*z/81 - 41215*t/81 + 19859*z^2/243 - 6508*z/27 + 29453/243)*hf
  norm_num at hh

private lemma cell_5_8 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 6*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^3/5 - 13*z^2/10 + 12*z/5 - 7/5)*h0 + (1 - 2*z/5)*hf
  norm_num at hh

private lemma cell_5_9 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(-3888*z^3 + 27216*z^2 - 49248*z + 7776) + 15552*z^3 - 107568*z^2 + 190512*z - 29808:ℝ)=0) (h2 : (t*(-5184*z^3 + 22032*z^2 - 25920*z + 3888) + 28512*z^3 - 107568*z^2 + 107568*z - 15552:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-31*z^3/3240 + 47*z^2/720 - 397*z/3240 + 359/6480)*h1 + (53*z^3/3888 - 361*z^2/3888 + 169*z/972 - 17/216)*h2 + (502*t*z^2/15 - 166*t*z/5 - 624*t/5 - 3598*z^2/15 + 1951*z/5 + 2142/5)*hf
  norm_num at hh

private lemma cell_5_10 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 8*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-z^3/2 + 7*z^2/2 - 13*z/2 + 5/2)*h0 + (z - 4)*hf
  norm_num at hh

private lemma cell_5_11 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z^3 - 384*z^2 + 384*z - 112) + t^6*(-480*z^3 + 3168*z^2 - 2400*z + 272) + t^5*(1760*z^3 - 16032*z^2 + 12096*z - 1376) + t^4*(-864*z^3 + 44544*z^2 - 36816*z + 5056) + t^3*(-15584*z^3 - 52848*z^2 + 53664*z - 7888) + t^2*(52272*z^3 - 15552*z^2 - 17856*z + 3296) + t*(-68464*z^3 + 97008*z^2 - 41568*z + 4720) + 32736*z^3 - 63648*z^2 + 34080*z - 4160:ℝ)=0) (h2 : (16*t^8 + t^7*(64*z^3 - 384*z^2 + 384*z - 112) + t^6*(-480*z^3 + 3360*z^2 - 2976*z + 464) + t^5*(32*z^3 - 10128*z^2 + 8784*z - 1232) + t^4*(19440*z^3 - 25728*z^2 + 11136*z - 1280) + t^3*(-136112*z^3 + 346080*z^2 - 210912*z + 26912) + t^2*(466128*z^3 - 1339344*z^2 + 846144*z - 108736) + t*(-852976*z^3 + 2548896*z^2 - 1629888*z + 210064) + 678576*z^3 - 2054496*z^2 + 1319424*z - 170240:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(-308*z^3/32805 + 2102*z^2/32805 - 2629*z/21870 + 3547/65610) + t^12*(190*z^3/6561 - 2599*z^2/13122 + 2447*z/6561 - 41/243) + t^11*(205*z^3/4374 - 1369*z^2/4374 + 829*z/1458 - 1099/4374) + t^10*(-1027*z^3/6561 + 12883*z^2/13122 - 10598*z/6561 + 1498/2187) + t^9*(9856*z^3/32805 - 84863*z^2/65610 + 10603*z/21870 + 9871/65610) + t^8*(-1567*z^3/729 + 7241*z^2/729 - 5045*z/729 + 208/243) + t^7*(104752*z^3/10935 - 945851*z^2/21870 + 107833*z/3645 - 74363/21870) + t^6*(-143809*z^3/4374 + 316072*z^2/2187 - 442235*z/4374 + 6409/486) + t^5*(63067*z^3/729 - 264283*z^2/729 + 40661*z/162 - 23551/729) + t^4*(-11746559*z^3/65610 + 23193758*z^2/32805 - 32111443*z/65610 + 719503/10935) + t^3*(18622423*z^3/65610 - 68549797*z^2/65610 + 15541547*z/21870 - 6254911/65610) + t^2*(-3549307*z^3/10935 + 24378601*z^2/21870 - 8020319*z/10935 + 223837/2430) + t*(3104887*z^3/13122 - 5088137*z^2/6561 + 1114445*z/2187 - 433589/6561) - 1048153*z^3/13122 + 1670605*z^2/6561 - 1108438*z/6561 + 33139/1458)*h0 + (t^7*(77*z^3/65610 - 1051*z^2/131220 + 2629*z/174960 - 3547/524880) + t^6*(-67*z^3/32805 + 458*z^2/32805 - 1723*z/65610 + 691/58320) + t^5*(-67*z^3/174960 + 209*z^2/87480 - 223*z/58320 + 61/43740) + t^4*(-34*z^3/32805 + 4211*z^2/524880 - 4609*z/262440 + 1501/174960) + t^3*(-1409*z^3/262440 + 17947*z^2/524880 - 10237*z/174960 + 13561/524880) + t^2*(-7*z^3/174960 + 833*z^2/174960 - 194*z/10935 + 11/1215) + t*(-505*z^3/52488 + 6269*z^2/104976 - 1801*z/17496 + 4667/104976) - 2419*z^3/262440 + 35497*z^2/524880 - 17419*z/131220 + 224/3645)*h1 + (-z^3/432 + z^2/72 - z/54 - 1/1296)*h2 + (-2464*t^14*z^2/32805 + 4784*t^14*z/10935 - 12884*t^14/32805 + 22768*t^13*z^2/32805 - 15904*t^13*z/3645 + 93898*t^13/32805 - 99116*t^12*z^2/32805 + 806216*t^12*z/32805 - 476984*t^12/32805 + 3274*t^11*z^2/729 - 305159*t^11*z/3645 + 1757696*t^11/32805 + 186386*t^10*z^2/10935 + 4999768*t^10*z/32805 - 3718657*t^10/32805 - 206138*t^9*z^2/2187 - 605890*t^9*z/6561 + 811505*t^9/6561 + 6242488*t^8*z^2/32805 - 614857*t^8*z/3645 - 1447418*t^8/32805 - 5997763*t^7*z^2/32805 + 14449867*t^7*z/32805 - 664871*t^7/32805 + 49235*t^6*z^2/2187 - 5759234*t^6*z/10935 - 764629*t^6/10935 + 2510444*t^5*z^2/10935 + 813580*t^5*z/2187 + 10788613*t^5/32805 - 4860106*t^4*z^2/10935 + 3025337*t^4*z/32805 - 25400207*t^4/32805 + 7125902*t^3*z^2/32805 - 2090734*t^3*z/10935 + 12192809*t^3/10935 + 29636357*t^2*z^2/32805 - 15486662*t^2*z/10935 - 6250411*t^2/6561 - 75142367*t*z^2/32805 + 15297407*t*z/3645 + 1837445*t/6561 + 20475971*z^2/10935 - 24365150*z/6561 + 58198/729)*hf
  norm_num at hh

private lemma cell_5_12 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z^3 + 768*z^2 - 1088*z + 16) + t^6*(1584*z^3 - 9792*z^2 + 14640*z - 1776) + t^5*(-8448*z^3 + 53040*z^2 - 81264*z + 11952) + t^4*(23760*z^3 - 150192*z^2 + 232128*z - 35712) + t^3*(-35712*z^3 + 226512*z^2 - 350928*z + 54432) + t^2*(26784*z^3 - 170640*z^2 + 264816*z - 41040) + t*(-7776*z^3 + 50112*z^2 - 78192*z + 12096):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(-z^3/810 + 7*z^2/405 - 16*z/405 + 2/135) + t^5*(4*z^3/135 - 4*z^2/15 + 68*z/135 - 2/15) + t^4*(-23*z^3/90 + 511*z^2/270 - 863*z/270 + 79/135) + t^3*(10*z^3/9 - 15*z^2/2 + 12*z - 17/9) + t^2*(-103*z^3/45 + 662*z^2/45 - 1031*z/45 + 52/15) + t*(34*z^3/15 - 206*z^2/15 + 207*z/10 - 16/5) - 29*z^3/30 + 26*z^2/5 - 109*z/15 + 14/15)*h0 + (z^3/6480 - 7*z^2/3240 + 2*z/405 - 1/540)*h1 + (8*t^7*z^2/405 - 104*t^7*z/405 + 52*t^7/135 - 11*t^6*z^2/45 + 29*t^6*z/9 - 142*t^6/27 + 176*t^5*z^2/135 - 779*t^5*z/45 + 1324*t^5/45 - 11*t^4*z^2/3 + 2198*t^4*z/45 - 422*t^4/5 + 248*t^3*z^2/45 - 1103*t^3*z/15 + 128*t^3 - 62*t^2*z^2/15 + 829*t^2*z/15 - 1456*t^2/15 + 6*t*z^2/5 - 242*t*z/15 + 29*t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_5_13 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^3 + 12*z^2 - 18*z - 2) + 2*z^3 - 12*z^2 + 18*z - 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-192*z^3 + 1152*z^2 - 1664*z + 144) + t^6*(2784*z^3 - 17312*z^2 + 26400*z - 3888) + t^5*(-20480*z^3 + 129024*z^2 - 199008*z + 30816) + t^4*(90304*z^3 - 572192*z^2 + 885296*z - 136864) + t^3*(-248032*z^3 + 1573968*z^2 - 2436608*z + 375536) + t^2*(412304*z^3 - 2614656*z^2 + 4046016*z - 623360) + t*(-375664*z^3 + 2380592*z^2 - 3682720*z + 567568) + 142816*z^3 - 904736*z^2 + 1399328*z - 215648:ℝ)=0) (h2 : (16*t^8 + t^7*(64*z - 240) + t^6*(144*z^3 - 896*z^2 + 912*z + 1104) + t^5*(-1472*z^3 + 9072*z^2 - 12528*z - 1296) + t^4*(6640*z^3 - 41264*z^2 + 61472*z - 5344) + t^3*(-16768*z^3 + 105744*z^2 - 162128*z + 22688) + t^2*(27392*z^3 - 174576*z^2 + 270480*z - 41456) + t*(-27712*z^3 + 176672*z^2 - 273808*z + 42400) + 15616*z^3 - 98912*z^2 + 152576*z - 23552:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(-2213*z^3/4374 + 45325*z^2/13122 - 85109*z/13122 + 19198/6561) + t^12*(55135*z^3/6561 - 752821*z^2/13122 + 706802*z/6561 - 70859/1458) + t^11*(-77303*z^3/1458 + 1583263*z^2/4374 - 2972963*z/4374 + 670609/2187) + t^10*(2004217*z^3/13122 - 13683049*z^2/13122 + 1427408*z/729 - 5795633/6561) + t^9*(-690823*z^3/4374 + 14149169*z^2/13122 - 26568733*z/13122 + 5993093/6561) + t^8*(-219209*z^3/1458 + 1496639*z^2/1458 - 936799*z/486 + 633955/729) + t^7*(1007998*z^3/2187 - 4588163*z^2/1458 + 12923707*z/2187 - 11661163/4374) + t^6*(-519391*z^3/2187 + 7091681*z^2/4374 - 2219423*z/729 + 3004117/2187) + t^5*(-107365*z^3/729 + 244576*z^2/243 - 2756711*z/1458 + 621686/729) + t^4*(1701449*z^3/13122 - 5810828*z^2/6561 + 10911923*z/6561 - 20242/27) + t^3*(113092*z^3/6561 - 521419*z^2/4374 + 2962439*z/13122 - 675575/6561) + t^2*(-97141*z^3/4374 + 333745*z^2/2187 - 1258619*z/4374 + 190181/1458) + t*(-2635*z^3/1458 + 166787*z^2/13122 - 160754*z/6561 + 76415/6561) + 3997*z^3/13122 - 15334*z^2/6561 + 65717*z/13122 - 7073/2187)*h0 + (t^7*(2213*z^3/34992 - 45325*z^2/104976 + 85109*z/104976 - 9599/26244) + t^6*(-80327*z^3/104976 + 548401*z^2/104976 - 64360*z/6561 + 154855/34992) + t^5*(9313*z^3/2916 - 762971*z^2/34992 + 1432669*z/34992 - 646333/34992) + t^4*(-586583*z^3/104976 + 4004657*z^2/104976 - 417763*z/5832 + 848111/26244) + t^3*(133175*z^3/34992 - 2727559*z^2/104976 + 5121635*z/104976 - 2310563/104976) + t^2*(-4967*z^3/8748 + 135641*z^2/34992 - 7075*z/972 + 114905/34992) + t*(-8581*z^3/26244 + 78079*z^2/34992 - 439753*z/104976 + 198377/104976) + 5113*z^3/104976 - 17435*z^2/52488 + 10909*z/17496 - 7381/26244)*h1 + (z^3/72 - 61*z^2/648 + 227*z/1296 - 17/216)*h2 + (24343*t^14*z^2/2187 - 425546*t^14*z/6561 + 557126*t^14/6561 - 2002201*t^13*z^2/6561 + 3973099*t^13*z/2187 - 16195303*t^13/6561 + 25692037*t^12*z^2/6561 - 155311885*t^12*z/6561 + 215875727*t^12/6561 - 22551640*t^11*z^2/729 + 1238883302*t^11*z/6561 - 1742143562*t^11/6561 + 1088209462*t^10*z^2/6561 - 2226732257*t^10*z/2187 + 9443391574*t^10/6561 - 1376507129*t^9*z^2/2187 + 25428993707*t^9*z/6561 - 36026144621*t^9/6561 + 3754398203*t^8*z^2/2187 - 69457743860*t^8*z/6561 + 98481250688*t^8/6561 - 22012330927*t^7*z^2/6561 + 15088777435*t^7*z/729 - 192572748427*t^7/6561 + 30190601299*t^6*z^2/6561 - 186221063149*t^6*z/6561 + 264043427426*t^6/6561 - 9260095969*t^5*z^2/2187 + 19032353422*t^5*z/729 - 80942840011*t^5/2187 + 5196398018*t^4*z^2/2187 - 32028912632*t^4*z/2187 + 45397247723*t^4/2187 - 4000835207*t^3*z^2/6561 + 24652331485*t^3*z/6561 - 3881799380*t^3/729 - 135951059*t^2*z^2/2187 + 837525373*t^2*z/2187 - 1186904512*t^2/2187 + 142992373*t*z^2/2187 - 880627927*t*z/2187 + 415892750*t/729 - 47065643*z^2/6561 + 10726765*z/243 - 410122013/6561)*hf
  norm_num at hh

private lemma cell_5_14 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z^3 + 768*z^2 - 1152*z + 80) + t^6*(1584*z^3 - 9504*z^2 + 14208*z - 2080) + t^5*(-7744*z^3 + 46752*z^2 - 70128*z + 11008) + t^4*(18528*z^3 - 113760*z^2 + 172800*z - 26912) + t^3*(-21680*z^3 + 137616*z^2 - 213792*z + 32816) + t^2*(11232*z^3 - 74592*z^2 + 118656*z - 18160) + t*(-1168*z^3 + 8304*z^2 - 13104*z + 2080) - 720*z^3 + 4896*z^2 - 7872*z + 1216:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-31*z^3/1215 + 209*z^2/1215 - 769*z/2430 + 113/810) + t^6*(463*z^3/2430 - 1556*z^2/1215 + 946*z/405 - 1208/1215) + t^5*(-313*z^3/810 + 1036*z^2/405 - 3611*z/810 + 206/135) + t^4*(269*z^3/1215 - 3007*z^2/2430 + 406*z/405 + 2047/1215) + t^3*(-247*z^3/243 + 1490*z^2/243 - 3871*z/486 - 121/81) + t^2*(1097*z^3/405 - 13981*z^2/810 + 7421*z/270 - 5083/810) + t*(-1673*z^3/1215 + 10732*z^2/1215 - 17266*z/1215 + 1322/405) - 296*z^3/1215 + 3763*z^2/2430 - 1054*z/405 + 1457/1215)*h0 + (t*(31*z^3/9720 - 209*z^2/9720 + 769*z/19440 - 113/6480) - 193*z^3/19440 + 1297*z^2/19440 - 11*z/90 + 1051/19440)*h1 + (496*t^8*z^2/1215 - 2848*t^8*z/1215 + 1246*t^8/405 - 7682*t^7*z^2/1215 + 44138*t^7*z/1215 - 58204*t^7/1215 + 9823*t^6*z^2/243 - 94393*t^6*z/405 + 25040*t^6/81 - 165208*t^5*z^2/1215 + 320347*t^5*z/405 - 428392*t^5/405 + 307504*t^4*z^2/1215 - 1821818*t^4*z/1215 + 822322*t^4/405 - 305039*t^3*z^2/1215 + 373421*t^3*z/243 - 2575166*t^3/1215 + 140012*t^2*z^2/1215 - 179890*t^2*z/243 + 421718*t^2/405 - 11299*t*z^2/1215 + 81319*t*z/1215 - 22594*t/243 - 193*z^2/27 + 11444*z/243 - 16315/243)*hf
  norm_num at hh

private lemma cell_5_15 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z^3 + 384*z^2 - 640*z + 16) + t^6*(704*z^3 - 3936*z^2 + 6176*z - 912) + t^5*(-3264*z^3 + 16512*z^2 - 23616*z + 3872) + t^4*(8320*z^3 - 37344*z^2 + 46960*z - 7264) + t^3*(-11936*z^3 + 47088*z^2 - 49856*z + 7056) + t^2*(8400*z^3 - 27552*z^2 + 20448*z - 2624) + t*(-1552*z^3 + 720*z^2 + 7424*z - 1232) - 544*z^3 + 3936*z^2 - 6784*z + 1056:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-5*z^3/162 + 52*z^2/243 - 199*z/486 + 44/243) + t^6*(25*z^3/162 - 266*z^2/243 + 523*z/243 - 223/243) + t^5*(-5*z^3/81 + 49*z^2/81 - 257*z/162 + 11/27) + t^4*(-7*z^3/18 + 569*z^2/243 - 1697*z/486 + 610/243) + t^3*(-17*z^3/162 + 319*z^2/486 - 839*z/486 - 379/486) + t^2*(85*z^3/81 - 1009*z^2/162 + 1723*z/162 - 191/54) + t*(-38*z^3/81 + 490*z^2/243 - 931*z/486 + 349/486) - 4*z^3/27 + 358*z^2/243 - 875*z/243 + 553/486)*h0 + (t*(5*z^3/1296 - 13*z^2/486 + 199*z/3888 - 11/486) - z^3/72 + 47*z^2/486 - 725*z/3888 + 163/1944)*h1 + (20*t^8*z^2/81 - 356*t^8*z/243 + 560*t^8/243 - 292*t^7*z^2/81 + 4934*t^7*z/243 - 7412*t^7/243 + 604*t^6*z^2/27 - 28472*t^6*z/243 + 39896*t^6/243 - 6272*t^5*z^2/81 + 89810*t^5*z/243 - 113783*t^5/243 + 13090*t^4*z^2/81 - 168395*t^4*z/243 + 185795*t^4/243 - 5351*t^3*z^2/27 + 182735*t^3*z/243 - 165044*t^3/243 + 9935*t^2*z^2/81 - 92516*t^2*z/243 + 49250*t^2/243 - 1576*t*z^2/81 - 1420*t*z/243 + 32773*t/243 - 68*z^2/9 + 13216*z/243 - 21826/243)*hf
  norm_num at hh

private lemma cell_5_16 (z t : ℝ) (_hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/2)*h0
  norm_num at hh

private lemma cell_5_17 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z^3 + 12*z^2 - 18*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^3/2 - 3*z^2 + 9*z/2 - 2)*h0 + (z^2 - 5*z + 5)*hf
  norm_num at hh

private lemma cell_5_18 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h2 : (t*(1296*z^3 - 6480*z^2 + 9072*z - 1296):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (-z^3/324 + z^2/48 - 25*z/648 + 23/1296)*h2 + (4*t*z^2 - 19*t*z + 24*t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_5_19 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^3 + 12*z^2 - 18*z - 2) + 2*z^3 - 12*z^2 + 18*z - 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 48) + t^6*(144*z^3 - 416*z^2 + 1536*z - 192) + t^5*(-2048*z^3 + 5616*z^2 - 8208*z + 1296) + t^4*(14272*z^3 - 42464*z^2 + 38768*z - 5584) + t^3*(-53632*z^3 + 165264*z^2 - 126272*z + 17264) + t^2*(115376*z^3 - 360336*z^2 + 257520*z - 34400) + t*(-133840*z^3 + 416624*z^2 - 285712*z + 37648) + 65440*z^3 - 202016*z^2 + 134480*z - 17552:ℝ)=0) (h2 : (16*t^8 + t^7*(-128*z - 48) + t^6*(-48*z^3 + 736*z^2 - 192*z) + t^5*(-464*z^3 - 2736*z^2 + 3744*z - 288) + t^4*(6352*z^3 - 10640*z^2 + 1760*z - 112) + t^3*(-22000*z^3 + 63024*z^2 - 42320*z + 5264) + t^2*(31280*z^3 - 97536*z^2 + 68736*z - 9056) + t*(-18784*z^3 + 55760*z^2 - 32272*z + 4096) + 4384*z^3 - 13376*z^2 + 8192*z - 1040:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(473*z^3/98415 - 479*z^2/14580 + 24329*z/393660 - 2746/98415) + t^12*(-1151*z^3/39366 + 15835*z^2/78732 - 835*z/2187 + 3406/19683) + t^11*(2051*z^3/131220 - 1432*z^2/10935 + 20491*z/65610 - 10091/65610) + t^10*(90607*z^3/393660 - 531023*z^2/393660 + 757289*z/393660 - 98303/131220) + t^9*(-161503*z^3/196830 + 47164*z^2/10935 - 899521*z/196830 + 540667/393660) + t^8*(101227*z^3/43740 - 476423*z^2/43740 + 76781*z/10935 - 3989/7290) + t^7*(-127091*z^3/21870 + 895181*z^2/32805 - 1141301*z/65610 + 81611/65610) + t^6*(1312351*z^3/131220 - 6289259*z^2/131220 + 4543007*z/131220 - 52726/10935) + t^5*(-50231*z^3/4860 + 545074*z^2/10935 - 1660433*z/43740 + 137869/21870) + t^4*(938483*z^3/196830 - 8227459*z^2/393660 + 315781*z/32805 + 567863/393660) + t^3*(-1763*z^3/13122 - 107699*z^2/78732 + 440887*z/78732 - 251605/78732) + t^2*(5257*z^3/131220 - 93509*z^2/65610 + 31924*z/3645 - 700489/131220) + t*(164149*z^3/393660 - 256277*z^2/131220 - 59507*z/393660 + 388117/393660) - 63413*z^3/196830 + 861049*z^2/393660 - 131896*z/32805 + 397661/196830)*h0 + (t^7*(-473*z^3/787320 + 479*z^2/116640 - 24329*z/3149280 + 1373/393660) + t^6*(7853*z^3/3149280 - 6739*z^2/393660 + 11339*z/349920 - 11549/787320) + t^5*(83*z^3/69984 - 1565*z^2/209952 + 2569*z/209952 - 1087/209952) + t^4*(-17587*z^3/1574640 + 234091*z^2/3149280 - 211499*z/1574640 + 10421/174960) + t^3*(9049*z^3/3149280 - 18167*z^2/1049760 + 10301*z/393660 - 33263/3149280) + t^2*(11189*z^3/1049760 - 38533*z^2/524880 + 48851*z/349920 - 33229/524880) + t*(-23*z^3/23328 + 4159*z^2/629856 - 7583*z/629856 + 3371/629856) - 9959*z^3/3149280 + 34763*z^2/1574640 - 134743*z/3149280 + 5129/262440)*h1 + (-23*z^3/1296 + 157*z^2/1296 - 295*z/1296 + 67/648)*h2 + (946*t^14*z^2/98415 - 11041*t^14*z/196830 + 22*t^14/98415 + 1813*t^13*z^2/98415 + 10771*t^13*z/65610 + 127207*t^13/196830 - 29519*t^12*z^2/19683 + 235289*t^12*z/65610 - 689033*t^12/98415 + 2743687*t^11*z^2/196830 - 1281124*t^11*z/32805 + 7079507*t^11/196830 - 12965827*t^10*z^2/196830 + 2135441*t^10*z/10935 - 794725*t^10/6561 + 16642592*t^9*z^2/98415 - 17367013*t^9*z/32805 + 17132761*t^9/65610 - 30902147*t^8*z^2/196830 + 57173714*t^8*z/98415 - 39971327*t^8/196830 - 34465102*t^7*z^2/98415 + 25109183*t^7*z/32805 - 114689617*t^7/196830 + 302066*t^6*z^2/243 - 314586607*t^6*z/98415 + 178339784*t^6/98415 - 25642264*t^5*z^2/19683 + 34498718*t^5*z/10935 - 152291413*t^5/98415 - 376115*t^4*z^2/19683 + 24617672*t^4*z/32805 - 45876281*t^4/65610 + 52001681*t^3*z^2/65610 - 5761063*t^3*z/2187 + 29158888*t^3/19683 + 8982661*t^2*z^2/98415 - 31659437*t^2*z/98415 + 11149471*t^2/39366 - 13651342*t*z^2/19683 + 45233699*t*z/21870 - 20850779*t/19683 + 3120722*z^2/10935 - 56590829*z/65610 + 44837804/98415)*hf
  norm_num at hh

private lemma cell_5_20 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z^3 + 12*z^2 - 18*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^3/2 - 3*z^2 + 9*z/2 - 2)*h0 + (z^2 - 5*z + 5)*hf
  norm_num at hh

private lemma cell_5_21 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-6*z^3 + 36*z^2 - 54*z + 8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z^3/2 - 9*z^2 + 27*z/2 - 11/2)*h0 + (9*z^2 - 45*z + 45)*hf
  norm_num at hh

private lemma cell_5_22 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z^3 + 10*z^2 - 12*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-3*z^3/2 + 10*z^2 - 18*z + 15/2)*h0 + (-3*z^2 + 14*z - 14)*hf
  norm_num at hh

private lemma cell_5_23 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z^3 + 24*z^2 - 36*z + 2) + 2*z^3 - 12*z^2 + 18*z - 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z^3 + 384*z^2 - 704*z + 80) + t^6*(704*z^3 - 3328*z^2 + 5232*z - 896) + t^5*(-5056*z^3 + 17904*z^2 - 19152*z + 2928) + t^4*(26576*z^3 - 82528*z^2 + 60592*z - 8032) + t^3*(-89328*z^3 + 270144*z^2 - 172688*z + 22128) + t^2*(177632*z^3 - 536592*z^2 + 336768*z - 43136) + t*(-190400*z^3 + 576704*z^2 - 364912*z + 46864) + 84416*z^3 - 256288*z^2 + 163552*z - 21056:ℝ)=0) : (t - z^2 + 3*z - 2:ℝ)=0 := by
  have hh : (t - z^2 + 3*z - 2:ℝ)=0 := by linear_combination (t^6*(-2869*z^3/810 + 19591*z^2/810 - 6133*z/135 + 16603/810) + t^5*(13*z^3/27 - 91*z^2/27 + 59*z/9 - 3) + t^4*(2947*z^3/135 - 20053*z^2/135 + 37474*z/135 - 33743/270) + t^3*(7679*z^3/810 - 989*z^2/15 + 51454*z/405 - 46933/810) + t^2*(-1397*z^3/90 + 9623*z^2/90 - 27416*z/135 + 24857/270) + t*(-541*z^3/90 + 5566*z^2/135 - 21211*z/270 + 4813/135) + 299*z^3/162 - 2023*z^2/162 + 3853*z/162 - 98/9)*h0 + (2869*z^3/6480 - 19591*z^2/6480 + 6133*z/1080 - 16603/6480)*h1 + (5738*t^7*z^2/405 - 3716*t^7*z/45 + 68842*t^7/405 - 122587*t^6*z^2/405 + 553702*t^6*z/405 - 809506*t^6/405 + 941578*t^5*z^2/405 - 1085957*t^5*z/135 + 3184081*t^5/405 - 4767733*t^4*z^2/405 + 13992272*t^4*z/405 - 940397*t^4/45 + 15984802*t^3*z^2/405 - 9099913*t^3*z/81 + 22811567*t^3/405 - 31848803*t^2*z^2/405 + 30246163*t^2*z/135 - 8941435*t^2/81 + 34148959*t*z^2/405 - 97601203*t*z/405 + 9733658*t/81 - 5046113*z^2/135 + 8673694*z/81 - 21859178/405)*hf
  exact hh

private lemma cell_5_24 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(-5184*z^3 + 22032*z^2 - 25920*z + 3888) + 28512*z^3 - 107568*z^2 + 107568*z - 15552:ℝ)=0) (h2 : (t*(-12960*z^3 + 37584*z^2 - 20736*z + 2592) + 117936*z^3 - 358992*z^2 + 230688*z - 29808:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-35*z^3/648 + 1433*z^2/3888 - 2689*z/3888 + 1213/3888)*h1 + (209*z^3/6480 - 53*z^2/240 + 1349*z/3240 - 203/1080)*h2 + (138*t*z^2 - 113*t*z/15 - 3629*t/5 - 11319*z^2/5 + 81863*z/15 - 3749/5)*hf
  norm_num at hh

private lemma cell_5_25 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z^3 + 10*z^2 - 12*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-3*z^3/2 + 10*z^2 - 18*z + 15/2)*h0 + (-3*z^2 + 14*z - 14)*hf
  norm_num at hh

private lemma cell_5_26 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z^2 + 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^2/2 - 5*z/2 + 2)*h0 + (1)*hf
  norm_num at hh

private lemma cell_5_27 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^3 + 12*z^2 - 20*z) + 2*z^3 - 12*z^2 + 20*z - 2:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 192*z) + t^6*(144*z^3 + 1488*z - 368) + t^5*(-2880*z^3 + 3024*z^2 - 5616*z + 976) + t^4*(26928*z^3 - 56880*z^2 + 45312*z - 6080) + t^3*(-122400*z^3 + 306576*z^2 - 210768*z + 27808) + t^2*(304416*z^3 - 830736*z^2 + 562032*z - 74000) + t*(-390240*z^3 + 1107072*z^2 - 736752*z + 96352) + 207360*z^3 - 614592*z^2 + 426144*z - 56384:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(6794*z^3/3645 - 92747*z^2/7290 + 174101*z/7290 - 26177/2430) + t^6*(-3182*z^3/3645 + 21508*z^2/3645 - 79583*z/7290 + 1981/405) + t^5*(-31597*z^3/2430 + 108529*z^2/1215 - 205642*z/1215 + 31049/405) + t^4*(-197*z^3/729 - 1411*z^2/1458 + 6995*z/729 - 2857/486) + t^3*(197711*z^3/7290 - 1288219*z^2/7290 + 1124021*z/3645 - 36301/270) + t^2*(-12953*z^3/2430 + 26291*z^2/1215 + 1199*z/2430 - 3404/405) + t*(-4513*z^3/3645 + 79952*z^2/3645 - 575827*z/7290 + 52577/1215) - 2921*z^3/1458 + 13417*z^2/1458 - 3392*z/729 - 85/162)*h0 + (t*(-3397*z^3/14580 + 92747*z^2/58320 - 174101*z/58320 + 26177/19440) + 12673*z^3/58320 - 86507*z^2/58320 + 162401*z/58320 - 2713/2160)*h1 + (13588*t^8*z^2/3645 - 79159*t^8*z/3645 - 13646*t^8/1215 + 20468*t^7*z^2/729 + 137132*t^7*z/3645 + 414017*t^7/1215 - 2648324*t^6*z^2/3645 + 2641607*t^6*z/3645 - 78971*t^6/45 + 5048513*t^5*z^2/729 - 46882198*t^5*z/3645 + 2389940*t^5/243 - 125077178*t^4*z^2/3645 + 282498518*t^4*z/3645 - 54767947*t^4/1215 + 355237168*t^3*z^2/3645 - 885187312*t^3*z/3645 + 54357836*t^3/405 - 114499597*t^2*z^2/729 + 1498494506*t^2*z/3645 - 270585668*t^2/1215 + 485189371*t*z^2/3645 - 262890614*t*z/729 + 239392076*t/1215 - 32845495*z^2/729 + 458178956*z/3645 - 28681856/405)*hf
  norm_num at hh

private lemma cell_5_28 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^3 + 12*z^2 - 18*z - 2) + 2*z^3 - 12*z^2 + 18*z - 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-192*z^3 + 1152*z^2 - 1664*z + 144) + t^6*(2784*z^3 - 17120*z^2 + 25824*z - 3696) + t^5*(-19904*z^3 + 123408*z^2 - 188496*z + 28656) + t^4*(84112*z^3 - 521504*z^2 + 797312*z - 122464) + t^3*(-215344*z^3 + 1329312*z^2 - 2026880*z + 311840) + t^2*(326768*z^3 - 1996176*z^2 + 3025344*z - 465248) + t*(-271408*z^3 + 1620992*z^2 - 2424736*z + 372304) + 98896*z^3 - 557792*z^2 + 805280*z - 123104:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(26*z^3/243 - 53*z^2/81 + 248*z/243 - 205/486) + t^6*(-193*z^3/486 + 689*z^2/243 - 2761*z/486 + 653/243) + t^5*(77*z^3/162 - 340*z^2/81 + 1729*z/162 - 965/162) + t^4*(-151*z^3/486 + 1069*z^2/486 - 1301*z/243 + 485/81) + t^3*(-277*z^3/162 + 3097*z^2/243 - 11563*z/486 + 269/486) + t^2*(1105*z^3/162 - 3509*z^2/81 + 1213*z/18 - 595/54) + t*(-3637*z^3/486 + 21953*z^2/486 - 15680*z/243 + 2884/243) + 1259*z^3/486 - 3749*z^2/243 + 3505*z/162 - 1172/243)*h0 + (t*(-13*z^3/972 + 53*z^2/648 - 31*z/243 + 205/3888) + 29*z^3/972 - 89*z^2/486 + 559*z/1944 - 77/648)*h1 + (-572*t^8*z^2/243 + 2926*t^8*z/243 - 2894*t^8/243 + 10195*t^7*z^2/243 - 17779*t^7*z/81 + 18503*t^7/81 - 84448*t^6*z^2/243 + 447578*t^6*z/243 - 478376*t^6/243 + 417286*t^5*z^2/243 - 2220647*t^5*z/243 + 2396258*t^5/243 - 1310360*t^4*z^2/243 + 6960799*t^4*z/243 - 278632*t^4/9 + 2627386*t^3*z^2/243 - 13862828*t^3*z/243 + 14954516*t^3/243 - 1086032*t^2*z^2/81 + 1883773*t^2*z/27 - 18201424*t^2/243 + 764672*t*z^2/81 - 11608945*t*z/243 + 1370108*t/27 - 718255*z^2/243 + 3432131*z/243 - 3556729/243)*hf
  norm_num at hh

private lemma cell_5_29 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z^3 + 24*z^2 - 36*z + 2) + 2*z^3 - 12*z^2 + 18*z - 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-256*z^3 + 1536*z^2 - 2240*z + 272) + t^6*(4112*z^3 - 25408*z^2 + 38736*z - 5936) + t^5*(-35152*z^3 + 219072*z^2 - 335952*z + 51888) + t^4*(178928*z^3 - 1120672*z^2 + 1722688*z - 265408) + t^3*(-554352*z^3 + 3484272*z^2 - 5365904*z + 826464) + t^2*(1019168*z^3 - 6422304*z^2 + 9904272*z - 1525760) + t*(-1016720*z^3 + 6420032*z^2 - 9912016*z + 1527184) + 422144*z^3 - 2670160*z^2 + 4126384*z - 635840:ℝ)=0) : (t - 2*z^3 + 13*z^2 - 21*z + 3:ℝ)=0 := by
  have hh : (t - 2*z^3 + 13*z^2 - 21*z + 3:ℝ)=0 := by linear_combination (t^6*(5*z^3/162 - 41*z^2/162 + 16*z/27 - 47/162) + t^5*(-7*z^3/27 + 41*z^2/27 - 59*z/27 + 23/27) + t^4*(-8*z^3/27 + 49*z^2/27 - 8*z/3 + 10/9) + t^3*(-5*z^3/81 - 2*z^2/9 + 245*z/162 - 101/81) + t^2*(37*z^3/54 - 211*z^2/54 + 359*z/54 - 43/27) + t*(-91*z^3/54 + 9*z^2 - 311*z/27 + 5/3) + 187*z^3/162 - 1109*z^2/162 + 844*z/81 - 35/18)*h0 + (-5*z^3/1296 + 41*z^2/1296 - 2*z/27 + 47/1296)*h1 + (-70*t^7*z^2/81 + 56*t^7*z/9 - 890*t^7/81 + 1196*t^6*z^2/81 - 9038*t^6*z/81 + 17072*t^6/81 - 11039*t^5*z^2/81 + 27310*t^5*z/27 - 152261*t^5/81 + 55943*t^4*z^2/81 - 417646*t^4*z/81 + 260092*t^4/27 - 173003*t^3*z^2/81 + 1295719*t^3*z/81 - 2427952*t^3/81 + 317833*t^2*z^2/81 - 795422*t^2*z/27 + 4481707*t^2/81 - 317078*t*z^2/81 + 2384501*t*z/81 - 4485437*t/81 + 4879*z^2/3 - 991807*z/81 + 1867708/81)*hf
  exact hh

private lemma cell_5_30 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^3 + 12*z^2 - 20*z) + 2*z^3 - 12*z^2 + 20*z - 2:ℝ)=0) (h2 : (16*t^8 - 176*t^7 + t^6*(-48*z^3 + 288*z^2 - 480*z + 736) + t^5*(432*z^3 - 2592*z^2 + 4320*z - 1616) + t^4*(-1008*z^3 + 6192*z^2 - 10512*z + 1792) + t^3*(-192*z^3 + 144*z^2 + 1104*z + 400) + t^2*(1728*z^3 - 9072*z^2 + 13392*z - 2288) + t*(576*z^3 - 2304*z^2 + 2304*z - 320) - 192*z^3 + 864*z^2 - 1056*z + 160:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-229*z^3/1215 + 517*z^2/405 - 2878*z/1215 + 2581/2430) + t^6*(4817*z^3/2430 - 10891*z^2/810 + 30382*z/1215 - 27289/2430) + t^5*(-5519*z^3/810 + 18778*z^2/405 - 11698*z/135 + 31613/810) + t^4*(9338*z^3/1215 - 42743*z^2/810 + 121406*z/1215 - 55021/1215) + t^3*(2614*z^3/1215 - 11429*z^2/810 + 30298*z/1215 - 13433/1215) + t^2*(-4867*z^3/810 + 16754*z^2/405 - 10619*z/135 + 28939/810) + t*(-139*z^3/486 + 49*z^2/27 - 1495*z/486 + 370/243) - 379*z^3/2430 + 31*z^2/30 - 2279*z/1215 + 2423/2430)*h0 + (t*(229*z^3/9720 - 517*z^2/3240 + 1439*z/4860 - 2581/19440) - 259*z^3/9720 + 1169*z^2/6480 - 3253*z/9720 + 1463/9720)*h2 + (-458*t^8*z^2/1215 + 2644*t^8*z/1215 - 4028*t^8/1215 + 6649*t^7*z^2/1215 - 38432*t^7*z/1215 + 58654*t^7/1215 - 35294*t^6*z^2/1215 + 204322*t^6*z/1215 - 312524*t^6/1215 + 78073*t^5*z^2/1215 - 457061*t^5*z/1215 + 706303*t^5/1215 - 40586*t^4*z^2/1215 + 270589*t^4*z/1215 - 460046*t^4/1215 - 75509*t^3*z^2/1215 + 73334*t^3*z/243 - 472799*t^3/1215 + 53362*t^2*z^2/1215 - 300854*t^2*z/1215 + 451192*t^2/1215 + 4892*t*z^2/243 - 19075*t*z/243 + 17606*t/243 - 5837*z^2/1215 + 24412*z/1215 - 25622/1215)*hf
  norm_num at hh

private lemma cell_5_31 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z^3 + 24*z^2 - 36*z) + 4*z^3 - 24*z^2 + 36*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-192*z^3 + 1152*z^2 - 1792*z + 272) + t^6*(2784*z^3 - 15968*z^2 + 23552*z - 3728) + t^5*(-20416*z^3 + 112272*z^2 - 159600*z + 24368) + t^4*(90992*z^3 - 479072*z^2 + 659424*z - 99936) + t^3*(-253232*z^3 + 1271424*z^2 - 1687936*z + 255104) + t^2*(428176*z^3 - 2042640*z^2 + 2599200*z - 390688) + t*(-400496*z^3 + 1809920*z^2 - 2191648*z + 326960) + 158096*z^3 - 674816*z^2 + 770784*z - 113920:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-100*z^3/81 + 4087*z^2/486 - 7649*z/486 + 1723/243) + t^6*(8*z^3/243 - 31*z^2/486 - 26*z/81 + 107/486) + t^5*(721*z^3/81 - 9913*z^2/162 + 9401*z/81 - 2833/54) + t^4*(451*z^3/486 - 1516*z^2/243 + 2764*z/243 - 473/81) + t^3*(-859*z^3/54 + 26786*z^2/243 - 102557*z/486 + 48041/486) + t^2*(-404*z^3/81 + 269*z^2/9 - 7429*z/162 + 2015/162) + t*(3124*z^3/243 - 6721*z^2/81 + 70049*z/486 - 13424/243) - 1337*z^3/486 + 4064*z^2/243 - 6437*z/243 + 1145/162)*h0 + (t*(25*z^3/162 - 4087*z^2/3888 + 7649*z/3888 - 1723/1944) - 737*z^3/1944 + 2509*z^2/972 - 6257*z/1296 + 8455/3888)*h1 + (2000*t^8*z^2/81 - 34870*t^8*z/243 + 50020*t^8/243 - 120856*t^7*z^2/243 + 674878*t^7*z/243 - 914264*t^7/243 + 1030696*t^6*z^2/243 - 1846264*t^6*z/81 + 7221325*t^6/243 - 5300774*t^5*z^2/243 + 1013017*t^5*z/9 - 34499716*t^5/243 + 5954158*t^4*z^2/81 - 29441293*t^4*z/81 + 107741233*t^4/243 - 39374984*t^3*z^2/243 + 186174251*t^3*z/243 - 218828018*t^3/243 + 54481658*t^2*z^2/243 - 245767465*t^2*z/243 + 276881855*t^2/243 - 42839464*t*z^2/243 + 183950923*t*z/243 - 65789047*t/81 + 4855756*z^2/81 - 6599396*z/27 + 60206713/243)*hf
  norm_num at hh

private lemma cell_5_32 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 6*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^3/5 - 13*z^2/10 + 12*z/5 - 7/5)*h0 + (1 - 2*z/5)*hf
  norm_num at hh

private lemma cell_5_33 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(-5184*z^3 + 22032*z^2 - 25920*z + 3888) + 28512*z^3 - 107568*z^2 + 107568*z - 15552:ℝ)=0) (h2 : (t*(-3888*z^3 + 27216*z^2 - 49248*z + 7776) + 15552*z^3 - 107568*z^2 + 190512*z - 29808:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (53*z^3/3888 - 361*z^2/3888 + 169*z/972 - 17/216)*h1 + (-31*z^3/3240 + 47*z^2/720 - 397*z/3240 + 359/6480)*h2 + (502*t*z^2/15 - 166*t*z/5 - 624*t/5 - 3598*z^2/15 + 1951*z/5 + 2142/5)*hf
  norm_num at hh

private lemma cell_5_34 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 8*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-z^3/2 + 7*z^2/2 - 13*z/2 + 5/2)*h0 + (z - 4)*hf
  norm_num at hh

private lemma cell_5_35 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z^3 - 384*z^2 + 384*z - 112) + t^6*(-480*z^3 + 3360*z^2 - 2976*z + 464) + t^5*(32*z^3 - 10128*z^2 + 8784*z - 1232) + t^4*(19440*z^3 - 25728*z^2 + 11136*z - 1280) + t^3*(-136112*z^3 + 346080*z^2 - 210912*z + 26912) + t^2*(466128*z^3 - 1339344*z^2 + 846144*z - 108736) + t*(-852976*z^3 + 2548896*z^2 - 1629888*z + 210064) + 678576*z^3 - 2054496*z^2 + 1319424*z - 170240:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(52*z^3/243 - 356*z^2/243 + 673*z/243 - 23/18) + t^6*(-175*z^3/243 + 397*z^2/81 - 4453*z/486 + 2009/486) + t^5*(47*z^3/81 - 305*z^2/81 + 1043*z/162 - 68/27) + t^4*(-215*z^3/486 + 131*z^2/54 - 659*z/243 + 157/243) + t^3*(-34*z^3/243 + 380*z^2/243 - 2561*z/486 + 347/162) + t^2*(119*z^3/81 - 241*z^2/27 + 1355*z/81 - 184/27) + t*(-364*z^3/243 + 1469*z^2/243 - 3359*z/486 + 49/18) + 671*z^3/486 - 839*z^2/162 + 2443*z/486 - 1091/486)*h0 + (t*(-13*z^3/486 + 89*z^2/486 - 673*z/1944 + 23/144) + 31*z^3/648 - 319*z^2/972 + 1211*z/1944 - 47/162)*h1 + (416*t^8*z^2/243 - 2432*t^8*z/243 + 2224*t^8/243 - 1288*t^7*z^2/81 + 25616*t^7*z/243 - 20042*t^7/243 + 5788*t^6*z^2/243 - 103730*t^6*z/243 + 75758*t^6/243 + 41996*t^5*z^2/81 - 30388*t^5*z/243 - 36365*t^5/243 - 1110718*t^4*z^2/243 + 264569*t^4*z/27 - 1129682*t^4/243 + 1537378*t^3*z^2/81 - 4013846*t^3*z/81 + 678736*t^3/27 - 10963082*t^2*z^2/243 + 30526550*t^2*z/243 - 15811948*t^2/243 + 4775530*t*z^2/81 - 40919750*t*z/243 + 21413447*t/243 - 876494*z^2/27 + 22780159*z/243 - 12000586/243)*hf
  norm_num at hh

private lemma cell_5_36 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(-12960*z^3 + 37584*z^2 - 20736*z + 2592) + 117936*z^3 - 358992*z^2 + 230688*z - 29808:ℝ)=0) (h2 : (t*(-5184*z^3 + 22032*z^2 - 25920*z + 3888) + 28512*z^3 - 107568*z^2 + 107568*z - 15552:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (209*z^3/6480 - 53*z^2/240 + 1349*z/3240 - 203/1080)*h1 + (-35*z^3/648 + 1433*z^2/3888 - 2689*z/3888 + 1213/3888)*h2 + (138*t*z^2 - 113*t*z/15 - 3629*t/5 - 11319*z^2/5 + 81863*z/15 - 3749/5)*hf
  norm_num at hh

private lemma cell_5_37 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z^3 + 10*z^2 - 12*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-3*z^3/2 + 10*z^2 - 18*z + 15/2)*h0 + (-3*z^2 + 14*z - 14)*hf
  norm_num at hh

private lemma cell_5_38 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z^2 + 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^2/2 - 5*z/2 + 2)*h0 + (1)*hf
  norm_num at hh

private lemma cell_5_39 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^3 + 12*z^2 - 20*z) + 2*z^3 - 12*z^2 + 20*z - 2:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 192*z) + t^6*(-48*z^3 + 1344*z^2 - 816*z + 16) + t^5*(-3024*z^3 + 576*z^2 + 3024*z - 464) + t^4*(38736*z^3 - 92448*z^2 + 52224*z - 6368) + t^3*(-205392*z^3 + 582960*z^2 - 371184*z + 47776) + t^2*(590112*z^3 - 1751040*z^2 + 1121904*z - 144704) + t*(-912240*z^3 + 2748384*z^2 - 1758864*z + 226672) + 596832*z^3 - 1811184*z^2 + 1163856*z - 150176:ℝ)=0) (h2 : (16*t^8 + t^7*(16 - 192*z) + t^6*(144*z^3 + 1488*z - 368) + t^5*(-2880*z^3 + 3024*z^2 - 5616*z + 976) + t^4*(26928*z^3 - 56880*z^2 + 45312*z - 6080) + t^3*(-122400*z^3 + 306576*z^2 - 210768*z + 27808) + t^2*(304416*z^3 - 830736*z^2 + 562032*z - 74000) + t*(-390240*z^3 + 1107072*z^2 - 736752*z + 96352) + 207360*z^3 - 614592*z^2 + 426144*z - 56384:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(8222*z^3/32805 - 56152*z^2/32805 + 105493*z/32805 - 6347/4374) + t^12*(103*z^3/32805 + 178*z^2/32805 - 2749*z/32805 + 1141/21870) + t^11*(-14933*z^3/4374 + 497861*z^2/21870 - 902291*z/21870 + 66784/3645) + t^10*(71488*z^3/32805 - 54490*z^2/6561 - 158447*z/65610 + 50339/10935) + t^9*(-815687*z^3/65610 + 417527*z^2/13122 + 2809552*z/32805 - 732698/10935) + t^8*(1145833*z^3/7290 - 5621819*z^2/7290 + 4525463*z/7290 - 144154/1215) + t^7*(-6925313*z^3/10935 + 13467481*z^2/4374 - 25925164*z/10935 + 2946007/7290) + t^6*(19946714*z^3/10935 - 95084863*z^2/10935 + 26379853*z/4374 - 5189329/7290) + t^5*(-29589961*z^3/7290 + 28328125*z^2/1458 - 100558133*z/7290 + 2182261/1215) + t^4*(211438384*z^3/32805 - 202802815*z^2/6561 + 1455097639*z/65610 - 32893738/10935) + t^3*(-230478262*z^3/32805 + 2206969981*z^2/65610 - 1570021573*z/65610 + 34346983/10935) + t^2*(109031509*z^3/21870 - 104394517*z^2/4374 + 185787916*z/10935 - 8152159/3645) + t*(-66506704*z^3/32805 + 637136137*z^2/65610 - 456111931*z/65610 + 20458457/21870) + 2266652*z^3/6561 - 21673955*z^2/13122 + 7726012*z/6561 - 340970/2187)*h0 + (t^7*(-4111*z^3/131220 + 7019*z^2/32805 - 105493*z/262440 + 6347/34992) + t^6*(8119*z^3/524880 - 5633*z^2/52488 + 54121*z/262440 - 8219/87480) + t^5*(40717*z^3/174960 - 55019*z^2/34992 + 10597*z/3645 - 56983/43740) + t^4*(-39811*z^3/524880 + 226109*z^2/524880 - 299387*z/524880 + 12293/58320) + t^3*(-69043*z^3/262440 + 217313*z^2/104976 - 2434453*z/524880 + 97933/43740) + t^2*(-23729*z^3/87480 + 117167*z^2/87480 - 64771*z/58320 + 9931/43740) + t*(214151*z^3/524880 - 237599*z^2/104976 + 92488*z/32805 - 86831/87480) - 11083*z^3/104976 + 26401*z^2/52488 - 36515*z/104976 + 239/5832)*h1 + (71*z^3/810 - 647*z^2/1080 + 7301*z/6480 - 206/405)*h2 + (16444*t^14*z^2/32805 - 19172*t^14*z/6561 - 16438*t^14/10935 - 13114*t^13*z^2/6561 + 1469306*t^13*z/32805 - 73268*t^13/3645 - 661552*t^12*z^2/6561 + 650567*t^12*z/32805 + 1028269*t^12/10935 + 42078839*t^11*z^2/32805 - 20053009*t^11*z/6561 + 13819249*t^11/10935 - 208739284*t^10*z^2/32805 + 122985155*t^10*z/6561 - 11742883*t^10/1215 + 418173287*t^9*z^2/32805 - 277992277*t^9*z/6561 + 235886552*t^9/10935 + 116348483*t^8*z^2/10935 - 132303053*t^8*z/10935 + 8105132*t^8/729 - 1156885327*t^7*z^2/10935 + 2718681592*t^7*z/10935 - 168213523*t^7/1215 + 423725026*t^6*z^2/2187 - 4276267259*t^6*z/10935 + 765862319*t^6/3645 - 3392533102*t^5*z^2/32805 - 3718283198*t^5*z/32805 + 669479497*t^5/10935 + 785045846*t^4*z^2/32805 + 22933517959*t^4*z/32805 - 1457846728*t^4/3645 - 10436236924*t^3*z^2/32805 - 3805868411*t^3*z/32805 + 1724921501*t^3/10935 + 3645802820*t^2*z^2/6561 - 21722763187*t^2*z/32805 + 2440873244*t^2/10935 - 9869931779*t*z^2/32805 + 2301184210*t*z/6561 - 130577849*t/1215 + 289632026*z^2/6561 + 102893816*z/32805 - 249708953/10935)*hf
  norm_num at hh

private lemma cell_5_40 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 8*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-z^3/2 + 7*z^2/2 - 13*z/2 + 5/2)*h0 + (z - 4)*hf
  norm_num at hh

private lemma cell_5_41 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z^2 + 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^2/2 - 5*z/2 + 2)*h0 + (1)*hf
  norm_num at hh

private lemma cell_5_42 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 6*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-27*z^3/58 + 90*z^2/29 - 159*z/29 + 55/29)*h0 + (-81/29)*hf
  norm_num at hh

private lemma cell_5_43 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z^3 - 384*z^2 + 320*z - 48) + t^6*(-480*z^3 + 3776*z^2 - 2896*z + 288) + t^5*(-608*z^3 - 14832*z^2 + 12768*z - 1744) + t^4*(33216*z^3 - 29152*z^2 + 5072*z - 16) + t^3*(-230112*z^3 + 513216*z^2 - 294848*z + 36800) + t^2*(759408*z^3 - 2024928*z^2 + 1247712*z - 159184) + t*(-1262224*z^3 + 3607056*z^2 - 2275616*z + 292176) + 849696*z^3 - 2507072*z^2 + 1597888*z - 205728:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-421*z^3/29646 + 1702*z^2/14823 - 8699*z/29646 + 89/366) + t^6*(-361*z^3/14823 + 3040*z^2/14823 - 5131*z/9882 + 10307/29646) + t^5*(-566*z^3/4941 + 2047*z^2/4941 + 4561*z/9882 - 415/366) + t^4*(17300*z^3/14823 - 197605*z^2/29646 + 85519*z/9882 - 44147/14823) + t^3*(-24022*z^3/14823 + 113192*z^2/14823 - 117817*z/29646 + 4684/4941) + t^2*(10153*z^3/4941 - 44401*z^2/4941 - 1184*z/1647 + 11426/4941) + t*(-96875*z^3/29646 + 566155*z^2/29646 - 578491*z/29646 + 4721/1098) + 13937*z^3/29646 - 100403*z^2/29646 + 16651*z/9882 + 15781/29646)*h0 + (t*(421*z^3/237168 - 851*z^2/59292 + 8699*z/237168 - 89/2928) + 1483*z^3/118584 - 9493*z^2/118584 + 10075*z/79056 - 6071/237168)*h1 + (-1684*t^8*z^2/14823 + 11932*t^8*z/14823 - 6218*t^8/4941 + 766*t^7*z^2/14823 - 48565*t^7*z/14823 + 148262*t^7/14823 + 104978*t^6*z^2/14823 - 273073*t^6*z/14823 - 632131*t^6/14823 - 761288*t^5*z^2/14823 + 4536160*t^5*z/14823 - 250577*t^5/4941 - 34198*t^4*z^2/4941 - 18394094*t^4*z/14823 + 16622471*t^4/14823 + 7558363*t^3*z^2/4941 + 5424569*t^3*z/14823 - 948296*t^3/243 - 107562989*t^2*z^2/14823 + 160052888*t^2*z/14823 + 7920700*t^2/1647 + 211627148*t*z^2/14823 - 438217493*t*z/14823 + 18057523*t/14823 - 52504132*z^2/4941 + 370418279*z/14823 - 78061876/14823)*hf
  norm_num at hh

private lemma cell_5_44 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z^3 + 768*z^2 - 1152*z + 80) + t^6*(1584*z^3 - 9312*z^2 + 13824*z - 1888) + t^5*(-8896*z^3 + 49776*z^2 - 71568*z + 10576) + t^4*(30624*z^3 - 152928*z^2 + 202320*z - 30224) + t^3*(-79616*z^3 + 324240*z^2 - 350976*z + 51248) + t^2*(187056*z^3 - 622512*z^2 + 492624*z - 67552) + t*(-346192*z^3 + 1064112*z^2 - 702288*z + 91504) + 390240*z^3 - 1185888*z^2 + 759312*z - 97904:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(10861*z^3/150660 - 110957*z^2/225990 + 103892*z/112995 - 94177/225990) + t^6*(-181513*z^3/451980 + 413303*z^2/150660 - 2337793*z/451980 + 1081799/451980) + t^5*(3709*z^3/5022 - 51377*z^2/10044 + 50009*z/5022 - 50893/10044) + t^4*(-38651*z^3/90396 + 500539*z^2/150660 - 907918*z/112995 + 1415599/225990) + t^3*(-153733*z^3/150660 + 134210*z^2/22599 - 1509181*z/225990 - 1509991/451980) + t^2*(121721*z^3/50220 - 84881*z^2/5580 + 286693*z/12555 - 118777/50220) + t*(-53861*z^3/30132 + 5142007*z^2/451980 - 4036681*z/225990 + 381542/112995) + 302887*z^3/451980 - 667031*z^2/150660 + 869566*z/112995 - 1288529/451980)*h0 + (t*(-10861*z^3/1205280 + 110957*z^2/1807920 - 25973*z/225990 + 94177/1807920) + 63361*z^3/3615840 - 47789*z^2/401760 + 801439*z/3615840 - 18115/180792)*h1 + (-43444*t^8*z^2/37665 + 757324*t^8*z/112995 - 2037977*t^8/225990 + 746521*t^7*z^2/45198 - 10659638*t^7*z/112995 + 3186601*t^7/25110 - 8129629*t^6*z^2/75330 + 66832651*t^6*z/112995 - 175746761*t^6/225990 + 48796289*t^5*z^2/112995 - 489609701*t^5*z/225990 + 302371789*t^5/112995 - 47234327*t^4*z^2/37665 + 201617972*t^4*z/37665 - 430821583*t^4/75330 + 696212189*t^3*z^2/225990 - 1206175037*t^3*z/112995 + 390704665*t^3/45198 - 240958637*t^2*z^2/37665 + 2170344887*t^2*z/112995 - 1300708634*t^2/112995 + 2165641327*t*z^2/225990 - 3093608707*t*z/112995 + 35782540*t/2511 - 17170831*z^2/2511 + 4368427571*z/225990 - 2215399181/225990)*hf
  norm_num at hh

private lemma cell_5_45 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^3 + 12*z^2 - 20*z) + 2*z^3 - 12*z^2 + 20*z - 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-192*z^3 + 1152*z^2 - 1728*z + 208) + t^6*(2784*z^3 - 16704*z^2 + 25200*z - 3872) + t^5*(-20736*z^3 + 123120*z^2 - 183888*z + 28336) + t^4*(94128*z^3 - 551232*z^2 + 815760*z - 125120) + t^3*(-272112*z^3 + 1560384*z^2 - 2277648*z + 348592) + t^2*(490752*z^3 - 2726352*z^2 + 3898656*z - 595136) + t*(-511680*z^3 + 2708352*z^2 - 3743856*z + 569008) + 240384*z^3 - 1184256*z^2 + 1549152*z - 233696:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(16721*z^3/3645 - 228323*z^2/7290 + 214387*z/3645 - 64493/2430) + t^6*(-20009*z^3/1458 + 68321*z^2/729 - 256741*z/1458 + 38681/486) + t^5*(-4109*z^3/486 + 27913*z^2/486 - 51823*z/486 + 7525/162) + t^4*(22870*z^3/729 - 154916*z^2/729 + 285680*z/729 - 81115/486) + t^3*(-48857*z^3/3645 + 312328*z^2/3645 - 991493*z/7290 + 65461/2430) + t^2*(63439*z^3/2430 - 202438*z^2/1215 + 639203*z/2430 - 40091/810) + t*(-16748*z^3/729 + 105310*z^2/729 - 318119*z/1458 + 12137/486) + 64811*z^3/7290 - 405499*z^2/7290 + 300626*z/3645 - 15749/2430)*h0 + (t*(-16721*z^3/29160 + 228323*z^2/58320 - 214387*z/29160 + 64493/19440) + 32527*z^3/58320 - 222083*z^2/58320 + 208537*z/29160 - 20911/6480)*h1 + (-367862*t^8*z^2/3645 + 2143691*t^8*z/3645 - 323027*t^8/405 + 1215149*t^7*z^2/729 - 7081184*t^7*z/729 + 16245467*t^7/1215 - 9792424*t^6*z^2/729 + 282613613*t^6*z/3645 - 128799509*t^6/1215 + 239184613*t^5*z^2/3645 - 272580080*t^5*z/729 + 205160939*t^5/405 - 760430849*t^4*z^2/3645 + 4252737719*t^4*z/3645 - 1895966353*t^4/1215 + 1579207744*t^3*z^2/3645 - 8599781521*t^3*z/3645 + 753130055*t^3/243 - 2067501101*t^2*z^2/3645 + 10848703562*t^2*z/3645 - 514120639*t^2/135 + 1542878359*t*z^2/3645 - 1543279268*t*z/729 + 3173019122*t/1215 - 488750459*z^2/3645 + 2323634576*z/3645 - 916292732/1215)*hf
  norm_num at hh

private lemma cell_5_46 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z^3 + 768*z^2 - 1216*z + 144) + t^6*(1584*z^3 - 8896*z^2 + 13136*z - 2064) + t^5*(-8960*z^3 + 45648*z^2 - 61680*z + 9488) + t^4*(30672*z^3 - 134800*z^2 + 158336*z - 23488) + t^3*(-72672*z^3 + 265296*z^2 - 246416*z + 34976) + t^2*(123360*z^3 - 391824*z^2 + 280176*z - 37360) + t*(-130336*z^3 + 392832*z^2 - 246128*z + 31488) + 60960*z^3 - 182624*z^2 + 112480*z - 14304:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(347*z^3/7533 - 2497*z^2/7533 + 10091*z/15066 - 1577/5022) + t^6*(-533*z^3/7533 + 5039*z^2/7533 - 4477*z/2511 + 14527/15066) + t^5*(-1093*z^3/1674 + 3163*z^2/837 - 8515*z/1674 + 793/558) + t^4*(25661*z^3/15066 - 162911*z^2/15066 + 43798*z/2511 - 40195/7533) + t^3*(-12997*z^3/15066 + 46873*z^2/7533 - 169157*z/15066 + 778/837) + t^2*(95*z^3/837 - 58*z^2/31 + 8303*z/1674 + 1087/837) + t*(-4919*z^3/7533 + 72845*z^2/15066 - 68662*z/7533 + 7309/2511) - 4613*z^3/15066 + 31169*z^2/15066 - 20695*z/5022 + 20807/15066)*h0 + (t*(-347*z^3/60264 + 2497*z^2/60264 - 10091*z/120528 + 1577/40176) + 443*z^3/60264 - 917*z^2/15066 + 2887*z/20088 - 8569/120528)*h1 + (-5552*t^8*z^2/7533 + 34400*t^8*z/7533 - 17756*t^8/2511 + 75794*t^7*z^2/7533 - 451622*t^7*z/7533 + 685267*t^7/7533 - 476354*t^6*z^2/7533 + 2662090*t^6*z/7533 - 3823610*t^6/7533 + 1826558*t^5*z^2/7533 - 9260623*t^5*z/7533 + 3970240*t^5/2511 - 1616870*t^4*z^2/2511 + 21737693*t^4*z/7533 - 22846430*t^4/7533 + 3124984*t^3*z^2/2511 - 37872323*t^3*z/7533 + 29740427*t^3/7533 - 12484384*t^2*z^2/7533 + 48585628*t^2*z/7533 - 9771914*t^2/2511 + 9861496*t*z^2/7533 - 39420274*t*z/7533 + 21070259*t/7533 - 1125220*z^2/2511 + 14437957*z/7533 - 7673960/7533)*hf
  norm_num at hh

private lemma cell_5_47 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 2*z^2 - 2*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z^3 + 384*z^2 - 768*z + 144) + t^6*(704*z^3 - 2592*z^2 + 4224*z - 752) + t^5*(-8576*z^3 + 23952*z^2 - 20592*z + 2800) + t^4*(71568*z^3 - 204384*z^2 + 135648*z - 17536) + t^3*(-351728*z^3 + 1038528*z^2 - 663936*z + 85632) + t^2*(1006576*z^3 - 3024240*z^2 + 1932768*z - 249088) + t*(-1562608*z^3 + 4732032*z^2 - 3033696*z + 391184) + 1018800*z^3 - 3095424*z^2 + 1988448*z - 256544:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(6329*z^3/2430 - 43211*z^2/2430 + 9017*z/270 - 18319/1215) + t^6*(1183*z^3/243 - 2692*z^2/81 + 15154*z/243 - 13609/486) + t^5*(-1093*z^3/81 + 830*z^2/9 - 14032*z/81 + 6284/81) + t^4*(-41*z^3/2 + 33799*z^2/243 - 63056*z/243 + 57385/486) + t^3*(50447*z^3/2430 - 168109*z^2/1215 + 204563*z/810 - 276839/2430) + t^2*(6544*z^3/405 - 95327*z^2/810 + 31891*z/135 - 88691/810) + t*(-1273*z^3/243 + 10895*z^2/243 - 24530*z/243 + 8113/162) - 1151*z^3/810 + 5696*z^2/1215 - 1901*z/2430 - 2792/1215)*h0 + (t*(-6329*z^3/19440 + 43211*z^2/19440 - 9017*z/2160 + 18319/9720) + 11969*z^3/19440 - 9079*z^2/2160 + 153443*z/19440 - 69283/19440)*h1 + (-25316*t^8*z^2/1215 + 5464*t^8*z/45 - 53138*t^8/243 + 108784*t^7*z^2/405 - 15587*t^7*z/15 + 2057561*t^7/1215 - 783796*t^6*z^2/243 + 10725181*t^6*z/1215 - 9509791*t^6/1215 + 34725001*t^5*z^2/1215 - 92736341*t^5*z/1215 + 5882438*t^5/135 - 192667744*t^4*z^2/1215 + 58941229*t^4*z/135 - 272595274*t^4/1215 + 220426082*t^3*z^2/405 - 1858962646*t^3*z/1215 + 940805998*t^3/1215 - 1371090886*t^2*z^2/1215 + 3897096091*t^2*z/1215 - 1973845159*t^2/1215 + 1571927522*t*z^2/1215 - 1497461926*t*z/405 + 2281220896*t/1215 - 16936135*z^2/27 + 727879823*z/405 - 1110876823/1215)*hf
  norm_num at hh

private lemma cell_5_48 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z^3 - 384*z^2 + 640*z - 368) + t^6*(-480*z^3 + 3168*z^2 - 5664*z + 2640) + t^5*(1632*z^3 - 11040*z^2 + 20256*z - 8928) + t^4*(-2880*z^3 + 19584*z^2 - 36432*z + 15840) + t^3*(2592*z^3 - 18000*z^2 + 34272*z - 14832) + t^2*(-1296*z^3 + 8640*z^2 - 16416*z + 6912) + t*(432*z^3 - 2160*z^2 + 3456*z - 1296):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(z^3/18 - 32*z^2/81 + 64*z/81 - 31/81) + t^5*(-8*z^3/9 + 166*z^2/27 - 106*z/9 + 146/27) + t^4*(83*z^3/18 - 853*z^2/27 + 1610*z/27 - 728/27) + t^3*(-191*z^3/18 + 652*z^2/9 - 136*z + 551/9) + t^2*(35*z^3/3 - 715*z^2/9 + 1337*z/9 - 1201/18) + t*(-6*z^3 + 122*z^2/3 - 151*z/2 + 101/3) + 7*z^3/6 - 47*z^2/6 + 43*z/3 - 13/2)*h0 + (-z^3/144 + 4*z^2/81 - 8*z/81 + 31/648)*h1 + (4*t^7*z^2/9 - 220*t^7*z/81 + 364*t^7/81 - 10*t^6*z^2/3 + 604*t^6*z/27 - 1078*t^6/27 + 34*t^5*z^2/3 - 2104*t^5*z/27 + 1286*t^5/9 - 20*t^4*z^2 + 1244*t^4*z/9 - 257*t^4 + 18*t^3*z^2 - 127*t^3*z + 2177*t^3/9 - 9*t^2*z^2 + 61*t^2*z - 347*t^2/3 + 3*t*z^2 - 46*t*z/3 + 24*t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_5_49 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^3 + 12*z^2 - 18*z - 2) + 2*z^3 - 12*z^2 + 18*z - 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 240) + t^6*(144*z^3 - 896*z^2 + 912*z + 1104) + t^5*(-1472*z^3 + 9072*z^2 - 12528*z - 1296) + t^4*(6640*z^3 - 41264*z^2 + 61472*z - 5344) + t^3*(-16768*z^3 + 105744*z^2 - 162128*z + 22688) + t^2*(27392*z^3 - 174576*z^2 + 270480*z - 41456) + t*(-27712*z^3 + 176672*z^2 - 273808*z + 42400) + 15616*z^3 - 98912*z^2 + 152576*z - 23552:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(5*z^3/243 - 11*z^2/81 + 59*z/243 - 26/243) + t^6*(-92*z^3/243 + 623*z^2/243 - 2311*z/486 + 518/243) + t^5*(437*z^3/162 - 2975*z^2/162 + 2780*z/81 - 2501/162) + t^4*(-2129*z^3/243 + 14507*z^2/243 - 54325*z/486 + 4075/81) + t^3*(1046*z^3/81 - 21374*z^2/243 + 80033*z/486 - 35977/486) + t^2*(-1145*z^3/162 + 3904*z^2/81 - 4873*z/54 + 1088/27) + t*(77*z^3/486 - 305*z^2/243 + 574*z/243 - 265/486) + 353*z^3/486 - 1160*z^2/243 + 157*z/18 - 1058/243)*h0 + (t*(-5*z^3/1944 + 11*z^2/648 - 59*z/1944 + 13/972) + 37*z^3/1944 - 251*z^2/1944 + 935*z/3888 - 35/324)*h1 + (10*t^8*z^2/243 - 56*t^8*z/243 + 112*t^8/243 - 104*t^7*z^2/243 + 22*t^7*z/9 - 467*t^7/81 - 91*t^6*z^2/243 + 626*t^6*z/243 + 2275*t^6/243 + 5389*t^5*z^2/243 - 32246*t^5*z/243 + 36272*t^5/243 - 30656*t^4*z^2/243 + 184876*t^4*z/243 - 81709*t^4/81 + 84961*t^3*z^2/243 - 518099*t^3*z/243 + 714164*t^3/243 - 46832*t^2*z^2/81 + 95888*t^2*z/27 - 1204585*t^2/243 + 15356*t*z^2/27 - 848746*t*z/243 + 43969*t/9 - 72577*z^2/243 + 443819*z/243 - 620113/243)*hf
  norm_num at hh

private lemma cell_5_50 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 2*z^2 - 4*z + 2:ℝ)=0) (h2 : (16*t^8 + t^7*(-128*z^3 + 768*z^2 - 1152*z + 80) + t^6*(1584*z^3 - 9504*z^2 + 14208*z - 2080) + t^5*(-7744*z^3 + 46752*z^2 - 70128*z + 11008) + t^4*(18528*z^3 - 113760*z^2 + 172800*z - 26912) + t^3*(-21680*z^3 + 137616*z^2 - 213792*z + 32816) + t^2*(11232*z^3 - 74592*z^2 + 118656*z - 18160) + t*(-1168*z^3 + 8304*z^2 - 13104*z + 2080) - 720*z^3 + 4896*z^2 - 7872*z + 1216:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-31*z^3/1215 + 209*z^2/1215 - 769*z/2430 + 113/810) + t^6*(463*z^3/2430 - 1556*z^2/1215 + 946*z/405 - 1208/1215) + t^5*(-313*z^3/810 + 1036*z^2/405 - 3611*z/810 + 206/135) + t^4*(269*z^3/1215 - 3007*z^2/2430 + 406*z/405 + 2047/1215) + t^3*(-247*z^3/243 + 1490*z^2/243 - 3871*z/486 - 121/81) + t^2*(1097*z^3/405 - 13981*z^2/810 + 7421*z/270 - 5083/810) + t*(-1673*z^3/1215 + 10732*z^2/1215 - 17266*z/1215 + 1322/405) - 296*z^3/1215 + 3763*z^2/2430 - 1054*z/405 + 1457/1215)*h0 + (t*(31*z^3/9720 - 209*z^2/9720 + 769*z/19440 - 113/6480) - 193*z^3/19440 + 1297*z^2/19440 - 11*z/90 + 1051/19440)*h2 + (496*t^8*z^2/1215 - 2848*t^8*z/1215 + 1246*t^8/405 - 7682*t^7*z^2/1215 + 44138*t^7*z/1215 - 58204*t^7/1215 + 9823*t^6*z^2/243 - 94393*t^6*z/405 + 25040*t^6/81 - 165208*t^5*z^2/1215 + 320347*t^5*z/405 - 428392*t^5/405 + 307504*t^4*z^2/1215 - 1821818*t^4*z/1215 + 822322*t^4/405 - 305039*t^3*z^2/1215 + 373421*t^3*z/243 - 2575166*t^3/1215 + 140012*t^2*z^2/1215 - 179890*t^2*z/243 + 421718*t^2/405 - 11299*t*z^2/1215 + 81319*t*z/1215 - 22594*t/243 - 193*z^2/27 + 11444*z/243 - 16315/243)*hf
  norm_num at hh

private lemma cell_5_51 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(128*z^3 - 768*z^2 + 1088*z - 368) + t^6*(-784*z^3 + 4416*z^2 - 5488*z + 1776) + t^5*(2496*z^3 - 13008*z^2 + 13104*z - 4048) + t^4*(-5264*z^3 + 26160*z^2 - 22304*z + 5504) + t^3*(6688*z^3 - 32688*z^2 + 26320*z - 4704) + t^2*(-4416*z^3 + 21552*z^2 - 18000*z + 2416) + t*(1088*z^3 - 5472*z^2 + 5552*z - 608) + 128*z^3 - 384*z^2 - 160*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(43*z^3/243 - 589*z^2/486 + 1117*z/486 - 175/162) + t^6*(-1189*z^3/486 + 4036*z^2/243 - 7507*z/243 + 371/27) + t^5*(1799*z^3/162 - 2033*z^2/27 + 22661*z/162 - 10123/162) + t^4*(-11291*z^3/486 + 38210*z^2/243 - 70913*z/243 + 21371/162) + t^3*(5672*z^3/243 - 38107*z^2/243 + 139943*z/486 - 10532/81) + t^2*(-1423*z^3/162 + 1543*z^2/27 - 8033*z/81 + 6797/162) + t*(-275*z^3/243 + 4487*z^2/486 - 10913*z/486 + 253/18) + 232*z^3/243 - 1643*z^2/243 + 3377*z/243 - 1321/162)*h0 + (t*(-43*z^3/1944 + 589*z^2/3888 - 1117*z/3888 + 175/1296) + 319*z^3/3888 - 2189*z^2/3888 + 4163*z/3888 - 653/1296)*h1 + (688*t^8*z^2/243 - 4024*t^8*z/243 + 584*t^8/27 - 6766*t^7*z^2/243 + 38059*t^7*z/243 - 15242*t^7/81 + 29047*t^6*z^2/243 - 153778*t^6*z/243 + 52669*t^6/81 - 78058*t^5*z^2/243 + 388816*t^5*z/243 - 12082*t^5/9 + 140899*t^4*z^2/243 - 677353*t^4*z/243 + 163658*t^4/81 - 157078*t^3*z^2/243 + 745579*t^3*z/243 - 172432*t^3/81 + 93892*t^2*z^2/243 - 446077*t^2*z/243 + 36295*t^2/27 - 21004*t*z^2/243 + 104146*t*z/243 - 32375*t/81 - 2552*z^2/243 + 7304*z/243 + 1402/81)*hf
  norm_num at hh

private lemma cell_5_52 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^3 + 12*z^2 - 18*z - 2) + 2*z^3 - 12*z^2 + 18*z - 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 240) + t^6*(-48*z^3 + 448*z^2 - 1392*z + 1488) + t^5*(688*z^3 - 4896*z^2 + 9936*z - 5040) + t^4*(-2288*z^3 + 15328*z^2 - 27232*z + 9344) + t^3*(2192*z^3 - 14352*z^2 + 24400*z - 7648) + t^2*(320*z^3 - 2208*z^2 + 3216*z + 736) + t*(-208*z^3 + 992*z^2 - 1360*z + 208) + 64*z^3 - 80*z^2 - 112*z - 32:ℝ)=0) (h2 : (16*t^8 + t^7*(-192*z^3 + 1152*z^2 - 1664*z + 144) + t^6*(2784*z^3 - 17120*z^2 + 25824*z - 3696) + t^5*(-19904*z^3 + 123408*z^2 - 188496*z + 28656) + t^4*(84112*z^3 - 521504*z^2 + 797312*z - 122464) + t^3*(-215344*z^3 + 1329312*z^2 - 2026880*z + 311840) + t^2*(326768*z^3 - 1996176*z^2 + 3025344*z - 465248) + t*(-271408*z^3 + 1620992*z^2 - 2424736*z + 372304) + 98896*z^3 - 557792*z^2 + 805280*z - 123104:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(7*z^3/729 - 341*z^2/6561 + 397*z/6561 - 269/13122) + t^12*(-397*z^3/6561 + 2519*z^2/6561 - 8473*z/13122 + 71/243) + t^11*(245*z^3/2187 - 266*z^2/243 + 6626*z/2187 - 7829/4374) + t^10*(-1244*z^3/6561 + 30313*z^2/13122 - 5611*z/729 + 39590/6561) + t^9*(745*z^3/4374 - 6337*z^2/6561 + 52957*z/13122 - 149539/13122) + t^8*(5153*z^3/1458 - 34747*z^2/1458 + 53131*z/1458 + 2428/243) + t^7*(-21799*z^3/2187 + 41747*z^2/729 - 304157*z/4374 - 17471/4374) + t^6*(-33943*z^3/4374 + 132962*z^2/2187 - 91679*z/729 + 115861/4374) + t^5*(27755*z^3/486 - 262190*z^2/729 + 400960*z/729 - 121079/1458) + t^4*(-883019*z^3/13122 + 2704694*z^2/6561 - 3941453*z/6561 + 199798/2187) + t^3*(81905*z^3/6561 - 54143*z^2/729 + 1379485*z/13122 - 346967/13122) + t^2*(55475*z^3/4374 - 160729*z^2/2187 + 134387*z/1458 + 859/4374) + t*(3130*z^3/243 - 579058*z^2/6561 + 1016948*z/6561 - 191861/6561) - 175411*z^3/13122 + 567067*z^2/6561 - 905482*z/6561 + 1676/81)*h0 + (t^7*(-7*z^3/5832 + 341*z^2/52488 - 397*z/52488 + 269/104976) + t^6*(-z^3/104976 - 35*z^2/13122 + 85*z/6561 - 13/1458) + t^5*(79*z^3/5832 - 2455*z^2/34992 + 2291*z/34992 + 5/17496) + t^4*(-1559*z^3/52488 + 10307*z^2/52488 - 11267*z/34992 + 4153/104976) + t^3*(343*z^3/3888 - 4016*z^2/6561 + 113791*z/104976 - 8963/52488) + t^2*(-3713*z^3/17496 + 47077*z^2/34992 - 12139*z/5832 + 5573/17496) + t*(12221*z^3/52488 - 4139*z^2/2916 + 215707*z/104976 - 34721/104976) - 8101*z^3/104976 + 24041*z^2/52488 - 21733*z/34992 + 7009/104976)*h1 + (13*z^3/1296 - 4*z^2/81 + 13*z/324 - 1/144)*h2 + (14*t^14*z^2/729 - 556*t^14*z/6561 + 868*t^14/6561 - 1298*t^13*z^2/6561 + 2576*t^13*z/2187 - 12035*t^13/6561 + 7679*t^12*z^2/6561 - 47927*t^12*z/6561 + 69247*t^12/6561 - 1963*t^11*z^2/729 + 112813*t^11*z/6561 - 169273*t^11/6561 - 48658*t^10*z^2/6561 + 27056*t^10*z/729 - 205372*t^10/6561 + 45778*t^9*z^2/729 - 2382509*t^9*z/6561 + 3068288*t^9/6561 - 142726*t^8*z^2/729 + 8021333*t^8*z/6561 - 11923856*t^8/6561 + 2796421*t^7*z^2/6561 - 6018980*t^7*z/2187 + 27723844*t^7/6561 - 4780978*t^6*z^2/6561 + 29818090*t^6*z/6561 - 41987987*t^6/6561 + 2113907*t^5*z^2/2187 - 3977317*t^5*z/729 + 13666871*t^5/2187 - 2805788*t^4*z^2/2187 + 4395028*t^4*z/729 - 2968580*t^4/729 + 14469281*t^3*z^2/6561 - 59957512*t^3*z/6561 + 2080496*t^3/729 - 2325994*t^2*z^2/729 + 28096961*t^2*z/2187 - 2406076*t^2/729 + 5771509*t*z^2/2187 - 7467961*t*z/729 + 5563444*t/2187 - 6300778*z^2/6561 + 2469679*z/729 - 5316835/6561)*hf
  norm_num at hh

private lemma cell_5_53 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z^3 + 24*z^2 - 36*z + 2) + 2*z^3 - 12*z^2 + 18*z - 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z^3 + 384*z^2 - 512*z - 112) + t^6*(704*z^3 - 4384*z^2 + 6336*z - 176) + t^5*(-3328*z^3 + 21072*z^2 - 31824*z + 3504) + t^4*(8432*z^3 - 53344*z^2 + 81952*z - 11872) + t^3*(-11568*z^3 + 72480*z^2 - 111488*z + 17568) + t^2*(7280*z^3 - 45552*z^2 + 70080*z - 11168) + t*(-464*z^3 + 3680*z^2 - 6400*z + 1072) - 976*z^3 + 5792*z^2 - 8576*z + 1312:ℝ)=0) : (t - 2*z^3 + 13*z^2 - 21*z + 3:ℝ)=0 := by
  have hh : (t - 2*z^3 + 13*z^2 - 21*z + 3:ℝ)=0 := by linear_combination (t^6*(z^3/162 - 8*z^2/81 + 19*z/54 - 37/162) + t^5*(-2*z^3/9 + 46*z^2/27 - 104*z/27 + 7/3) + t^4*(5*z^3/9 - 37*z^2/9 + 251*z/27 - 41/6) + t^3*(77*z^3/81 - 152*z^2/27 + 1045*z/162 + 302/81) + t^2*(-31*z^3/9 + 1205*z^2/54 - 655*z/18 + 431/54) + t*(47*z^3/27 - 623*z^2/54 + 1061*z/54 - 134/27) + 47*z^3/162 - 325*z^2/162 + 290*z/81 - 22/27)*h0 + (-z^3/1296 + z^2/81 - 19*z/432 + 37/1296)*h1 + (-2*t^7*z^2/81 + 10*t^7*z/27 - 82*t^7/81 - 29*t^6*z^2/81 - 175*t^6*z/81 + 1099*t^6/81 + 8*t^5*z^2/81 + 599*t^5*z/27 - 7222*t^5/81 + 745*t^4*z^2/81 - 9017*t^4*z/81 + 8150*t^4/27 - 1993*t^3*z^2/81 + 17909*t^3*z/81 - 40511*t^3/81 + 1577*t^2*z^2/81 - 4391*t^2*z/27 + 28055*t^2/81 - 217*t*z^2/81 + 1522*t*z/81 - 3070*t/81 - 4*z^2/3 + 1189*z/81 - 2923/81)*hf
  exact hh

private lemma cell_5_54 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^3 + 12*z^2 - 20*z) + 2*z^3 - 12*z^2 + 20*z - 2:ℝ)=0) (h1 : (16*t^8 - 176*t^7 + t^6*(-48*z^3 + 288*z^2 - 480*z + 736) + t^5*(432*z^3 - 2592*z^2 + 4320*z - 1616) + t^4*(-1008*z^3 + 6192*z^2 - 10512*z + 1792) + t^3*(-192*z^3 + 144*z^2 + 1104*z + 400) + t^2*(1728*z^3 - 9072*z^2 + 13392*z - 2288) + t*(576*z^3 - 2304*z^2 + 2304*z - 320) - 192*z^3 + 864*z^2 - 1056*z + 160:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-229*z^3/1215 + 517*z^2/405 - 2878*z/1215 + 2581/2430) + t^6*(4817*z^3/2430 - 10891*z^2/810 + 30382*z/1215 - 27289/2430) + t^5*(-5519*z^3/810 + 18778*z^2/405 - 11698*z/135 + 31613/810) + t^4*(9338*z^3/1215 - 42743*z^2/810 + 121406*z/1215 - 55021/1215) + t^3*(2614*z^3/1215 - 11429*z^2/810 + 30298*z/1215 - 13433/1215) + t^2*(-4867*z^3/810 + 16754*z^2/405 - 10619*z/135 + 28939/810) + t*(-139*z^3/486 + 49*z^2/27 - 1495*z/486 + 370/243) - 379*z^3/2430 + 31*z^2/30 - 2279*z/1215 + 2423/2430)*h0 + (t*(229*z^3/9720 - 517*z^2/3240 + 1439*z/4860 - 2581/19440) - 259*z^3/9720 + 1169*z^2/6480 - 3253*z/9720 + 1463/9720)*h1 + (-458*t^8*z^2/1215 + 2644*t^8*z/1215 - 4028*t^8/1215 + 6649*t^7*z^2/1215 - 38432*t^7*z/1215 + 58654*t^7/1215 - 35294*t^6*z^2/1215 + 204322*t^6*z/1215 - 312524*t^6/1215 + 78073*t^5*z^2/1215 - 457061*t^5*z/1215 + 706303*t^5/1215 - 40586*t^4*z^2/1215 + 270589*t^4*z/1215 - 460046*t^4/1215 - 75509*t^3*z^2/1215 + 73334*t^3*z/243 - 472799*t^3/1215 + 53362*t^2*z^2/1215 - 300854*t^2*z/1215 + 451192*t^2/1215 + 4892*t*z^2/243 - 19075*t*z/243 + 17606*t/243 - 5837*z^2/1215 + 24412*z/1215 - 25622/1215)*hf
  norm_num at hh

private lemma cell_5_55 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z^3 + 24*z^2 - 36*z) + 4*z^3 - 24*z^2 + 36*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 112) + t^6*(-48*z^3 + 448*z^2 - 208*z + 304) + t^5*(176*z^3 - 2784*z^2 + 3696*z - 688) + t^4*(944*z^3 + 1600*z^2 - 6144*z + 768) + t^3*(-5264*z^3 + 16176*z^2 - 11344*z + 1760) + t^2*(7552*z^3 - 27936*z^2 + 25200*z - 3616) + t*(-2960*z^3 + 8480*z^2 - 3568*z + 368) + 320*z^3 - 752*z^2 - 48*z + 32:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(17*z^3/9 - 2095*z^2/162 + 1975*z/81 - 595/54) + t^6*(-1118*z^3/81 + 7678*z^2/81 - 4847*z/27 + 1463/18) + t^5*(4469*z^3/162 - 5171*z^2/27 + 29833*z/81 - 13595/81) + t^4*(-415*z^3/162 + 2081*z^2/81 - 11431*z/162 + 5869/162) + t^3*(-2840*z^3/81 + 37379*z^2/162 - 33215*z/81 + 14611/81) + t^2*(3343*z^3/162 - 22831*z^2/162 + 4781*z/18 - 19459/162) + t*(226*z^3/81 - 364*z^2/27 + 253*z/27 - 82/81) - 185*z^3/81 + 27*z^2/2 - 527*z/27 + 70/9)*h0 + (t*(-17*z^3/72 + 2095*z^2/1296 - 1975*z/648 + 595/432) + 47*z^3/81 - 5147*z^2/1296 + 2425*z/324 - 2191/648)*h1 + (68*t^8*z^2/9 - 3578*t^8*z/81 + 3710*t^8/81 - 6002*t^7*z^2/81 + 38245*t^7*z/81 - 40969*t^7/81 + 6344*t^6*z^2/27 - 152786*t^6*z/81 + 180478*t^6/81 + 14*t^5*z^2/81 + 24838*t^5*z/9 - 119236*t^5/27 - 155572*t^4*z^2/81 + 267704*t^4*z/81 + 15061*t^4/27 + 409886*t^3*z^2/81 - 445415*t^3*z/27 + 944038*t^3/81 - 139112*t^2*z^2/27 + 482255*t^2*z/27 - 1071565*t^2/81 + 143596*t*z^2/81 - 127753*t*z/27 + 32296*t/27 - 14300*z^2/81 + 9790*z/27 + 11365/81)*hf
  norm_num at hh

private lemma cell_5_56 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z^3 - 384*z^2 + 576*z - 304) + t^6*(-480*z^3 + 2880*z^2 - 4176*z + 1760) + t^5*(1760*z^3 - 10128*z^2 + 13392*z - 4976) + t^4*(-3888*z^3 + 21600*z^2 - 24912*z + 7936) + t^3*(6448*z^3 - 33792*z^2 + 32400*z - 7888) + t^2*(-6912*z^3 + 36432*z^2 - 30528*z + 5312) + t*(5408*z^3 - 27552*z^2 + 21168*z - 2864) - 960*z^3 + 7200*z^2 - 6336*z + 832:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(7*z^3/243 - 241*z^2/1215 + 461*z/1215 - 73/405) + t^6*(-1657*z^3/2430 + 1889*z^2/405 - 4273*z/486 + 9733/2430) + t^5*(2101*z^3/405 - 28709*z^2/810 + 5398*z/81 - 452/15) + t^4*(-8513*z^3/486 + 48461*z^2/405 - 546461*z/2430 + 246649/2430) + t^3*(34666*z^3/1215 - 47374*z^2/243 + 445303*z/1215 - 133919/810) + t^2*(-17281*z^3/810 + 2627*z^2/18 - 222553*z/810 + 33427/270) + t*(2107*z^3/486 - 36368*z^2/1215 + 69283*z/1215 - 10334/405) + 701*z^3/486 - 7789*z^2/810 + 42617*z/2430 - 19813/2430)*h0 + (t*(-7*z^3/1944 + 241*z^2/9720 - 461*z/9720 + 73/3240) + 53*z^3/1296 - 2719*z^2/9720 + 10253*z/19440 - 1559/6480)*h1 + (56*t^8*z^2/243 - 1648*t^8*z/1215 + 478*t^8/243 - 352*t^7*z^2/81 + 30862*t^7*z/1215 - 8783*t^7/243 + 6310*t^6*z^2/243 - 181063*t^6*z/1215 + 247858*t^6/1215 - 6964*t^5*z^2/81 + 113843*t^5*z/243 - 703516*t^5/1215 + 44279*t^4*z^2/243 - 25432*t^4*z/27 + 236944*t^4/243 - 23375*t^3*z^2/81 + 571487*t^3*z/405 - 30794*t^3/27 + 73420*t^2*z^2/243 - 1821344*t^2*z/1215 + 1226128*t^2/1215 - 18194*t*z^2/81 + 1346549*t*z/1215 - 837581*t/1215 + 1060*z^2/27 - 70727*z/243 + 264232/1215)*hf
  norm_num at hh

private lemma cell_5_57 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^3 + 12*z^2 - 20*z) + 2*z^3 - 12*z^2 + 20*z - 2:ℝ)=0) (h1 : (16*t^8 - 176*t^7 + t^6*(144*z^3 - 1056*z^2 + 2016*z + 352) + t^5*(-1152*z^3 + 8496*z^2 - 16272*z + 1552) + t^4*(4896*z^3 - 36000*z^2 + 68400*z - 10448) + t^3*(-12672*z^3 + 92688*z^2 - 174528*z + 27952) + t^2*(24912*z^3 - 179568*z^2 + 332496*z - 52544) + t*(-30384*z^3 + 216144*z^2 - 394992*z + 62032) + 25920*z^3 - 181056*z^2 + 324144*z - 50768:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-189563*z^3/422820 + 258845*z^2/84564 - 1215137*z/211410 + 91369/35235) + t^6*(998683*z^3/211410 - 13636789*z^2/422820 + 6401713*z/105705 - 1925437/70470) + t^5*(-2333377*z^3/140940 + 7965361*z^2/70470 - 29914073*z/140940 + 899743/9396) + t^4*(8675377*z^3/422820 - 14806622*z^2/105705 + 111207179*z/422820 - 4181537/35235) + t^3*(96326*z^3/105705 - 1323017*z^2/211410 + 2497733*z/211410 - 148459/28188) + t^2*(-945571*z^3/70470 + 12924403*z^2/140940 - 24290659*z/140940 + 3645943/46980) + t*(662623*z^3/422820 - 2287597*z^2/211410 + 8676443*z/422820 - 634669/70470) - 57497*z^3/211410 + 824351*z^2/422820 - 1626323*z/422820 + 203761/140940)*h0 + (t*(189563*z^3/3382560 - 258845*z^2/676512 + 1215137*z/1691280 - 91369/281880) - 206789*z^3/3382560 + 1412197*z^2/3382560 - 663031*z/845640 + 99721/281880)*h1 + (-189563*t^8*z^2/211410 + 552331*t^8*z/105705 - 284123*t^8/35235 + 240431*t^7*z^2/105705 - 527371*t^7*z/211410 - 702473*t^7/70470 + 651214*t^6*z^2/21141 - 59201083*t^6*z/211410 + 6591833*t^6/11745 - 28609789*t^5*z^2/105705 + 86484799*t^5*z/42282 - 131554568*t^5/35235 + 205121257*t^4*z^2/211410 - 147840250*t^4*z/21141 + 871293847*t^4/70470 - 464985209*t^3*z^2/211410 + 656367547*t^3*z/42282 - 632182163*t^3/23490 + 688286659*t^2*z^2/211410 - 2400740801*t^2*z/105705 + 1368809788*t^2/35235 - 350280994*t*z^2/105705 + 4823145443*t*z/211410 - 1353698977*t/35235 + 167556587*z^2/105705 - 2283505561*z/211410 + 421977721/23490)*hf
  norm_num at hh

private lemma cell_5_58 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z^3 - 384*z^2 + 512*z - 240) + t^6*(-480*z^3 + 2720*z^2 - 3136*z + 1008) + t^5*(1696*z^3 - 8784*z^2 + 8016*z - 1744) + t^4*(-3792*z^3 + 17984*z^2 - 13024*z + 1568) + t^3*(5136*z^3 - 23520*z^2 + 15904*z - 1504) + t^2*(-3216*z^3 + 15408*z^2 - 11136*z + 1376) + t*(368*z^3 - 2304*z^2 + 1696*z - 240) + 240*z^3 - 992*z^2 + 736*z - 96:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-z^3/162 + z^2/18 - 13*z/81 + 4/27) + t^6*(25*z^3/162 - 185*z^2/162 + 5*z/2 - 128/81) + t^5*(-70*z^3/81 + 487*z^2/81 - 209*z/18 + 436/81) + t^4*(88*z^3/81 - 15*z^2/2 + 2249*z/162 - 785/162) + t^3*(61*z^3/162 - 61*z^2/27 + 323*z/81 - 314/81) + t^2*(-53*z^3/81 + 313*z^2/81 - 965*z/162 + 205/54) + t*(-43*z^3/54 + 458*z^2/81 - 1729*z/162 + 523/162) - 17*z^3/54 + 56*z^2/27 - 583*z/162 + 205/162)*h0 + (t*(z^3/1296 - z^2/144 + 13*z/648 - 1/54) + 17*z^3/1296 - 35*z^2/432 + 151*z/1296 - 1/216)*h1 + (-4*t^8*z^2/81 + 32*t^8*z/81 - 74*t^8/81 - 38*t^7*z^2/81 + 41*t^7*z/27 + 10*t^7/3 + 404*t^6*z^2/81 - 578*t^6*z/27 - 325*t^6/81 - 1565*t^5*z^2/81 + 6391*t^5*z/81 + 223*t^5/27 + 412*t^4*z^2/9 - 4618*t^4*z/27 - 2126*t^4/81 - 584*t^3*z^2/9 + 19070*t^3*z/81 + 740*t^3/27 + 3394*t^2*z^2/81 - 13261*t^2*z/81 - 47*t^2/27 - 406*t*z^2/81 + 2347*t*z/81 - 184*t/27 - 85*z^2/27 + 895*z/81 - 160/81)*hf
  norm_num at hh

private lemma cell_5_59 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 2*z^2 - 2*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(128*z^3 - 768*z^2 + 960*z - 240) + t^6*(-784*z^3 + 4416*z^2 - 3408*z + 592) + t^5*(4672*z^3 - 27024*z^2 + 18864*z - 2384) + t^4*(-17232*z^3 + 106512*z^2 - 78336*z + 10208) + t^3*(34144*z^3 - 237360*z^2 + 178704*z - 23904) + t^2*(-32096*z^3 + 291216*z^2 - 226800*z + 30704) + t*(5216*z^3 - 165696*z^2 + 137040*z - 18784) + 7392*z^3 + 24960*z^2 - 25440*z + 3616:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z^3 + 384*z^2 - 768*z + 144) + t^6*(704*z^3 - 2592*z^2 + 4224*z - 752) + t^5*(-8576*z^3 + 23952*z^2 - 20592*z + 2800) + t^4*(71568*z^3 - 204384*z^2 + 135648*z - 17536) + t^3*(-351728*z^3 + 1038528*z^2 - 663936*z + 85632) + t^2*(1006576*z^3 - 3024240*z^2 + 1932768*z - 249088) + t*(-1562608*z^3 + 4732032*z^2 - 3033696*z + 391184) + 1018800*z^3 - 3095424*z^2 + 1988448*z - 256544:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(294446*z^3/112995 - 7236755*z^2/406782 + 6794390*z/203391 - 30652121/2033910) + t^12*(-9664337*z^3/2033910 + 32989672*z^2/1016955 - 41297491*z/677970 + 55892717/2033910) + t^11*(-23375261*z^3/677970 + 31916969*z^2/135594 - 149829551*z/338985 + 22531288/112995) + t^10*(38478253*z^3/1016955 - 52538275*z^2/203391 + 986517499*z/2033910 - 148351123/677970) + t^9*(95741659*z^3/677970 - 392191519*z^2/406782 + 736461329*z/406782 - 830628062/1016955) + t^8*(-12119444*z^3/112995 + 27584533*z^2/37665 - 155426603*z/112995 + 70126336/112995) + t^7*(-153909553*z^3/677970 + 350158021*z^2/225990 - 197172640*z/67797 + 444681952/338985) + t^6*(92628941*z^3/677970 - 63166891*z^2/67797 + 1184002291*z/677970 - 17790779/22599) + t^5*(26865587*z^3/225990 - 183838823*z^2/225990 + 2139307*z/1395 - 156663839/225990) + t^4*(-80431357*z^3/1016955 + 551214781*z^2/1016955 - 347828248*z/338985 + 473168932/1016955) + t^3*(24063449*z^3/2033910 - 11050285*z^2/135594 + 163135321*z/1016955 - 152483209/2033910) + t^2*(4693837*z^3/225990 - 48566756*z^2/338985 + 90061873*z/338985 - 80500217/677970) + t*(-2593964*z^3/338985 + 110853133*z^2/2033910 - 104111902*z/1016955 + 95465183/2033910) + 23417*z^3/2033910 - 1189441*z^2/1016955 + 630527*z/225990 - 940585/406782)*h0 + (t^7*(-147223*z^3/451980 + 7236755*z^2/3254256 - 3397195*z/813564 + 30652121/16271280) + t^6*(-9804613*z^3/16271280 + 13387391*z^2/3254256 - 13965601*z/1807920 + 7087961/2033910) + t^5*(9064049*z^3/5423760 - 61881029*z^2/5423760 + 2420762*z/112995 - 2621029/271188) + t^4*(41714579*z^3/16271280 - 35598719*z^2/2033910 + 33422764*z/1016955 - 40209017/2711880) + t^3*(-4459237*z^3/1807920 + 273993409*z^2/16271280 - 514492511*z/16271280 + 232109063/16271280) + t^2*(-30019*z^3/12555 + 88534949*z^2/5423760 - 33249065*z/1084752 + 14999903/1084752) + t*(9193111*z^3/8135640 - 41841647*z^2/5423760 + 235704257*z/16271280 - 53168213/8135640) - 571631*z^3/8135640 + 3902773*z^2/8135640 - 2931361*z/3254256 + 440875/1084752)*h1 + (379*z^3/810 - 6901*z^2/2160 + 4321*z/720 - 4391/1620)*h2 + (4711136*t^14*z^2/112995 - 247069976*t^14*z/1016955 + 285881168*t^14/1016955 - 181264468*t^13*z^2/1016955 + 191108867*t^13*z/203391 - 389437046*t^13/1016955 + 849644963*t^12*z^2/1016955 - 4783878779*t^12*z/1016955 + 310348919*t^12/203391 - 19854673*t^11*z^2/10935 + 12970437487*t^11*z/1016955 - 974872633*t^11/112995 - 4824335938*t^10*z^2/1016955 + 18220068353*t^10*z/1016955 - 5771377183*t^10/1016955 + 5148237340*t^9*z^2/203391 - 4715302786*t^9*z/32805 + 86691010373*t^9/1016955 - 7125408727*t^8*z^2/338985 + 189624306992*t^8*z/1016955 - 24696176461*t^8/203391 - 59749257581*t^7*z^2/1016955 + 216920196737*t^7*z/1016955 - 3664396189*t^7/32805 + 117328578382*t^6*z^2/1016955 - 248709137626*t^6*z/338985 + 448421393359*t^6/1016955 + 38015228*t^5*z^2/67797 + 407018993363*t^5*z/1016955 - 92319812858*t^5/338985 - 158753424302*t^4*z^2/1016955 + 115556164781*t^4*z/203391 - 63437090050*t^4/203391 + 237911214326*t^3*z^2/1016955 - 1145133110768*t^3*z/1016955 + 661245618368*t^3/1016955 - 52141882592*t^2*z^2/112995 + 1630276930576*t^2*z/1016955 - 874540768099*t^2/1016955 + 735421065224*t*z^2/1016955 - 2165809083677*t*z/1016955 + 1109970204589*t/1016955 - 161417333852*z^2/338985 + 1391482534762*z/1016955 - 708639619306/1016955)*hf
  norm_num at hh

private lemma cell_5_60 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z^3 + 384*z^2 - 448*z - 176) + t^6*(704*z^3 - 4224*z^2 + 5552*z + 576) + t^5*(-3264*z^3 + 20112*z^2 - 28656*z + 272) + t^4*(8176*z^3 - 51168*z^2 + 75856*z - 5344) + t^3*(-10928*z^3 + 68544*z^2 - 103088*z + 10896) + t^2*(6240*z^3 - 39504*z^2 + 59904*z - 7520) + t*(32*z^3 + 288*z^2 - 592*z + 16) - 832*z^3 + 5376*z^2 - 8416*z + 1248:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(1213*z^3/9882 - 19417*z^2/29646 + 10816*z/14823 - 3481/14823) + t^6*(-1165*z^3/3294 + 39826*z^2/14823 - 86057*z/14823 + 41888/14823) + t^5*(1871*z^3/1098 - 7544*z^2/549 + 1934*z/61 - 52265/3294) + t^4*(-79285*z^3/9882 + 1591705*z^2/29646 - 2914217*z/29646 + 1343699/29646) + t^3*(1669*z^3/122 - 1284577*z^2/14823 + 2151182*z/14823 - 1922923/29646) + t^2*(-3427*z^3/549 + 15895*z^2/366 - 46465*z/549 + 136885/3294) + t*(-26705*z^3/9882 + 305105*z^2/29646 + 48085*z/14823 - 101392/14823) + 2795*z^3/1647 - 125279*z^2/14823 + 110746*z/14823 - 61241/29646)*h0 + (t*(-1213*z^3/79056 + 19417*z^2/237168 - 1352*z/14823 + 3481/118584) + 1139*z^3/19764 - 73025*z^2/237168 + 40817*z/118584 - 13091/118584)*h1 + (-4852*t^8*z^2/4941 + 63112*t^8*z/14823 - 8860*t^8/14823 + 71596*t^7*z^2/4941 - 931660*t^7*z/14823 + 273817*t^7/14823 - 447916*t^6*z^2/4941 + 5950507*t^6*z/14823 - 2484817*t^6/14823 + 1549267*t^5*z^2/4941 - 21102778*t^5*z/14823 + 10538506*t^5/14823 - 3156595*t^4*z^2/4941 + 714571*t^4*z/243 - 23753266*t^4/14823 + 3584818*t^3*z^2/4941 - 49705930*t^3*z/14823 + 28155649*t^3/14823 - 1774414*t^2*z^2/4941 + 24990016*t^2*z/14823 - 14294362*t^2/14823 - 72188*t*z^2/4941 + 10106*t*z/243 - 559034*t/14823 + 236912*z^2/4941 - 3414596*z/14823 + 2118260/14823)*hf
  norm_num at hh

private lemma cell_5_61 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z^3 + 24*z^2 - 36*z) + 4*z^3 - 24*z^2 + 36*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-192*z^3 + 1152*z^2 - 1600*z + 80) + t^6*(2784*z^3 - 17600*z^2 + 26960*z - 3584) + t^5*(-22144*z^3 + 140496*z^2 - 217200*z + 32720) + t^4*(101936*z^3 - 646304*z^2 + 999984*z - 153984) + t^3*(-284336*z^3 + 1801728*z^2 - 2787184*z + 429968) + t^2*(472096*z^3 - 2991312*z^2 + 4626720*z - 713248) + t*(-425984*z^3 + 2700032*z^2 - 4177072*z + 643760) + 159680*z^3 - 1012352*z^2 + 1566432*z - 241408:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(241*z^3/162 - 9889*z^2/972 + 18617*z/972 - 2102/243) + t^6*(-3604*z^3/243 + 98299*z^2/972 - 20473*z/108 + 20764/243) + t^5*(15571*z^3/324 - 106349*z^2/324 + 49952*z/81 - 15023/54) + t^4*(-53245*z^3/972 + 90911*z^2/243 - 682961*z/972 + 102557/324) + t^3*(-1519*z^3/324 + 31475*z^2/972 - 60655*z/972 + 14675/486) + t^2*(12079*z^3/324 - 511*z^2/2 + 39142*z/81 - 18014/81) + t*(-3799*z^3/486 + 1490*z^2/27 - 26672*z/243 + 53599/972) - 1315*z^3/972 + 2171*z^2/243 - 14609*z/972 + 329/81)*h0 + (t*(-241*z^3/1296 + 9889*z^2/7776 - 18617*z/7776 + 1051/972) + 110*z^3/243 - 12035*z^2/3888 + 472*z/81 - 1279/486)*h1 + (-2410*t^8*z^2/81 + 42215*t^8*z/243 - 52316*t^8/243 + 131060*t^7*z^2/243 - 806003*t^7*z/243 + 1119655*t^7/243 - 1245743*t^6*z^2/243 + 2572540*t^6*z/81 - 21919855*t^6/486 + 6942115*t^5*z^2/243 - 28626685*t^5*z/162 + 61098647*t^5/243 - 8004235*t^4*z^2/81 + 98892991*t^4*z/162 - 211031105*t^4/243 + 52650592*t^3*z^2/243 - 325096834*t^3*z/243 + 924745997*t^3/486 - 71223547*t^2*z^2/243 + 439799261*t^2*z/243 - 625488178*t^2/243 + 54080063*t*z^2/243 - 334037339*t*z/243 + 158389357*t/81 - 5854495*z^2/81 + 12056339*z/27 - 154376225/243)*hf
  norm_num at hh

private lemma cell_5_62 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 2*z^2 - 2*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z^3 + 384*z^2 - 576*z - 48) + t^6*(704*z^3 - 4224*z^2 + 6288*z - 608) + t^5*(-2816*z^3 + 17040*z^2 - 25344*z + 3664) + t^4*(4896*z^3 - 30528*z^2 + 46224*z - 7408) + t^3*(-3008*z^3 + 20736*z^2 - 33696*z + 5568) + t^2*(-848*z^3 + 3648*z^2 - 3456*z + 464) + t*(1520*z^3 - 10128*z^2 + 16128*z - 2512) - 480*z^3 + 3552*z^2 - 5952*z + 928:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-541*z^3/2430 + 614*z^2/405 - 1147*z/405 + 3067/2430) + t^6*(758*z^3/405 - 15466*z^2/1215 + 57611*z/2430 - 12713/1215) + t^5*(-3827*z^3/810 + 25943*z^2/810 - 23962*z/405 + 6853/270) + t^4*(643*z^3/243 - 947*z^2/54 + 1649*z/54 - 1661/162) + t^3*(152*z^3/45 - 6413*z^2/270 + 115861*z/2430 - 31733/1215) + t^2*(-1709*z^3/810 + 2006*z^2/135 - 11989*z/405 + 6244/405) + t*(-34*z^3/81 + 487*z^2/162 - 515*z/81 + 2015/486) - 101*z^3/162 + 1913*z^2/486 - 331*z/54 + 295/243)*h0 + (t*(541*z^3/19440 - 307*z^2/1620 + 1147*z/3240 - 3067/19440) - 371*z^3/6480 + 631*z^2/1620 - 14131*z/19440 + 2107/6480)*h1 + (2164*t^8*z^2/1215 - 12572*t^8*z/1215 + 66*t^8/5 - 28256*t^7*z^2/1215 + 164669*t^7*z/1215 - 213179*t^7/1215 + 144188*t^6*z^2/1215 - 846781*t^6*z/1215 + 1116236*t^6/1215 - 120478*t^5*z^2/405 + 239888*t^5*z/135 - 971857*t^5/405 + 442286*t^4*z^2/1215 - 2744792*t^4*z/1215 + 3854458*t^4/1215 - 180571*t^3*z^2/1215 + 1275179*t^3*z/1215 - 1982446*t^3/1215 - 110384*t^2*z^2/1215 + 579952*t^2*z/1215 - 228364*t^2/405 + 8131*t*z^2/81 - 266572*t*z/405 + 1166108*t/1215 - 742*z^2/27 + 80677*z/405 - 368353/1215)*hf
  norm_num at hh

private lemma cell_5_63 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 6*t:ℝ)=0) (h1 : (t*(-144*z^2 + 288*z - 48) + 64*z^3 - 48*z^2 - 176*z + 32:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-z^3/3 + 7*z^2/3 - 9*z/2 + 11/6)*h0 + (169*z^3/240 - 289*z^2/60 + 363*z/40 - 247/60)*h1 + (507*t*z/5 - 933*t/5 - 676*z^2/15 + 133*z/5 + 1936/15)*hf
  norm_num at hh

private lemma pair_5_23_29 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z^2 + 3*z - 2:ℝ)=0) (h1 : (t - 2*z^3 + 13*z^2 - 21*z + 3:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z^3/15 - 6*z^2/5 + 44*z/15 - 19/15)*h0 + (-2*z^3/15 + 6*z^2/5 - 44*z/15 + 19/15)*h1 + (-4*z^2/15 + 12*z/5 - 16/3)*hf
  norm_num at hh

private lemma pair_5_23_53 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z^2 + 3*z - 2:ℝ)=0) (h1 : (t - 2*z^3 + 13*z^2 - 21*z + 3:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z^3/15 - 6*z^2/5 + 44*z/15 - 19/15)*h0 + (-2*z^3/15 + 6*z^2/5 - 44*z/15 + 19/15)*h1 + (-4*z^2/15 + 12*z/5 - 16/3)*hf
  norm_num at hh

private lemma pair_5_29_53 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z^3 + 13*z^2 - 21*z + 3:ℝ)=0) (h2 : (1296*t^8 + t^7*(-10368*z^3 + 62208*z^2 - 93312*z + 9072) + t^6*(115344*z^3 - 692064*z^2 + 1036800*z - 152928) + t^5*(-598752*z^3 + 3600288*z^2 - 5403024*z + 829440) + t^4*(1816992*z^3 - 10964160*z^2 + 16498080*z - 2537568) + t^3*(-3370896*z^3 + 20434032*z^2 - 30837024*z + 4739472) + t^2*(3740256*z^3 - 22796640*z^2 + 34509888*z - 5304528) + t*(-2269296*z^3 + 13915152*z^2 - 21136464*z + 3250368) + 576720*z^3 - 3558816*z^2 + 5425056*z - 834624:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(117*z^3/5 - 2294*z^2/15 + 4027*z/15 - 1762/15) + t^6*(-1271*z^3/15 + 8419*z^2/15 - 15097*z/15 + 2224/5) + t^5*(1102*z^3/15 - 2551*z^2/5 + 14689*z/15 - 6689/15) + t^4*(34*z^3 - 192*z^2 + 262*z - 99) + t^3*(-258*z^3/5 + 1677*z^2/5 - 3071*z/5 + 1371/5) + t^2*(16*z^3/5 - 142*z^2/15 + 461*z/15 - 251/15) + t*(-16*z^3/15 - 82*z^2/5 + 863*z/15 - 463/15) + 10*z^3/3 - 44*z^2/3 + 56*z/3 - 7)*h0 + (-13*z^3/720 + 1147*z^2/9720 - 4027*z/19440 + 881/9720)*h2 + (-702*t^7*z^2/5 + 3769*t^7*z/5 - 2744*t^7/3 + 28697*t^6*z^2/15 - 31472*t^6*z/3 + 64863*t^6/5 - 159958*t^5*z^2/15 + 885568*t^5*z/15 - 1106128*t^5/15 + 164374*t^4*z^2/5 - 2746184*t^4*z/15 + 3450338*t^4/15 - 304833*t^3*z^2/5 + 1706514*t^3*z/5 - 6455722*t^3/15 + 337694*t^2*z^2/5 - 5703908*t^2*z/15 + 7213082*t^2/15 - 614633*t*z^2/15 + 1160922*t*z/5 - 1472534*t/5 + 31259*z^2/3 - 891701*z/15 + 1135058/15)*hf
  norm_num at hh

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_0 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 0) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_0 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_1 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 1) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_1 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 24*z^5 + 108*z^4 - 226*z^3 + 222*z^2 - 90*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_2 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 2) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_2 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_3 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 3) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_3 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z^3 - 384*t^7*z^2 + 448*t^7*z - 176*t^7 + 160*t^6*z^6 - 1920*t^6*z^5 + 8192*t^6*z^4 - 15424*t^6*z^3 + 14368*t^6*z^2 - 6352*t^6*z + 928*t^6 + 256*t^5*z^9 - 4608*t^5*z^8 + 33600*t^5*z^7 - 128688*t^5*z^6 + 284160*t^5*z^5 - 379200*t^5*z^4 + 309040*t^5*z^3 - 148128*t^5*z^2 + 37056*t^5*z - 3200*t^5 + 304*t^4*z^12 - 7296*t^4*z^11 + 75328*t^4*z^10 - 439664*t^4*z^9 + 1608288*t^4*z^8 - 3877728*t^4*z^7 + 6327232*t^4*z^6 - 7051152*t^4*z^5 + 5318368*t^4*z^4 - 2626240*t^4*z^3 + 789840*t^4*z^2 - 124976*t^4*z + 7408*t^4 + 256*t^3*z^15 - 7680*t^3*z^14 + 102464*t^3*z^13 - 803440*t^3*z^12 + 4127104*t^3*z^11 - 14674720*t^3*z^10 + 37259984*t^3*z^9 - 68762304*t^3*z^8 + 92985824*t^3*z^7 - 92067264*t^3*z^6 + 66017872*t^3*z^5 - 33451088*t^3*z^4 + 11441904*t^3*z^3 - 2429936*t^3*z^2 + 272816*t^3*z - 11792*t^3 + 160*t^2*z^18 - 5760*t^2*z^17 + 94272*t^2*z^16 - 929712*t^2*z^15 + 6176544*t^2*z^14 - 29292000*t^2*z^13 + 102587456*t^2*z^12 - 270908256*t^2*z^11 + 546202128*t^2*z^10 - 846061072*t^2*z^9 + 1007551536*t^2*z^8 - 917736624*t^2*z^7 + 631710928*t^2*z^6 - 321768672*t^2*z^5 + 117292320*t^2*z^4 - 29043952*t^2*z^3 + 4493328*t^2*z^2 - 374880*t^2*z + 12256*t^2 + 64*t*z^21 - 2688*t*z^20 + 52096*t*z^19 - 618560*t*z^18 + 5039040*t*z^17 - 29899200*t*z^16 + 133925168*t*z^15 - 463312752*t*z^14 + 1256493824*t*z^13 - 2696622848*t*z^12 + 4604046960*t*z^11 - 6263673952*t*z^10 + 6777134448*t*z^9 - 5797496544*t*z^8 + 3879798976*t*z^7 - 1997510976*t*z^6 + 771463392*t*z^5 - 215176672*t*z^4 + 40893024*t*z^3 - 4829808*t*z^2 + 304240*t*z - 7232*t + 16*z^24 - 768*z^23 + 17216*z^22 - 239536*z^21 + 2319232*z^20 - 16607536*z^19 + 91265280*z^18 - 394262784*z^17 + 1360706656*z^16 - 3792841824*z^15 + 8598605840*z^14 - 15916504336*z^13 + 24083836864*z^12 - 29744357920*z^11 + 29853748896*z^10 - 24167729376*z^9 + 15602967280*z^8 - 7907109600*z^7 + 3078168048*z^6 - 894206752*z^5 + 186373728*z^4 - 26362736*z^3 + 2320672*z^2 - 108352*z + 1792:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z^2 + 800*t^6*z - 352*t^6 - 256*t^5*z^5 + 2816*t^5*z^4 - 10304*t^5*z^3 + 15088*t^5*z^2 - 11504*t^5*z + 2192*t^5 - 304*t^4*z^8 + 5168*t^4*z^7 - 34896*t^4*z^6 + 120608*t^4*z^5 - 233840*t^4*z^4 + 268000*t^4*z^3 - 177712*t^4*z^2 + 63840*t^4*z - 5680*t^4 - 256*t^3*z^11 + 5888*t^3*z^10 - 57664*t^3*z^9 + 315312*t^3*z^8 - 1065264*t^3*z^7 + 2336304*t^3*z^6 - 3412000*t^3*z^5 + 3332624*t^3*z^4 - 2133760*t^3*z^3 + 841904*t^3*z^2 - 178912*t^3*z + 9344*t^3 - 160*t^2*z^14 + 4640*t^2*z^13 - 59552*t^2*z^12 + 446608*t^2*z^11 - 2179280*t^2*z^10 + 7303472*t^2*z^9 - 17320816*t^2*z^8 + 29533088*t^2*z^7 - 36372032*t^2*z^6 + 32123616*t^2*z^5 - 19892256*t^2*z^4 + 8250864*t^2*z^3 - 2102336*t^2*z^2 + 278560*t^2*z - 10528*t^2 - 64*t*z^17 + 2240*t*z^16 - 35520*t*z^15 + 338048*t*z^14 - 2157440*t*z^13 + 9778048*t*z^12 - 32534768*t*z^11 + 81079136*t*z^10 - 153071296*t*z^9 + 219959680*t*z^8 - 240163200*t*z^7 + 197446528*t*z^6 - 119975216*t*z^5 + 52153360*t*z^4 - 15337008*t*z^3 + 2756624*t*z^2 - 246816*t*z + 6800*t - 16*z^20 + 656*z^19 - 12400*z^18 + 143424*z^17 - 1136400*z^16 + 6544944*z^15 - 28381280*z^14 + 94729984*z^13 - 246762896*z^12 + 505686592*z^11 - 817898000*z^10 + 1042772896*z^9 - 1041598960*z^8 + 805474064*z^7 - 472963840*z^6 + 204781024*z^5 - 62614880*z^4 + 12686320*z^3 - 1543456*z^2 + 94016*z - 1792)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_4 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 4) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_4 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 24*z^5 + 108*z^4 - 226*z^3 + 222*z^2 - 90*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_5 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 5) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_5 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 24*z^5 + 108*z^4 - 228*z^3 + 234*z^2 - 108*z + 12:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_6 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 6) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_6 z t hf hn0 hn1 hn2 hn3
  · have hr : (1296*t*z^4 - 7776*t*z^3 + 11664*t*z^2 - 1296*t*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1296*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_7 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 7) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_7 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^3 + 12*t*z^2 - 18*t*z - 2*t + 2*z^6 - 24*z^5 + 108*z^4 - 224*z^3 + 210*z^2 - 72*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 - 48*t^6*z^3 + 736*t^6*z^2 - 192*t^6*z + 288*t^5*z^4 - 2480*t^5*z^3 + 1296*t^5*z^2 + 1440*t^5*z - 720*t^4*z^5 + 5008*t^4*z^4 - 3504*t^4*z^3 - 5328*t^4*z^2 + 1296*t^4*z - 144*t^4 + 960*t^3*z^6 - 6368*t^3*z^5 + 6144*t^3*z^4 + 9072*t^3*z^3 - 6480*t^3*z^2 - 3312*t^3*z + 432*t^3 - 720*t^2*z^7 + 5056*t^2*z^6 - 6912*t^2*z^5 - 7920*t^2*z^4 + 12960*t^2*z^3 + 3024*t^2*z^2 - 432*t^2*z + 288*t*z^8 - 2288*t*z^7 + 4416*t*z^6 + 2736*t*z^5 - 10368*t*z^4 - 3312*t*z^3 + 11232*t*z^2 - 1296*t*z - 48*z^9 + 448*z^8 - 1200*z^7 + 3888*z^5 - 4032*z^4 + 432*z^3:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-288*t^5 + 720*t^4*z + 32*t^4 - 960*t^3*z^2 - 352*t^3*z + 4832*t^3 + 720*t^2*z^3 - 16*t^2*z^2 - 3280*t^2*z - 9056*t^2 - 288*t*z^4 + 272*t*z^3 + 1520*t*z^2 + 1792*t*z + 4096*t + 48*z^5 - 112*z^4 - 256*z^3 + 160*z^2 - 128*z - 1040)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_8 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 8) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_8 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_9 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 9) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_9 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^18 + 46656*t*z^17 - 762048*t*z^16 + 7474032*t*z^15 - 49105440*t*z^14 + 228326688*t*z^13 - 773975088*t*z^12 + 1941770880*t*z^11 - 3623762448*t*z^10 + 5014870704*t*z^9 - 5091298416*t*z^8 + 3721765968*t*z^7 - 1906125696*t*z^6 + 659371104*t*z^5 - 146958624*t*z^4 + 19730304*t*z^3 - 1420416*t*z^2 + 41472*t*z + 1296*z^24 - 62208*z^23 + 1389312*z^22 - 19171728*z^21 + 183091104*z^20 - 1284488928*z^19 + 6858496800*z^18 - 28495058688*z^17 + 93400093008*z^16 - 243467653824*z^15 + 506523379536*z^14 - 840905858448*z^13 + 1110020419152*z^12 - 1157064098112*z^11 + 942711386256*z^10 - 592200708336*z^9 + 282003507504*z^8 - 99776988432*z^7 + 25632847872*z^6 - 4651569504*z^5 + 574659360*z^4 - 45608832*z^3 + 2083968*z^2 - 41472*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^14 - 37584*t*z^13 + 480816*t*z^12 - 3571776*t*z^11 + 17069616*t*z^10 - 54950400*t*z^9 + 121292640*t*z^8 - 183288096*t*z^7 + 185976000*t*z^6 - 121713840*t*z^5 + 48040128*t*z^4 - 10395216*t*z^3 + 1110672*t*z^2 - 28512*t*z + 7776*t - 1296*z^20 + 53136*z^19 - 999216*z^18 + 11422944*z^17 - 88715088*z^16 + 495515232*z^15 - 2055496176*z^14 + 6448228560*z^13 - 15432709680*z^12 + 28224001584*z^11 - 39256108272*z^10 + 41067172368*z^9 - 31739974416*z^8 + 17670996288*z^7 - 6861283200*z^6 + 1790810208*z^5 - 301926528*z^4 + 30897936*z^3 - 1826064*z^2 - 6480*z - 29808)*hf
  · have hr : (-1296*t*z^18 + 46656*t*z^17 - 765936*t*z^16 + 7594560*t*z^15 - 50785056*t*z^14 + 242236656*t*z^13 - 850249872*t*z^12 + 2233902240*t*z^11 - 4427371872*t*z^10 + 6623363520*t*z^9 - 7439706144*t*z^8 + 6207324192*t*z^7 - 3786333984*t*z^6 + 1653702480*t*z^5 - 503717616*t*z^4 + 103214736*t*z^3 - 13423968*t*z^2 + 990144*t*z - 31104*t + 1296*z^24 - 62208*z^23 + 1394496*z^22 - 19394640*z^21 + 187531200*z^20 - 1338872976*z^19 + 7317090288*z^18 - 31319799552*z^17 + 106561081872*z^16 - 290862397152*z^15 + 640195996032*z^14 - 1138364671392*z^13 + 1633788769968*z^12 - 1886213865168*z^11 + 1741919078448*z^10 - 1276967783808*z^9 + 736061059008*z^8 - 329862724272*z^7 + 113408202384*z^6 - 29416391568*z^5 + 5625145440*z^4 - 765460368*z^3 + 69836256*z^2 - 3810240*z + 93312:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^14 - 37584*t*z^13 + 484704*t*z^12 - 3665088*t*z^11 + 18041616*t*z^10 - 60718896*t*z^9 + 142829568*t*z^8 - 236032704*t*z^7 + 271736208*t*z^6 - 213396768*t*z^5 + 110530656*t*z^4 - 36132480*t*z^3 + 7067088*t*z^2 - 736128*t*z + 34992*t - 1296*z^20 + 53136*z^19 - 1004400*z^18 + 11609568*z^17 - 91776240*z^16 + 525817008*z^15 - 2257622928*z^14 + 7409181456*z^13 - 18791778384*z^12 + 37004607648*z^11 - 56547770544*z^10 + 66722361984*z^9 - 60234808896*z^8 + 41070363120*z^7 - 20812545648*z^6 + 7694047440*z^5 - 2029374000*z^4 + 369713808*z^3 - 44044560*z^2 + 3046896*z - 108864)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_10 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 10) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_10 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_11 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 11) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_11 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z^3 - 384*t^7*z^2 + 384*t^7*z - 112*t^7 + 160*t^6*z^6 - 1920*t^6*z^5 + 7872*t^6*z^4 - 13184*t^6*z^3 + 10176*t^6*z^2 - 3456*t^6*z + 304*t^6 + 256*t^5*z^9 - 4608*t^5*z^8 + 32832*t^5*z^7 - 118704*t^5*z^6 + 236160*t^5*z^5 - 270576*t^5*z^4 + 180480*t^5*z^3 - 66960*t^5*z^2 + 11952*t^5*z - 544*t^5 + 304*t^4*z^12 - 7296*t^4*z^11 + 74112*t^4*z^10 - 416560*t^4*z^9 + 1427904*t^4*z^8 - 3123504*t^4*z^7 + 4465392*t^4*z^6 - 4203792*t^4*z^5 + 2572992*t^4*z^4 - 979840*t^4*z^3 + 209328*t^4*z^2 - 19824*t^4*z + 496*t^4 + 256*t^3*z^15 - 7680*t^3*z^14 + 101184*t^3*z^13 - 771440*t^3*z^12 + 3781248*t^3*z^11 - 12548016*t^3*z^10 + 28998400*t^3*z^9 - 47403360*t^3*z^8 + 55172592*t^3*z^7 - 45600016*t^3*z^6 + 26375520*t^3*z^5 - 10332528*t^3*z^4 + 2566256*t^3*z^3 - 349296*t^3*z^2 + 16704*t^3*z + 176*t^3 + 160*t^2*z^18 - 5760*t^2*z^17 + 93312*t^2*z^16 - 899952*t^2*z^15 + 5765184*t^2*z^14 - 25939728*t^2*z^13 + 84624720*t^2*z^12 - 203993424*t^2*z^11 + 367297344*t^2*z^10 - 496294448*t^2*z^9 + 502658496*t^2*z^8 - 378524880*t^2*z^7 + 208227264*t^2*z^6 - 81032544*t^2*z^5 + 21091392*t^2*z^4 - 3312672*t^2*z^3 + 247104*t^2*z^2 - 1008*t^2*z - 560*t^2 + 64*t*z^21 - 2688*t*z^20 + 51648*t*z^19 - 601984*t*z^18 + 4760064*t*z^17 - 27068112*t*z^16 + 114554208*t*z^15 - 368590608*t*z^14 + 913918896*t*z^13 - 1760457824*t*z^12 + 2644985568*t*z^11 - 3100196928*t*z^10 + 2823888992*t*z^9 - 1981217952*t*z^8 + 1053799920*t*z^7 - 413849424*t*z^6 + 114721488*t*z^5 - 20604672*t*z^4 + 1928320*t*z^3 - 7152*t*z^2 - 12432*t*z + 608*t + 16*z^24 - 768*z^23 + 17088*z^22 - 234032*z^21 + 2209920*z^20 - 15276240*z^19 + 80129824*z^18 - 326350080*z^17 + 1047682800*z^16 - 2677162928*z^15 + 5477242416*z^14 - 8995703376*z^13 + 11855615248*z^12 - 12492292800*z^11 + 10444396608*z^10 - 6840260960*z^9 + 3439237536*z^8 - 1287039312*z^7 + 341346256*z^6 - 58841472*z^5 + 5317872*z^4 + 15088*z^3 - 53184*z^2 + 4608*z - 128:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z^2 + 800*t^6*z - 32*t^6 - 256*t^5*z^5 + 2816*t^5*z^4 - 9536*t^5*z^3 + 10480*t^5*z^2 - 6512*t^5*z - 832*t^5 - 304*t^4*z^8 + 5168*t^4*z^7 - 33680*t^4*z^6 + 106016*t^4*z^5 - 172624*t^4*z^4 + 156304*t^4*z^3 - 72720*t^4*z^2 + 19488*t^4*z + 4560*t^4 - 256*t^3*z^11 + 5888*t^3*z^10 - 56384*t^3*z^9 + 292272*t^3*z^8 - 898608*t^3*z^7 + 1708992*t^3*z^6 - 2060384*t^3*z^5 + 1573648*t^3*z^4 - 741136*t^3*z^3 + 188928*t^3*z^2 - 27552*t^3*z - 8064*t^3 - 160*t^2*z^14 + 4640*t^2*z^13 - 58592*t^2*z^12 + 423568*t^2*z^11 - 1942640*t^2*z^10 + 5937920*t^2*z^9 - 12415184*t^2*z^8 + 17991568*t^2*z^7 - 18097792*t^2*z^6 + 12468560*t^2*z^5 - 5661760*t^2*z^4 + 1558816*t^2*z^3 - 204640*t^2*z^2 + 14000*t^2*z + 3856*t^2 - 64*t*z^17 + 2240*t*z^16 - 35072*t*z^15 + 324608*t*z^14 - 1978816*t*z^13 + 8389072*t*z^12 - 25495344*t*z^11 + 56521056*t*z^10 - 92245296*t*z^9 + 111094144*t*z^8 - 98228624*t*z^7 + 62795120*t*z^6 - 28123968*t*z^5 + 8295360*t*z^4 - 1407264*t*z^3 + 76672*t*z^2 + 3760*t*z + 4112*t - 16*z^20 + 656*z^19 - 12272*z^18 + 138816*z^17 - 1061136*z^16 + 5806032*z^15 - 23508896*z^14 + 71875456*z^13 - 167920672*z^12 + 301584640*z^11 - 416747984*z^10 + 441041696*z^9 - 353253808*z^8 + 209363888*z^7 - 88214528*z^6 + 24592672*z^5 - 3920528*z^4 + 218096*z^3 + 23712*z^2 - 2784*z - 4032)*hf
  · have hr : (16*t^8 + 64*t^7*z^3 - 384*t^7*z^2 + 384*t^7*z - 112*t^7 + 160*t^6*z^6 - 1920*t^6*z^5 + 8064*t^6*z^4 - 14528*t^6*z^3 + 13056*t^6*z^2 - 5568*t^6*z + 688*t^6 + 256*t^5*z^9 - 4608*t^5*z^8 + 33408*t^5*z^7 - 126192*t^5*z^6 + 272448*t^5*z^5 - 353952*t^5*z^4 + 278544*t^5*z^3 - 127008*t^5*z^2 + 29952*t^5*z - 2560*t^5 + 304*t^4*z^12 - 7296*t^4*z^11 + 75264*t^4*z^10 - 438448*t^4*z^9 + 1599840*t^4*z^8 - 3851712*t^4*z^7 + 6296928*t^4*z^6 - 7064064*t^4*z^5 + 5388912*t^4*z^4 - 2699776*t^4*z^3 + 821904*t^4*z^2 - 130128*t^4*z + 7984*t^4 + 256*t^3*z^15 - 7680*t^3*z^14 + 102528*t^3*z^13 - 805040*t^3*z^12 + 4145280*t^3*z^11 - 14798112*t^3*z^10 + 37808848*t^3*z^9 - 70413408*t^3*z^8 + 96375456*t^3*z^7 - 96835648*t^3*z^6 + 70620960*t^3*z^5 - 36494352*t^3*z^4 + 12813056*t^3*z^3 - 2841360*t^3*z^2 + 346416*t^3*z - 17200*t^3 + 160*t^2*z^18 - 5760*t^2*z^17 + 94464*t^2*z^16 - 935664*t^2*z^15 + 6260256*t^2*z^14 - 29999232*t^2*z^13 + 106592352*t^2*z^12 - 286970688*t^2*z^11 + 593226576*t^2*z^10 - 948209360*t^2*z^9 + 1173414096*t^2*z^8 - 1119082464*t^2*z^7 + 813104448*t^2*z^6 - 441056592*t^2*z^5 + 172926432*t^2*z^4 - 46623264*t^2*z^3 + 8003664*t^2*z^2 - 770544*t^2*z + 31120*t^2 + 64*t*z^21 - 2688*t*z^20 + 52224*t*z^19 - 623296*t*z^18 + 5119488*t*z^17 - 30731616*t*z^16 + 139796112*t*z^15 - 493241184*t*z^14 + 1370620512*t*z^13 - 3029110352*t*z^12 + 5353639392*t*z^11 - 7580795952*t*z^10 + 8585633696*t*z^9 - 7735244112*t*z^8 + 5491059120*t*z^7 - 3026535888*t*z^6 + 1267774848*t*z^5 - 391161168*t*z^4 + 84795280*t*z^3 - 11980464*t*z^2 + 969360*t*z - 33376*t + 16*z^24 - 768*z^23 + 17280*z^22 - 242288*z^21 + 2374368*z^20 - 17291328*z^19 + 97148272*z^18 - 431561088*z^17 + 1541415600*z^16 - 4477674128*z^15 + 10659828912*z^14 - 20892050352*z^13 + 33770577616*z^12 - 44988020256*z^11 + 49224597888*z^10 - 43961115248*z^9 + 31739534208*z^8 - 18277717680*z^7 + 8242868608*z^6 - 2840540880*z^5 + 723544560*z^4 - 130036544*z^3 + 15366912*z^2 - 1055040*z + 31360:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z^2 + 800*t^6*z - 224*t^6 - 256*t^5*z^5 + 2816*t^5*z^4 - 10112*t^5*z^3 + 13936*t^5*z^2 - 10544*t^5*z + 1328*t^5 - 304*t^4*z^8 + 5168*t^4*z^7 - 34832*t^4*z^6 + 119840*t^4*z^5 - 231664*t^4*z^4 + 268480*t^4*z^3 - 180720*t^4*z^2 + 67152*t^4*z - 9264*t^4 - 256*t^3*z^11 + 5888*t^3*z^10 - 57728*t^3*z^9 + 316464*t^3*z^8 - 1074480*t^3*z^7 + 2378544*t^3*z^6 - 3526880*t^3*z^5 + 3513328*t^3*z^4 - 2303008*t^3*z^3 + 934416*t^3*z^2 - 204432*t^3*z + 44112*t^3 - 160*t^2*z^14 + 4640*t^2*z^13 - 59744*t^2*z^12 + 451216*t^2*z^11 - 2228048*t^2*z^10 + 7603280*t^2*z^9 - 18507248*t^2*z^8 + 32698432*t^2*z^7 - 42181792*t^2*z^6 + 39497504*t^2*z^5 - 26291776*t^2*z^4 + 11922208*t^2*z^3 - 3402304*t^2*z^2 + 497840*t^2*z - 139856*t^2 - 64*t*z^17 + 2240*t*z^16 - 35648*t*z^15 + 341888*t*z^14 - 2209216*t*z^13 + 10193248*t*z^12 - 34743600*t*z^11 + 89314896*t*z^10 - 175250640*t*z^9 + 263805280*t*z^8 - 304230704*t*z^7 + 266587088*t*z^6 - 174601344*t*z^5 + 83164560*t*z^4 - 27560976*t*z^3 + 5907376*t*z^2 - 651728*t*z + 243440*t - 16*z^20 + 656*z^19 - 12464*z^18 + 145728*z^17 - 1174512*z^16 + 6929184*z^15 - 31022528*z^14 + 107852992*z^13 - 295521280*z^12 + 643973872*z^11 - 1120867424*z^10 + 1558320944*z^9 - 1722874816*z^8 + 1500490064*z^7 - 1013485040*z^6 + 518539600*z^5 - 194171120*z^4 + 50595056*z^3 - 8505696*z^2 + 761664*z - 201600)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_12 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 12) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_12 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z^3 + 768*t^7*z^2 - 1088*t^7*z + 16*t^7 + 448*t^6*z^6 - 5376*t^6*z^5 + 23744*t^6*z^4 - 45904*t^6*z^3 + 33664*t^6*z^2 - 1936*t^6*z + 16*t^6 - 896*t^5*z^9 + 16128*t^5*z^8 - 119616*t^5*z^7 + 468624*t^5*z^6 - 1027968*t^5*z^5 + 1216320*t^5*z^4 - 652016*t^5*z^3 + 75936*t^5*z^2 - 2112*t^5*z - 32*t^5 + 1120*t^4*z^12 - 26880*t^4*z^11 + 280000*t^4*z^10 - 1655120*t^4*z^9 + 6086400*t^4*z^8 - 14329680*t^4*z^7 + 21343504*t^4*z^6 - 18997824*t^4*z^5 + 8818624*t^4*z^4 - 1533568*t^4*z^3 + 90144*t^4*z^2 + 64*t^4*z - 176*t^4 - 896*t^3*z^15 + 26880*t^3*z^14 - 360640*t^3*z^13 + 2851760*t^3*z^12 - 14739200*t^3*z^11 + 52161536*t^3*z^10 - 128620576*t^3*z^9 + 220249152*t^3*z^8 - 255766048*t^3*z^7 + 191505792*t^3*z^6 - 84270032*t^3*z^5 + 18592624*t^3*z^4 - 1801920*t^3*z^3 + 46000*t^3*z^2 + 2768*t^3*z + 112*t^3 + 448*t^2*z^18 - 16128*t^2*z^17 + 264768*t^2*z^16 - 2622576*t^2*z^15 + 17473920*t^2*z^14 - 82640688*t^2*z^13 + 285222512*t^2*z^12 - 727052160*t^2*z^11 + 1368991200*t^2*z^10 - 1883536000*t^2*z^9 + 1850182368*t^2*z^8 - 1247795712*t^2*z^7 + 543600208*t^2*z^6 - 140052336*t^2*z^5 + 19215936*t^2*z^4 - 1146976*t^2*z^3 + 10608*t^2*z^2 - 912*t^2*z + 16*t^2 - 128*t*z^21 + 5376*t*z^20 - 104384*t*z^19 + 1242544*t*z^18 - 10137984*t*z^17 + 60045504*t*z^16 - 266697328*t*z^15 + 904800288*t*z^14 - 2365759264*t*z^13 + 4775039776*t*z^12 - 7403151696*t*z^11 + 8713529840*t*z^10 - 7635594816*t*z^9 + 4838805120*t*z^8 - 2128111232*t*z^7 + 614218992*t*z^6 - 108122016*t*z^5 + 10358960*t*z^4 - 392880*t*z^3 - 5664*t*z^2 - 272*t*z + 160*t + 16*z^24 - 768*z^23 + 17216*z^22 - 239344*z^21 + 2311168*z^20 - 16451056*z^19 + 89403888*z^18 - 379075392*z^17 + 1270591456*z^16 - 3390525312*z^15 + 7219160864*z^14 - 12240439456*z^13 + 16425883168*z^12 - 17262129472*z^11 + 13986715104*z^10 - 8550428016*z^9 + 3830524480*z^8 - 1209783264*z^7 + 255361872*z^6 - 32787520*z^5 + 1759440*z^4 + 169072*z^3 - 41504*z^2 + 3488*z - 128:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6*z^2 + 2240*t^6*z - 1792*t^6 + 896*t^5*z^5 - 9856*t^5*z^4 + 38080*t^5*z^3 - 56912*t^5*z^2 + 16720*t^5*z + 11984*t^5 - 1120*t^4*z^8 + 19040*t^4*z^7 - 131040*t^4*z^6 + 462320*t^4*z^5 - 862160*t^4*z^4 + 754720*t^4*z^3 - 160624*t^4*z^2 - 52224*t^4*z - 35536*t^4 + 896*t^3*z^11 - 20608*t^3*z^10 + 203840*t^3*z^9 - 1129200*t^3*z^8 + 3815280*t^3*z^7 - 7994448*t^3*z^6 + 10008080*t^3*z^5 - 6618880*t^3*z^4 + 1549904*t^3*z^3 + 66944*t^3*z^2 + 80864*t^3*z + 54320*t^3 - 448*t^2*z^14 + 12992*t^2*z^13 - 167552*t^2*z^12 + 1264240*t^2*z^11 - 6174128*t^2*z^10 + 20369024*t^2*z^9 - 45920080*t^2*z^8 + 69788000*t^2*z^7 - 68467760*t^2*z^6 + 39500016*t^2*z^5 - 10909536*t^2*z^4 + 898656*t^2*z^3 - 108224*t^2*z^2 - 62720*t^2*z - 41056*t^2 + 128*t*z^17 - 4480*t*z^16 + 71232*t*z^15 - 680176*t*z^14 + 4343536*t*z^13 - 19543952*t*z^12 + 63567520*t*z^11 - 150783856*t*z^10 + 259631840*t*z^9 - 318558800*t*z^8 + 268555968*t*z^7 - 145976288*t*z^6 + 45875008*t*z^5 - 7005488*t*z^4 + 456432*t*z^3 + 29216*t*z^2 + 17568*t*z + 11936*t - 16*z^20 + 656*z^19 - 12400*z^18 + 143232*z^17 - 1129680*z^16 + 6438192*z^15 - 27362768*z^14 + 88220656*z^13 - 217332896*z^12 + 408765520*z^11 - 582013664*z^10 + 616742704*z^9 - 473035888*z^8 + 251605568*z^7 - 87018400*z^6 + 17791456*z^5 - 1846256*z^4 + 26320*z^3 + 20000*z^2 - 2464*z + 128)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_13 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 13) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_13 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^3 + 12*t*z^2 - 18*t*z - 2*t + 2*z^6 - 24*z^5 + 108*z^4 - 224*z^3 + 210*z^2 - 72*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf
  · have hr : (16*t^8 - 192*t^7*z^3 + 1152*t^7*z^2 - 1664*t^7*z + 144*t^7 + 1056*t^6*z^6 - 12672*t^6*z^5 + 56256*t^6*z^4 - 111168*t^6*z^3 + 89152*t^6*z^2 - 14976*t^6*z + 624*t^6 - 3456*t^5*z^9 + 62208*t^5*z^8 - 462528*t^5*z^7 + 1826928*t^5*z^6 - 4091904*t^5*z^5 + 5097168*t^5*z^4 - 3156224*t^5*z^3 + 721008*t^5*z^2 - 62352*t^5*z + 1728*t^5 + 7344*t^4*z^12 - 176256*t^4*z^11 + 1838592*t^4*z^10 - 10913616*t^4*z^9 + 40505472*t^4*z^8 - 97145136*t^4*z^7 + 150000432*t^4*z^6 - 143531280*t^4*z^5 + 78260992*t^4*z^4 - 21083040*t^4*z^3 + 2724336*t^4*z^2 - 159408*t^4*z + 3312*t^4 - 10368*t^3*z^15 + 311040*t^3*z^14 - 4176576*t^3*z^13 + 33103728*t^3*z^12 - 171932544*t^3*z^11 + 613957968*t^3*z^10 - 1537700928*t^3*z^9 + 2703644640*t^3*z^8 - 3283948560*t^3*z^7 + 2660969520*t^3*z^6 - 1357728800*t^3*z^5 + 404180496*t^3*z^4 - 67495632*t^3*z^3 + 6085584*t^3*z^2 - 272448*t^3*z + 4752*t^3 + 9504*t^2*z^18 - 342144*t^2*z^17 + 5619456*t^2*z^16 - 55734480*t^2*z^15 + 372345984*t^2*z^14 - 1769362704*t^2*z^13 + 6154886736*t^2*z^12 - 15885508752*t^2*z^11 + 30492137088*t^2*z^10 - 43212136176*t^2*z^9 + 44443047168*t^2*z^8 - 32254393104*t^2*z^7 + 15877999744*t^2*z^6 - 5062588128*t^2*z^5 + 1009639872*t^2*z^4 - 121986432*t^2*z^3 + 8519040*t^2*z^2 - 313200*t^2*z + 4752*t^2 - 5184*t*z^21 + 217728*t*z^20 - 4228416*t*z^19 + 50365152*t*z^18 - 411485184*t*z^17 + 2443067568*t*z^16 - 10894296096*t*z^15 + 37187865936*t*z^14 - 98127809424*t*z^13 + 200715630912*t*z^12 - 317210159520*t*z^11 + 383814141120*t*z^10 - 350165872704*t*z^9 + 235704950208*t*z^8 - 113851761776*t*z^7 + 38258027568*t*z^6 - 8692902000*t*z^5 + 1298747520*t*z^4 - 123130656*t*z^3 + 6996240*t*z^2 - 212976*t*z + 2592*t + 1296*z^24 - 62208*z^23 + 1394496*z^22 - 19389456*z^21 + 187310016*z^20 - 1334513232*z^19 + 7264419552*z^18 - 30883464864*z^17 + 103933686384*z^16 - 278968189968*z^15 + 598894726320*z^14 - 1027113062256*z^13 + 1400177869392*z^12 - 1503898179264*z^11 + 1256587066464*z^10 - 803264989248*z^9 + 384981572032*z^8 - 135262357200*z^7 + 34040314128*z^6 - 5981217120*z^5 + 709270416*z^4 - 53717040*z^3 + 2333664*z^2 - 44064*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6*z^2 + 5280*t^6*z - 4512*t^6 + 3456*t^5*z^5 - 38016*t^5*z^4 + 148032*t^5*z^3 - 230832*t^5*z^2 + 96048*t^5*z + 29088*t^5 - 7344*t^4*z^8 + 124848*t^4*z^7 - 861840*t^4*z^6 + 3074112*t^4*z^5 - 5914800*t^4*z^4 + 5684400*t^4*z^3 - 1947696*t^4*z^2 - 76704*t^4*z - 140176*t^4 + 10368*t^3*z^11 - 238464*t^3*z^10 + 2362176*t^3*z^9 - 13147056*t^3*z^8 + 44914608*t^3*z^7 - 96361056*t^3*z^6 + 126830400*t^3*z^5 - 94313136*t^3*z^4 + 32327952*t^3*z^3 - 3285696*t^3*z^2 + 802112*t^3*z + 370784*t^3 - 9504*t^2*z^14 + 275616*t^2*z^13 - 3557088*t^2*z^12 + 26900208*t^2*z^11 - 132030864*t^2*z^10 + 439811424*t^2*z^9 - 1009015920*t^2*z^8 + 1581890256*t^2*z^7 - 1642160160*t^2*z^6 + 1058612688*t^2*z^5 - 378378144*t^2*z^4 + 65996928*t^2*z^3 - 7665568*t^2*z^2 - 665680*t^2*z - 628112*t^2 + 5184*t*z^17 - 181440*t*z^16 + 2885760*t*z^15 - 27583200*t*z^14 + 176545440*t*z^13 - 797817168*t*z^12 + 2614388400*t*z^11 - 6277760064*t*z^10 + 11022968592*t*z^9 - 13953285504*t*z^8 + 12379131792*t*z^7 - 7352712720*t*z^6 + 2739785952*t*z^5 - 602130624*t*z^4 + 79010528*t*z^3 - 4124800*t*z^2 + 1050064*t*z + 564976*t - 1296*z^20 + 53136*z^19 - 1004400*z^18 + 11604384*z^17 - 91591344*z^16 + 522824112*z^15 - 2228532480*z^14 + 7219864800*z^13 - 17920993824*z^12 + 34092042048*z^11 - 49369067568*z^10 + 53653185216*z^9 - 42781296720*z^8 + 24239926608*z^7 - 9374876832*z^6 + 2378319936*z^5 - 384347248*z^4 + 36506096*z^3 - 2473664*z^2 - 281792*z - 215648)*hf
  · have hr : (16*t^8 + 64*t^7*z - 240*t^7 + 192*t^6*z^6 - 2304*t^6*z^5 + 10176*t^6*z^4 - 20208*t^6*z^3 + 17728*t^6*z^2 - 6192*t^6*z + 1872*t^6 + 576*t^5*z^7 - 9072*t^5*z^6 + 56448*t^5*z^5 - 175104*t^5*z^4 + 280336*t^5*z^3 - 215712*t^5*z^2 + 66240*t^5*z - 9504*t^5 + 864*t^4*z^12 - 20736*t^4*z^11 + 216000*t^4*z^10 - 1280880*t^4*z^9 + 4768704*t^4*z^8 - 11603952*t^4*z^7 + 18667728*t^4*z^6 - 19756512*t^4*z^5 + 13661440*t^4*z^4 - 6294912*t^4*z^3 + 2015136*t^4*z^2 - 386208*t^4*z + 33552*t^4 + 1728*t^3*z^13 - 47952*t^3*z^12 + 587520*t^3*z^11 - 4181760*t^3*z^10 + 19143264*t^3*z^9 - 58954752*t^3*z^8 + 124173600*t^3*z^7 - 178433472*t^3*z^6 + 171821488*t^3*z^5 - 107540496*t^3*z^4 + 42277824*t^3*z^3 - 10215504*t^3*z^2 + 1403280*t^3*z - 84240*t^3 + 1728*t^2*z^18 - 62208*t^2*z^17 + 1021248*t^2*z^16 - 10125648*t^2*z^15 + 67697856*t^2*z^14 - 322746768*t^2*z^13 + 1131669360*t^2*z^12 - 2967995520*t^2*z^11 + 5867230752*t^2*z^10 - 8753102784*t^2*z^9 + 9822817440*t^2*z^8 - 8246443968*t^2*z^7 + 5154300016*t^2*z^6 - 2393488080*t^2*z^5 + 821490624*t^2*z^4 - 202656384*t^2*z^3 + 33669648*t^2*z^2 - 3331152*t^2*z + 146448*t^2 + 1728*t*z^19 - 68688*t*z^18 + 1254528*t*z^17 - 13955328*t*z^16 + 105668496*t*z^15 - 576592992*t*z^14 + 2341615392*t*z^13 - 7208181792*t*z^12 + 16973471088*t*z^11 - 30645565488*t*z^10 + 42285274848*t*z^9 - 44221010112*t*z^8 + 34602141664*t*z^7 - 19923176400*t*z^6 + 8278262784*t*z^5 - 2427875856*t*z^4 + 487571760*t*z^3 - 63630144*t*z^2 + 4850928*t*z - 163296*t + 1296*z^24 - 62208*z^23 + 1394496*z^22 - 19394640*z^21 + 187527744*z^20 - 1338743376*z^19 + 7314861168*z^18 - 31296484512*z^17 + 106395307488*z^16 - 290013773760*z^15 + 636964144416*z^14 - 1129033281312*z^13 + 1613158057632*z^12 - 1851171998688*z^11 + 1696291441728*z^10 - 1231741650576*z^9 + 702326160448*z^8 - 311218336224*z^7 + 105917790384*z^6 - 27278965728*z^5 + 5205681936*z^4 - 711838800*z^3 + 65829024*z^2 - 3678048*z + 93312:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6*z^2 + 960*t^6*z - 768*t^6 - 576*t^5*z^3 + 5040*t^5*z^2 - 13104*t^5*z + 8208*t^5 - 864*t^4*z^8 + 14688*t^4*z^7 - 101088*t^4*z^6 + 360720*t^4*z^5 - 710064*t^4*z^4 + 760032*t^4*z^3 - 419760*t^4*z^2 + 136512*t^4*z - 38896*t^4 - 1728*t^3*z^9 + 35856*t^3*z^8 - 312336*t^3*z^7 + 1479600*t^3*z^6 - 4124784*t^3*z^5 + 6832320*t^3*z^4 - 6451248*t^3*z^3 + 3144384*t^3*z^2 - 709984*t^3*z + 106928*t^3 - 1728*t^2*z^14 + 50112*t^2*z^13 - 646272*t^2*z^12 + 4886352*t^2*z^11 - 24042960*t^2*z^10 + 80816832*t^2*z^9 - 189613008*t^2*z^8 + 312038784*t^2*z^7 - 357799536*t^2*z^6 + 282242160*t^2*z^5 - 152005536*t^2*z^4 + 56579904*t^2*z^3 - 14426368*t^2*z^2 + 2098400*t^2*z - 187904*t^2 - 1728*t*z^15 + 56592*t*z^14 - 834192*t*z^13 + 7309872*t*z^12 - 42366240*t*z^11 + 170960976*t*z^10 - 492448032*t*z^9 + 1021352112*t*z^8 - 1519679808*t*z^7 + 1598332032*t*z^6 - 1158168384*t*z^5 + 558392400*t*z^4 - 172701424*t*z^3 + 33093728*t*z^2 - 3479168*t*z + 205696*t - 1296*z^20 + 53136*z^19 - 1004400*z^18 + 11609568*z^17 - 91772784*z^16 + 525711600*z^15 - 2256180048*z^14 + 7397469936*z^13 - 18729031680*z^12 + 36770820912*z^11 - 55926014976*z^10 + 65529960336*z^9 - 58588526640*z^8 + 39453926784*z^7 - 19708883616*z^6 + 7186316832*z^5 - 1877631088*z^4 + 341487248*z^3 - 41126144*z^2 + 2895712*z - 116864)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_14 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 14) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_14 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z^3 + 768*t^7*z^2 - 1152*t^7*z + 80*t^7 + 448*t^6*z^6 - 5376*t^6*z^5 + 24192*t^6*z^4 - 49040*t^6*z^3 + 40224*t^6*z^2 - 5952*t^6*z + 160*t^6 - 896*t^5*z^9 + 16128*t^5*z^8 - 120960*t^5*z^7 + 486096*t^5*z^6 - 1115712*t^5*z^5 + 1428480*t^5*z^4 - 899952*t^5*z^3 + 193680*t^5*z^2 - 12672*t^5*z + 176*t^5 + 1120*t^4*z^12 - 26880*t^4*z^11 + 282240*t^4*z^10 - 1697680*t^4*z^9 + 6426720*t^4*z^8 - 15814080*t^4*z^7 + 25164384*t^4*z^6 - 24842448*t^4*z^5 + 13863024*t^4*z^4 - 3664960*t^4*z^3 + 399696*t^4*z^2 - 14544*t^4*z + 16*t^4 - 896*t^3*z^15 + 26880*t^3*z^14 - 362880*t^3*z^13 + 2907760*t^3*z^12 - 15354240*t^3*z^11 + 56057856*t^3*z^10 - 144330656*t^3*z^9 + 262183968*t^3*z^8 - 330383232*t^3*z^7 + 278278880*t^3*z^6 - 146927904*t^3*z^5 + 44034624*t^3*z^4 - 6684016*t^3*z^3 + 440016*t^3*z^2 - 8880*t^3*z + 32*t^3 + 448*t^2*z^18 - 16128*t^2*z^17 + 266112*t^2*z^16 - 2664240*t^2*z^15 + 18056160*t^2*z^14 - 87484608*t^2*z^13 + 311904672*t^2*z^12 - 829417248*t^2*z^11 + 1649026656*t^2*z^10 - 2433211520*t^2*z^9 + 2618140896*t^2*z^8 - 1994174640*t^2*z^7 + 1027707072*t^2*z^6 - 335977920*t^2*z^5 + 64002384*t^2*z^4 - 6329328*t^2*z^3 + 274032*t^2*z^2 - 4464*t^2*z + 160*t^2 - 128*t*z^21 + 5376*t*z^20 - 104832*t*z^19 + 1259120*t*z^18 - 10419264*t*z^17 + 62945280*t*z^16 - 286976112*t*z^15 + 1006515792*t*z^14 - 2743005312*t*z^13 + 5826016240*t*z^12 - 9614608800*t*z^11 + 12217649760*t*z^10 - 11769784048*t*z^9 + 8396436528*t*z^8 - 4290333120*t*z^7 + 1499357760*t*z^6 - 336362832*t*z^5 + 44227872*t*z^4 - 2910128*t*z^3 + 58080*t*z^2 + 1728*t*z - 64*t + 16*z^24 - 768*z^23 + 17280*z^22 - 242096*z^21 + 2366112*z^20 - 17126976*z^19 + 95137504*z^18 - 414633744*z^17 + 1437385392*z^16 - 3994384064*z^15 + 8925815184*z^14 - 16024099104*z^13 + 23001964048*z^12 - 26170720512*z^11 + 23288779824*z^10 - 15907170272*z^9 + 8126956080*z^8 - 2997241488*z^7 + 758604256*z^6 - 121452672*z^5 + 10155456*z^4 - 46544*z^3 - 68064*z^2 + 5280*z - 128:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6*z^2 + 2240*t^6*z - 2240*t^6 + 896*t^5*z^5 - 9856*t^5*z^4 + 39424*t^5*z^3 - 64976*t^5*z^2 + 29200*t^5*z + 10832*t^5 - 1120*t^4*z^8 + 19040*t^4*z^7 - 133280*t^4*z^6 + 489200*t^4*z^5 - 982960*t^4*z^4 + 999280*t^4*z^3 - 361104*t^4*z^2 - 28080*t^4*z - 26928*t^4 + 896*t^3*z^11 - 20608*t^3*z^10 + 206080*t^3*z^9 - 1169520*t^3*z^8 + 4116720*t^3*z^7 - 9198288*t^3*z^6 + 12746320*t^3*z^5 - 10080416*t^3*z^4 + 3668816*t^3*z^3 - 302496*t^3*z^2 + 57360*t^3*z + 32784*t^3 - 448*t^2*z^14 + 12992*t^2*z^13 - 168896*t^2*z^12 + 1296496*t^2*z^11 - 6511760*t^2*z^10 + 22387184*t^2*z^9 - 53488880*t^2*z^8 + 88183936*t^2*z^7 - 97285552*t^2*z^6 + 67339328*t^2*z^5 - 25807504*t^2*z^4 + 4303168*t^2*z^3 - 279664*t^2*z^2 - 23440*t^2*z - 18320*t^2 + 128*t*z^17 - 4480*t*z^16 + 71680*t*z^15 - 693616*t*z^14 + 4524464*t*z^13 - 20985488*t*z^12 + 71114592*t*z^11 - 178027488*t*z^10 + 328800240*t*z^9 - 442127504*t*z^8 + 421178416*t*z^7 - 271186384*t*z^6 + 109161264*t*z^5 - 24143472*t*z^4 + 2401632*t*z^3 - 61232*t*z^2 + 2320*t*z + 2144*t - 16*z^20 + 656*z^19 - 12464*z^18 + 145536*z^17 - 1167600*z^16 + 6815904*z^15 - 29903024*z^14 + 100403584*z^13 - 260223136*z^12 + 521131840*z^11 - 801636704*z^10 + 934607744*z^9 - 807518128*z^8 + 499359728*z^7 - 209509280*z^6 + 54816352*z^5 - 7715744*z^4 + 368384*z^3 + 34944*z^2 - 2400*z + 1344)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_15 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 15) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_15 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z^3 + 384*t^7*z^2 - 640*t^7*z + 16*t^7 + 160*t^6*z^6 - 1920*t^6*z^5 + 8768*t^6*z^4 - 18272*t^6*z^3 + 15616*t^6*z^2 - 2048*t^6*z + 16*t^6 - 256*t^5*z^9 + 4608*t^5*z^8 - 34752*t^5*z^7 + 141168*t^5*z^6 - 329088*t^5*z^5 + 429360*t^5*z^4 - 274912*t^5*z^3 + 56496*t^5*z^2 - 1776*t^5*z - 32*t^5 + 304*t^4*z^12 - 7296*t^4*z^11 + 76672*t^4*z^10 - 461968*t^4*z^9 + 1753728*t^4*z^8 - 4334160*t^4*z^7 + 6941392*t^4*z^6 - 6913296*t^4*z^5 + 3894112*t^4*z^4 - 1020320*t^4*z^3 + 91632*t^4*z^2 - 496*t^4*z - 176*t^4 - 256*t^3*z^15 + 7680*t^3*z^14 - 103616*t^3*z^13 + 829232*t^3*z^12 - 4370560*t^3*z^11 + 15919280*t^3*z^10 - 40879520*t^3*z^9 + 74070816*t^3*z^8 - 93147824*t^3*z^7 + 78344784*t^3*z^6 - 41232928*t^3*z^5 + 12102640*t^3*z^4 - 1619760*t^3*z^3 + 55312*t^3*z^2 + 1312*t^3*z + 112*t^3 + 160*t^2*z^18 - 5760*t^2*z^17 + 94848*t^2*z^16 - 945744*t^2*z^15 + 6370944*t^2*z^14 - 30626544*t^2*z^13 + 108169328*t^2*z^12 - 284627760*t^2*z^11 + 559640352*t^2*z^10 - 816812336*t^2*z^9 + 870308448*t^2*z^8 - 657641520*t^2*z^7 + 336637792*t^2*z^6 - 108680160*t^2*z^5 + 19723392*t^2*z^4 - 1624448*t^2*z^3 + 27456*t^2*z^2 + 1776*t^2*z + 16*t^2 - 64*t*z^21 + 2688*t*z^20 - 52288*t*z^19 + 624928*t*z^18 - 5132928*t*z^17 + 30703056*t*z^16 - 138267776*t*z^15 + 477964944*t*z^14 - 1281351920*t*z^13 + 2673160000*t*z^12 - 4328961984*t*z^11 + 5396636576*t*z^10 - 5102360256*t*z^9 + 3575027904*t*z^8 - 1793332912*t*z^7 + 611653584*t*z^6 - 131027088*t*z^5 + 15519776*t*z^4 - 825696*t*z^3 + 26064*t*z^2 - 3184*t*z + 160*t + 16*z^24 - 768*z^23 + 17216*z^22 - 239408*z^21 + 2313856*z^20 - 16503152*z^19 + 90021792*z^18 - 384090816*z^17 + 1300103824*z^16 - 3520632336*z^15 + 7657118384*z^14 - 13377117968*z^13 + 18706839472*z^12 - 20789131808*z^11 + 18149404800*z^10 - 12239321088*z^9 + 6224698144*z^8 - 2307414384*z^7 + 592780560*z^6 - 97078592*z^5 + 8307600*z^4 - 20848*z^3 - 63008*z^2 + 5056*z - 128:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z^2 + 800*t^6*z - 928*t^6 + 256*t^5*z^5 - 2816*t^5*z^4 + 11456*t^5*z^3 - 19504*t^5*z^2 + 9392*t^5*z + 3904*t^5 - 304*t^4*z^8 + 5168*t^4*z^7 - 36240*t^4*z^6 + 133504*t^4*z^5 - 270192*t^4*z^4 + 278672*t^4*z^3 - 103728*t^4*z^2 - 9248*t^4*z - 7088*t^4 + 256*t^3*z^11 - 5888*t^3*z^10 + 58816*t^3*z^9 - 333040*t^3*z^8 + 1168496*t^3*z^7 - 2600832*t^3*z^6 + 3591616*t^3*z^5 - 2836848*t^3*z^4 + 1032112*t^3*z^3 - 70368*t^3*z^2 + 4384*t^3*z + 6944*t^3 - 160*t^2*z^14 + 4640*t^2*z^13 - 60128*t^2*z^12 + 458608*t^2*z^11 - 2281616*t^2*z^10 + 7749056*t^2*z^9 - 18254320*t^2*z^8 + 29649200*t^2*z^7 - 32261408*t^2*z^6 + 22110064*t^2*z^5 - 8430368*t^2*z^4 + 1347584*t^2*z^3 - 37632*t^2*z^2 - 2448*t^2*z - 2640*t^2 + 64*t*z^17 - 2240*t*z^16 + 35712*t*z^15 - 343072*t*z^14 + 2213472*t*z^13 - 10117808*t*z^12 + 33674224*t*z^11 - 82545216*t*z^10 + 148940336*t*z^9 - 195433024*t*z^8 + 181730160*t*z^7 - 114395216*t*z^6 + 44966976*t*z^5 - 9451744*t*z^4 + 741152*t*z^3 - 10080*t*z^2 - 528*t*z - 1392*t - 16*z^20 + 656*z^19 - 12400*z^18 + 143296*z^17 - 1131920*z^16 + 6473712*z^15 - 27700160*z^14 + 90359072*z^13 - 226866464*z^12 + 439465088*z^11 - 654159536*z^10 + 740199200*z^9 - 624624400*z^8 + 381230832*z^7 - 160294240*z^6 + 42835360*z^5 - 6260208*z^4 + 313136*z^3 + 31424*z^2 - 2368*z + 1184)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_16 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 16) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_16 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 24*z^5 + 108*z^4 - 226*z^3 + 222*z^2 - 90*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_17 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 17) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_17 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 24*z^5 + 108*z^4 - 228*z^3 + 234*z^2 - 108*z + 12:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_18 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 18) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_18 z t hf hn0 hn1 hn2 hn3
  · have hr : (1296*t*z^4 - 7776*t*z^3 + 11664*t*z^2 - 1296*t*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1296*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_19 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 19) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_19 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^3 + 12*t*z^2 - 18*t*z - 2*t + 2*z^6 - 24*z^5 + 108*z^4 - 224*z^3 + 210*z^2 - 72*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 192*t^6*z^6 - 2304*t^6*z^5 + 10368*t^6*z^4 - 21552*t^6*z^3 + 20896*t^6*z^2 - 7104*t^6*z + 768*t^6 - 1152*t^5*z^7 + 13392*t^5*z^6 - 57024*t^5*z^5 + 105984*t^5*z^4 - 75056*t^5*z^3 - 2592*t^5*z^2 + 12384*t^5*z - 1728*t^5 + 864*t^4*z^12 - 20736*t^4*z^11 + 217728*t^4*z^10 - 1313712*t^4*z^9 + 5033952*t^4*z^8 - 12782016*t^4*z^7 + 21764160*t^4*z^6 - 24562368*t^4*z^5 + 17751568*t^4*z^4 - 7780368*t^4*z^3 + 1955376*t^4*z^2 - 257904*t^4*z + 13680*t^4 - 3456*t^3*z^13 + 81648*t^3*z^12 - 839808*t^3*z^11 + 4928256*t^3*z^10 - 18157344*t^3*z^9 + 43489728*t^3*z^8 - 67540608*t^3*z^7 + 65056512*t^3*z^6 - 33886976*t^3*z^5 + 4448400*t^3*z^4 + 4097712*t^3*z^3 - 2052432*t^3*z^2 + 349200*t^3*z - 20304*t^3 + 1728*t^2*z^18 - 62208*t^2*z^17 + 1026432*t^2*z^16 - 10286352*t^2*z^15 + 69950304*t^2*z^14 - 341610048*t^2*z^13 + 1236746880*t^2*z^12 - 3378132864*t^2*z^11 + 7018127136*t^2*z^10 - 11097292896*t^2*z^9 + 13279428576*t^2*z^8 - 11885180256*t^2*z^7 + 7818027424*t^2*z^6 - 3694556448*t^2*z^5 + 1219730544*t^2*z^4 - 271192320*t^2*z^3 + 38349936*t^2*z^2 - 3090096*t^2*z + 107136*t^2 - 3456*t*z^19 + 123120*t*z^18 - 2006208*t*z^17 + 19802880*t*z^16 - 132178608*t*z^15 + 630589536*t*z^14 - 2215597536*t*z^13 + 5819048640*t*z^12 - 11468080512*t*z^11 + 16850295216*t*z^10 - 18110746800*t*z^9 + 13677470064*t*z^8 - 6611819312*t*z^7 + 1437438192*t*z^6 + 396883008*t*z^5 - 405569808*t*z^4 + 135935424*t*z^3 - 23750928*t*z^2 + 2137968*t*z - 77760*t + 1296*z^24 - 62208*z^23 + 1399680*z^22 - 19617552*z^21 + 191983392*z^20 - 1393713216*z^19 + 7783594560*z^18 - 34228204992*z^17 + 120325709520*z^16 - 341406266256*z^15 + 786154791024*z^14 - 1472400361008*z^13 + 2241610088304*z^12 - 2765248307712*z^11 + 2748607287408*z^10 - 2183810609184*z^9 + 1372447583440*z^8 - 673400880624*z^7 + 253824229920*z^6 - 72017162208*z^5 + 14971064832*z^4 - 2193488640*z^3 + 212920704*z^2 - 12208320*z + 311040:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6*z^2 + 960*t^6*z - 960*t^6 + 1152*t^5*z^3 - 5328*t^5*z^2 + 3600*t^5*z + 3024*t^5 - 864*t^4*z^8 + 14688*t^4*z^7 - 102816*t^4*z^6 + 381456*t^4*z^5 - 805968*t^4*z^4 + 962640*t^4*z^3 - 587664*t^4*z^2 + 142560*t^4*z - 19264*t^4 + 3456*t^3*z^9 - 57456*t^3*z^8 + 389232*t^3*z^7 - 1371600*t^3*z^6 + 2643792*t^3*z^5 - 2609472*t^3*z^4 + 899184*t^3*z^3 + 292320*t^3*z^2 - 174928*t^3*z + 37568*t^3 - 1728*t^2*z^14 + 50112*t^2*z^13 - 651456*t^2*z^12 + 5010768*t^2*z^11 - 25351920*t^2*z^10 + 88734096*t^2*z^9 - 219943728*t^2*z^8 + 388423296*t^2*z^7 - 484727184*t^2*z^6 + 417992544*t^2*z^5 - 239970096*t^2*z^4 + 87253200*t^2*z^3 - 19006144*t^2*z^2 + 2215328*t^2*z - 141536*t^2 + 3456*t*z^15 - 98928*t*z^14 + 1265328*t*z^13 - 9532944*t*z^12 + 46938528*t*z^11 - 158337072*t*z^10 + 372569760*t*z^9 - 609300144*t*z^8 + 673367760*t*z^7 - 467623728*t*z^6 + 163261152*t*z^5 + 8332416*t*z^4 - 29867488*t*z^3 + 10548512*t*z^2 - 1500416*t*z + 115408*t - 1296*z^20 + 53136*z^19 - 1009584*z^18 + 11796192*z^17 - 94849488*z^16 + 556490304*z^15 - 2464890480*z^14 + 8412515280*z^13 - 22382863920*z^12 + 46675390752*z^11 - 76301948160*z^10 + 97355826720*z^9 - 96106037088*z^8 + 72433497984*z^7 - 40939720368*z^6 + 16959471408*z^5 - 5001177472*z^4 + 1008777680*z^3 - 130809920*z^2 + 9714064*z - 328592)*hf
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 - 48*t^6*z^3 + 736*t^6*z^2 - 192*t^6*z + 288*t^5*z^4 - 2480*t^5*z^3 + 1296*t^5*z^2 + 1440*t^5*z - 720*t^4*z^5 + 5008*t^4*z^4 - 3504*t^4*z^3 - 5328*t^4*z^2 + 1296*t^4*z - 144*t^4 + 960*t^3*z^6 - 6368*t^3*z^5 + 6144*t^3*z^4 + 9072*t^3*z^3 - 6480*t^3*z^2 - 3312*t^3*z + 432*t^3 - 720*t^2*z^7 + 5056*t^2*z^6 - 6912*t^2*z^5 - 7920*t^2*z^4 + 12960*t^2*z^3 + 3024*t^2*z^2 - 432*t^2*z + 288*t*z^8 - 2288*t*z^7 + 4416*t*z^6 + 2736*t*z^5 - 10368*t*z^4 - 3312*t*z^3 + 11232*t*z^2 - 1296*t*z - 48*z^9 + 448*z^8 - 1200*z^7 + 3888*z^5 - 4032*z^4 + 432*z^3:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-288*t^5 + 720*t^4*z + 32*t^4 - 960*t^3*z^2 - 352*t^3*z + 4832*t^3 + 720*t^2*z^3 - 16*t^2*z^2 - 3280*t^2*z - 9056*t^2 - 288*t*z^4 + 272*t*z^3 + 1520*t*z^2 + 1792*t*z + 4096*t + 48*z^5 - 112*z^4 - 256*z^3 + 160*z^2 - 128*z - 1040)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_20 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 20) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_20 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 24*z^5 + 108*z^4 - 228*z^3 + 234*z^2 - 108*z + 12:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_21 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 21) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_21 z t hf hn0 hn1 hn2 hn3
  · have hr : (-6*z^3 + 36*z^2 - 54*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_22 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 22) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_22 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 24*z^5 + 104*z^4 - 200*z^3 + 176*z^2 - 70*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 6)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_23 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 23) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : (t - z^2 + 3*z - 2:ℝ)=0 := by
  apply cell_5_23 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z^3 + 24*t*z^2 - 36*t*z + 2*t + 2*z^6 - 24*z^5 + 108*z^4 - 224*z^3 + 210*z^2 - 72*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf
  · have hr : (16*t^8 - 64*t^7*z^3 + 384*t^7*z^2 - 704*t^7*z + 80*t^7 + 160*t^6*z^6 - 1920*t^6*z^5 + 9088*t^6*z^4 - 20512*t^6*z^3 + 20704*t^6*z^2 - 5552*t^6*z + 352*t^6 - 256*t^5*z^9 + 4608*t^5*z^8 - 35520*t^5*z^7 + 151152*t^5*z^6 - 380928*t^5*z^5 + 563712*t^5*z^4 - 451088*t^5*z^3 + 159360*t^5*z^2 - 21120*t^5*z + 896*t^5 + 304*t^4*z^12 - 7296*t^4*z^11 + 77888*t^4*z^10 - 485072*t^4*z^9 + 1941792*t^4*z^8 - 5186208*t^4*z^7 + 9276224*t^4*z^6 - 10844496*t^4*z^5 + 7835104*t^4*z^4 - 3184416*t^4*z^3 + 655632*t^4*z^2 - 61360*t^4*z + 2032*t^4 - 256*t^3*z^15 + 7680*t^3*z^14 - 104896*t^3*z^13 + 861232*t^3*z^12 - 4726144*t^3*z^11 + 18228512*t^3*z^10 - 50571120*t^3*z^9 + 101505792*t^3*z^8 - 146199776*t^3*z^7 + 147783616*t^3*z^6 - 100925360*t^3*z^5 + 44034768*t^3*z^4 - 11436496*t^3*z^3 + 1633616*t^3*z^2 - 117904*t^3*z + 3440*t^3 + 160*t^2*z^18 - 5760*t^2*z^17 + 95808*t^2*z^16 - 975504*t^2*z^15 + 6789984*t^2*z^14 - 34169376*t^2*z^13 + 128200384*t^2*z^12 - 364455840*t^2*z^11 + 789878160*t^2*z^10 - 1302472144*t^2*z^9 + 1618528944*t^2*z^8 - 1489501200*t^2*z^7 + 988871920*t^2*z^6 - 456879168*t^2*z^5 + 140347488*t^2*z^4 - 27171440*t^2*z^3 + 3113520*t^2*z^2 - 190464*t^2*z + 4768*t^2 - 64*t*z^21 + 2688*t*z^20 - 52736*t*z^19 + 641504*t*z^18 - 5415744*t*z^17 + 33652608*t*z^16 - 159281680*t*z^15 + 586228176*t*z^14 - 1697825984*t*z^13 + 3891042816*t*z^12 - 7059424272*t*z^11 + 10096247072*t*z^10 - 11281628496*t*z^9 + 9713195712*t*z^8 - 6318903872*t*z^7 + 3026657632*t*z^6 - 1033095840*t*z^5 + 241684672*t*z^4 - 37069280*t*z^3 + 3535248*t*z^2 - 191120*t*z + 4544*t + 16*z^24 - 768*z^23 + 17344*z^22 - 244912*z^21 + 2424064*z^20 - 17867600*z^19 + 101719040*z^18 - 457784160*z^17 + 1653507424*z^16 - 4839170048*z^15 + 11536163920*z^14 - 22443489456*z^13 + 35591198784*z^12 - 45817107328*z^11 + 47538435360*z^10 - 39343653184*z^9 + 25609690576*z^8 - 12873403936*z^7 + 4882743472*z^6 - 1357071872*z^5 + 266111936*z^4 - 34927440*z^3 + 2823520*z^2 - 120128*z + 1792:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z^2 + 800*t^6*z - 1248*t^6 + 256*t^5*z^5 - 2816*t^5*z^4 + 12224*t^5*z^3 - 24112*t^5*z^2 + 18224*t^5*z + 2032*t^5 - 304*t^4*z^8 + 5168*t^4*z^7 - 37456*t^4*z^6 + 148096*t^4*z^5 - 339088*t^4*z^4 + 434432*t^4*z^3 - 265744*t^4*z^2 + 41440*t^4*z - 10064*t^4 + 256*t^3*z^11 - 5888*t^3*z^10 + 60096*t^3*z^9 - 356080*t^3*z^8 + 1344880*t^3*z^7 - 3342576*t^3*z^6 + 5436032*t^3*z^5 - 5542384*t^3*z^4 + 3213152*t^3*z^3 - 867344*t^3*z^2 + 94720*t^3*z + 18688*t^3 - 160*t^2*z^14 + 4640*t^2*z^13 - 61088*t^2*z^12 + 481648*t^2*z^11 - 2525936*t^2*z^10 + 9251408*t^2*z^9 - 24163152*t^2*z^8 + 45104928*t^2*z^7 - 59322336*t^2*z^6 + 53190176*t^2*z^5 - 30682432*t^2*z^4 + 10378096*t^2*z^3 - 1827456*t^2*z^2 + 144000*t^2*z - 47904*t^2 + 64*t*z^17 - 2240*t*z^16 + 36160*t*z^15 - 356512*t*z^14 + 2395936*t*z^13 - 11598368*t*z^12 + 41661744*t*z^11 - 112694816*t*z^10 + 230514976*t*z^9 - 354818240*t*z^8 + 405266656*t*z^7 - 335110496*t*z^6 + 193060944*t*z^5 - 73270672*t*z^4 + 17005328*t*z^3 - 2232880*t*z^2 + 164768*t*z + 42320*t - 16*z^20 + 656*z^19 - 12528*z^18 + 147904*z^17 - 1208080*z^16 + 7239504*z^15 - 32933632*z^14 + 116083136*z^13 - 320730512*z^12 + 698184000*z^11 - 1197050032*z^10 + 1607636000*z^9 - 1672843824*z^8 + 1325712304*z^7 - 780497664*z^6 + 329810688*z^5 - 95506208*z^4 + 17817232*z^3 - 1952768*z^2 + 100896*z - 22848)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_24 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 24) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_24 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^18 + 46656*t*z^17 - 765936*t*z^16 + 7594560*t*z^15 - 50785056*t*z^14 + 242236656*t*z^13 - 850249872*t*z^12 + 2233902240*t*z^11 - 4427371872*t*z^10 + 6623363520*t*z^9 - 7439706144*t*z^8 + 6207324192*t*z^7 - 3786333984*t*z^6 + 1653702480*t*z^5 - 503717616*t*z^4 + 103214736*t*z^3 - 13423968*t*z^2 + 990144*t*z - 31104*t + 1296*z^24 - 62208*z^23 + 1394496*z^22 - 19394640*z^21 + 187531200*z^20 - 1338872976*z^19 + 7317090288*z^18 - 31319799552*z^17 + 106561081872*z^16 - 290862397152*z^15 + 640195996032*z^14 - 1138364671392*z^13 + 1633788769968*z^12 - 1886213865168*z^11 + 1741919078448*z^10 - 1276967783808*z^9 + 736061059008*z^8 - 329862724272*z^7 + 113408202384*z^6 - 29416391568*z^5 + 5625145440*z^4 - 765460368*z^3 + 69836256*z^2 - 3810240*z + 93312:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^14 - 37584*t*z^13 + 484704*t*z^12 - 3665088*t*z^11 + 18041616*t*z^10 - 60718896*t*z^9 + 142829568*t*z^8 - 236032704*t*z^7 + 271736208*t*z^6 - 213396768*t*z^5 + 110530656*t*z^4 - 36132480*t*z^3 + 7067088*t*z^2 - 736128*t*z + 34992*t - 1296*z^20 + 53136*z^19 - 1004400*z^18 + 11609568*z^17 - 91776240*z^16 + 525817008*z^15 - 2257622928*z^14 + 7409181456*z^13 - 18791778384*z^12 + 37004607648*z^11 - 56547770544*z^10 + 66722361984*z^9 - 60234808896*z^8 + 41070363120*z^7 - 20812545648*z^6 + 7694047440*z^5 - 2029374000*z^4 + 369713808*z^3 - 44044560*z^2 + 3046896*z - 108864)*hf
  · have hr : (1296*t*z^7 - 15552*t*z^6 + 68688*t*z^5 - 139968*t*z^4 + 130896*t*z^3 - 46656*t*z^2 + 5184*t*z - 1296*z^9 + 18144*z^8 - 101088*z^7 + 292896*z^6 - 479520*z^5 + 448416*z^4 - 229392*z^3 + 57024*z^2 - 5184*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1296*t*z^3 + 6480*t*z^2 - 5184*t*z + 2592*t + 1296*z^5 - 9072*z^4 + 19440*z^3 - 19440*z^2 - 2592*z - 29808)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_25 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 25) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_25 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 24*z^5 + 104*z^4 - 200*z^3 + 176*z^2 - 70*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 6)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_26 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 26) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_26 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 24*z^5 + 104*z^4 - 198*z^3 + 164*z^2 - 54*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 6)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_27 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 27) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_27 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^3 + 12*t*z^2 - 20*t*z + 2*z^6 - 24*z^5 + 106*z^4 - 210*z^3 + 182*z^2 - 54*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 8)*hf
  · have hr : (16*t^8 - 192*t^7*z + 16*t^7 + 192*t^6*z^6 - 2304*t^6*z^5 + 10176*t^6*z^4 - 20208*t^6*z^3 + 18624*t^6*z^2 - 5616*t^6*z + 400*t^6 - 1728*t^5*z^7 + 20880*t^5*z^6 - 93312*t^5*z^5 + 189504*t^5*z^4 - 176688*t^5*z^3 + 62784*t^5*z^2 - 7488*t^5*z + 256*t^5 + 864*t^4*z^12 - 20736*t^4*z^11 + 216000*t^4*z^10 - 1280880*t^4*z^9 + 4774464*t^4*z^8 - 11669616*t^4*z^7 + 18922320*t^4*z^6 - 20068992*t^4*z^5 + 13343040*t^4*z^4 - 5170464*t^4*z^3 + 1076832*t^4*z^2 - 106464*t^4*z + 3856*t^4 - 5184*t^3*z^13 + 124848*t^3*z^12 - 1306368*t^3*z^11 + 7793280*t^3*z^10 - 29261088*t^3*z^9 + 72083520*t^3*z^8 - 117888480*t^3*z^7 + 126691392*t^3*z^6 - 86757840*t^3*z^5 + 36048912*t^3*z^4 - 8613120*t^3*z^3 + 1110576*t^3*z^2 - 71856*t^3*z + 1936*t^3 + 1728*t^2*z^18 - 62208*t^2*z^17 + 1021248*t^2*z^16 - 10125648*t^2*z^15 + 67708224*t^2*z^14 - 322990416*t^2*z^13 + 1134121392*t^2*z^12 - 2981696832*t^2*z^11 + 5912886816*t^2*z^10 - 8840688192*t^2*z^9 + 9890910432*t^2*z^8 - 8159444064*t^2*z^7 + 4855519152*t^2*z^6 - 2025407376*t^2*z^5 + 572136192*t^2*z^4 - 104793696*t^2*z^3 + 11688912*t^2*z^2 - 710928*t^2*z + 17872*t^2 - 5184*t*z^19 + 187056*t*z^18 - 3079296*t*z^17 + 30632256*t*z^16 - 205632432*t*z^15 + 985322880*t*z^14 - 3477009888*t*z^13 + 9191558592*t*z^12 - 18341439120*t*z^11 + 27636374448*t*z^10 - 31256398368*t*z^9 + 26222197824*t*z^8 - 16038559008*t*z^7 + 6997591440*t*z^6 - 2124561312*t*z^5 + 437102928*t*z^4 - 59253264*t*z^3 + 5121504*t*z^2 - 264432*t*z + 6496*t + 1296*z^24 - 62208*z^23 + 1394496*z^22 - 19394640*z^21 + 187531200*z^20 - 1338867792*z^19 + 7316900208*z^18 - 31316611392*z^17 + 106528662432*z^16 - 290639044512*z^15 + 639092179872*z^14 - 1134322429248*z^13 + 1622612714400*z^12 - 1862655499872*z^11 + 1703934436032*z^10 - 1230216791760*z^9 + 692431386624*z^8 - 299327837184*z^7 + 97623123024*z^6 - 23505797952*z^5 + 4062597072*z^4 - 484218192*z^3 + 37333056*z^2 - 1653120*z + 31360:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6*z^2 + 960*t^6*z - 768*t^6 + 1728*t^5*z^3 - 8784*t^5*z^2 + 7632*t^5*z + 720*t^5 - 864*t^4*z^8 + 14688*t^4*z^7 - 101088*t^4*z^6 + 360720*t^4*z^5 - 715824*t^4*z^4 + 785376*t^4*z^3 - 416304*t^4*z^2 + 72288*t^4*z - 9936*t^4 + 5184*t^3*z^9 - 88560*t^3*z^8 + 613872*t^3*z^7 - 2214864*t^3*z^6 + 4449168*t^3*z^5 - 4931712*t^3*z^4 + 2745360*t^3*z^3 - 621696*t^3*z^2 + 68064*t^3*z + 25872*t^3 - 1728*t^2*z^14 + 50112*t^2*z^13 - 646272*t^2*z^12 + 4886352*t^2*z^11 - 24053328*t^2*z^10 + 80987904*t^2*z^9 - 190722384*t^2*z^8 + 315496512*t^2*z^7 - 362341296*t^2*z^6 + 280580976*t^2*z^5 - 139370976*t^2*z^4 + 41486688*t^2*z^3 - 6929568*t^2*z^2 + 537984*t^2*z - 91872*t^2 + 5184*t*z^15 - 150768*t*z^14 + 1951344*t*z^13 - 14820624*t*z^12 + 73357920*t*z^11 - 248567184*t*z^10 + 589512384*t*z^9 - 983347344*t*z^8 + 1142938944*t*z^7 - 904272768*t*z^6 + 469052640*t*z^5 - 152151696*t*z^4 + 29639088*t*z^3 - 3300192*t*z^2 + 246528*t*z + 89856*t - 1296*z^20 + 53136*z^19 - 1004400*z^18 + 11609568*z^17 - 91776240*z^16 + 525811824*z^15 - 2257469136*z^14 + 7407142416*z^13 - 18775826784*z^12 + 36922698288*z^11 - 56257108416*z^10 + 65991137616*z^9 - 58917820176*z^8 + 39375266400*z^7 - 19271879424*z^6 + 6726207168*z^5 - 1621673136*z^4 + 258923088*z^3 - 25700736*z^2 + 1377312*z - 87744)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_28 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 28) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_28 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^3 + 12*t*z^2 - 18*t*z - 2*t + 2*z^6 - 24*z^5 + 108*z^4 - 224*z^3 + 210*z^2 - 72*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf
  · have hr : (16*t^8 - 192*t^7*z^3 + 1152*t^7*z^2 - 1664*t^7*z + 144*t^7 + 1056*t^6*z^6 - 12672*t^6*z^5 + 56448*t^6*z^4 - 112512*t^6*z^3 + 92032*t^6*z^2 - 17088*t^6*z + 1008*t^6 - 3456*t^5*z^9 + 62208*t^5*z^8 - 464256*t^5*z^7 + 1849392*t^5*z^6 - 4205376*t^5*z^5 + 5377824*t^5*z^4 - 3507440*t^5*z^3 + 925920*t^5*z^2 - 106560*t^5*z + 4320*t^5 + 7344*t^4*z^12 - 176256*t^4*z^11 + 1845504*t^4*z^10 - 11044944*t^4*z^9 + 41558688*t^4*z^8 - 101780928*t^4*z^7 + 162189600*t^4*z^6 - 163043712*t^4*z^5 + 96802864*t^4*z^4 - 30820896*t^4*z^3 + 5226192*t^4*z^2 - 447120*t^4*z + 15408*t^4 - 10368*t^3*z^15 + 311040*t^3*z^14 - 4192128*t^3*z^13 + 33492528*t^3*z^12 - 176211072*t^3*z^11 + 641208096*t^3*z^10 - 1648789296*t^3*z^9 + 3006264096*t^3*z^8 - 3842128800*t^3*z^7 + 3352275456*t^3*z^6 - 1916426336*t^3*z^5 + 684482736*t^3*z^4 - 149193216*t^3*z^3 + 19207152*t^3*z^2 - 1336464*t^3*z + 38448*t^3 + 9504*t^2*z^18 - 342144*t^2*z^17 + 5640192*t^2*z^16 - 56377296*t^2*z^15 + 381342816*t^2*z^14 - 1844498304*t^2*z^13 + 6571771488*t^2*z^12 - 17504652096*t^2*z^11 + 35009965008*t^2*z^10 - 52358968080*t^2*z^9 + 57852747792*t^2*z^8 - 46309933728*t^2*z^7 + 26169043264*t^2*z^6 - 10154284560*t^2*z^5 + 2647294560*t^2*z^4 - 452564928*t^2*z^3 + 48537360*t^2*z^2 - 2965680*t^2*z + 79056*t^2 - 5184*t*z^21 + 217728*t*z^20 - 4243968*t*z^19 + 50940576*t*z^18 - 421262208*t*z^17 + 2544169824*t*z^16 - 11605210416*t*z^15 + 40785132960*t*z^14 - 111647713824*t*z^13 + 239120673264*t*z^12 - 400319620704*t*z^11 + 520906132656*t*z^10 - 521547921984*t*z^9 + 396179337744*t*z^8 - 224450654768*t*z^7 + 93123896976*t*z^6 - 27798591168*t*z^5 + 5850471888*t*z^4 - 841911696*t*z^3 + 78456816*t*z^2 - 4246992*t*z + 101088*t + 1296*z^24 - 62208*z^23 + 1399680*z^22 - 19612368*z^21 + 191765664*z^20 - 1389472704*z^19 + 7732769328*z^18 - 33808669056*z^17 + 117796728816*z^16 - 329887133136*z^15 + 745688544048*z^14 - 1361461167792*z^13 + 2002940021712*z^12 - 2362094721504*z^11 + 2215921704480*z^10 - 1637471392176*z^9 + 942373035232*z^8 - 417273241488*z^7 + 140357274048*z^6 - 35336780496*z^5 + 6523055568*z^4 - 854413920*z^3 + 74994336*z^2 - 3942432*z + 93312:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6*z^2 + 5280*t^6*z - 4704*t^6 + 3456*t^5*z^5 - 38016*t^5*z^4 + 149760*t^5*z^3 - 241200*t^5*z^2 + 112752*t^5*z + 24336*t^5 - 7344*t^4*z^8 + 124848*t^4*z^7 - 868752*t^4*z^6 + 3157056*t^4*z^5 - 6290640*t^4*z^4 + 6472800*t^4*z^3 - 2685840*t^4*z^2 + 141456*t^4*z - 137872*t^4 + 10368*t^3*z^11 - 238464*t^3*z^10 + 2377728*t^3*z^9 - 13426992*t^3*z^8 + 47015856*t^3*z^7 - 104858928*t^3*z^6 + 146761152*t^3*z^5 - 121357200*t^3*z^4 + 52084992*t^3*z^3 - 9731568*t^3*z^2 + 1496720*t^3*z + 273392*t^3 - 9504*t^2*z^14 + 275616*t^2*z^13 - 3577824*t^2*z^12 + 27397872*t^2*z^11 - 137253744*t^2*z^10 + 471253680*t^2*z^9 - 1128682512*t^2*z^8 + 1880895168*t^2*z^7 - 2134860480*t^2*z^6 + 1581698592*t^2*z^5 - 716967072*t^2*z^4 + 187604928*t^2*z^3 - 29820544*t^2*z^2 + 1636592*t^2*z - 544304*t^2 + 5184*t*z^17 - 181440*t*z^16 + 2901312*t*z^15 - 28049760*t*z^14 + 182838816*t*z^13 - 848209536*t*z^12 + 2880700848*t*z^11 - 7254533232*t*z^10 + 13567654224*t*z^9 - 18689812128*t*z^8 + 18626809968*t*z^7 - 13065326064*t*z^6 + 6229148736*t*z^5 - 1956439824*t*z^4 + 398075216*t*z^3 - 48696976*t*z^2 + 3991984*t*z + 271216*t - 1296*z^20 + 53136*z^19 - 1009584*z^18 + 11791008*z^17 - 94668048*z^16 + 553592448*z^15 - 2436931872*z^14 + 8230716288*z^13 - 21541260960*z^12 + 43819230960*z^11 - 69093611712*z^10 + 83775848400*z^9 - 77103410304*z^8 + 52940847120*z^7 - 26587631472*z^6 + 9582981360*z^5 - 2435137840*z^4 + 423638672*z^3 - 48391232*z^2 + 3016384*z - 216416)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_29 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 29) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : (t - 2*z^3 + 13*z^2 - 21*z + 3:ℝ)=0 := by
  apply cell_5_29 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z^3 + 24*t*z^2 - 36*t*z + 2*t + 2*z^6 - 24*z^5 + 108*z^4 - 224*z^3 + 210*z^2 - 72*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf
  · have hr : (16*t^8 - 256*t^7*z^3 + 1536*t^7*z^2 - 2240*t^7*z + 272*t^7 + 1792*t^6*z^6 - 21504*t^6*z^5 + 95872*t^6*z^4 - 192112*t^6*z^3 + 160960*t^6*z^2 - 34736*t^6*z + 2128*t^6 - 7168*t^5*z^9 + 129024*t^5*z^8 - 962304*t^5*z^7 + 3830784*t^5*z^6 - 8715648*t^5*z^5 + 11198544*t^5*z^4 - 7426304*t^5*z^3 + 2063904*t^5*z^2 - 243024*t^5*z + 10112*t^5 + 17920*t^4*z^12 - 430080*t^4*z^11 + 4497920*t^4*z^10 - 26857280*t^4*z^9 + 100723200*t^4*z^8 - 245687520*t^4*z^7 + 389815328*t^4*z^6 - 390320640*t^4*z^5 + 231096208*t^4*z^4 - 73373088*t^4*z^3 + 12205440*t^4*z^2 - 1002880*t^4*z + 32080*t^4 - 28672*t^3*z^15 + 860160*t^3*z^14 - 11576320*t^3*z^13 + 92212480*t^3*z^12 - 482913280*t^3*z^11 + 1746069632*t^3*z^10 - 4452489984*t^3*z^9 + 8032353024*t^3*z^8 - 10127155904*t^3*z^7 + 8679771088*t^3*z^6 - 4840621568*t^3*z^5 + 1666754304*t^3*z^4 - 344576608*t^3*z^3 + 41352992*t^3*z^2 - 2646304*t^3*z + 69776*t^3 + 28672*t^2*z^18 - 1032192*t^2*z^17 + 16988160*t^2*z^16 - 169238784*t^2*z^15 + 1138744320*t^2*z^14 - 5467464192*t^2*z^13 + 19290686464*t^2*z^12 - 50741382144*t^2*z^11 + 99877275648*t^2*z^10 - 146366423776*t^2*z^9 + 157541171232*t^2*z^8 - 121825829280*t^2*z^7 + 65705320096*t^2*z^6 - 23931978624*t^2*z^5 + 5745492336*t^2*z^4 - 886698800*t^2*z^3 + 84169536*t^2*z^2 - 4459344*t^2*z + 100816*t^2 - 16384*t*z^21 + 688128*t*z^20 - 13389824*t*z^19 + 160139264*t*z^18 - 1316812800*t*z^17 + 7889807616*t*z^16 - 35613260800*t*z^15 + 123488911872*t*z^14 - 332394088448*t*z^13 + 697110628800*t*z^12 - 1136944270464*t*z^11 + 1431775532672*t*z^10 - 1375371116352*t*z^9 + 990804513456*t*z^8 - 524248894592*t*z^7 + 199312217104*t*z^6 - 53388866400*t*z^5 + 9874421728*t*z^4 - 1225017008*t*z^3 + 96807936*t*z^2 - 4384496*t*z + 86240*t + 4096*z^24 - 196608*z^23 + 4415488*z^22 - 61631488*z^21 + 598982656*z^20 - 4303445504*z^19 + 23684155904*z^18 - 102092034048*z^17 + 349486266112*z^16 - 957713316992*z^15 + 2108168327296*z^14 - 3726338020992*z^13 + 5268785015808*z^12 - 5917077716320*z^11 + 5224187188896*z^10 - 3578883903856*z^9 + 1873571016016*z^8 - 737562986128*z^7 + 214915868032*z^6 - 45578152400*z^5 + 6881882192*z^4 - 714935088*z^3 + 48155584*z^2 - 1872416*z + 31360:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1792*t^6*z^2 + 8960*t^6*z - 8064*t^6 + 7168*t^5*z^5 - 78848*t^5*z^4 + 310016*t^5*z^3 - 499456*t^5*z^2 + 241280*t^5*z + 41776*t^5 - 17920*t^4*z^8 + 304640*t^4*z^7 - 2114560*t^4*z^6 + 7647040*t^4*z^5 - 15135040*t^4*z^4 + 15462560*t^4*z^3 - 6395968*t^4*z^2 + 345664*t^4*z - 297488*t^4 + 28672*t^3*z^11 - 659456*t^3*z^10 + 6558720*t^3*z^9 - 36839680*t^3*z^8 + 127909120*t^3*z^7 - 281821056*t^3*z^6 + 387738752*t^3*z^5 - 312574336*t^3*z^4 + 128315456*t^3*z^3 - 21791120*t^3*z^2 + 3333904*t^3*z + 756688*t^3 - 28672*t^2*z^14 + 831488*t^2*z^13 - 10766336*t^2*z^12 + 82004224*t^2*z^11 - 407305472*t^2*z^10 + 1381304576*t^2*z^9 - 3252477696*t^2*z^8 + 5295326208*t^2*z^7 - 5817562368*t^2*z^6 + 4107794144*t^2*z^5 - 1725651712*t^2*z^4 + 401324128*t^2*z^3 - 57011712*t^2*z^2 + 1351008*t^2*z - 1626576*t^2 + 16384*t*z^17 - 573440*t*z^16 + 9146368*t*z^15 - 87955456*t*z^14 + 568471552*t*z^13 - 2605385984*t*z^12 + 8704167168*t*z^11 - 21448610048*t*z^10 + 38983918336*t*z^9 - 51703936448*t*z^8 + 48948811072*t*z^7 - 31958788160*t*z^6 + 13760834304*t*z^5 - 3761214064*t*z^4 + 649599536*t*z^3 - 62560864*t*z^2 + 6000032*t*z + 1440944*t - 4096*z^20 + 167936*z^19 - 3182592*z^18 + 36969472*z^17 - 294292480*z^16 + 1700196864*z^15 - 7363744768*z^14 + 24351755264*z^13 - 62035685120*z^12 + 121928792448*z^11 - 183989401600*z^10 + 210771879296*z^9 - 180064213632*z^8 + 111977905504*z^7 - 49278423552*z^6 + 14958673584*z^5 - 3074913536*z^4 + 411867280*z^3 - 36195344*z^2 + 661200*z - 667200)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_30 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 30) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_30 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^3 + 12*t*z^2 - 20*t*z + 2*z^6 - 24*z^5 + 106*z^4 - 210*z^3 + 182*z^2 - 54*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 8)*hf
  · have hr : (16*t^8 - 176*t^7 - 48*t^6*z^3 + 288*t^6*z^2 - 480*t^6*z + 736*t^6 + 432*t^5*z^3 - 2592*t^5*z^2 + 4320*t^5*z - 1616*t^5 + 144*t^4*z^4 - 2016*t^4*z^3 + 8208*t^4*z^2 - 11664*t^4*z + 1936*t^4 - 1008*t^3*z^4 + 6864*t^3*z^3 - 13968*t^3*z^2 + 9168*t^3*z - 608*t^3 + 1296*t^2*z^4 - 7344*t^2*z^3 + 9072*t^2*z^2 + 3024*t^2*z - 992*t^2 + 1152*t*z^4 - 7488*t*z^3 + 13824*t*z^2 - 6912*t*z + 832*t - 288*z^4 + 1824*z^3 - 3168*z^2 + 1248*z - 128:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-144*t^4 + 1008*t^3 - 1296*t^2 - 1152*t + 288)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_31 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 31) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_31 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z^3 + 24*t*z^2 - 36*t*z + 2*z^6 - 24*z^5 + 108*z^4 - 222*z^3 + 198*z^2 - 54*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf
  · have hr : (16*t^8 - 192*t^7*z^3 + 1152*t^7*z^2 - 1792*t^7*z + 272*t^7 + 1056*t^6*z^6 - 12672*t^6*z^5 + 57600*t^6*z^4 - 120576*t^6*z^3 + 109312*t^6*z^2 - 28576*t^6*z + 2128*t^6 - 3456*t^5*z^9 + 62208*t^5*z^8 - 468864*t^5*z^7 + 1909296*t^5*z^6 - 4509504*t^5*z^5 + 6134400*t^5*z^4 - 4449424*t^5*z^3 + 1452192*t^5*z^2 - 204384*t^5*z + 10112*t^5 + 7344*t^4*z^12 - 176256*t^4*z^11 + 1855872*t^4*z^10 - 11241936*t^4*z^9 + 43144992*t^4*z^8 - 108815904*t^4*z^7 + 180863616*t^4*z^6 - 193197312*t^4*z^5 + 125536336*t^4*z^4 - 45728000*t^4*z^3 + 8910096*t^4*z^2 - 859184*t^4*z + 32080*t^4 - 10368*t^3*z^15 + 311040*t^3*z^14 - 4205952*t^3*z^13 + 33838128*t^3*z^12 - 180026496*t^3*z^11 + 665661888*t^3*z^10 - 1749376272*t^3*z^9 + 3283302816*t^3*z^8 - 4359241152*t^3*z^7 + 3999842784*t^3*z^6 - 2443708768*t^3*z^5 + 948992080*t^3*z^4 - 225412000*t^3*z^3 + 31261424*t^3*z^2 - 2307056*t^3*z + 69776*t^3 + 9504*t^2*z^18 - 342144*t^2*z^17 + 5650560*t^2*z^16 - 56698704*t^2*z^15 + 385852896*t^2*z^14 - 1882354464*t^2*z^13 + 6783350400*t^2*z^12 - 18333941760*t^2*z^11 + 37347980976*t^2*z^10 - 57143177712*t^2*z^9 + 64933557264*t^2*z^8 - 53777380608*t^2*z^7 + 31632342496*t^2*z^6 - 12822143664*t^2*z^5 + 3477531840*t^2*z^4 - 610456864*t^2*z^3 + 65921424*t^2*z^2 - 3958032*t^2*z + 100816*t^2 - 5184*t*z^21 + 217728*t*z^20 - 4247424*t*z^19 + 51068448*t*z^18 - 423439488*t*z^17 + 2566774656*t*z^16 - 11765034000*t*z^15 + 41599072800*t*z^14 - 114727069440*t*z^13 + 247917346704*t*z^12 - 419413031712*t*z^11 + 552335618448*t*z^10 - 560410567392*t*z^9 + 431641227024*t*z^8 - 247686765904*t*z^7 + 103638269744*t*z^6 - 30910973952*t*z^5 + 6406358608*t*z^4 - 891612752*t*z^3 + 78827568*t*z^2 - 3972112*t*z + 86240*t + 1296*z^24 - 62208*z^23 + 1399680*z^22 - 19612368*z^21 + 191765664*z^20 - 1389469248*z^19 + 7732641456*z^18 - 33806491776*z^17 + 117774113616*z^16 - 329726988144*z^15 + 744870094128*z^14 - 1358343942192*z^13 + 1993931423760*z^12 - 2342168205408*z^11 + 2182129738560*z^10 - 1593723753168*z^9 + 899551711456*z^8 - 386045531536*z^7 + 123713300800*z^6 - 28998798448*z^5 + 4842931024*z^4 - 554744992*z^3 + 40957792*z^2 - 1732864*z + 31360:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6*z^2 + 5280*t^6*z - 5856*t^6 + 3456*t^5*z^5 - 38016*t^5*z^4 + 154368*t^5*z^3 - 268848*t^5*z^2 + 158832*t^5*z + 14256*t^5 - 7344*t^4*z^8 + 124848*t^4*z^7 - 879120*t^4*z^6 + 3281472*t^4*z^5 - 6860880*t^4*z^4 + 7691328*t^4*z^3 - 3841104*t^4*z^2 + 462480*t^4*z - 132016*t^4 + 10368*t^3*z^11 - 238464*t^3*z^10 + 2391552*t^3*z^9 - 13675824*t^3*z^8 + 48895920*t^3*z^7 - 112558032*t^3*z^6 + 165129024*t^3*z^5 - 146744016*t^3*z^4 + 70866528*t^3*z^3 - 15770640*t^3*z^2 + 2101744*t^3*z + 185328*t^3 - 9504*t^2*z^14 + 275616*t^2*z^13 - 3588192*t^2*z^12 + 27646704*t^2*z^11 - 139876848*t^2*z^10 + 487181520*t^2*z^9 - 1190042064*t^2*z^8 + 2036444544*t^2*z^7 - 2394951264*t^2*z^6 + 1860777216*t^2*z^5 - 897200640*t^2*z^4 + 250040448*t^2*z^3 - 40081408*t^2*z^2 + 2625200*t^2*z - 491504*t^2 + 5184*t*z^17 - 181440*t*z^16 + 2904768*t*z^15 - 28153440*t*z^14 + 184241952*t*z^13 - 859513248*t*z^12 + 2940921648*t*z^11 - 7477346736*t*z^10 + 14152391280*t*z^9 - 19780867008*t*z^8 + 20053789200*t*z^7 - 14330478960*t*z^6 + 6944838528*t*z^5 - 2189471280*t*z^4 + 435106672*t*z^3 - 50737936*t*z^2 + 3706224*t*z + 240720*t - 1296*z^20 + 53136*z^19 - 1009584*z^18 + 11791008*z^17 - 94668048*z^16 + 553588992*z^15 - 2436828192*z^14 + 8229313152*z^13 - 21529946880*z^12 + 43758761328*z^11 - 68868175104*z^10 + 83175169680*z^9 - 75950747040*z^8 + 51356438448*z^7 - 25054678320*z^6 + 8569720656*z^5 - 1995915760*z^4 + 304167024*z^3 - 28867424*z^2 + 1341408*z - 145280)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_32 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 32) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_32 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_33 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 33) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_33 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^18 + 46656*t*z^17 - 765936*t*z^16 + 7594560*t*z^15 - 50785056*t*z^14 + 242236656*t*z^13 - 850249872*t*z^12 + 2233902240*t*z^11 - 4427371872*t*z^10 + 6623363520*t*z^9 - 7439706144*t*z^8 + 6207324192*t*z^7 - 3786333984*t*z^6 + 1653702480*t*z^5 - 503717616*t*z^4 + 103214736*t*z^3 - 13423968*t*z^2 + 990144*t*z - 31104*t + 1296*z^24 - 62208*z^23 + 1394496*z^22 - 19394640*z^21 + 187531200*z^20 - 1338872976*z^19 + 7317090288*z^18 - 31319799552*z^17 + 106561081872*z^16 - 290862397152*z^15 + 640195996032*z^14 - 1138364671392*z^13 + 1633788769968*z^12 - 1886213865168*z^11 + 1741919078448*z^10 - 1276967783808*z^9 + 736061059008*z^8 - 329862724272*z^7 + 113408202384*z^6 - 29416391568*z^5 + 5625145440*z^4 - 765460368*z^3 + 69836256*z^2 - 3810240*z + 93312:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^14 - 37584*t*z^13 + 484704*t*z^12 - 3665088*t*z^11 + 18041616*t*z^10 - 60718896*t*z^9 + 142829568*t*z^8 - 236032704*t*z^7 + 271736208*t*z^6 - 213396768*t*z^5 + 110530656*t*z^4 - 36132480*t*z^3 + 7067088*t*z^2 - 736128*t*z + 34992*t - 1296*z^20 + 53136*z^19 - 1004400*z^18 + 11609568*z^17 - 91776240*z^16 + 525817008*z^15 - 2257622928*z^14 + 7409181456*z^13 - 18791778384*z^12 + 37004607648*z^11 - 56547770544*z^10 + 66722361984*z^9 - 60234808896*z^8 + 41070363120*z^7 - 20812545648*z^6 + 7694047440*z^5 - 2029374000*z^4 + 369713808*z^3 - 44044560*z^2 + 3046896*z - 108864)*hf
  · have hr : (-1296*t*z^18 + 46656*t*z^17 - 762048*t*z^16 + 7474032*t*z^15 - 49105440*t*z^14 + 228326688*t*z^13 - 773975088*t*z^12 + 1941770880*t*z^11 - 3623762448*t*z^10 + 5014870704*t*z^9 - 5091298416*t*z^8 + 3721765968*t*z^7 - 1906125696*t*z^6 + 659371104*t*z^5 - 146958624*t*z^4 + 19730304*t*z^3 - 1420416*t*z^2 + 41472*t*z + 1296*z^24 - 62208*z^23 + 1389312*z^22 - 19171728*z^21 + 183091104*z^20 - 1284488928*z^19 + 6858496800*z^18 - 28495058688*z^17 + 93400093008*z^16 - 243467653824*z^15 + 506523379536*z^14 - 840905858448*z^13 + 1110020419152*z^12 - 1157064098112*z^11 + 942711386256*z^10 - 592200708336*z^9 + 282003507504*z^8 - 99776988432*z^7 + 25632847872*z^6 - 4651569504*z^5 + 574659360*z^4 - 45608832*z^3 + 2083968*z^2 - 41472*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^14 - 37584*t*z^13 + 480816*t*z^12 - 3571776*t*z^11 + 17069616*t*z^10 - 54950400*t*z^9 + 121292640*t*z^8 - 183288096*t*z^7 + 185976000*t*z^6 - 121713840*t*z^5 + 48040128*t*z^4 - 10395216*t*z^3 + 1110672*t*z^2 - 28512*t*z + 7776*t - 1296*z^20 + 53136*z^19 - 999216*z^18 + 11422944*z^17 - 88715088*z^16 + 495515232*z^15 - 2055496176*z^14 + 6448228560*z^13 - 15432709680*z^12 + 28224001584*z^11 - 39256108272*z^10 + 41067172368*z^9 - 31739974416*z^8 + 17670996288*z^7 - 6861283200*z^6 + 1790810208*z^5 - 301926528*z^4 + 30897936*z^3 - 1826064*z^2 - 6480*z - 29808)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_34 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 34) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_34 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_35 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 35) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_35 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z^3 - 384*t^7*z^2 + 384*t^7*z - 112*t^7 + 160*t^6*z^6 - 1920*t^6*z^5 + 8064*t^6*z^4 - 14528*t^6*z^3 + 13056*t^6*z^2 - 5568*t^6*z + 688*t^6 + 256*t^5*z^9 - 4608*t^5*z^8 + 33408*t^5*z^7 - 126192*t^5*z^6 + 272448*t^5*z^5 - 353952*t^5*z^4 + 278544*t^5*z^3 - 127008*t^5*z^2 + 29952*t^5*z - 2560*t^5 + 304*t^4*z^12 - 7296*t^4*z^11 + 75264*t^4*z^10 - 438448*t^4*z^9 + 1599840*t^4*z^8 - 3851712*t^4*z^7 + 6296928*t^4*z^6 - 7064064*t^4*z^5 + 5388912*t^4*z^4 - 2699776*t^4*z^3 + 821904*t^4*z^2 - 130128*t^4*z + 7984*t^4 + 256*t^3*z^15 - 7680*t^3*z^14 + 102528*t^3*z^13 - 805040*t^3*z^12 + 4145280*t^3*z^11 - 14798112*t^3*z^10 + 37808848*t^3*z^9 - 70413408*t^3*z^8 + 96375456*t^3*z^7 - 96835648*t^3*z^6 + 70620960*t^3*z^5 - 36494352*t^3*z^4 + 12813056*t^3*z^3 - 2841360*t^3*z^2 + 346416*t^3*z - 17200*t^3 + 160*t^2*z^18 - 5760*t^2*z^17 + 94464*t^2*z^16 - 935664*t^2*z^15 + 6260256*t^2*z^14 - 29999232*t^2*z^13 + 106592352*t^2*z^12 - 286970688*t^2*z^11 + 593226576*t^2*z^10 - 948209360*t^2*z^9 + 1173414096*t^2*z^8 - 1119082464*t^2*z^7 + 813104448*t^2*z^6 - 441056592*t^2*z^5 + 172926432*t^2*z^4 - 46623264*t^2*z^3 + 8003664*t^2*z^2 - 770544*t^2*z + 31120*t^2 + 64*t*z^21 - 2688*t*z^20 + 52224*t*z^19 - 623296*t*z^18 + 5119488*t*z^17 - 30731616*t*z^16 + 139796112*t*z^15 - 493241184*t*z^14 + 1370620512*t*z^13 - 3029110352*t*z^12 + 5353639392*t*z^11 - 7580795952*t*z^10 + 8585633696*t*z^9 - 7735244112*t*z^8 + 5491059120*t*z^7 - 3026535888*t*z^6 + 1267774848*t*z^5 - 391161168*t*z^4 + 84795280*t*z^3 - 11980464*t*z^2 + 969360*t*z - 33376*t + 16*z^24 - 768*z^23 + 17280*z^22 - 242288*z^21 + 2374368*z^20 - 17291328*z^19 + 97148272*z^18 - 431561088*z^17 + 1541415600*z^16 - 4477674128*z^15 + 10659828912*z^14 - 20892050352*z^13 + 33770577616*z^12 - 44988020256*z^11 + 49224597888*z^10 - 43961115248*z^9 + 31739534208*z^8 - 18277717680*z^7 + 8242868608*z^6 - 2840540880*z^5 + 723544560*z^4 - 130036544*z^3 + 15366912*z^2 - 1055040*z + 31360:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z^2 + 800*t^6*z - 224*t^6 - 256*t^5*z^5 + 2816*t^5*z^4 - 10112*t^5*z^3 + 13936*t^5*z^2 - 10544*t^5*z + 1328*t^5 - 304*t^4*z^8 + 5168*t^4*z^7 - 34832*t^4*z^6 + 119840*t^4*z^5 - 231664*t^4*z^4 + 268480*t^4*z^3 - 180720*t^4*z^2 + 67152*t^4*z - 9264*t^4 - 256*t^3*z^11 + 5888*t^3*z^10 - 57728*t^3*z^9 + 316464*t^3*z^8 - 1074480*t^3*z^7 + 2378544*t^3*z^6 - 3526880*t^3*z^5 + 3513328*t^3*z^4 - 2303008*t^3*z^3 + 934416*t^3*z^2 - 204432*t^3*z + 44112*t^3 - 160*t^2*z^14 + 4640*t^2*z^13 - 59744*t^2*z^12 + 451216*t^2*z^11 - 2228048*t^2*z^10 + 7603280*t^2*z^9 - 18507248*t^2*z^8 + 32698432*t^2*z^7 - 42181792*t^2*z^6 + 39497504*t^2*z^5 - 26291776*t^2*z^4 + 11922208*t^2*z^3 - 3402304*t^2*z^2 + 497840*t^2*z - 139856*t^2 - 64*t*z^17 + 2240*t*z^16 - 35648*t*z^15 + 341888*t*z^14 - 2209216*t*z^13 + 10193248*t*z^12 - 34743600*t*z^11 + 89314896*t*z^10 - 175250640*t*z^9 + 263805280*t*z^8 - 304230704*t*z^7 + 266587088*t*z^6 - 174601344*t*z^5 + 83164560*t*z^4 - 27560976*t*z^3 + 5907376*t*z^2 - 651728*t*z + 243440*t - 16*z^20 + 656*z^19 - 12464*z^18 + 145728*z^17 - 1174512*z^16 + 6929184*z^15 - 31022528*z^14 + 107852992*z^13 - 295521280*z^12 + 643973872*z^11 - 1120867424*z^10 + 1558320944*z^9 - 1722874816*z^8 + 1500490064*z^7 - 1013485040*z^6 + 518539600*z^5 - 194171120*z^4 + 50595056*z^3 - 8505696*z^2 + 761664*z - 201600)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_36 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 36) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_36 z t hf hn0 hn1 hn2 hn3
  · have hr : (1296*t*z^7 - 15552*t*z^6 + 68688*t*z^5 - 139968*t*z^4 + 130896*t*z^3 - 46656*t*z^2 + 5184*t*z - 1296*z^9 + 18144*z^8 - 101088*z^7 + 292896*z^6 - 479520*z^5 + 448416*z^4 - 229392*z^3 + 57024*z^2 - 5184*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1296*t*z^3 + 6480*t*z^2 - 5184*t*z + 2592*t + 1296*z^5 - 9072*z^4 + 19440*z^3 - 19440*z^2 - 2592*z - 29808)*hf
  · have hr : (-1296*t*z^18 + 46656*t*z^17 - 765936*t*z^16 + 7594560*t*z^15 - 50785056*t*z^14 + 242236656*t*z^13 - 850249872*t*z^12 + 2233902240*t*z^11 - 4427371872*t*z^10 + 6623363520*t*z^9 - 7439706144*t*z^8 + 6207324192*t*z^7 - 3786333984*t*z^6 + 1653702480*t*z^5 - 503717616*t*z^4 + 103214736*t*z^3 - 13423968*t*z^2 + 990144*t*z - 31104*t + 1296*z^24 - 62208*z^23 + 1394496*z^22 - 19394640*z^21 + 187531200*z^20 - 1338872976*z^19 + 7317090288*z^18 - 31319799552*z^17 + 106561081872*z^16 - 290862397152*z^15 + 640195996032*z^14 - 1138364671392*z^13 + 1633788769968*z^12 - 1886213865168*z^11 + 1741919078448*z^10 - 1276967783808*z^9 + 736061059008*z^8 - 329862724272*z^7 + 113408202384*z^6 - 29416391568*z^5 + 5625145440*z^4 - 765460368*z^3 + 69836256*z^2 - 3810240*z + 93312:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^14 - 37584*t*z^13 + 484704*t*z^12 - 3665088*t*z^11 + 18041616*t*z^10 - 60718896*t*z^9 + 142829568*t*z^8 - 236032704*t*z^7 + 271736208*t*z^6 - 213396768*t*z^5 + 110530656*t*z^4 - 36132480*t*z^3 + 7067088*t*z^2 - 736128*t*z + 34992*t - 1296*z^20 + 53136*z^19 - 1004400*z^18 + 11609568*z^17 - 91776240*z^16 + 525817008*z^15 - 2257622928*z^14 + 7409181456*z^13 - 18791778384*z^12 + 37004607648*z^11 - 56547770544*z^10 + 66722361984*z^9 - 60234808896*z^8 + 41070363120*z^7 - 20812545648*z^6 + 7694047440*z^5 - 2029374000*z^4 + 369713808*z^3 - 44044560*z^2 + 3046896*z - 108864)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_37 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 37) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_37 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 24*z^5 + 104*z^4 - 200*z^3 + 176*z^2 - 70*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 6)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_38 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 38) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_38 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 24*z^5 + 104*z^4 - 198*z^3 + 164*z^2 - 54*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 6)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_39 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 39) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_39 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^3 + 12*t*z^2 - 20*t*z + 2*z^6 - 24*z^5 + 106*z^4 - 210*z^3 + 182*z^2 - 54*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 8)*hf
  · have hr : (16*t^8 - 192*t^7*z + 16*t^7 - 48*t^6*z^3 + 1344*t^6*z^2 - 816*t^6*z + 16*t^6 + 432*t^5*z^4 - 6048*t^5*z^3 + 6624*t^5*z^2 - 432*t^5*z - 32*t^5 - 1728*t^4*z^5 + 18288*t^4*z^4 - 28800*t^4*z^3 + 8064*t^4*z^2 + 960*t^4*z - 176*t^4 + 3888*t^3*z^6 - 37152*t^3*z^5 + 76320*t^3*z^4 - 41952*t^3*z^3 - 960*t^3*z^2 + 192*t^3*z + 112*t^3 - 5184*t^2*z^7 + 49248*t^2*z^6 - 127008*t^2*z^5 + 113616*t^2*z^4 - 23760*t^2*z^3 - 2304*t^2*z^2 + 432*t^2*z + 16*t^2 + 3888*t*z^8 - 38880*t*z^7 + 123120*t*z^6 - 158976*t*z^5 + 76320*t*z^4 - 8784*t*z^3 + 6624*t*z^2 - 2064*t*z + 160*t - 1296*z^9 + 14256*z^8 - 55728*z^7 + 101088*z^6 - 85968*z^5 + 23472*z^4 + 10896*z^3 - 9024*z^2 + 1920*z - 128:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-432*t^5 + 1728*t^4*z - 6192*t^4 - 3888*t^3*z^2 + 9936*t^3*z + 47664*t^3 + 5184*t^2*z^3 - 12960*t^2*z^2 - 36288*t^2*z - 144720*t^2 - 3888*t*z^4 + 11664*t*z^3 + 12960*t*z^2 + 55296*t*z + 226512*t + 1296*z^5 - 5184*z^4 + 1296*z^3 - 9072*z^2 - 38448*z - 150048)*hf
  · have hr : (16*t^8 - 192*t^7*z + 16*t^7 + 192*t^6*z^6 - 2304*t^6*z^5 + 10176*t^6*z^4 - 20208*t^6*z^3 + 18624*t^6*z^2 - 5616*t^6*z + 400*t^6 - 1728*t^5*z^7 + 20880*t^5*z^6 - 93312*t^5*z^5 + 189504*t^5*z^4 - 176688*t^5*z^3 + 62784*t^5*z^2 - 7488*t^5*z + 256*t^5 + 864*t^4*z^12 - 20736*t^4*z^11 + 216000*t^4*z^10 - 1280880*t^4*z^9 + 4774464*t^4*z^8 - 11669616*t^4*z^7 + 18922320*t^4*z^6 - 20068992*t^4*z^5 + 13343040*t^4*z^4 - 5170464*t^4*z^3 + 1076832*t^4*z^2 - 106464*t^4*z + 3856*t^4 - 5184*t^3*z^13 + 124848*t^3*z^12 - 1306368*t^3*z^11 + 7793280*t^3*z^10 - 29261088*t^3*z^9 + 72083520*t^3*z^8 - 117888480*t^3*z^7 + 126691392*t^3*z^6 - 86757840*t^3*z^5 + 36048912*t^3*z^4 - 8613120*t^3*z^3 + 1110576*t^3*z^2 - 71856*t^3*z + 1936*t^3 + 1728*t^2*z^18 - 62208*t^2*z^17 + 1021248*t^2*z^16 - 10125648*t^2*z^15 + 67708224*t^2*z^14 - 322990416*t^2*z^13 + 1134121392*t^2*z^12 - 2981696832*t^2*z^11 + 5912886816*t^2*z^10 - 8840688192*t^2*z^9 + 9890910432*t^2*z^8 - 8159444064*t^2*z^7 + 4855519152*t^2*z^6 - 2025407376*t^2*z^5 + 572136192*t^2*z^4 - 104793696*t^2*z^3 + 11688912*t^2*z^2 - 710928*t^2*z + 17872*t^2 - 5184*t*z^19 + 187056*t*z^18 - 3079296*t*z^17 + 30632256*t*z^16 - 205632432*t*z^15 + 985322880*t*z^14 - 3477009888*t*z^13 + 9191558592*t*z^12 - 18341439120*t*z^11 + 27636374448*t*z^10 - 31256398368*t*z^9 + 26222197824*t*z^8 - 16038559008*t*z^7 + 6997591440*t*z^6 - 2124561312*t*z^5 + 437102928*t*z^4 - 59253264*t*z^3 + 5121504*t*z^2 - 264432*t*z + 6496*t + 1296*z^24 - 62208*z^23 + 1394496*z^22 - 19394640*z^21 + 187531200*z^20 - 1338867792*z^19 + 7316900208*z^18 - 31316611392*z^17 + 106528662432*z^16 - 290639044512*z^15 + 639092179872*z^14 - 1134322429248*z^13 + 1622612714400*z^12 - 1862655499872*z^11 + 1703934436032*z^10 - 1230216791760*z^9 + 692431386624*z^8 - 299327837184*z^7 + 97623123024*z^6 - 23505797952*z^5 + 4062597072*z^4 - 484218192*z^3 + 37333056*z^2 - 1653120*z + 31360:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6*z^2 + 960*t^6*z - 768*t^6 + 1728*t^5*z^3 - 8784*t^5*z^2 + 7632*t^5*z + 720*t^5 - 864*t^4*z^8 + 14688*t^4*z^7 - 101088*t^4*z^6 + 360720*t^4*z^5 - 715824*t^4*z^4 + 785376*t^4*z^3 - 416304*t^4*z^2 + 72288*t^4*z - 9936*t^4 + 5184*t^3*z^9 - 88560*t^3*z^8 + 613872*t^3*z^7 - 2214864*t^3*z^6 + 4449168*t^3*z^5 - 4931712*t^3*z^4 + 2745360*t^3*z^3 - 621696*t^3*z^2 + 68064*t^3*z + 25872*t^3 - 1728*t^2*z^14 + 50112*t^2*z^13 - 646272*t^2*z^12 + 4886352*t^2*z^11 - 24053328*t^2*z^10 + 80987904*t^2*z^9 - 190722384*t^2*z^8 + 315496512*t^2*z^7 - 362341296*t^2*z^6 + 280580976*t^2*z^5 - 139370976*t^2*z^4 + 41486688*t^2*z^3 - 6929568*t^2*z^2 + 537984*t^2*z - 91872*t^2 + 5184*t*z^15 - 150768*t*z^14 + 1951344*t*z^13 - 14820624*t*z^12 + 73357920*t*z^11 - 248567184*t*z^10 + 589512384*t*z^9 - 983347344*t*z^8 + 1142938944*t*z^7 - 904272768*t*z^6 + 469052640*t*z^5 - 152151696*t*z^4 + 29639088*t*z^3 - 3300192*t*z^2 + 246528*t*z + 89856*t - 1296*z^20 + 53136*z^19 - 1004400*z^18 + 11609568*z^17 - 91776240*z^16 + 525811824*z^15 - 2257469136*z^14 + 7407142416*z^13 - 18775826784*z^12 + 36922698288*z^11 - 56257108416*z^10 + 65991137616*z^9 - 58917820176*z^8 + 39375266400*z^7 - 19271879424*z^6 + 6726207168*z^5 - 1621673136*z^4 + 258923088*z^3 - 25700736*z^2 + 1377312*z - 87744)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_40 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 40) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_40 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_41 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 41) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_41 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 24*z^5 + 104*z^4 - 198*z^3 + 164*z^2 - 54*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 6)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_42 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 42) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_42 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_43 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 43) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_43 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z^3 - 384*t^7*z^2 + 320*t^7*z - 48*t^7 + 160*t^6*z^6 - 1920*t^6*z^5 + 7744*t^6*z^4 - 12288*t^6*z^3 + 8992*t^6*z^2 - 2928*t^6*z + 192*t^6 + 256*t^5*z^9 - 4608*t^5*z^8 + 32640*t^5*z^7 - 116208*t^5*z^6 + 224832*t^5*z^5 - 248400*t^5*z^4 + 157280*t^5*z^3 - 53280*t^5*z^2 + 8208*t^5*z - 432*t^5 + 304*t^4*z^12 - 7296*t^4*z^11 + 74048*t^4*z^10 - 415344*t^4*z^9 + 1419648*t^4*z^8 - 3100176*t^4*z^7 + 4447376*t^4*z^6 - 4237680*t^4*z^5 + 2653840*t^4*z^4 - 1046544*t^4*z^3 + 233712*t^4*z^2 - 22896*t^4*z + 720*t^4 + 256*t^3*z^15 - 7680*t^3*z^14 + 101248*t^3*z^13 - 773040*t^3*z^12 + 3799168*t^3*z^11 - 12666288*t^3*z^10 + 29502080*t^3*z^9 - 48824304*t^3*z^8 + 57828944*t^3*z^7 - 48878160*t^3*z^6 + 29031968*t^3*z^5 - 11737680*t^3*z^4 + 3056928*t^3*z^3 - 467856*t^3*z^2 + 35280*t^3*z - 864*t^3 + 160*t^2*z^18 - 5760*t^2*z^17 + 93504*t^2*z^16 - 905904*t^2*z^15 + 5847936*t^2*z^14 - 26622000*t^2*z^13 + 88341808*t^2*z^12 - 218112192*t^2*z^11 + 405767616*t^2*z^10 - 572600448*t^2*z^9 + 613486848*t^2*z^8 - 496244448*t^2*z^7 + 298827808*t^2*z^6 - 130542768*t^2*z^5 + 39605760*t^2*z^4 - 7766496*t^2*z^3 + 875664*t^2*z^2 - 47952*t^2*z + 864*t^2 + 64*t*z^21 - 2688*t*z^20 + 51776*t*z^19 - 606720*t*z^18 + 4839744*t*z^17 - 27875952*t*z^16 + 120070144*t*z^15 - 395452464*t*z^14 + 1010350256*t*z^13 - 2020736208*t*z^12 + 3179283648*t*z^11 - 3939179616*t*z^10 + 3832860400*t*z^9 - 2907843216*t*z^8 + 1699039328*t*z^7 - 750429984*t*z^6 + 243817344*t*z^5 - 55938384*t*z^4 + 8464896*t*z^3 - 740016*t*z^2 + 27648*t*z + 16*z^24 - 768*z^23 + 17152*z^22 - 236784*z^21 + 2264608*z^20 - 15943008*z^19 + 85715152*z^18 - 360470064*z^17 + 1205191840*z^16 - 3239156496*z^15 + 7049790736*z^14 - 12478075968*z^13 + 17989152400*z^12 - 21097494048*z^11 + 20043032992*z^10 - 15305546784*z^9 + 9283558528*z^8 - 4397088576*z^7 + 1588561536*z^6 - 423949248*z^5 + 79926336*z^4 - 9952848*z^3 + 726624*z^2 - 23328*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z^2 + 800*t^6*z + 96*t^6 - 256*t^5*z^5 + 2816*t^5*z^4 - 9344*t^5*z^3 + 9328*t^5*z^2 - 5936*t^5*z - 1312*t^5 - 304*t^4*z^8 + 5168*t^4*z^7 - 33616*t^4*z^6 + 105248*t^4*z^5 - 170640*t^4*z^4 + 158128*t^4*z^3 - 75920*t^4*z^2 + 22080*t^4*z - 736*t^4 - 256*t^3*z^11 + 5888*t^3*z^10 - 56448*t^3*z^9 + 293424*t^3*z^8 - 907568*t^3*z^7 + 1747904*t^3*z^6 - 2156960*t^3*z^5 + 1700960*t^3*z^4 - 833984*t^3*z^3 + 223248*t^3*z^2 - 28816*t^3*z + 37664*t^3 - 160*t^2*z^14 + 4640*t^2*z^13 - 58784*t^2*z^12 + 428176*t^2*z^11 - 1990448*t^2*z^10 + 6219488*t^2*z^9 - 13454928*t^2*z^8 + 20503104*t^2*z^7 - 22130544*t^2*z^6 + 16784272*t^2*z^5 - 8689568*t^2*z^4 + 2890208*t^2*z^3 - 537680*t^2*z^2 + 15280*t^2*z - 160048*t^2 - 64*t*z^17 + 2240*t*z^16 - 35200*t*z^15 + 328448*t*z^14 - 2029824*t*z^13 + 8785072*t*z^12 - 27494320*t*z^11 + 63434176*t*z^10 - 109080144*t*z^9 + 140357104*t*z^8 - 134694176*t*z^7 + 95245600*t*z^6 - 48485760*t*z^5 + 17093984*t*z^4 - 3921824*t*z^3 + 529760*t*z^2 + 34144*t*z + 292176*t - 16*z^20 + 656*z^19 - 12336*z^18 + 141120*z^17 - 1098800*z^16 + 6176384*z^15 - 25955968*z^14 + 83377392*z^13 - 207656672*z^12 + 404452176*z^11 - 618456992*z^10 + 741915792*z^9 - 694069888*z^8 + 500075632*z^7 - 271741808*z^6 + 107820384*z^5 - 29755584*z^4 + 5304016*z^3 - 550368*z^2 - 24608*z - 205728)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_44 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 44) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_44 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z^3 + 768*t^7*z^2 - 1152*t^7*z + 80*t^7 + 448*t^6*z^6 - 5376*t^6*z^5 + 24192*t^6*z^4 - 49040*t^6*z^3 + 40416*t^6*z^2 - 6336*t^6*z + 352*t^6 - 896*t^5*z^9 + 16128*t^5*z^8 - 120960*t^5*z^7 + 486096*t^5*z^6 - 1116864*t^5*z^5 + 1437696*t^5*z^4 - 925296*t^5*z^3 + 222048*t^5*z^2 - 24480*t^5*z + 896*t^5 + 1120*t^4*z^12 - 26880*t^4*z^11 + 282240*t^4*z^10 - 1697680*t^4*z^9 + 6429600*t^4*z^8 - 15854400*t^4*z^7 + 25391904*t^4*z^6 - 25503552*t^4*z^5 + 14910480*t^4*z^4 - 4544656*t^4*z^3 + 747312*t^4*z^2 - 60912*t^4*z + 2032*t^4 - 896*t^3*z^15 + 26880*t^3*z^14 - 362880*t^3*z^13 + 2907760*t^3*z^12 - 15358080*t^3*z^11 + 56134656*t^3*z^10 - 144991136*t^3*z^9 + 265374144*t^3*z^8 - 339867072*t^3*z^7 + 296160512*t^3*z^6 - 168175680*t^3*z^5 + 59332752*t^3*z^4 - 12842896*t^3*z^3 + 1652592*t^3*z^2 - 116784*t^3*z + 3440*t^3 + 448*t^2*z^18 - 16128*t^2*z^17 + 266112*t^2*z^16 - 2664240*t^2*z^15 + 18059040*t^2*z^14 - 87559488*t^2*z^13 + 312771552*t^2*z^12 - 835304832*t^2*z^11 + 1675044000*t^2*z^10 - 2511631904*t^2*z^9 + 2782504800*t^2*z^8 - 2233925568*t^2*z^7 + 1267512000*t^2*z^6 - 495426816*t^2*z^5 + 131076144*t^2*z^4 - 23019072*t^2*z^3 + 2574288*t^2*z^2 - 166608*t^2*z + 4768*t^2 - 128*t*z^21 + 5376*t*z^20 - 104832*t*z^19 + 1259120*t*z^18 - 10420416*t*z^17 + 62982144*t*z^16 - 287512944*t*z^15 + 1011223008*t*z^14 - 2770719264*t*z^13 + 5941685248*t*z^12 - 9966830784*t*z^11 + 13011077520*t*z^10 - 13096399312*t*z^9 + 10034074512*t*z^8 - 5762779344*t*z^7 + 2442558768*t*z^6 - 753603264*t*z^5 + 166755024*t*z^4 - 25757024*t*z^3 + 2630928*t*z^2 - 159984*t*z + 4544*t + 16*z^24 - 768*z^23 + 17280*z^22 - 242096*z^21 + 2366304*z^20 - 17134272*z^19 + 95265568*z^18 - 416010816*z^17 + 1447530192*z^16 - 4048635344*z^15 + 9143531376*z^14 - 16692684912*z^13 + 24589889200*z^12 - 29099692992*z^11 + 27479767248*z^10 - 20531599328*z^9 + 12020486832*z^8 - 5460636528*z^7 + 1906662688*z^6 - 506163648*z^5 + 100322208*z^4 - 14349056*z^3 + 1387968*z^2 - 78912*z + 1792:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6*z^2 + 2240*t^6*z - 2240*t^6 + 896*t^5*z^5 - 9856*t^5*z^4 + 39424*t^5*z^3 - 64976*t^5*z^2 + 30352*t^5*z + 9680*t^5 - 1120*t^4*z^8 + 19040*t^4*z^7 - 133280*t^4*z^6 + 489200*t^4*z^5 - 985840*t^4*z^4 + 1019440*t^4*z^3 - 407184*t^4*z^2 + 5184*t^4*z - 32256*t^4 + 896*t^3*z^11 - 20608*t^3*z^10 + 206080*t^3*z^9 - 1169520*t^3*z^8 + 4120560*t^3*z^7 - 9248208*t^3*z^6 + 13003600*t^3*z^5 - 10740032*t^3*z^4 + 4530224*t^3*z^3 - 811488*t^3*z^2 + 148272*t^3*z + 47808*t^3 - 448*t^2*z^14 + 12992*t^2*z^13 - 168896*t^2*z^12 + 1296496*t^2*z^11 - 6514640*t^2*z^10 + 22441904*t^2*z^9 - 53932400*t^2*z^8 + 90177760*t^2*z^7 - 102696208*t^2*z^6 + 76368704*t^2*z^5 - 34822480*t^2*z^4 + 9258928*t^2*z^3 - 1538944*t^2*z^2 + 80672*t^2*z - 72320*t^2 + 128*t*z^17 - 4480*t*z^16 + 71680*t*z^15 - 693616*t*z^14 + 4525616*t*z^13 - 21014288*t*z^12 + 71433696*t*z^11 - 180088560*t*z^10 + 337387680*t*z^9 - 466247792*t*z^8 + 467526544*t*z^7 - 331732624*t*z^6 + 161529312*t*z^5 - 52652448*t*z^4 + 11414304*t*z^3 - 1557248*t*z^2 + 153376*t*z + 86960*t - 16*z^20 + 656*z^19 - 12464*z^18 + 145536*z^17 - 1167792*z^16 + 6821856*z^15 - 29986736*z^14 + 101109808*z^13 - 264204592*z^12 + 536950144*z^11 - 847150880*z^10 + 1030580192*z^9 - 955909792*z^8 + 666044576*z^7 - 342925712*z^6 + 128636752*z^5 - 34803200*z^4 + 6649328*z^3 - 852864*z^2 + 40656*z - 99696)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_45 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 45) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_45 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^3 + 12*t*z^2 - 20*t*z + 2*z^6 - 24*z^5 + 106*z^4 - 210*z^3 + 182*z^2 - 54*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 8)*hf
  · have hr : (16*t^8 - 192*t^7*z^3 + 1152*t^7*z^2 - 1728*t^7*z + 208*t^7 + 1056*t^6*z^6 - 12672*t^6*z^5 + 56832*t^6*z^4 - 115200*t^6*z^3 + 97824*t^6*z^2 - 20784*t^6*z + 1216*t^6 - 3456*t^5*z^9 + 62208*t^5*z^8 - 464832*t^5*z^7 + 1856880*t^5*z^6 - 4243968*t^5*z^5 + 5475456*t^5*z^4 - 3627216*t^5*z^3 + 983808*t^5*z^2 - 110592*t^5*z + 4288*t^5 + 7344*t^4*z^12 - 176256*t^4*z^11 + 1843776*t^4*z^10 - 11012112*t^4*z^9 + 41298336*t^4*z^8 - 100658592*t^4*z^7 + 159314112*t^4*z^6 - 158535792*t^4*z^5 + 92498400*t^4*z^4 - 28401888*t^4*z^3 + 4488624*t^4*z^2 - 344304*t^4*z + 10096*t^4 - 10368*t^3*z^15 + 311040*t^3*z^14 - 4183488*t^3*z^13 + 33276528*t^3*z^12 - 173840256*t^3*z^11 + 626184864*t^3*z^10 - 1587990960*t^3*z^9 + 2842112448*t^3*z^8 - 3542190048*t^3*z^7 + 2983732032*t^3*z^6 - 1619451504*t^3*z^5 + 534303888*t^3*z^4 - 104236560*t^3*z^3 + 11642448*t^3*z^2 - 684624*t^3*z + 16432*t^3 + 9504*t^2*z^18 - 342144*t^2*z^17 + 5624640*t^2*z^16 - 55895184*t^2*z^15 + 374603616*t^2*z^14 - 1788358176*t^2*z^13 + 6261446016*t^2*z^12 - 16305242976*t^2*z^11 + 31682741328*t^2*z^10 - 45665914320*t^2*z^9 + 48104332272*t^2*z^8 - 36150936336*t^2*z^7 + 18758171664*t^2*z^6 - 6485392224*t^2*z^5 + 1457865792*t^2*z^4 - 208090800*t^2*z^3 + 18072144*t^2*z^2 - 868320*t^2*z + 17728*t^2 - 5184*t*z^21 + 217728*t*z^20 - 4230144*t*z^19 + 50429088*t*z^18 - 412579008*t*z^17 + 2454535872*t*z^16 - 10976608080*t*z^15 + 37615613328*t*z^14 - 99787505472*t*z^13 + 205602525504*t*z^12 - 328199979600*t*z^11 + 402667314048*t*z^10 - 374644167408*t*z^9 + 259413714720*t*z^8 - 130624713504*t*z^7 + 46690153632*t*z^6 - 11609090208*t*z^5 + 1968832800*t*z^4 - 221343168*t*z^3 + 15645744*t*z^2 - 622512*t*z + 10432*t + 1296*z^24 - 62208*z^23 + 1394496*z^22 - 19389456*z^21 + 187313472*z^20 - 1334642832*z^19 + 7266650400*z^18 - 30906831744*z^17 + 104100155424*z^16 - 279822288960*z^15 + 602154682992*z^14 - 1036542387600*z^13 + 1421041264704*z^12 - 1539300723840*z^11 + 1302513622560*z^10 - 848435332032*z^9 + 418219832880*z^8 - 153236436768*z^7 + 41028639024*z^6 - 7885962720*z^5 + 1062394656*z^4 - 96430608*z^3 + 5480544*z^2 - 167232*z + 1792:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6*z^2 + 5280*t^6*z - 5088*t^6 + 3456*t^5*z^5 - 38016*t^5*z^4 + 150336*t^5*z^3 - 244656*t^5*z^2 + 119088*t^5*z + 24048*t^5 - 7344*t^4*z^8 + 124848*t^4*z^7 - 867024*t^4*z^6 + 3136320*t^4*z^5 - 6199632*t^4*z^4 + 6291648*t^4*z^3 - 2520144*t^4*z^2 + 78336*t^4*z - 135216*t^4 + 10368*t^3*z^11 - 238464*t^3*z^10 + 2369088*t^3*z^9 - 13271472*t^3*z^8 + 45854640*t^3*z^7 - 100210608*t^3*z^6 + 136010880*t^3*z^5 - 106979184*t^3*z^4 + 41643936*t^3*z^3 - 6218256*t^3*z^2 + 1064256*t^3*z + 332160*t^3 - 9504*t^2*z^14 + 275616*t^2*z^13 - 3562272*t^2*z^12 + 27024624*t^2*z^11 - 133345008*t^2*z^10 + 447824592*t^2*z^9 - 1040084496*t^2*z^8 + 1661322528*t^2*z^7 - 1776358944*t^2*z^6 + 1204385760*t^2*z^5 - 473942016*t^2*z^4 + 99747504*t^2*z^3 - 13305888*t^2*z^2 - 135936*t^2*z - 612864*t^2 + 5184*t*z^17 - 181440*t*z^16 + 2887488*t*z^15 - 27635040*t*z^14 + 177252192*t*z^13 - 803598624*t*z^12 + 2645919216*t*z^11 - 6398145504*t*z^10 + 11351576736*t*z^9 - 14596498944*t*z^8 + 13271329440*t*z^7 - 8206263360*t*z^6 + 3278143440*t*z^5 - 811889136*t*z^4 + 126045072*t*z^3 - 9979344*t*z^2 + 1347264*t*z + 558576*t - 1296*z^20 + 53136*z^19 - 1004400*z^18 + 11604384*z^17 - 91594800*z^16 + 522929520*z^15 - 2229977088*z^14 + 7231616064*z^13 - 17984132784*z^12 + 34327988352*z^11 - 49997999952*z^10 + 54859872672*z^9 - 44442117072*z^8 + 25855698960*z^7 - 10457109504*z^6 + 2858970816*z^5 - 519795360*z^4 + 59702832*z^3 - 4708128*z^2 - 167520*z - 235488)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_46 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 46) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_46 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z^3 + 768*t^7*z^2 - 1216*t^7*z + 144*t^7 + 448*t^6*z^6 - 5376*t^6*z^5 + 24640*t^6*z^4 - 52176*t^6*z^3 + 47104*t^6*z^2 - 10608*t^6*z + 624*t^6 - 896*t^5*z^9 + 16128*t^5*z^8 - 122304*t^5*z^7 + 503568*t^5*z^6 - 1205376*t^5*z^5 + 1656000*t^5*z^4 - 1190128*t^5*z^3 + 358848*t^5*z^2 - 43200*t^5*z + 1728*t^5 + 1120*t^4*z^12 - 26880*t^4*z^11 + 284480*t^4*z^10 - 1740240*t^4*z^9 + 6771840*t^4*z^8 - 17365680*t^4*z^7 + 29364464*t^4*z^6 - 31789344*t^4*z^5 + 20655808*t^4*z^4 - 7268544*t^4*z^3 + 1294272*t^4*z^2 - 108000*t^4*z + 3312*t^4 - 896*t^3*z^15 + 26880*t^3*z^14 - 365120*t^3*z^13 + 2963760*t^3*z^12 - 15975680*t^3*z^11 + 60082176*t^3*z^10 - 161141536*t^3*z^9 + 309436032*t^3*z^8 - 420807520*t^3*z^7 + 394843584*t^3*z^6 - 244931728*t^3*z^5 + 94821072*t^3*z^4 - 21662976*t^3*z^3 + 2765232*t^3*z^2 - 180720*t^3*z + 4752*t^3 + 448*t^2*z^18 - 16128*t^2*z^17 + 267456*t^2*z^16 - 2705904*t^2*z^15 + 18643200*t^2*z^14 - 92453328*t^2*z^13 + 340031632*t^2*z^12 - 941594688*t^2*z^11 + 1972413600*t^2*z^10 - 3113457408*t^2*z^9 + 3659250720*t^2*z^8 - 3137381280*t^2*z^7 + 1905596944*t^2*z^6 - 789869808*t^2*z^5 + 214367904*t^2*z^4 - 36500544*t^2*z^3 + 3705264*t^2*z^2 - 204336*t^2*z + 4752*t^2 - 128*t*z^21 + 5376*t*z^20 - 105280*t*z^19 + 1275696*t*z^18 - 10702464*t*z^17 + 65906496*t*z^16 - 308149616*t*z^15 + 1116076224*t*z^14 - 3166426720*t*z^13 + 7069570560*t*z^12 - 12411500304*t*z^11 + 17036195472*t*z^10 - 18088628864*t*z^9 + 14623552416*t*z^8 - 8812739008*t*z^7 + 3855881808*t*z^6 - 1187966304*t*z^5 + 249127920*t*z^4 - 34158384*t*z^3 + 2885760*t*z^2 - 134352*t*z + 2592*t + 16*z^24 - 768*z^23 + 17344*z^22 - 244848*z^21 + 2421376*z^20 - 17815056*z^19 + 101084560*z^18 - 452487072*z^17 + 1621081888*z^16 - 4688571072*z^15 + 10994443456*z^14 - 20916344544*z^13 + 32198736448*z^12 - 39876623328*z^11 + 39373891264*z^10 - 30613841328*z^9 + 18445840288*z^8 - 8444814720*z^7 + 2869293360*z^6 - 703431648*z^5 + 119933424*z^4 - 13427856*z^3 + 884736*z^2 - 25920*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6*z^2 + 2240*t^6*z - 2688*t^6 + 896*t^5*z^5 - 9856*t^5*z^4 + 40768*t^5*z^3 - 73040*t^5*z^2 + 43600*t^5*z + 7760*t^5 - 1120*t^4*z^8 + 19040*t^4*z^7 - 135520*t^4*z^6 + 516080*t^4*z^5 - 1108560*t^4*z^4 + 1277440*t^4*z^3 - 638384*t^4*z^2 + 51936*t^4*z - 26800*t^4 + 896*t^3*z^11 - 20608*t^3*z^10 + 208320*t^3*z^9 - 1209840*t^3*z^8 + 4424560*t^3*z^7 - 10485328*t^3*z^6 + 15913360*t^3*z^5 - 14641600*t^3*z^4 + 7222096*t^3*z^3 - 1514304*t^3*z^2 + 176096*t^3*z + 30224*t^3 - 448*t^2*z^14 + 12992*t^2*z^13 - 170240*t^2*z^12 + 1328752*t^2*z^11 - 6854192*t^2*z^10 + 24496544*t^2*z^9 - 61796880*t^2*z^8 + 109902624*t^2*z^7 - 135112368*t^2*z^6 + 110162512*t^2*z^5 - 55522112*t^2*z^4 + 15649760*t^2*z^3 - 2326592*t^2*z^2 + 147616*t^2*z - 42112*t^2 + 128*t*z^17 - 4480*t*z^16 + 72128*t*z^15 - 707056*t*z^14 + 4707312*t*z^13 - 22475024*t*z^12 + 79193504*t*z^11 - 208705808*t*z^10 + 412269504*t*z^9 - 605779664*t*z^8 + 650429632*t*z^7 - 495410912*t*z^6 + 256230816*t*z^5 - 84967216*t*z^4 + 17020144*t*z^3 - 1942336*t*z^2 + 119392*t*z + 28896*t - 16*z^20 + 656*z^19 - 12528*z^18 + 147840*z^17 - 1205840*z^16 + 7203536*z^15 - 32582800*z^14 + 113763408*z^13 - 309744704*z^12 + 659804496*z^11 - 1096696064*z^10 + 1410488112*z^9 - 1383394096*z^8 + 1012658080*z^7 - 537166400*z^6 + 198822528*z^5 - 49094256*z^4 + 7650256*z^3 - 675360*z^2 + 23968*z - 14304)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_47 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 47) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_47 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z^3 + 384*t^7*z^2 - 768*t^7*z + 144*t^7 + 160*t^6*z^6 - 1920*t^6*z^5 + 9216*t^6*z^4 - 21408*t^6*z^3 + 23232*t^6*z^2 - 7584*t^6*z + 624*t^6 - 256*t^5*z^9 + 4608*t^5*z^8 - 35712*t^5*z^7 + 153648*t^5*z^6 - 394560*t^5*z^5 + 602496*t^5*z^4 - 511056*t^5*z^3 + 203040*t^5*z^2 - 33120*t^5*z + 1728*t^5 + 304*t^4*z^12 - 7296*t^4*z^11 + 77952*t^4*z^10 - 486288*t^4*z^9 + 1952928*t^4*z^8 - 5247648*t^4*z^7 + 9490176*t^4*z^6 - 11311488*t^4*z^5 + 8454096*t^4*z^4 - 3644640*t^4*z^3 + 825552*t^4*z^2 - 86832*t^4*z + 3312*t^4 - 256*t^3*z^15 + 7680*t^3*z^14 - 104832*t^3*z^13 + 859632*t^3*z^12 - 4708992*t^3*z^11 + 18125376*t^3*z^10 - 50194128*t^3*z^9 + 100675872*t^3*z^8 - 145260288*t^3*z^7 + 147792096*t^3*z^6 - 102445344*t^3*z^5 + 46019664*t^3*z^4 - 12584736*t^3*z^3 + 1942704*t^3*z^2 - 152496*t^3*z + 4752*t^3 + 160*t^2*z^18 - 5760*t^2*z^17 + 95616*t^2*z^16 - 969552*t^2*z^15 + 6706656*t^2*z^14 - 33472800*t^2*z^13 + 124327872*t^2*z^12 - 349367040*t^2*z^11 + 747585648*t^2*z^10 - 1216370736*t^2*z^9 + 1491595344*t^2*z^8 - 1355993568*t^2*z^7 + 891411264*t^2*z^6 - 409539024*t^2*z^5 + 125910720*t^2*z^4 - 24591168*t^2*z^3 + 2862000*t^2*z^2 - 180144*t^2*z + 4752*t^2 - 64*t*z^21 + 2688*t*z^20 - 52608*t*z^19 + 636768*t*z^18 - 5334912*t*z^17 + 32808960*t*z^16 - 153264528*t*z^15 + 555188256*t*z^14 - 1578278016*t*z^13 + 3541183632*t*z^12 - 6275034144*t*z^11 + 8747570160*t*z^10 - 9512497152*t*z^9 + 7962691824*t*z^8 - 5035618800*t*z^7 + 2347094448*t*z^6 - 781665984*t*z^5 + 179225136*t*z^4 - 27047088*t*z^3 + 2520720*t*z^2 - 128304*t*z + 2592*t + 16*z^24 - 768*z^23 + 17280*z^22 - 242160*z^21 + 2368992*z^20 - 17186496*z^19 + 95888208*z^18 - 421106688*z^17 + 1477873872*z^16 - 4184579088*z^15 + 9610937712*z^14 - 17939470896*z^13 + 27180883440*z^12 - 33288096096*z^11 + 32708946528*z^10 - 25506771696*z^9 + 15551965440*z^8 - 7271027856*z^7 + 2542830624*z^6 - 644636880*z^5 + 113637168*z^4 - 13087008*z^3 + 878688*z^2 - 25920*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z^2 + 800*t^6*z - 1376*t^6 + 256*t^5*z^5 - 2816*t^5*z^4 + 12416*t^5*z^3 - 25264*t^5*z^2 + 21104*t^5*z + 1072*t^5 - 304*t^4*z^8 + 5168*t^4*z^7 - 37520*t^4*z^6 + 148864*t^4*z^5 - 343952*t^4*z^4 + 450560*t^4*z^3 - 292496*t^4*z^2 + 55696*t^4*z - 20848*t^4 + 256*t^3*z^11 - 5888*t^3*z^10 + 60032*t^3*z^9 - 354928*t^3*z^8 + 1336688*t^3*z^7 - 3313424*t^3*z^6 + 5387072*t^3*z^5 - 5530000*t^3*z^4 + 3287200*t^3*z^3 - 951696*t^3*z^2 + 135600*t^3*z + 80880*t^3 - 160*t^2*z^14 + 4640*t^2*z^13 - 60896*t^2*z^12 + 477040*t^2*z^11 - 2477552*t^2*z^10 + 8959568*t^2*z^9 - 23047952*t^2*z^8 + 42299968*t^2*z^7 - 54660448*t^2*z^6 + 48204864*t^2*z^5 - 27467328*t^2*z^4 + 9270624*t^2*z^3 - 1674944*t^2*z^2 + 82192*t^2*z - 253840*t^2 + 64*t*z^17 - 2240*t*z^16 + 36032*t*z^15 - 352672*t*z^14 + 2343776*t*z^13 - 11174624*t*z^12 + 39371888*t*z^11 - 104037424*t*z^10 + 207068848*t*z^9 - 309028032*t*z^8 + 341202768*t*z^7 - 272170128*t*z^6 + 151174400*t*z^5 - 55439056*t*z^4 + 12540016*t*z^3 - 1602224*t*z^2 + 203344*t*z + 388592*t - 16*z^20 + 656*z^19 - 12464*z^18 + 145600*z^17 - 1170032*z^16 + 6857504*z^15 - 30327968*z^14 + 103300000*z^13 - 274152256*z^12 + 569832048*z^11 - 927253824*z^10 + 1174527408*z^9 - 1144829408*z^8 + 843043888*z^7 - 456554512*z^6 + 175113008*z^5 - 45230704*z^4 + 7350832*z^3 - 686368*z^2 - 37984*z - 256544)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_48 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 48) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_48 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z^3 - 384*t^7*z^2 + 640*t^7*z - 368*t^7 + 160*t^6*z^6 - 1920*t^6*z^5 + 8768*t^6*z^4 - 19456*t^6*z^3 + 22720*t^6*z^2 - 13888*t^6*z + 3568*t^6 + 256*t^5*z^9 - 4608*t^5*z^8 + 34752*t^5*z^7 - 143664*t^5*z^6 + 359040*t^5*z^5 - 565968*t^5*z^4 + 568096*t^5*z^3 - 353616*t^5*z^2 + 125328*t^5*z - 19328*t^5 + 304*t^4*z^12 - 7296*t^4*z^11 + 76672*t^4*z^10 - 465200*t^4*z^9 + 1811904*t^4*z^8 - 4772688*t^4*z^7 + 8736784*t^4*z^6 - 11245008*t^4*z^5 + 10150624*t^4*z^4 - 6295840*t^4*z^3 + 2555568*t^4*z^2 - 610352*t^4*z + 64240*t^4 + 256*t^3*z^15 - 7680*t^3*z^14 + 103616*t^3*z^13 - 832240*t^3*z^12 + 4442752*t^3*z^11 - 16677520*t^3*z^10 + 45459104*t^3*z^9 - 91654560*t^3*z^8 + 137968976*t^3*z^7 - 155318832*t^3*z^6 + 129938464*t^3*z^5 - 79470800*t^3*z^4 + 34436304*t^3*z^3 - 9983600*t^3*z^2 + 1729184*t^3*z - 133424*t^3 + 160*t^2*z^18 - 5760*t^2*z^17 + 94848*t^2*z^16 - 947568*t^2*z^15 + 6425664*t^2*z^14 - 31364592*t^2*z^13 + 114083120*t^2*z^12 - 315970320*t^2*z^11 + 675433632*t^2*z^10 - 1123092304*t^2*z^9 + 1457093184*t^2*z^8 - 1472843376*t^2*z^7 + 1152251488*t^2*z^6 - 688601760*t^2*z^5 + 307465632*t^2*z^4 - 98910592*t^2*z^3 + 21550272*t^2*z^2 - 2828784*t^2*z + 167056*t^2 + 64*t*z^21 - 2688*t*z^20 + 52288*t*z^19 - 625664*t*z^18 + 5159424*t*z^17 - 31139184*t*z^16 + 142617152*t*z^15 - 507325776*t*z^14 + 1423355216*t*z^13 - 3181258400*t*z^12 + 5698719552*t*z^11 - 8204838208*t*z^10 + 9492847488*t*z^9 - 8796986304*t*z^8 + 6485451664*t*z^7 - 3762019632*t*z^6 + 1688741808*t*z^5 - 572397952*t*z^4 + 141102240*t*z^3 - 23773584*t*z^2 + 2433616*t*z - 113120*t + 16*z^24 - 768*z^23 + 17216*z^22 - 239536*z^21 + 2319232*z^20 - 16607728*z^19 + 91272384*z^18 - 394383168*z^17 + 1361946064*z^16 - 3801515952*z^15 + 8642369744*z^14 - 16081294288*z^13 + 24557005552*z^12 - 30794284096*z^11 + 31667683104*z^10 - 26614584768*z^9 + 18175604032*z^8 - 10001744880*z^7 + 4382993136*z^6 - 1504453696*z^5 + 394795344*z^4 - 76285136*z^3 + 10192576*z^2 - 835744*z + 31360:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z^2 + 800*t^6*z - 928*t^6 - 256*t^5*z^5 + 2816*t^5*z^4 - 11456*t^5*z^3 + 22000*t^5*z^2 - 21872*t^5*z + 10400*t^5 - 304*t^4*z^8 + 5168*t^4*z^7 - 36240*t^4*z^6 + 136736*t^4*z^5 - 305744*t^4*z^4 + 423088*t^4*z^3 - 364624*t^4*z^2 + 186720*t^4*z - 48400*t^4 - 256*t^3*z^11 + 5888*t^3*z^10 - 58816*t^3*z^9 + 336048*t^3*z^8 - 1219632*t^3*z^7 + 2959008*t^3*z^6 - 4924000*t^3*z^5 + 5667344*t^3*z^4 - 4469872*t^3*z^3 + 2335904*t^3*z^2 - 746176*t^3*z + 118592*t^3 - 160*t^2*z^14 + 4640*t^2*z^13 - 60128*t^2*z^12 + 460432*t^2*z^11 - 2323568*t^2*z^10 + 8167904*t^2*z^9 - 20634256*t^2*z^8 + 38130896*t^2*z^7 - 51970976*t^2*z^6 + 52220976*t^2*z^5 - 38271264*t^2*z^4 + 19952160*t^2*z^3 - 7049888*t^2*z^2 + 1531216*t^2*z - 160144*t^2 - 64*t*z^17 + 2240*t*z^16 - 35712*t*z^15 + 343808*t*z^14 - 2234816*t*z^13 + 10394224*t*z^12 - 35783984*t*z^11 + 93096416*t*z^10 - 185315920*t*z^9 + 284031040*t*z^8 - 335524080*t*z^7 + 304111312*t*z^6 - 209166944*t*z^5 + 107035648*t*z^4 - 39450336*t*z^3 + 9921344*t*z^2 - 1535568*t*z + 111824*t - 16*z^20 + 656*z^19 - 12400*z^18 + 143424*z^17 - 1136400*z^16 + 6545136*z^15 - 28387040*z^14 + 94807360*z^13 - 247378496*z^12 + 508921984*z^11 - 829770992*z^10 + 1074154240*z^9 - 1102377616*z^8 + 892391504*z^7 - 564651040*z^6 + 275371264*z^5 - 101380976*z^4 + 27280528*z^3 - 5074624*z^2 + 584864*z - 31360)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_49 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 49) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_49 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^3 + 12*t*z^2 - 18*t*z - 2*t + 2*z^6 - 24*z^5 + 108*z^4 - 224*z^3 + 210*z^2 - 72*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf
  · have hr : (16*t^8 + 64*t^7*z - 240*t^7 + 192*t^6*z^6 - 2304*t^6*z^5 + 10176*t^6*z^4 - 20208*t^6*z^3 + 17728*t^6*z^2 - 6192*t^6*z + 1872*t^6 + 576*t^5*z^7 - 9072*t^5*z^6 + 56448*t^5*z^5 - 175104*t^5*z^4 + 280336*t^5*z^3 - 215712*t^5*z^2 + 66240*t^5*z - 9504*t^5 + 864*t^4*z^12 - 20736*t^4*z^11 + 216000*t^4*z^10 - 1280880*t^4*z^9 + 4768704*t^4*z^8 - 11603952*t^4*z^7 + 18667728*t^4*z^6 - 19756512*t^4*z^5 + 13661440*t^4*z^4 - 6294912*t^4*z^3 + 2015136*t^4*z^2 - 386208*t^4*z + 33552*t^4 + 1728*t^3*z^13 - 47952*t^3*z^12 + 587520*t^3*z^11 - 4181760*t^3*z^10 + 19143264*t^3*z^9 - 58954752*t^3*z^8 + 124173600*t^3*z^7 - 178433472*t^3*z^6 + 171821488*t^3*z^5 - 107540496*t^3*z^4 + 42277824*t^3*z^3 - 10215504*t^3*z^2 + 1403280*t^3*z - 84240*t^3 + 1728*t^2*z^18 - 62208*t^2*z^17 + 1021248*t^2*z^16 - 10125648*t^2*z^15 + 67697856*t^2*z^14 - 322746768*t^2*z^13 + 1131669360*t^2*z^12 - 2967995520*t^2*z^11 + 5867230752*t^2*z^10 - 8753102784*t^2*z^9 + 9822817440*t^2*z^8 - 8246443968*t^2*z^7 + 5154300016*t^2*z^6 - 2393488080*t^2*z^5 + 821490624*t^2*z^4 - 202656384*t^2*z^3 + 33669648*t^2*z^2 - 3331152*t^2*z + 146448*t^2 + 1728*t*z^19 - 68688*t*z^18 + 1254528*t*z^17 - 13955328*t*z^16 + 105668496*t*z^15 - 576592992*t*z^14 + 2341615392*t*z^13 - 7208181792*t*z^12 + 16973471088*t*z^11 - 30645565488*t*z^10 + 42285274848*t*z^9 - 44221010112*t*z^8 + 34602141664*t*z^7 - 19923176400*t*z^6 + 8278262784*t*z^5 - 2427875856*t*z^4 + 487571760*t*z^3 - 63630144*t*z^2 + 4850928*t*z - 163296*t + 1296*z^24 - 62208*z^23 + 1394496*z^22 - 19394640*z^21 + 187527744*z^20 - 1338743376*z^19 + 7314861168*z^18 - 31296484512*z^17 + 106395307488*z^16 - 290013773760*z^15 + 636964144416*z^14 - 1129033281312*z^13 + 1613158057632*z^12 - 1851171998688*z^11 + 1696291441728*z^10 - 1231741650576*z^9 + 702326160448*z^8 - 311218336224*z^7 + 105917790384*z^6 - 27278965728*z^5 + 5205681936*z^4 - 711838800*z^3 + 65829024*z^2 - 3678048*z + 93312:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6*z^2 + 960*t^6*z - 768*t^6 - 576*t^5*z^3 + 5040*t^5*z^2 - 13104*t^5*z + 8208*t^5 - 864*t^4*z^8 + 14688*t^4*z^7 - 101088*t^4*z^6 + 360720*t^4*z^5 - 710064*t^4*z^4 + 760032*t^4*z^3 - 419760*t^4*z^2 + 136512*t^4*z - 38896*t^4 - 1728*t^3*z^9 + 35856*t^3*z^8 - 312336*t^3*z^7 + 1479600*t^3*z^6 - 4124784*t^3*z^5 + 6832320*t^3*z^4 - 6451248*t^3*z^3 + 3144384*t^3*z^2 - 709984*t^3*z + 106928*t^3 - 1728*t^2*z^14 + 50112*t^2*z^13 - 646272*t^2*z^12 + 4886352*t^2*z^11 - 24042960*t^2*z^10 + 80816832*t^2*z^9 - 189613008*t^2*z^8 + 312038784*t^2*z^7 - 357799536*t^2*z^6 + 282242160*t^2*z^5 - 152005536*t^2*z^4 + 56579904*t^2*z^3 - 14426368*t^2*z^2 + 2098400*t^2*z - 187904*t^2 - 1728*t*z^15 + 56592*t*z^14 - 834192*t*z^13 + 7309872*t*z^12 - 42366240*t*z^11 + 170960976*t*z^10 - 492448032*t*z^9 + 1021352112*t*z^8 - 1519679808*t*z^7 + 1598332032*t*z^6 - 1158168384*t*z^5 + 558392400*t*z^4 - 172701424*t*z^3 + 33093728*t*z^2 - 3479168*t*z + 205696*t - 1296*z^20 + 53136*z^19 - 1004400*z^18 + 11609568*z^17 - 91772784*z^16 + 525711600*z^15 - 2256180048*z^14 + 7397469936*z^13 - 18729031680*z^12 + 36770820912*z^11 - 55926014976*z^10 + 65529960336*z^9 - 58588526640*z^8 + 39453926784*z^7 - 19708883616*z^6 + 7186316832*z^5 - 1877631088*z^4 + 341487248*z^3 - 41126144*z^2 + 2895712*z - 116864)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_50 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 50) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_50 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z^3 + 768*t^7*z^2 - 1152*t^7*z + 80*t^7 + 448*t^6*z^6 - 5376*t^6*z^5 + 24192*t^6*z^4 - 49040*t^6*z^3 + 40224*t^6*z^2 - 5952*t^6*z + 160*t^6 - 896*t^5*z^9 + 16128*t^5*z^8 - 120960*t^5*z^7 + 486096*t^5*z^6 - 1115712*t^5*z^5 + 1428480*t^5*z^4 - 899952*t^5*z^3 + 193680*t^5*z^2 - 12672*t^5*z + 176*t^5 + 1120*t^4*z^12 - 26880*t^4*z^11 + 282240*t^4*z^10 - 1697680*t^4*z^9 + 6426720*t^4*z^8 - 15814080*t^4*z^7 + 25164384*t^4*z^6 - 24842448*t^4*z^5 + 13863024*t^4*z^4 - 3664960*t^4*z^3 + 399696*t^4*z^2 - 14544*t^4*z + 16*t^4 - 896*t^3*z^15 + 26880*t^3*z^14 - 362880*t^3*z^13 + 2907760*t^3*z^12 - 15354240*t^3*z^11 + 56057856*t^3*z^10 - 144330656*t^3*z^9 + 262183968*t^3*z^8 - 330383232*t^3*z^7 + 278278880*t^3*z^6 - 146927904*t^3*z^5 + 44034624*t^3*z^4 - 6684016*t^3*z^3 + 440016*t^3*z^2 - 8880*t^3*z + 32*t^3 + 448*t^2*z^18 - 16128*t^2*z^17 + 266112*t^2*z^16 - 2664240*t^2*z^15 + 18056160*t^2*z^14 - 87484608*t^2*z^13 + 311904672*t^2*z^12 - 829417248*t^2*z^11 + 1649026656*t^2*z^10 - 2433211520*t^2*z^9 + 2618140896*t^2*z^8 - 1994174640*t^2*z^7 + 1027707072*t^2*z^6 - 335977920*t^2*z^5 + 64002384*t^2*z^4 - 6329328*t^2*z^3 + 274032*t^2*z^2 - 4464*t^2*z + 160*t^2 - 128*t*z^21 + 5376*t*z^20 - 104832*t*z^19 + 1259120*t*z^18 - 10419264*t*z^17 + 62945280*t*z^16 - 286976112*t*z^15 + 1006515792*t*z^14 - 2743005312*t*z^13 + 5826016240*t*z^12 - 9614608800*t*z^11 + 12217649760*t*z^10 - 11769784048*t*z^9 + 8396436528*t*z^8 - 4290333120*t*z^7 + 1499357760*t*z^6 - 336362832*t*z^5 + 44227872*t*z^4 - 2910128*t*z^3 + 58080*t*z^2 + 1728*t*z - 64*t + 16*z^24 - 768*z^23 + 17280*z^22 - 242096*z^21 + 2366112*z^20 - 17126976*z^19 + 95137504*z^18 - 414633744*z^17 + 1437385392*z^16 - 3994384064*z^15 + 8925815184*z^14 - 16024099104*z^13 + 23001964048*z^12 - 26170720512*z^11 + 23288779824*z^10 - 15907170272*z^9 + 8126956080*z^8 - 2997241488*z^7 + 758604256*z^6 - 121452672*z^5 + 10155456*z^4 - 46544*z^3 - 68064*z^2 + 5280*z - 128:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6*z^2 + 2240*t^6*z - 2240*t^6 + 896*t^5*z^5 - 9856*t^5*z^4 + 39424*t^5*z^3 - 64976*t^5*z^2 + 29200*t^5*z + 10832*t^5 - 1120*t^4*z^8 + 19040*t^4*z^7 - 133280*t^4*z^6 + 489200*t^4*z^5 - 982960*t^4*z^4 + 999280*t^4*z^3 - 361104*t^4*z^2 - 28080*t^4*z - 26928*t^4 + 896*t^3*z^11 - 20608*t^3*z^10 + 206080*t^3*z^9 - 1169520*t^3*z^8 + 4116720*t^3*z^7 - 9198288*t^3*z^6 + 12746320*t^3*z^5 - 10080416*t^3*z^4 + 3668816*t^3*z^3 - 302496*t^3*z^2 + 57360*t^3*z + 32784*t^3 - 448*t^2*z^14 + 12992*t^2*z^13 - 168896*t^2*z^12 + 1296496*t^2*z^11 - 6511760*t^2*z^10 + 22387184*t^2*z^9 - 53488880*t^2*z^8 + 88183936*t^2*z^7 - 97285552*t^2*z^6 + 67339328*t^2*z^5 - 25807504*t^2*z^4 + 4303168*t^2*z^3 - 279664*t^2*z^2 - 23440*t^2*z - 18320*t^2 + 128*t*z^17 - 4480*t*z^16 + 71680*t*z^15 - 693616*t*z^14 + 4524464*t*z^13 - 20985488*t*z^12 + 71114592*t*z^11 - 178027488*t*z^10 + 328800240*t*z^9 - 442127504*t*z^8 + 421178416*t*z^7 - 271186384*t*z^6 + 109161264*t*z^5 - 24143472*t*z^4 + 2401632*t*z^3 - 61232*t*z^2 + 2320*t*z + 2144*t - 16*z^20 + 656*z^19 - 12464*z^18 + 145536*z^17 - 1167600*z^16 + 6815904*z^15 - 29903024*z^14 + 100403584*z^13 - 260223136*z^12 + 521131840*z^11 - 801636704*z^10 + 934607744*z^9 - 807518128*z^8 + 499359728*z^7 - 209509280*z^6 + 54816352*z^5 - 7715744*z^4 + 368384*z^3 + 34944*z^2 - 2400*z + 1344)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_51 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 51) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_51 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z^3 - 768*t^7*z^2 + 1088*t^7*z - 368*t^7 + 448*t^6*z^6 - 5376*t^6*z^5 + 23744*t^6*z^4 - 48272*t^6*z^3 + 47872*t^6*z^2 - 22064*t^6*z + 3568*t^6 + 896*t^5*z^9 - 16128*t^5*z^8 + 119616*t^5*z^7 - 475440*t^5*z^6 + 1109760*t^5*z^5 - 1577568*t^5*z^4 + 1368560*t^5*z^3 - 697056*t^5*z^2 + 186144*t^5*z - 19328*t^5 + 1120*t^4*z^12 - 26880*t^4*z^11 + 280000*t^4*z^10 - 1666000*t^4*z^9 + 6282240*t^4*z^8 - 15782160*t^4*z^7 + 27075856*t^4*z^6 - 31983552*t^4*z^5 + 25812640*t^4*z^4 - 13831424*t^4*z^3 + 4627200*t^4*z^2 - 852832*t^4*z + 64240*t^4 + 896*t^3*z^15 - 26880*t^3*z^14 + 360640*t^3*z^13 - 2862160*t^3*z^12 + 14988800*t^3*z^11 - 54761536*t^3*z^10 + 144040864*t^3*z^9 - 277689792*t^3*z^8 + 395684512*t^3*z^7 - 416711904*t^3*z^6 + 321304208*t^3*z^5 - 177494960*t^3*z^4 + 67534080*t^3*z^3 - 16520816*t^3*z^2 + 2288176*t^3*z - 133424*t^3 + 448*t^2*z^18 - 16128*t^2*z^17 + 264768*t^2*z^16 - 2628528*t^2*z^15 + 17652480*t^2*z^14 - 85036368*t^2*z^13 + 304201424*t^2*z^12 - 825804672*t^2*z^11 + 1724268000*t^2*z^10 - 2789954912*t^2*z^9 + 3506301888*t^2*z^8 - 3412253664*t^2*z^7 + 2547822736*t^2*z^6 - 1434927504*t^2*z^5 + 592872768*t^2*z^4 - 171987968*t^2*z^3 + 32620272*t^2*z^2 - 3563952*t^2*z + 167056*t^2 + 128*t*z^21 - 5376*t*z^20 + 104384*t*z^19 - 1244432*t*z^18 + 10205952*t*z^17 - 61161312*t*z^16 + 277762288*t*z^15 - 978820704*t*z^14 + 2719134400*t*z^13 - 6017465504*t*z^12 + 10677051216*t*z^11 - 15234203248*t*z^10 + 17470308288*t*z^9 - 16034570112*t*z^8 + 11678086976*t*z^7 - 6655902768*t*z^6 + 2907321216*t*z^5 - 943836592*t*z^4 + 217539600*t*z^3 - 33128352*t*z^2 + 2938736*t*z - 113120*t + 16*z^24 - 768*z^23 + 17216*z^22 - 239600*z^21 + 2321920*z^20 - 16659824*z^19 + 91890864*z^18 - 399419328*z^17 + 1391798272*z^16 - 3934980768*z^15 + 9102657056*z^14 - 17323658720*z^13 + 27205123456*z^12 - 35273307872*z^11 + 37686094464*z^10 - 33022564560*z^9 + 23545555552*z^8 - 13501760832*z^7 + 6124690512*z^6 - 2148081824*z^5 + 564185616*z^4 - 105979024*z^3 + 13261600*z^2 - 975296*z + 31360:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6*z^2 + 2240*t^6*z - 1792*t^6 - 896*t^5*z^5 + 9856*t^5*z^4 - 38080*t^5*z^3 + 63728*t^5*z^2 - 50800*t^5*z + 15280*t^5 - 1120*t^4*z^8 + 19040*t^4*z^7 - 131040*t^4*z^6 + 473200*t^4*z^5 - 981840*t^4*z^4 + 1217120*t^4*z^3 - 893616*t^4*z^2 + 360640*t^4*z - 58736*t^4 - 896*t^3*z^11 + 20608*t^3*z^10 - 203840*t^3*z^9 + 1139600*t^3*z^8 - 3992080*t^3*z^7 + 9211248*t^3*z^6 - 14352368*t^3*z^5 + 15189504*t^3*z^4 - 10742768*t^3*z^3 + 4829280*t^3*z^2 - 1232096*t^3*z + 128720*t^3 - 448*t^2*z^14 + 12992*t^2*z^13 - 167552*t^2*z^12 + 1270192*t^2*z^11 - 6311024*t^2*z^10 + 21723104*t^2*z^9 - 53456272*t^2*z^8 + 95728928*t^2*z^7 - 125681840*t^2*z^6 + 120603760*t^2*z^5 - 83242112*t^2*z^4 + 39922592*t^2*z^3 - 12463104*t^2*z^2 + 2228832*t^2*z - 164640*t^2 - 128*t*z^17 + 4480*t*z^16 - 71232*t*z^15 + 682064*t*z^14 - 4398288*t*z^13 + 20250064*t*z^12 - 68908064*t*z^11 + 177094992*t*z^10 - 348357760*t*z^9 + 528116720*t*z^8 - 617557536*t*z^7 + 553709344*t*z^6 - 375245856*t*z^5 + 187341296*t*z^4 - 66023632*t*z^3 + 15283008*t*z^2 - 2033088*t*z + 112512*t - 16*z^20 + 656*z^19 - 12400*z^18 + 143488*z^17 - 1138640*z^16 + 6580656*z^15 - 28725008*z^14 + 96962480*z^13 - 257126912*z^12 + 541236944*z^11 - 909796832*z^10 + 1223785904*z^9 - 1314444016*z^8 + 1119585504*z^7 - 746695648*z^6 + 382159936*z^5 - 145568880*z^4 + 39388880*z^3 - 7028896*z^2 + 724256*z - 31360)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_52 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 52) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_52 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^3 + 12*t*z^2 - 18*t*z - 2*t + 2*z^6 - 24*z^5 + 108*z^4 - 224*z^3 + 210*z^2 - 72*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf
  · have hr : (16*t^8 + 64*t^7*z - 240*t^7 - 48*t^6*z^3 + 448*t^6*z^2 - 1392*t^6*z + 1488*t^6 - 144*t^5*z^4 + 1696*t^5*z^3 - 6912*t^5*z^2 + 11088*t^5*z - 5184*t^5 - 288*t^4*z^5 + 3760*t^4*z^4 - 18528*t^4*z^3 + 42048*t^4*z^2 - 41472*t^4*z + 11088*t^4 - 336*t^3*z^6 + 5152*t^3*z^5 - 30912*t^3*z^4 + 90336*t^3*z^3 - 129600*t^3*z^2 + 80064*t^3*z - 14256*t^3 - 288*t^2*z^7 + 4768*t^2*z^6 - 31968*t^2*z^5 + 110736*t^2*z^4 - 207792*t^2*z^3 + 198720*t^2*z^2 - 79056*t^2*z + 9936*t^2 - 144*t*z^8 + 2656*t*z^7 - 20112*t*z^6 + 79776*t*z^5 - 175392*t*z^4 + 208368*t*z^3 - 121824*t*z^2 + 30672*t*z - 2592*t - 48*z^9 + 880*z^8 - 6576*z^7 + 26112*z^6 - 60048*z^5 + 81072*z^4 - 60912*z^3 + 21600*z^2 - 2592*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(144*t^5 + 288*t^4*z - 1744*t^4 + 336*t^3*z^2 - 2800*t^3*z + 6608*t^3 + 288*t^2*z^3 - 2752*t^2*z^2 + 8672*t^2*z - 9200*t^2 + 144*t*z^4 - 1648*t*z^3 + 6560*t*z^2 - 9632*t*z + 2800*t + 48*z^5 - 544*z^4 + 2096*z^3 - 3440*z^2 + 2224*z - 32)*hf
  · have hr : (16*t^8 - 192*t^7*z^3 + 1152*t^7*z^2 - 1664*t^7*z + 144*t^7 + 1056*t^6*z^6 - 12672*t^6*z^5 + 56448*t^6*z^4 - 112512*t^6*z^3 + 92032*t^6*z^2 - 17088*t^6*z + 1008*t^6 - 3456*t^5*z^9 + 62208*t^5*z^8 - 464256*t^5*z^7 + 1849392*t^5*z^6 - 4205376*t^5*z^5 + 5377824*t^5*z^4 - 3507440*t^5*z^3 + 925920*t^5*z^2 - 106560*t^5*z + 4320*t^5 + 7344*t^4*z^12 - 176256*t^4*z^11 + 1845504*t^4*z^10 - 11044944*t^4*z^9 + 41558688*t^4*z^8 - 101780928*t^4*z^7 + 162189600*t^4*z^6 - 163043712*t^4*z^5 + 96802864*t^4*z^4 - 30820896*t^4*z^3 + 5226192*t^4*z^2 - 447120*t^4*z + 15408*t^4 - 10368*t^3*z^15 + 311040*t^3*z^14 - 4192128*t^3*z^13 + 33492528*t^3*z^12 - 176211072*t^3*z^11 + 641208096*t^3*z^10 - 1648789296*t^3*z^9 + 3006264096*t^3*z^8 - 3842128800*t^3*z^7 + 3352275456*t^3*z^6 - 1916426336*t^3*z^5 + 684482736*t^3*z^4 - 149193216*t^3*z^3 + 19207152*t^3*z^2 - 1336464*t^3*z + 38448*t^3 + 9504*t^2*z^18 - 342144*t^2*z^17 + 5640192*t^2*z^16 - 56377296*t^2*z^15 + 381342816*t^2*z^14 - 1844498304*t^2*z^13 + 6571771488*t^2*z^12 - 17504652096*t^2*z^11 + 35009965008*t^2*z^10 - 52358968080*t^2*z^9 + 57852747792*t^2*z^8 - 46309933728*t^2*z^7 + 26169043264*t^2*z^6 - 10154284560*t^2*z^5 + 2647294560*t^2*z^4 - 452564928*t^2*z^3 + 48537360*t^2*z^2 - 2965680*t^2*z + 79056*t^2 - 5184*t*z^21 + 217728*t*z^20 - 4243968*t*z^19 + 50940576*t*z^18 - 421262208*t*z^17 + 2544169824*t*z^16 - 11605210416*t*z^15 + 40785132960*t*z^14 - 111647713824*t*z^13 + 239120673264*t*z^12 - 400319620704*t*z^11 + 520906132656*t*z^10 - 521547921984*t*z^9 + 396179337744*t*z^8 - 224450654768*t*z^7 + 93123896976*t*z^6 - 27798591168*t*z^5 + 5850471888*t*z^4 - 841911696*t*z^3 + 78456816*t*z^2 - 4246992*t*z + 101088*t + 1296*z^24 - 62208*z^23 + 1399680*z^22 - 19612368*z^21 + 191765664*z^20 - 1389472704*z^19 + 7732769328*z^18 - 33808669056*z^17 + 117796728816*z^16 - 329887133136*z^15 + 745688544048*z^14 - 1361461167792*z^13 + 2002940021712*z^12 - 2362094721504*z^11 + 2215921704480*z^10 - 1637471392176*z^9 + 942373035232*z^8 - 417273241488*z^7 + 140357274048*z^6 - 35336780496*z^5 + 6523055568*z^4 - 854413920*z^3 + 74994336*z^2 - 3942432*z + 93312:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6*z^2 + 5280*t^6*z - 4704*t^6 + 3456*t^5*z^5 - 38016*t^5*z^4 + 149760*t^5*z^3 - 241200*t^5*z^2 + 112752*t^5*z + 24336*t^5 - 7344*t^4*z^8 + 124848*t^4*z^7 - 868752*t^4*z^6 + 3157056*t^4*z^5 - 6290640*t^4*z^4 + 6472800*t^4*z^3 - 2685840*t^4*z^2 + 141456*t^4*z - 137872*t^4 + 10368*t^3*z^11 - 238464*t^3*z^10 + 2377728*t^3*z^9 - 13426992*t^3*z^8 + 47015856*t^3*z^7 - 104858928*t^3*z^6 + 146761152*t^3*z^5 - 121357200*t^3*z^4 + 52084992*t^3*z^3 - 9731568*t^3*z^2 + 1496720*t^3*z + 273392*t^3 - 9504*t^2*z^14 + 275616*t^2*z^13 - 3577824*t^2*z^12 + 27397872*t^2*z^11 - 137253744*t^2*z^10 + 471253680*t^2*z^9 - 1128682512*t^2*z^8 + 1880895168*t^2*z^7 - 2134860480*t^2*z^6 + 1581698592*t^2*z^5 - 716967072*t^2*z^4 + 187604928*t^2*z^3 - 29820544*t^2*z^2 + 1636592*t^2*z - 544304*t^2 + 5184*t*z^17 - 181440*t*z^16 + 2901312*t*z^15 - 28049760*t*z^14 + 182838816*t*z^13 - 848209536*t*z^12 + 2880700848*t*z^11 - 7254533232*t*z^10 + 13567654224*t*z^9 - 18689812128*t*z^8 + 18626809968*t*z^7 - 13065326064*t*z^6 + 6229148736*t*z^5 - 1956439824*t*z^4 + 398075216*t*z^3 - 48696976*t*z^2 + 3991984*t*z + 271216*t - 1296*z^20 + 53136*z^19 - 1009584*z^18 + 11791008*z^17 - 94668048*z^16 + 553592448*z^15 - 2436931872*z^14 + 8230716288*z^13 - 21541260960*z^12 + 43819230960*z^11 - 69093611712*z^10 + 83775848400*z^9 - 77103410304*z^8 + 52940847120*z^7 - 26587631472*z^6 + 9582981360*z^5 - 2435137840*z^4 + 423638672*z^3 - 48391232*z^2 + 3016384*z - 216416)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_53 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 53) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : (t - 2*z^3 + 13*z^2 - 21*z + 3:ℝ)=0 := by
  apply cell_5_53 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z^3 + 24*t*z^2 - 36*t*z + 2*t + 2*z^6 - 24*z^5 + 108*z^4 - 224*z^3 + 210*z^2 - 72*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf
  · have hr : (16*t^8 - 64*t^7*z^3 + 384*t^7*z^2 - 512*t^7*z - 112*t^7 + 160*t^6*z^6 - 1920*t^6*z^5 + 8320*t^6*z^4 - 15136*t^6*z^3 + 8896*t^6*z^2 + 1696*t^6*z + 304*t^6 - 256*t^5*z^9 + 4608*t^5*z^8 - 33792*t^5*z^7 + 128688*t^5*z^6 - 266304*t^5*z^5 + 277728*t^5*z^4 - 100592*t^5*z^3 - 18912*t^5*z^2 + 192*t^5*z - 544*t^5 + 304*t^4*z^12 - 7296*t^4*z^11 + 75392*t^4*z^10 - 437648*t^4*z^9 + 1559328*t^4*z^8 - 3487872*t^4*z^7 + 4775648*t^4*z^6 - 3648384*t^4*z^5 + 1175728*t^4*z^4 + 15360*t^4*z^3 + 1872*t^4*z^2 - 2800*t^4*z + 496*t^4 - 256*t^3*z^15 + 7680*t^3*z^14 - 102400*t^3*z^13 + 798832*t^3*z^12 - 4037248*t^3*z^11 + 13815584*t^3*z^10 - 32449392*t^3*z^9 + 51773664*t^3*z^8 - 53995616*t^3*z^7 + 33699520*t^3*z^6 - 9994400*t^3*z^5 + 143088*t^3*z^4 + 375296*t^3*z^3 - 62992*t^3*z^2 + 5168*t^3*z + 176*t^3 + 160*t^2*z^18 - 5760*t^2*z^17 + 94080*t^2*z^16 - 921936*t^2*z^15 + 6038880*t^2*z^14 - 27875136*t^2*z^13 + 93109600*t^2*z^12 - 227361792*t^2*z^11 + 404792208*t^2*z^10 - 517321360*t^2*z^9 + 459594192*t^2*z^8 - 267897216*t^2*z^7 + 92063968*t^2*z^6 - 14882256*t^2*z^5 + 657120*t^2*z^4 - 125792*t^2*z^3 + 55536*t^2*z^2 - 3696*t^2*z - 560*t^2 - 64*t*z^21 + 2688*t*z^20 - 51968*t*z^19 + 613088*t*z^18 - 4932480*t*z^17 + 28646304*t*z^16 - 123986416*t*z^15 + 407007648*t*z^14 - 1021254176*t*z^13 + 1958476656*t*z^12 - 2848313760*t*z^11 + 3089623760*t*z^10 - 2427603552*t*z^9 + 1312647696*t*z^8 - 440372240*t*z^7 + 65989072*t*z^6 + 7326048*t*z^5 - 4348784*t*z^4 + 537424*t*z^3 + 2640*t*z^2 - 6608*t*z + 608*t + 16*z^24 - 768*z^23 + 17152*z^22 - 236656*z^21 + 2259040*z^20 - 15831968*z^19 + 84368432*z^18 - 349357632*z^17 + 1139058160*z^16 - 2945464880*z^15 + 6056270704*z^14 - 9886426704*z^13 + 12743514576*z^12 - 12846467872*z^11 + 9983363136*z^10 - 5860804048*z^9 + 2527161760*z^8 - 769731472*z^7 + 156381088*z^6 - 18988592*z^5 + 781136*z^4 + 163488*z^3 - 34592*z^2 + 3040*z - 128:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z^2 + 800*t^6*z - 480*t^6 + 256*t^5*z^5 - 2816*t^5*z^4 + 10496*t^5*z^3 - 13744*t^5*z^2 + 368*t^5*z + 4048*t^5 - 304*t^4*z^8 + 5168*t^4*z^7 - 34960*t^4*z^6 + 118144*t^4*z^5 - 201232*t^4*z^4 + 140384*t^4*z^3 + 4400*t^4*z^2 - 14192*t^4*z - 12368*t^4 + 256*t^3*z^11 - 5888*t^3*z^10 + 57600*t^3*z^9 - 311152*t^3*z^8 + 1005424*t^3*z^7 - 1954800*t^3*z^6 + 2143040*t^3*z^5 - 1050640*t^3*z^4 - 5248*t^3*z^3 + 71824*t^3*z^2 + 22480*t^3*z + 17392*t^3 - 160*t^2*z^14 + 4640*t^2*z^13 - 59360*t^2*z^12 + 440176*t^2*z^11 - 2089328*t^2*z^10 + 6607856*t^2*z^9 - 14023248*t^2*z^8 + 19534272*t^2*z^7 - 16774656*t^2*z^6 + 7625120*t^2*z^5 - 1075744*t^2*z^4 - 116192*t^2*z^3 - 41280*t^2*z^2 - 11088*t^2*z - 10608*t^2 + 64*t*z^17 - 2240*t*z^16 + 35392*t*z^15 - 333472*t*z^14 + 2084704*t*z^13 - 9099392*t*z^12 + 28401648*t*z^11 - 63793520*t*z^10 + 102196624*t*z^9 - 113678432*t*z^8 + 83062192*t*z^7 - 35323856*t*z^6 + 5841792*t*z^5 + 954800*t*z^4 - 382288*t*z^3 + 25904*t*z^2 + 3920*t*z + 464*t - 16*z^20 + 656*z^19 - 12336*z^18 + 140992*z^17 - 1094128*z^16 + 6099840*z^15 - 25211488*z^14 + 78585440*z^13 - 186106400*z^12 + 334732176*z^11 - 453760864*z^10 + 456413552*z^9 - 332003808*z^8 + 167832400*z^7 - 55413744*z^6 + 10810224*z^5 - 1034768*z^4 + 2608*z^3 + 19456*z^2 - 96*z + 1440)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_54 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 54) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_54 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^3 + 12*t*z^2 - 20*t*z + 2*z^6 - 24*z^5 + 106*z^4 - 210*z^3 + 182*z^2 - 54*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 8)*hf
  · have hr : (16*t^8 - 176*t^7 - 48*t^6*z^3 + 288*t^6*z^2 - 480*t^6*z + 736*t^6 + 432*t^5*z^3 - 2592*t^5*z^2 + 4320*t^5*z - 1616*t^5 + 144*t^4*z^4 - 2016*t^4*z^3 + 8208*t^4*z^2 - 11664*t^4*z + 1936*t^4 - 1008*t^3*z^4 + 6864*t^3*z^3 - 13968*t^3*z^2 + 9168*t^3*z - 608*t^3 + 1296*t^2*z^4 - 7344*t^2*z^3 + 9072*t^2*z^2 + 3024*t^2*z - 992*t^2 + 1152*t*z^4 - 7488*t*z^3 + 13824*t*z^2 - 6912*t*z + 832*t - 288*z^4 + 1824*z^3 - 3168*z^2 + 1248*z - 128:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-144*t^4 + 1008*t^3 - 1296*t^2 - 1152*t + 288)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_55 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 55) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_55 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z^3 + 24*t*z^2 - 36*t*z + 2*z^6 - 24*z^5 + 108*z^4 - 222*z^3 + 198*z^2 - 54*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf
  · have hr : (16*t^8 - 64*t^7*z - 112*t^7 - 48*t^6*z^3 + 448*t^6*z^2 - 208*t^6*z + 304*t^6 + 144*t^5*z^4 - 832*t^5*z^3 - 768*t^5*z^2 + 2544*t^5*z - 544*t^5 - 288*t^4*z^5 + 1744*t^4*z^4 - 1184*t^4*z^3 + 96*t^4*z^2 - 4256*t^4*z + 496*t^4 + 336*t^3*z^6 - 1984*t^3*z^5 + 544*t^3*z^4 + 8288*t^3*z^3 - 8608*t^3*z^2 + 1696*t^3*z + 176*t^3 - 288*t^2*z^7 + 2176*t^2*z^6 - 4224*t^2*z^5 + 1104*t^2*z^4 - 2416*t^2*z^3 + 7584*t^2*z^2 + 1680*t^2*z - 560*t^2 + 144*t*z^8 - 1216*t*z^7 + 2384*t*z^6 + 3552*t*z^5 - 13184*t*z^4 + 3856*t*z^3 + 10752*t*z^2 - 5488*t*z + 608*t - 48*z^9 + 592*z^8 - 2704*z^7 + 5536*z^6 - 4432*z^5 - 1232*z^4 + 5456*z^3 - 5024*z^2 + 1472*z - 128:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-144*t^5 + 288*t^4*z + 272*t^4 - 336*t^3*z^2 - 368*t^3*z + 1584*t^3 + 288*t^2*z^3 - 160*t^2*z^2 - 928*t^2*z - 3056*t^2 - 144*t*z^4 + 208*t*z^3 + 1088*t*z^2 - 240*t + 48*z^5 - 256*z^4 + 240*z^3 + 112*z^2 - 240*z + 160)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_56 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 56) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_56 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z^3 - 384*t^7*z^2 + 576*t^7*z - 304*t^7 + 160*t^6*z^6 - 1920*t^6*z^5 + 8448*t^6*z^4 - 17216*t^6*z^3 + 17952*t^6*z^2 - 9840*t^6*z + 2368*t^6 + 256*t^5*z^9 - 4608*t^5*z^8 + 33984*t^5*z^7 - 133680*t^5*z^6 + 308736*t^5*z^5 - 438912*t^5*z^4 + 391152*t^5*z^3 - 215136*t^5*z^2 + 68544*t^5*z - 10048*t^5 + 304*t^4*z^12 - 7296*t^4*z^11 + 75456*t^4*z^10 - 442096*t^4*z^9 + 1627488*t^4*z^8 - 3962016*t^4*z^7 + 6564480*t^4*z^6 - 7519824*t^4*z^5 + 5977440*t^4*z^4 - 3254176*t^4*z^3 + 1166640*t^4*z^2 - 252144*t^4*z + 25456*t^4 + 256*t^3*z^15 - 7680*t^3*z^14 + 102336*t^3*z^13 - 800240*t^3*z^12 + 4092288*t^3*z^11 - 14458656*t^3*z^10 + 36418768*t^3*z^9 - 66638592*t^3*z^8 + 89540064*t^3*z^7 - 88731904*t^3*z^6 + 64699536*t^3*z^5 - 34338768*t^3*z^4 + 12949808*t^3*z^3 - 3309360*t^3*z^2 + 520752*t^3*z - 38608*t^3 + 160*t^2*z^18 - 5760*t^2*z^17 + 93888*t^2*z^16 - 917808*t^2*z^15 + 6011424*t^2*z^14 - 27937440*t^2*z^13 + 95265024*t^2*z^12 - 243381024*t^2*z^11 + 472131216*t^2*z^10 - 701334608*t^2*z^9 + 801418032*t^2*z^8 - 705031920*t^2*z^7 + 475754640*t^2*z^6 - 243946656*t^2*z^5 + 93415680*t^2*z^4 - 25927152*t^2*z^3 + 4945104*t^2*z^2 - 585504*t^2*z + 32704*t^2 + 64*t*z^21 - 2688*t*z^20 + 51840*t*z^19 - 609088*t*z^18 + 4879296*t*z^17 - 28271232*t*z^16 + 122715120*t*z^15 - 408039984*t*z^14 + 1054628352*t*z^13 - 2139148736*t*z^12 + 3425514096*t*z^11 - 4344431328*t*z^10 + 4366758512*t*z^9 - 3472178688*t*z^8 + 2173752576*t*z^7 - 1062720768*t*z^6 + 400674816*t*z^5 - 114375168*t*z^4 + 23999776*t*z^3 - 3499440*t*z^2 + 315792*t*z - 13120*t + 16*z^24 - 768*z^23 + 17088*z^22 - 234032*z^21 + 2209920*z^20 - 15276432*z^19 + 80136928*z^18 - 326469312*z^17 + 1048885344*z^16 - 2685305984*z^15 + 5516445552*z^14 - 9134416272*z^13 + 12223694656*z^12 - 13233744768*z^11 + 11585706432*z^10 - 8185485152*z^9 + 4650474384*z^8 - 2114015040*z^7 + 763738000*z^6 - 216961248*z^5 + 47533632*z^4 - 7757744*z^3 + 884256*z^2 - 61248*z + 1792:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z^2 + 800*t^6*z - 608*t^6 - 256*t^5*z^5 + 2816*t^5*z^4 - 10688*t^5*z^3 + 17392*t^5*z^2 - 14576*t^5*z + 5072*t^5 - 304*t^4*z^8 + 5168*t^4*z^7 - 35024*t^4*z^6 + 122144*t^4*z^5 - 240496*t^4*z^4 + 283168*t^4*z^3 - 203184*t^4*z^2 + 87072*t^4*z - 17520*t^4 - 256*t^3*z^11 + 5888*t^3*z^10 - 57536*t^3*z^9 + 313008*t^3*z^8 - 1048368*t^3*z^7 + 2271792*t^3*z^6 - 3277472*t^3*z^5 + 3191248*t^3*z^4 - 2094016*t^3*z^3 + 904752*t^3*z^2 - 242592*t^3*z + 30720*t^3 - 160*t^2*z^14 + 4640*t^2*z^13 - 59168*t^2*z^12 + 437392*t^2*z^11 - 2084048*t^2*z^10 + 6747632*t^2*z^9 - 15296624*t^2*z^8 + 24728032*t^2*z^7 - 28817152*t^2*z^6 + 24301472*t^2*z^5 - 14746720*t^2*z^4 + 6319024*t^2*z^3 - 1838464*t^2*z^2 + 335840*t^2*z - 27392*t^2 - 64*t*z^17 + 2240*t*z^16 - 35264*t*z^15 + 330368*t*z^14 - 2055040*t*z^13 + 8976448*t*z^12 - 28431216*t*z^11 + 66580512*t*z^10 - 116661120*t*z^9 + 153967552*t*z^8 - 153410240*t*z^7 + 115144448*t*z^6 - 64602480*t*z^5 + 26689584*t*z^4 - 7924944*t*z^3 + 1627696*t*z^2 - 212576*t*z + 10256*t - 16*z^20 + 656*z^19 - 12272*z^18 + 138816*z^17 - 1061136*z^16 + 5806224*z^15 - 23514656*z^14 + 71951680*z^13 - 168507472*z^12 + 304506688*z^11 - 426666032*z^10 + 464648960*z^9 - 393266512*z^8 + 257958800*z^7 - 130405952*z^6 + 50439232*z^5 - 14779520*z^4 + 3202736*z^3 - 485760*z^2 + 47232*z - 960)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_57 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 57) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_57 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^3 + 12*t*z^2 - 20*t*z + 2*z^6 - 24*z^5 + 106*z^4 - 210*z^3 + 182*z^2 - 54*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 8)*hf
  · have hr : (16*t^8 - 176*t^7 + 192*t^6*z^6 - 2304*t^6*z^5 + 9984*t^6*z^4 - 18864*t^6*z^3 + 14880*t^6*z^2 - 3552*t^6*z + 928*t^6 - 1584*t^5*z^6 + 19008*t^5*z^5 - 82368*t^5*z^4 + 155664*t^5*z^3 - 122976*t^5*z^2 + 29664*t^5*z - 3200*t^5 + 864*t^4*z^12 - 20736*t^4*z^11 + 214272*t^4*z^10 - 1248048*t^4*z^9 + 4507488*t^4*z^8 - 10467360*t^4*z^7 + 15693984*t^4*z^6 - 14895360*t^4*z^5 + 8656848*t^4*z^4 - 3094416*t^4*z^3 + 782640*t^4*z^2 - 117360*t^4*z + 7408*t^4 - 4752*t^3*z^12 + 114048*t^3*z^11 - 1178496*t^3*z^10 + 6864480*t^3*z^9 - 24795072*t^3*z^8 + 57599424*t^3*z^7 - 86412480*t^3*z^6 + 81953280*t^3*z^5 - 46943088*t^3*z^4 + 15346800*t^3*z^3 - 2871888*t^3*z^2 + 290064*t^3*z - 11792*t^3 + 1728*t^2*z^18 - 62208*t^2*z^17 + 1016064*t^2*z^16 - 9964944*t^2*z^15 + 65460960*t^2*z^14 - 304261920*t^2*z^13 + 1030604256*t^2*z^12 - 2582150400*t^2*z^11 + 4808668896*t^2*z^10 - 6636255264*t^2*z^9 + 6723280800*t^2*z^8 - 4932103392*t^2*z^7 + 2586261600*t^2*z^6 - 967170240*t^2*z^5 + 260684208*t^2*z^4 - 49697856*t^2*z^3 + 6205104*t^2*z^2 - 437040*t^2*z + 12256*t^2 - 4752*t*z^18 + 171072*t*z^17 - 2794176*t*z^16 + 27403920*t*z^15 - 180027360*t*z^14 + 836850528*t*z^13 - 2835172800*t*z^12 + 7105812480*t*z^11 - 13238421840*t*z^10 + 18271779984*t*z^9 - 18481504752*t*z^8 + 13455043920*t*z^7 - 6882180624*t*z^6 + 2407351968*t*z^5 - 561773232*t*z^4 + 84798144*t*z^3 - 7819920*t*z^2 + 387792*t*z - 7232*t + 1296*z^24 - 62208*z^23 + 1389312*z^22 - 19171728*z^21 + 183091104*z^20 - 1284488928*z^19 + 6858498528*z^18 - 28495120896*z^17 + 93401109072*z^16 - 243477618768*z^15 + 506588840496*z^14 - 841210120368*z^13 + 1111051016496*z^12 - 1159646082624*z^11 + 947518340976*z^10 - 598826978784*z^9 + 288690720624*z^8 - 104625295056*z^7 + 28093361088*z^6 - 5499454752*z^5 + 767148384*z^4 - 73368000*z^3 + 4475712*z^2 - 149568*z + 1792:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6*z^2 + 960*t^6*z - 576*t^6 + 1584*t^5*z^2 - 7920*t^5*z + 4752*t^5 - 864*t^4*z^8 + 14688*t^4*z^7 - 99360*t^4*z^6 + 339984*t^4*z^5 - 618192*t^4*z^4 + 570672*t^4*z^3 - 225360*t^4*z^2 + 42912*t^4*z - 17856*t^4 + 4752*t^3*z^8 - 80784*t^3*z^7 + 546480*t^3*z^6 - 1870128*t^3*z^5 + 3402432*t^3*z^4 - 3147984*t^3*z^3 + 1235040*t^3*z^2 - 146640*t^3*z + 39744*t^3 - 1728*t^2*z^14 + 50112*t^2*z^13 - 641088*t^2*z^12 + 4761936*t^2*z^11 - 22749552*t^2*z^10 + 73169136*t^2*z^9 - 161190000*t^2*z^8 + 242694144*t^2*z^7 - 245047248*t^2*z^6 + 160517376*t^2*z^5 - 66254544*t^2*z^4 + 18006192*t^2*z^3 - 3468384*t^2*z^2 + 251136*t^2*z - 64800*t^2 + 4752*t*z^14 - 137808*t*z^13 + 1762992*t*z^12 - 13095648*t*z^11 + 62568720*t*z^10 - 201288672*t*z^9 + 443661840*t*z^8 - 668492784*t*z^7 + 674828496*t*z^6 - 438498144*t*z^5 + 172814688*t*z^4 - 39246336*t*z^3 + 5236992*t*z^2 - 228672*t*z + 69264*t - 1296*z^20 + 53136*z^19 - 999216*z^18 + 11422944*z^17 - 88715088*z^16 + 495515232*z^15 - 2055497904*z^14 + 6448278672*z^13 - 15433350768*z^12 + 28228763520*z^11 - 39278857824*z^10 + 41140341504*z^9 - 31901157504*z^8 + 17913572928*z^7 - 7105535568*z^6 + 1948607280*z^5 - 363230784*z^4 + 44320176*z^3 - 3495072*z^2 + 53232*z - 52560)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_58 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 58) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_58 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z^3 - 384*t^7*z^2 + 512*t^7*z - 240*t^7 + 160*t^6*z^6 - 1920*t^6*z^5 + 8320*t^6*z^4 - 16320*t^6*z^3 + 16000*t^6*z^2 - 7776*t^6*z + 1488*t^6 + 256*t^5*z^9 - 4608*t^5*z^8 + 33792*t^5*z^7 - 131184*t^5*z^6 + 296256*t^5*z^5 - 407520*t^5*z^4 + 346064*t^5*z^3 - 175968*t^5*z^2 + 48384*t^5*z - 5184*t^5 + 304*t^4*z^12 - 7296*t^4*z^11 + 75392*t^4*z^10 - 440880*t^4*z^9 + 1617504*t^4*z^8 - 3914496*t^4*z^7 + 6416288*t^4*z^6 - 7201920*t^4*z^5 + 5512048*t^4*z^4 - 2807040*t^4*z^3 + 898128*t^4*z^2 - 159408*t^4*z + 11088*t^4 + 256*t^3*z^15 - 7680*t^3*z^14 + 102400*t^3*z^13 - 801840*t^3*z^12 + 4109440*t^3*z^11 - 14561568*t^3*z^10 + 36796112*t^3*z^9 - 67496352*t^3*z^8 + 90660512*t^3*z^7 - 89213568*t^3*z^6 + 63748256*t^3*z^5 - 32377680*t^3*z^4 + 11224320*t^3*z^3 - 2467152*t^3*z^2 + 298800*t^3*z - 14256*t^3 + 160*t^2*z^18 - 5760*t^2*z^17 + 94080*t^2*z^16 - 923760*t^2*z^15 + 6093600*t^2*z^14 - 28604736*t^2*z^13 + 98812192*t^2*z^12 - 256389120*t^2*z^11 + 505935312*t^2*z^10 - 764283024*t^2*z^9 + 885244368*t^2*z^8 - 783381600*t^2*z^7 + 524540032*t^2*z^6 - 261087984*t^2*z^5 + 93827808*t^2*z^4 - 23213088*t^2*z^3 + 3640464*t^2*z^2 - 308880*t^2*z + 9936*t^2 + 64*t*z^21 - 2688*t*z^20 + 51968*t*z^19 - 613824*t*z^18 + 4958976*t*z^17 - 29079072*t*z^16 + 128231632*t*z^15 - 434915808*t*z^14 + 1151204192*t*z^13 - 2400254160*t*z^12 + 3962631840*t*z^11 - 5188956912*t*z^10 + 5380085536*t*z^9 - 4392015792*t*z^8 + 2793719024*t*z^7 - 1361809680*t*z^6 + 496047456*t*z^5 - 130044528*t*z^4 + 23176656*t*z^3 - 2557872*t*z^2 + 145584*t*z - 2592*t + 16*z^24 - 768*z^23 + 17152*z^22 - 236784*z^21 + 2264416*z^20 - 15935904*z^19 + 85595344*z^18 - 359249088*z^17 + 1196783536*z^16 - 3197681616*z^15 + 6898154800*z^14 - 12058360272*z^13 + 17098143472*z^12 - 19636532832*z^11 + 18189177856*z^10 - 13490774256*z^9 + 7925396128*z^8 - 3632635440*z^7 + 1273236096*z^6 - 332255952*z^5 + 62175888*z^4 - 7860672*z^3 + 599616*z^2 - 20736*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z^2 + 800*t^6*z - 480*t^6 - 256*t^5*z^5 + 2816*t^5*z^4 - 10496*t^5*z^3 + 16240*t^5*z^2 - 12848*t^5*z + 3440*t^5 - 304*t^4*z^8 + 5168*t^4*z^7 - 34960*t^4*z^6 + 121376*t^4*z^5 - 236784*t^4*z^4 + 272896*t^4*z^3 - 185072*t^4*z^2 + 70224*t^4*z - 9520*t^4 - 256*t^3*z^11 + 5888*t^3*z^10 - 57600*t^3*z^9 + 314160*t^3*z^8 - 1056560*t^3*z^7 + 2300720*t^3*z^6 - 3328352*t^3*z^5 + 3221168*t^3*z^4 - 2053088*t^3*z^3 + 818064*t^3*z^2 - 180880*t^3*z + 12752*t^3 - 160*t^2*z^14 + 4640*t^2*z^13 - 59360*t^2*z^12 + 442000*t^2*z^11 - 2131280*t^2*z^10 + 7018256*t^2*z^9 - 16251120*t^2*z^8 + 26883456*t^2*z^7 - 31958112*t^2*z^6 + 27180640*t^2*z^5 - 16247552*t^2*z^4 + 6571424*t^2*z^3 - 1671104*t^2*z^2 + 229264*t^2*z - 8560*t^2 - 64*t*z^17 + 2240*t*z^16 - 35392*t*z^15 + 334208*t*z^14 - 2106048*t*z^13 + 9372448*t*z^12 - 30430768*t*z^11 + 73503568*t*z^10 - 133562832*t*z^9 + 183445792*t*z^8 - 190172336*t*z^7 + 147503248*t*z^6 - 84020928*t*z^5 + 33999344*t*z^4 - 9232304*t*z^3 + 1522064*t*z^2 - 125072*t*z + 2352*t - 16*z^20 + 656*z^19 - 12336*z^18 + 141120*z^17 - 1098608*z^16 + 6170624*z^15 - 25879168*z^14 + 82776192*z^13 - 204578240*z^12 + 393563280*z^11 - 591027776*z^10 + 691877808*z^9 - 627525472*z^8 + 435779728*z^7 - 227312912*z^6 + 86586096*z^5 - 23149392*z^4 + 4101328*z^3 - 433632*z^2 + 20704*z - 96)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_59 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 59) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_59 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z^3 - 768*t^7*z^2 + 960*t^7*z - 240*t^7 + 448*t^6*z^6 - 5376*t^6*z^5 + 22848*t^6*z^4 - 42000*t^6*z^3 + 35328*t^6*z^2 - 12816*t^6*z + 1488*t^6 + 896*t^5*z^9 - 16128*t^5*z^8 + 116928*t^5*z^7 - 440496*t^5*z^6 + 937728*t^5*z^5 - 1167264*t^5*z^4 + 850608*t^5*z^3 - 348192*t^5*z^2 + 70560*t^5*z - 5184*t^5 + 1120*t^4*z^12 - 26880*t^4*z^11 + 275520*t^4*z^10 - 1580880*t^4*z^9 + 5610240*t^4*z^8 - 12901680*t^4*z^7 + 19678896*t^4*z^6 - 20068992*t^4*z^5 + 13577184*t^4*z^4 - 5908320*t^4*z^3 + 1543968*t^4*z^2 - 210816*t^4*z + 11088*t^4 + 896*t^3*z^15 - 26880*t^3*z^14 + 356160*t^3*z^13 - 2750160*t^3*z^12 + 13770240*t^3*z^11 - 47157696*t^3*z^10 + 113784864*t^3*z^9 - 196748352*t^3*z^8 + 245831904*t^3*z^7 - 221992992*t^3*z^6 + 143465040*t^3*z^5 - 64788336*t^3*z^4 + 19548288*t^3*z^3 - 3641328*t^3*z^2 + 363312*t^3*z - 14256*t^3 + 448*t^2*z^18 - 16128*t^2*z^17 + 262080*t^2*z^16 - 2545200*t^2*z^15 + 16496640*t^2*z^14 - 75543408*t^2*z^13 + 252666864*t^2*z^12 - 630077184*t^2*z^11 + 1186719264*t^2*z^10 - 1700729568*t^2*z^9 + 1859191488*t^2*z^8 - 1545510240*t^2*z^7 + 967124880*t^2*z^6 - 446780880*t^2*z^5 + 147504672*t^2*z^4 - 33039360*t^2*z^3 + 4609008*t^2*z^2 - 345168*t^2*z + 9936*t^2 + 128*t*z^21 - 5376*t*z^20 + 103488*t*z^19 - 1211280*t*z^18 + 9646848*t*z^17 - 55461024*t*z^16 + 238450608*t*z^15 - 784276128*t*z^14 + 2003427072*t*z^13 - 4015315872*t*z^12 + 6354517392*t*z^11 - 7964780976*t*z^10 + 7902259200*t*z^9 - 6176410272*t*z^8 + 3765153024*t*z^7 - 1760690736*t*z^6 + 615823776*t*z^5 - 155130768*t*z^4 + 26555472*t*z^3 - 2801952*t*z^2 + 151632*t*z - 2592*t + 16*z^24 - 768*z^23 + 17088*z^22 - 234096*z^21 + 2212608*z^20 - 15328080*z^19 + 80738832*z^18 - 331226496*z^17 + 1075906944*z^16 - 2799414720*z^15 + 5882215680*z^14 - 10035862848*z^13 + 13944409056*z^12 - 15785710272*z^11 + 14523967008*z^10 - 10797818832*z^9 + 6423071040*z^8 - 3012372288*z^7 + 1090790928*z^6 - 296117856*z^5 + 57764016*z^4 - 7580304*z^3 + 593568*z^2 - 20736*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6*z^2 + 2240*t^6*z - 896*t^6 - 896*t^5*z^5 + 9856*t^5*z^4 - 35392*t^5*z^3 + 47600*t^5*z^2 - 29296*t^5*z + 2800*t^5 - 1120*t^4*z^8 + 19040*t^4*z^7 - 126560*t^4*z^6 + 419440*t^4*z^5 - 748880*t^4*z^4 + 755840*t^4*z^3 - 421616*t^4*z^2 + 125440*t^4*z - 880*t^4 - 896*t^3*z^11 + 20608*t^3*z^10 - 199360*t^3*z^9 + 1058960*t^3*z^8 - 3400720*t^3*z^7 + 6911728*t^3*z^6 - 9121648*t^3*z^5 + 7867904*t^3*z^4 - 4358960*t^3*z^3 + 1444704*t^3*z^2 - 261792*t^3*z - 9648*t^3 - 448*t^2*z^14 + 12992*t^2*z^13 - 164864*t^2*z^12 + 1205680*t^2*z^11 - 5644400*t^2*z^10 + 17821184*t^2*z^9 - 39086672*t^2*z^8 + 60613024*t^2*z^7 - 67000816*t^2*z^6 + 52626960*t^2*z^5 - 28800480*t^2*z^4 + 10509888*t^2*z^3 - 2332448*t^2*z^2 + 284512*t^2*z + 20768*t^2 - 128*t*z^17 + 4480*t*z^16 - 70336*t*z^15 + 655184*t*z^14 - 4039888*t*z^13 + 17442064*t*z^12 - 54485920*t*z^11 + 125711504*t*z^10 - 217067264*t*z^9 + 282554544*t*z^8 - 277515936*t*z^7 + 204156192*t*z^6 - 110439136*t*z^5 + 42467600*t*z^4 - 10966448*t*z^3 + 1709920*t*z^2 - 144128*t*z - 16192*t - 16*z^20 + 656*z^19 - 12272*z^18 + 138880*z^17 - 1063376*z^16 + 5841296*z^15 - 23839184*z^14 + 73928176*z^13 - 176867392*z^12 + 329793744*z^11 - 482251392*z^10 + 554123376*z^9 - 498808592*z^8 + 348517984*z^7 - 185782432*z^6 + 73497920*z^5 - 20679088*z^4 + 3870352*z^3 - 425440*z^2 + 24224*z + 3616)*hf
  · have hr : (16*t^8 - 64*t^7*z^3 + 384*t^7*z^2 - 768*t^7*z + 144*t^7 + 160*t^6*z^6 - 1920*t^6*z^5 + 9216*t^6*z^4 - 21408*t^6*z^3 + 23232*t^6*z^2 - 7584*t^6*z + 624*t^6 - 256*t^5*z^9 + 4608*t^5*z^8 - 35712*t^5*z^7 + 153648*t^5*z^6 - 394560*t^5*z^5 + 602496*t^5*z^4 - 511056*t^5*z^3 + 203040*t^5*z^2 - 33120*t^5*z + 1728*t^5 + 304*t^4*z^12 - 7296*t^4*z^11 + 77952*t^4*z^10 - 486288*t^4*z^9 + 1952928*t^4*z^8 - 5247648*t^4*z^7 + 9490176*t^4*z^6 - 11311488*t^4*z^5 + 8454096*t^4*z^4 - 3644640*t^4*z^3 + 825552*t^4*z^2 - 86832*t^4*z + 3312*t^4 - 256*t^3*z^15 + 7680*t^3*z^14 - 104832*t^3*z^13 + 859632*t^3*z^12 - 4708992*t^3*z^11 + 18125376*t^3*z^10 - 50194128*t^3*z^9 + 100675872*t^3*z^8 - 145260288*t^3*z^7 + 147792096*t^3*z^6 - 102445344*t^3*z^5 + 46019664*t^3*z^4 - 12584736*t^3*z^3 + 1942704*t^3*z^2 - 152496*t^3*z + 4752*t^3 + 160*t^2*z^18 - 5760*t^2*z^17 + 95616*t^2*z^16 - 969552*t^2*z^15 + 6706656*t^2*z^14 - 33472800*t^2*z^13 + 124327872*t^2*z^12 - 349367040*t^2*z^11 + 747585648*t^2*z^10 - 1216370736*t^2*z^9 + 1491595344*t^2*z^8 - 1355993568*t^2*z^7 + 891411264*t^2*z^6 - 409539024*t^2*z^5 + 125910720*t^2*z^4 - 24591168*t^2*z^3 + 2862000*t^2*z^2 - 180144*t^2*z + 4752*t^2 - 64*t*z^21 + 2688*t*z^20 - 52608*t*z^19 + 636768*t*z^18 - 5334912*t*z^17 + 32808960*t*z^16 - 153264528*t*z^15 + 555188256*t*z^14 - 1578278016*t*z^13 + 3541183632*t*z^12 - 6275034144*t*z^11 + 8747570160*t*z^10 - 9512497152*t*z^9 + 7962691824*t*z^8 - 5035618800*t*z^7 + 2347094448*t*z^6 - 781665984*t*z^5 + 179225136*t*z^4 - 27047088*t*z^3 + 2520720*t*z^2 - 128304*t*z + 2592*t + 16*z^24 - 768*z^23 + 17280*z^22 - 242160*z^21 + 2368992*z^20 - 17186496*z^19 + 95888208*z^18 - 421106688*z^17 + 1477873872*z^16 - 4184579088*z^15 + 9610937712*z^14 - 17939470896*z^13 + 27180883440*z^12 - 33288096096*z^11 + 32708946528*z^10 - 25506771696*z^9 + 15551965440*z^8 - 7271027856*z^7 + 2542830624*z^6 - 644636880*z^5 + 113637168*z^4 - 13087008*z^3 + 878688*z^2 - 25920*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z^2 + 800*t^6*z - 1376*t^6 + 256*t^5*z^5 - 2816*t^5*z^4 + 12416*t^5*z^3 - 25264*t^5*z^2 + 21104*t^5*z + 1072*t^5 - 304*t^4*z^8 + 5168*t^4*z^7 - 37520*t^4*z^6 + 148864*t^4*z^5 - 343952*t^4*z^4 + 450560*t^4*z^3 - 292496*t^4*z^2 + 55696*t^4*z - 20848*t^4 + 256*t^3*z^11 - 5888*t^3*z^10 + 60032*t^3*z^9 - 354928*t^3*z^8 + 1336688*t^3*z^7 - 3313424*t^3*z^6 + 5387072*t^3*z^5 - 5530000*t^3*z^4 + 3287200*t^3*z^3 - 951696*t^3*z^2 + 135600*t^3*z + 80880*t^3 - 160*t^2*z^14 + 4640*t^2*z^13 - 60896*t^2*z^12 + 477040*t^2*z^11 - 2477552*t^2*z^10 + 8959568*t^2*z^9 - 23047952*t^2*z^8 + 42299968*t^2*z^7 - 54660448*t^2*z^6 + 48204864*t^2*z^5 - 27467328*t^2*z^4 + 9270624*t^2*z^3 - 1674944*t^2*z^2 + 82192*t^2*z - 253840*t^2 + 64*t*z^17 - 2240*t*z^16 + 36032*t*z^15 - 352672*t*z^14 + 2343776*t*z^13 - 11174624*t*z^12 + 39371888*t*z^11 - 104037424*t*z^10 + 207068848*t*z^9 - 309028032*t*z^8 + 341202768*t*z^7 - 272170128*t*z^6 + 151174400*t*z^5 - 55439056*t*z^4 + 12540016*t*z^3 - 1602224*t*z^2 + 203344*t*z + 388592*t - 16*z^20 + 656*z^19 - 12464*z^18 + 145600*z^17 - 1170032*z^16 + 6857504*z^15 - 30327968*z^14 + 103300000*z^13 - 274152256*z^12 + 569832048*z^11 - 927253824*z^10 + 1174527408*z^9 - 1144829408*z^8 + 843043888*z^7 - 456554512*z^6 + 175113008*z^5 - 45230704*z^4 + 7350832*z^3 - 686368*z^2 - 37984*z - 256544)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_60 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 60) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_60 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z^3 + 384*t^7*z^2 - 448*t^7*z - 176*t^7 + 160*t^6*z^6 - 1920*t^6*z^5 + 8192*t^6*z^4 - 14240*t^6*z^3 + 7264*t^6*z^2 + 1936*t^6*z + 928*t^6 - 256*t^5*z^9 + 4608*t^5*z^8 - 33600*t^5*z^7 + 126192*t^5*z^6 - 254208*t^5*z^5 + 251232*t^5*z^4 - 76336*t^5*z^3 - 23712*t^5*z^2 + 96*t^5*z - 3200*t^5 + 304*t^4*z^12 - 7296*t^4*z^11 + 75328*t^4*z^10 - 436432*t^4*z^9 + 1550112*t^4*z^8 - 3453312*t^4*z^7 + 4715296*t^4*z^6 - 3636720*t^4*z^5 + 1297600*t^4*z^4 - 159008*t^4*z^3 + 87888*t^4*z^2 - 21040*t^4*z + 7408*t^4 - 256*t^3*z^15 + 7680*t^3*z^14 - 102464*t^3*z^13 + 800432*t^3*z^12 - 4054912*t^3*z^11 + 13928960*t^3*z^10 - 32917520*t^3*z^9 + 53069280*t^3*z^8 - 56410112*t^3*z^7 + 36623520*t^3*z^6 - 12034192*t^3*z^5 + 586864*t^3*z^4 + 780240*t^3*z^3 - 373232*t^3*z^2 + 84208*t^3*z - 11792*t^3 + 160*t^2*z^18 - 5760*t^2*z^17 + 94272*t^2*z^16 - 927888*t^2*z^15 + 6121824*t^2*z^14 - 28561728*t^2*z^13 + 96868064*t^2*z^12 - 241696320*t^2*z^11 + 443886384*t^2*z^10 - 594339248*t^2*z^9 + 569024016*t^2*z^8 - 378782064*t^2*z^7 + 170785360*t^2*z^6 - 53542272*t^2*z^5 + 14187168*t^2*z^4 - 3935216*t^2*z^3 + 977712*t^2*z^2 - 156480*t^2*z + 12256*t^2 - 64*t*z^21 + 2688*t*z^20 - 52096*t*z^19 + 617824*t*z^18 - 5012544*t*z^17 + 29465376*t*z^16 - 129647216*t*z^15 + 434948400*t*z^14 - 1122765344*t*z^13 + 2234118304*t*z^12 - 3410276400*t*z^11 + 3945416576*t*z^10 - 3385148784*t*z^9 + 2073147072*t*z^8 - 837979552*t*z^7 + 173882592*t*z^6 + 16593216*t*z^5 - 24115456*t*z^4 + 8185344*t*z^3 - 1527984*t*z^2 + 158864*t*z - 7232*t + 16*z^24 - 768*z^23 + 17216*z^22 - 239408*z^21 + 2313856*z^20 - 16503344*z^19 + 90028896*z^18 - 384211200*z^17 + 1301342080*z^16 - 3529270752*z^15 + 7700384048*z^14 - 13537770512*z^13 + 19157211232*z^12 - 21751064480*z^11 + 19718370432*z^10 - 14186993184*z^9 + 8049068560*z^8 - 3579246912*z^7 + 1240366320*z^6 - 332386976*z^5 + 67770048*z^4 - 10185040*z^3 + 1061632*z^2 - 67136*z + 1792:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z^2 + 800*t^6*z - 352*t^6 + 256*t^5*z^5 - 2816*t^5*z^4 + 10304*t^5*z^3 - 12592*t^5*z^2 - 976*t^5*z + 3472*t^5 - 304*t^4*z^8 + 5168*t^4*z^7 - 34896*t^4*z^6 + 117376*t^4*z^5 - 198288*t^4*z^4 + 137696*t^4*z^3 - 1488*t^4*z^2 - 5120*t^4*z - 12752*t^4 + 256*t^3*z^11 - 5888*t^3*z^10 + 57664*t^3*z^9 - 312304*t^3*z^8 + 1014128*t^3*z^7 - 1990608*t^3*z^6 + 2229376*t^3*z^5 - 1169808*t^3*z^4 + 71200*t^3*z^3 + 77808*t^3*z^2 - 5792*t^3*z + 22688*t^3 - 160*t^2*z^14 + 4640*t^2*z^13 - 59552*t^2*z^12 + 444784*t^2*z^11 - 2137328*t^2*z^10 + 6892400*t^2*z^9 - 15080848*t^2*z^8 + 22093376*t^2*z^7 - 20824352*t^2*z^6 + 11722336*t^2*z^5 - 3598880*t^2*z^4 + 789008*t^2*z^3 - 274944*t^2*z^2 + 58176*t^2*z - 19776*t^2 + 64*t*z^17 - 2240*t*z^16 + 35520*t*z^15 - 337312*t*z^14 + 2136096*t*z^13 - 9503936*t*z^12 + 30480304*t*z^11 - 71105088*t*z^10 + 120137888*t*z^9 - 144335488*t*z^8 + 118676544*t*z^7 - 61775744*t*z^6 + 16425168*t*z^5 + 437360*t*z^4 - 1793776*t*z^3 + 615024*t*z^2 - 101472*t*z + 7248*t - 16*z^20 + 656*z^19 - 12400*z^18 + 143296*z^17 - 1131920*z^16 + 6473904*z^15 - 27705920*z^14 + 90436448*z^13 - 227480912*z^12 + 442672832*z^11 - 665743952*z^10 + 769859456*z^9 - 678916144*z^8 + 451994640*z^7 - 224962336*z^6 + 83143264*z^5 - 22719744*z^4 + 4509680*z^3 - 613696*z^2 + 54368*z - 544)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_61 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 61) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_61 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z^3 + 24*t*z^2 - 36*t*z + 2*z^6 - 24*z^5 + 108*z^4 - 222*z^3 + 198*z^2 - 54*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 10*z - 10)*hf
  · have hr : (16*t^8 - 192*t^7*z^3 + 1152*t^7*z^2 - 1600*t^7*z + 80*t^7 + 1056*t^6*z^6 - 12672*t^6*z^5 + 55680*t^6*z^4 - 107136*t^6*z^3 + 80800*t^6*z^2 - 9808*t^6*z + 352*t^6 - 3456*t^5*z^9 + 62208*t^5*z^8 - 460224*t^5*z^7 + 1796976*t^5*z^6 - 3942144*t^5*z^5 + 4737312*t^5*z^4 - 2735536*t^5*z^3 + 514464*t^5*z^2 - 37920*t^5*z + 896*t^5 + 7344*t^4*z^12 - 176256*t^4*z^11 + 1833408*t^4*z^10 - 10815120*t^4*z^9 + 39720096*t^4*z^8 - 93736512*t^4*z^7 + 141274848*t^4*z^6 - 130219344*t^4*z^5 + 66680896*t^4*z^4 - 15989504*t^4*z^3 + 1850640*t^4*z^2 - 100784*t^4*z + 2032*t^4 - 10368*t^3*z^15 + 311040*t^3*z^14 - 4169664*t^3*z^13 + 32930928*t^3*z^12 - 170038656*t^3*z^11 + 602007552*t^3*z^10 - 1489777104*t^3*z^9 + 2576500704*t^3*z^8 - 3058940544*t^3*z^7 + 2399906400*t^3*z^6 - 1168090384*t^3*z^5 + 325058224*t^3*z^4 - 50914096*t^3*z^3 + 4408016*t^3*z^2 - 193616*t^3*z + 3440*t^3 + 9504*t^2*z^18 - 342144*t^2*z^17 + 5614272*t^2*z^16 - 55573776*t^2*z^15 + 370103904*t^2*z^14 - 1750771584*t^2*z^13 + 6052987872*t^2*z^12 - 15497148096*t^2*z^11 + 29438356464*t^2*z^10 - 41163597936*t^2*z^9 + 41612618448*t^2*z^8 - 29537477424*t^2*z^7 + 14139102256*t^2*z^6 - 4367294688*t^2*z^5 + 850836768*t^2*z^4 - 102692272*t^2*z^3 + 7399824*t^2*z^2 - 291936*t^2*z + 4768*t^2 - 5184*t*z^21 + 217728*t*z^20 - 4226688*t*z^19 + 50301216*t*z^18 - 410401728*t*z^17 + 2431931040*t*z^16 - 10816794864*t*z^15 + 36801935280*t*z^14 - 96711054624*t*z^13 + 196824438432*t*z^12 - 309182103792*t*z^11 + 371439512928*t*z^10 - 336131772816*t*z^9 + 224316812736*t*z^8 - 107540297152*t*z^7 + 36052067552*t*z^6 - 8279168736*t*z^5 + 1277809792*t*z^4 - 128833184*t*z^3 + 8060208*t*z^2 - 284080*t*z + 4544*t + 1296*z^24 - 62208*z^23 + 1394496*z^22 - 19389456*z^21 + 187310016*z^20 - 1334514960*z^19 + 7264483488*z^18 - 30884548320*z^17 + 103944828096*z^16 - 279045851904*z^15 + 599282899056*z^14 - 1028548415088*z^13 + 1404171133536*z^12 - 1512316489536*z^11 + 1270027430880*z^10 - 819395649696*z^9 + 399328067536*z^8 - 144519156448*z^7 + 38254990288*z^6 - 7293343936*z^5 + 980074048*z^4 - 89408464*z^3 + 5155072*z^2 - 161344*z + 1792:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6*z^2 + 5280*t^6*z - 3936*t^6 + 3456*t^5*z^5 - 38016*t^5*z^4 + 145728*t^5*z^3 - 217008*t^5*z^2 + 75312*t^5*z + 31824*t^5 - 7344*t^4*z^8 + 124848*t^4*z^7 - 856656*t^4*z^6 + 3011904*t^4*z^5 - 5637456*t^4*z^4 + 5129568*t^4*z^3 - 1491600*t^4*z^2 - 147360*t^4*z - 156016*t^4 + 10368*t^3*z^11 - 238464*t^3*z^10 + 2355264*t^3*z^9 - 13022640*t^3*z^8 + 43988400*t^3*z^7 - 92691216*t^3*z^6 + 118564608*t^3*z^5 - 83941584*t^3*z^4 + 25926816*t^3*z^3 - 2028432*t^3*z^2 + 818656*t^3*z + 426528*t^3 - 9504*t^2*z^14 + 275616*t^2*z^13 - 3551904*t^2*z^12 + 26775792*t^2*z^11 - 130732272*t^2*z^10 + 432093744*t^2*z^9 - 980321616*t^2*z^8 + 1512950400*t^2*z^7 - 1535718816*t^2*z^6 + 957593952*t^2*z^5 - 325472544*t^2*z^4 + 54153360*t^2*z^3 - 6942688*t^2*z^2 - 825472*t^2*z - 718016*t^2 + 5184*t*z^17 - 181440*t*z^16 + 2884032*t*z^15 - 27531360*t*z^14 + 175849056*t*z^13 - 792294912*t*z^12 + 2585708784*t*z^11 - 6175521216*t*z^10 + 10768274784*t*z^9 - 13511252736*t*z^8 + 11857609152*t*z^7 - 6956991072*t*z^6 + 2568010512*t*z^5 - 570738192*t*z^4 + 79444912*t*z^3 - 4543312*t*z^2 + 1220736*t*z + 639216*t - 1296*z^20 + 53136*z^19 - 1004400*z^18 + 11604384*z^17 - 91591344*z^16 + 522825840*z^15 - 2228584320*z^14 + 7220561184*z^13 - 17926521264*z^12 + 34120846080*z^11 - 49472605008*z^10 + 53915603616*z^9 - 43252148208*z^8 + 24831315312*z^7 - 9880714848*z^6 + 2659442112*z^5 - 479294176*z^4 + 54873552*z^3 - 4505216*z^2 - 217824*z - 243200)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_62 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 62) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_62 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z^3 + 384*t^7*z^2 - 576*t^7*z - 48*t^7 + 160*t^6*z^6 - 1920*t^6*z^5 + 8640*t^6*z^4 - 17376*t^6*z^3 + 13536*t^6*z^2 - 912*t^6*z + 192*t^6 - 256*t^5*z^9 + 4608*t^5*z^8 - 34560*t^5*z^7 + 138672*t^5*z^6 - 316224*t^5*z^5 + 396720*t^5*z^4 - 234144*t^5*z^3 + 36288*t^5*z^2 + 144*t^5*z - 432*t^5 + 304*t^4*z^12 - 7296*t^4*z^11 + 76608*t^4*z^10 - 460752*t^4*z^9 + 1743552*t^4*z^8 - 4286160*t^4*z^7 + 6806160*t^4*z^6 - 6691248*t^4*z^5 + 3705552*t^4*z^4 - 970992*t^4*z^3 + 114480*t^4*z^2 - 10800*t^4*z + 720*t^4 - 256*t^3*z^15 + 7680*t^3*z^14 - 103680*t^3*z^13 + 830832*t^3*z^12 - 4387968*t^3*z^11 + 16027536*t^3*z^10 - 41304000*t^3*z^9 + 75162384*t^3*z^8 - 95005296*t^3*z^7 + 80411760*t^3*z^6 - 42689376*t^3*z^5 + 12705552*t^3*z^4 - 1725984*t^3*z^3 + 33264*t^3*z^2 + 15120*t^3*z - 864*t^3 + 160*t^2*z^18 - 5760*t^2*z^17 + 95040*t^2*z^16 - 951696*t^2*z^15 + 6454080*t^2*z^14 - 31318128*t^2*z^13 + 111985200*t^2*z^12 - 299347488*t^2*z^11 + 600409728*t^2*z^10 - 898789824*t^2*z^9 + 989947008*t^2*z^8 - 783142560*t^2*z^7 + 429570432*t^2*z^6 - 156078576*t^2*z^5 + 35938944*t^2*z^4 - 5253984*t^2*z^3 + 532656*t^2*z^2 - 35856*t^2*z + 864*t^2 - 64*t*z^21 + 2688*t*z^20 - 52416*t*z^19 + 629664*t*z^18 - 5213376*t*z^17 + 31534416*t*z^16 - 144106560*t*z^15 + 507450096*t*z^14 - 1391819472*t*z^13 + 2985476112*t*z^12 - 5000158080*t*z^11 + 6492686976*t*z^10 - 6452146512*t*z^9 + 4809524688*t*z^8 - 2610865440*t*z^7 + 988140384*t*z^6 - 243575424*t*z^5 + 34418736*t*z^4 - 1807488*t*z^3 - 130896*t*z^2 + 15552*t*z + 16*z^24 - 768*z^23 + 17280*z^22 - 242160*z^21 + 2368800*z^20 - 17179392*z^19 + 95767248*z^18 - 419850000*z^17 + 1468967328*z^16 - 4138966800*z^15 + 9436502160*z^14 - 17431710624*z^13 + 26044501392*z^12 - 31326226848*z^11 + 30102595488*z^10 - 22863493728*z^9 + 13533778080*z^8 - 6134733504*z^7 + 2084531328*z^6 - 517332096*z^5 + 90561888*z^4 - 10574064*z^3 + 738720*z^2 - 23328*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z^2 + 800*t^6*z - 800*t^6 + 256*t^5*z^5 - 2816*t^5*z^4 + 11264*t^5*z^3 - 18352*t^5*z^2 + 7280*t^5*z + 4096*t^5 - 304*t^4*z^8 + 5168*t^4*z^7 - 36176*t^4*z^6 + 132736*t^4*z^5 - 266288*t^4*z^4 + 269264*t^4*z^3 - 95216*t^4*z^2 - 8000*t^4*z - 8128*t^4 + 256*t^3*z^11 - 5888*t^3*z^10 + 58880*t^3*z^9 - 334192*t^3*z^8 + 1176944*t^3*z^7 - 2633312*t^3*z^6 + 3661184*t^3*z^5 - 2917984*t^3*z^4 + 1079392*t^3*z^3 - 81456*t^3*z^2 + 2640*t^3*z + 6432*t^3 - 160*t^2*z^14 + 4640*t^2*z^13 - 60320*t^2*z^12 + 463216*t^2*z^11 - 2329808*t^2*z^10 + 8037248*t^2*z^9 - 19341104*t^2*z^8 + 32336608*t^2*z^7 - 36650224*t^2*z^6 + 26759664*t^2*z^5 - 11492256*t^2*z^4 + 2523072*t^2*z^3 - 289808*t^2*z^2 + 29200*t^2*z - 400*t^2 + 64*t*z^17 - 2240*t*z^16 + 35840*t*z^15 - 346912*t*z^14 + 2265248*t*z^13 - 10531952*t*z^12 + 35858288*t*z^11 - 90525856*t*z^10 + 169601584*t*z^9 - 233504784*t*z^8 + 231137280*t*z^7 - 158320512*t*z^6 + 70341152*t*z^5 - 18046432*t*z^4 + 2062912*t*z^3 - 224*t*z^2 - 19520*t*z - 2512*t - 16*z^20 + 656*z^19 - 12464*z^18 + 145600*z^17 - 1169840*z^16 + 6851744*z^15 - 30250016*z^14 + 102671152*z^13 - 270785248*z^12 + 557222064*z^11 - 893335008*z^10 + 1108303536*z^9 - 1051124768*z^8 + 748201840*z^7 - 389672560*z^6 + 143658368*z^5 - 36014176*z^4 + 5834800*z^3 - 549760*z^2 + 24800*z + 928)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_5_63 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 63) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : False := by
  apply cell_5_63 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (-48*t*z^18 + 1728*t*z^17 - 28368*t*z^16 + 281376*t*z^15 - 1883808*t*z^14 + 9010512*t*z^13 - 31800048*t*z^12 + 84359808*t*z^11 - 169857504*t*z^10 + 260354016*t*z^9 - 302821920*t*z^8 + 264592512*t*z^7 - 170403744*t*z^6 + 78380496*t*z^5 - 24501744*t*z^4 + 4815504*t*z^3 - 521856*t*z^2 + 23328*t*z + 16*z^24 - 768*z^23 + 17216*z^22 - 239472*z^21 + 2316544*z^20 - 16555440*z^19 + 90646928*z^18 - 389231232*z^17 + 1330930096*z^16 - 3660127488*z^15 + 8143345760*z^14 - 14698210560*z^13 + 21520798384*z^12 - 25491459216*z^11 + 24291535184*z^10 - 18460189440*z^9 + 11048685568*z^8 - 5120498064*z^7 + 1796903184*z^6 - 463643568*z^5 + 84487392*z^4 - 10219824*z^3 + 731808*z^2 - 23328*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t*z^14 - 1392*t*z^13 + 17952*t*z^12 - 135840*t*z^11 + 670416*t*z^10 - 2270832*t*z^9 + 5413728*t*z^8 - 9172896*t*z^7 + 11017968*t*z^6 - 9227040*t*z^5 + 5184192*t*z^4 - 1807968*t*z^3 + 334992*t*z^2 - 23424*t*z - 48*t - 16*z^20 + 656*z^19 - 12400*z^18 + 143360*z^17 - 1134160*z^16 + 6509424*z^15 - 28043440*z^14 + 92578576*z^13 - 237062352*z^12 + 473734016*z^11 - 739662672*z^10 + 899218240*z^9 - 844058816*z^8 + 602956752*z^7 - 320605904*z^6 + 122864816*z^5 - 32436368*z^4 + 5532080*z^3 - 545040*z^2 + 23408*z + 32)*hf


private def limit5 (z t : ℝ) : Fin 64→Prop := ![False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,((t - z^2 + 3*z - 2:ℝ)=0),False,False,False,False,False,((t - 2*z^3 + 13*z^2 - 21*z + 3:ℝ)=0),False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,((t - 2*z^3 + 13*z^2 - 21*z + 3:ℝ)=0),False,False,False,False,False,False,False,False,False,False]

private def hue5 : Fin 64→Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_5_23_29 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit5 z t 23) (hj : limit5 z t 29) (_he : edge4 (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 23) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 29) (z^3 - 6*z^2 + 9*z - 1) (z) t=0) : False := by
  apply pair_5_23_29 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_5_23_53 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit5 z t 23) (hj : limit5 z t 53) (_he : edge4 (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 23) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 53) (z^3 - 6*z^2 + 9*z - 1) (z) t=0) : False := by
  apply pair_5_23_53 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_5_29_53 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit5 z t 29) (_hj : limit5 z t 53) (he : edge4 (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 29) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t 53) (z^3 - 6*z^2 + 9*z - 1) (z) t=0) : False := by
  apply pair_5_29_53 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (1296*t^8 - 10368*t^7*z^3 + 62208*t^7*z^2 - 93312*t^7*z + 9072*t^7 + 36288*t^6*z^6 - 435456*t^6*z^5 + 1959552*t^6*z^4 - 3985200*t^6*z^3 + 3335904*t^6*z^2 - 596160*t^6*z + 28512*t^6 - 72576*t^5*z^9 + 1306368*t^5*z^8 - 9797760*t^5*z^7 + 39397104*t^5*z^6 - 90652608*t^5*z^5 + 116951040*t^5*z^4 - 75394800*t^5*z^3 + 17873136*t^5*z^2 - 1674432*t^5*z + 53136*t^5 + 90720*t^4*z^12 - 2177280*t^4*z^11 + 22861440*t^4*z^10 - 137525040*t^4*z^9 + 520797600*t^4*z^8 - 1282651200*t^4*z^7 + 2044966176*t^4*z^6 - 2027315952*t^4*z^5 + 1143993456*t^4*z^4 - 315925920*t^4*z^3 + 42624144*t^4*z^2 - 2696976*t^4*z + 63504*t^4 - 72576*t^3*z^15 + 2177280*t^3*z^14 - 29393280*t^3*z^13 + 235515600*t^3*z^12 - 1243382400*t^3*z^11 + 4537368576*t^3*z^10 - 11670316704*t^3*z^9 + 21157539552*t^3*z^8 - 26564951808*t^3*z^7 + 22245282720*t^3*z^6 - 11670057504*t^3*z^5 + 3533243328*t^3*z^4 - 602133264*t^3*z^3 + 56317680*t^3*z^2 - 2665872*t^3*z + 49248*t^3 + 36288*t^2*z^18 - 1306368*t^2*z^17 + 21555072*t^2*z^16 - 215780112*t^2*z^15 + 1461849120*t^2*z^14 - 7076766528*t^2*z^13 + 25187726304*t^2*z^12 - 66775319136*t^2*z^11 + 132074538336*t^2*z^10 - 193240468800*t^2*z^9 + 205190545248*t^2*z^8 - 153272597328*t^2*z^7 + 77074555968*t^2*z^6 - 24815984256*t^2*z^5 + 4971589488*t^2*z^4 - 605093328*t^2*z^3 + 42795216*t^2*z^2 - 1587600*t^2*z + 23328*t^2 - 10368*t*z^21 + 435456*t*z^20 - 8491392*t*z^19 + 101975760*t*z^18 - 843493824*t*z^17 + 5090853888*t*z^16 - 23167564272*t*z^15 + 81000294192*t*z^14 - 219617707968*t*z^13 + 462742363728*t*z^12 - 754472861856*t*z^11 + 941810874912*t*z^10 - 884542883472*t*z^9 + 609708177936*t*z^8 - 298821402720*t*z^7 + 100645369344*t*z^6 - 22689485424*t*z^5 + 3343519296*t*z^4 - 311370480*t*z^3 + 17216064*t*z^2 - 495072*t*z + 5184*t + 1296*z^24 - 62208*z^23 + 1399680*z^22 - 19607184*z^21 + 191546208*z^20 - 1385159616*z^19 + 7680554784*z^18 - 33373071792*z^17 + 115142584752*z^16 - 317673625248*z^15 + 702402281424*z^14 - 1242048028032*z^13 + 1745519794128*z^12 - 1929172116672*z^11 + 1651687284240*z^10 - 1074058582176*z^9 + 518070335184*z^8 - 180747102672*z^7 + 44571269952*z^6 - 7590627936*z^5 + 865567296*z^4 - 62706960*z^3 + 2597184*z^2 - 46656*z:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-36288*t^6*z^2 + 181440*t^6*z - 181440*t^6 + 72576*t^5*z^5 - 798336*t^5*z^4 + 3193344*t^5*z^3 - 5286384*t^5*z^2 + 2481840*t^5*z + 776304*t^5 - 90720*t^4*z^8 + 1542240*t^4*z^7 - 10795680*t^4*z^6 + 39638160*t^4*z^5 - 79762320*t^4*z^4 + 81473040*t^4*z^3 - 30081456*t^4*z^2 - 1613520*t^4*z - 2601072*t^4 + 72576*t^3*z^11 - 1669248*t^3*z^10 + 16692480*t^3*z^9 - 94718160*t^3*z^8 + 333234000*t^3*z^7 - 743467248*t^3*z^6 + 1026332208*t^3*z^5 - 804082464*t^3*z^4 + 286751664*t^3*z^3 - 26741664*t^3*z^2 + 9350640*t^3*z + 4690224*t^3 - 36288*t^2*z^14 + 1052352*t^2*z^13 - 13680576*t^2*z^12 + 104992848*t^2*z^11 - 526916016*t^2*z^10 + 1807957584*t^2*z^9 - 4301575632*t^2*z^8 + 7032562560*t^2*z^7 - 7633964880*t^2*z^6 + 5126276160*t^2*z^5 - 1869027696*t^2*z^4 + 317255616*t^2*z^3 - 43204752*t^2*z^2 - 6525360*t^2*z - 5327856*t^2 + 10368*t*z^17 - 362880*t*z^16 + 5806080*t*z^15 - 56169936*t*z^14 + 366105744*t*z^13 - 1694923056*t*z^12 + 5722456896*t*z^11 - 14229157248*t*z^10 + 25973720496*t*z^9 - 34243540560*t*z^8 + 31580276112*t*z^7 - 19320453072*t*z^6 + 7253801424*t*z^5 - 1559475504*t*z^4 + 207953568*t*z^3 - 6172848*t*z^2 + 5320080*t*z + 3245184*t - 1296*z^20 + 53136*z^19 - 1009584*z^18 + 11785824*z^17 - 94484880*z^16 + 550634112*z^15 - 2408031504*z^14 + 8040308832*z^13 - 20648424096*z^12 + 40755446784*z^11 - 61305714432*z^10 + 69104070432*z^9 - 56819300688*z^8 + 32778863568*z^7 - 12626751744*z^6 + 3108754080*z^5 - 484322976*z^4 + 41407200*z^3 - 4113504*z^2 - 1205280*z - 834624)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma exclude_field_5 (z t : ℝ) (hf : z^4 - 7*z^3 + 14*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^3 - 6*z^2 + 9*z - 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (g : Fin 5→Fin 64) (hinj : Function.Injective g)
    (hc : ∀ i, cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t (g i)) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t)
    (he : ∀ i j : Fin 5, i≠j → edge4 (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t (g i)) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t (g j)) (z^3 - 6*z^2 + 9*z - 1) (z) t=0) : False := by
  have row (k : Fin 64) (hh : cell (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t k) ((1),(z^3 - 6*z^2 + 9*z - 1),(z)) ((z^3 - 6*z^2 + 9*z - 1),(1),(z)) (z^3 - 6*z^2 + 9*z - 1) (z) t) : limit5 z t k := by
    fin_cases k
    · exact row_5_0 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_1 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_2 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_3 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_4 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_5 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_6 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_7 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_8 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_9 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_10 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_11 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_12 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_13 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_14 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_15 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_16 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_17 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_18 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_19 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_20 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_21 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_22 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_23 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_24 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_25 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_26 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_27 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_28 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_29 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_30 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_31 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_32 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_33 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_34 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_35 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_36 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_37 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_38 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_39 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_40 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_41 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_42 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_43 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_44 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_45 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_46 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_47 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_48 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_49 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_50 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_51 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_52 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_53 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_54 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_55 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_56 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_57 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_58 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_59 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_60 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_61 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_62 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_5_63 z t hf hn0 hn1 hn2 hn3 hh
  have allowed (k : Fin 64) (hh : limit5 z t k) : k∈([23,29,53]:List (Fin 64)) := by
    fin_cases k <;> first | decide | exact False.elim hh
  have cert : ∀ i j : Fin 64, i∈([23,29,53]:List (Fin 64)) → j∈([23,29,53]:List (Fin 64)) → i<j → hue5 i=hue5 j → (i,j)∈([(23,29),(23,53),(29,53)]:List (Fin 64×Fin 64)) := by decide
  have bad (i j : Fin 64) (hi : limit5 z t i) (hj : limit5 z t j) (hlt : i<j) (hc : hue5 i=hue5 j) (hb : edge4 (1) (1) (1) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t i) (profile4 (z^3 - 6*z^2 + 9*z - 1) (z) t j) (z^3 - 6*z^2 + 9*z - 1) (z) t=0) : False := by
    have h := cert i j (allowed i hi) (allowed j hj) hlt hc
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact rowpair_5_23_29 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_5_23_53 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_5_29_53 z t hf hn0 hn1 hn2 hn3 hi hj hb
  have hi : Function.Injective (fun i : Fin 5 => hue5 (g i)) := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne (show g i≠g j from fun e => hne (hinj e)) with hl|hl
    · exact bad _ _ (row _ (hc i)) (row _ (hc j)) hl h (he i j hne)
    · exact bad _ _ (row _ (hc j)) (row _ (hc i)) hl h.symm (he j i (Ne.symm hne))
  have hh := Fintype.card_le_of_injective _ hi
  norm_num at hh

private lemma cell_7_0 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_7_1 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-16/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/16)*h0
  norm_num at hh

private lemma cell_7_2 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-40/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/40)*h0
  norm_num at hh

private lemma cell_7_3 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h2 : (16*t^8 - 112*t^7 + 176*t^6 + 224*t^5 - 592*t^4 - 16*t^3 + 400*t^2 - 96*t:ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6/96 - t^5/24 - t^4/96 + 11*t^3/96 - t^2/24 - 13*t/96 - 7/48)*h0 + (-1/768)*h2
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_7_4 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-16/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/16)*h0
  norm_num at hh

private lemma cell_7_5 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/4)*h0
  norm_num at hh

private lemma cell_7_6 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-16/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/16)*h0
  norm_num at hh

private lemma cell_7_7 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 14*t/3 + 8/9:ℝ)=0) (h1 : (16*t^8 - 784*t^7/3 + 14560*t^6/9 - 128128*t^5/27 + 533680*t^4/81 - 854896*t^3/243 + 43360*t^2/729 + 677888*t/2187 - 68096/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (27*t^7/256 - 441*t^6/256 + 1359*t^5/128 - 245*t^4/8 + 30907*t^3/768 - 13069*t^2/768 - 10675*t/3456 + 3847/2592)*h0 + (63/2048 - 27*t/2048)*h1
  norm_num at hh

private lemma cell_7_8 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-40/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/40)*h0
  norm_num at hh

private lemma cell_7_9 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-16/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/16)*h0
  norm_num at hh

private lemma cell_7_10 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-46/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/46)*h0
  norm_num at hh

private lemma cell_7_11 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 20*t/3 + 2/9:ℝ)=0) (h1 : (16*t^8 - 976*t^7/3 + 23440*t^6/9 - 284224*t^5/27 + 1851472*t^4/81 - 6422608*t^3/243 + 11394448*t^2/729 - 9336352*t/2187 + 2619904/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (189*t^7/9280 - 873*t^6/2320 + 24777*t^5/9280 - 17357*t^4/1856 + 242297*t^3/13920 - 488131*t^2/27840 + 230035*t/25056 - 26461/11745)*h0 + (279/74240 - 189*t/74240)*h1
  norm_num at hh

private lemma cell_7_12 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 - 112*t^7 + 176*t^6 + 224*t^5 - 592*t^4 - 16*t^3 + 400*t^2 - 96*t:ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6/96 - t^5/24 - t^4/96 + 11*t^3/96 - t^2/24 - 13*t/96 - 7/48)*h0 + (-1/768)*h1
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_7_13 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 14*t/3 + 8/9:ℝ)=0) (h1 : (16*t^8 - 208*t^7/3 + 592*t^6/9 + 1472*t^5/27 - 10352*t^4/81 + 31280*t^3/243 - 35696*t^2/729 - 182944*t/2187 + 413440/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (81*t^7/704 - 153*t^6/352 + 207*t^5/704 + 303*t^4/704 - 49*t^3/66 + 1343*t^2/2112 - 53*t/288 - 4901/7128)*h0 + (9/352 - 81*t/5632)*h1
  norm_num at hh

private lemma cell_7_14 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 20*t/3 + 2/9:ℝ)=0) (h1 : (16*t^8 - 400*t^7/3 + 2560*t^6/9 + 4784*t^5/27 - 74096*t^4/81 + 23840*t^3/243 + 530080*t^2/729 - 62464*t/2187 - 129920/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-567*t^7/4640 + 1179*t^6/1160 - 2493*t^5/1160 - 6603*t^4/4640 + 24259*t^3/3480 - 3701*t^2/6960 - 29309*t/5220 - 5/324)*h0 + (567*t/37120 - 1881/37120)*h1
  norm_num at hh

private lemma cell_7_15 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 - 240*t^7 + 1360*t^6 - 3648*t^5 + 4624*t^4 - 2160*t^3 - 240*t^2 + 288*t:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7/16 - 11*t^6/12 + 241*t^5/48 - 611*t^4/48 + 115*t^3/8 - 71*t^2/16 - 17*t/8 + 1/2)*h0 + (11/384 - t/128)*h1
  norm_num at hh

private lemma cell_7_16 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-16/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/16)*h0
  norm_num at hh

private lemma cell_7_17 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/4)*h0
  norm_num at hh

private lemma cell_7_18 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-16/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/16)*h0
  norm_num at hh

private lemma cell_7_19 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 14*t/3 + 8/9:ℝ)=0) (h1 : (16*t^8 - 784*t^7/3 + 14560*t^6/9 - 128128*t^5/27 + 533680*t^4/81 - 854896*t^3/243 + 43360*t^2/729 + 677888*t/2187 - 68096/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (27*t^7/256 - 441*t^6/256 + 1359*t^5/128 - 245*t^4/8 + 30907*t^3/768 - 13069*t^2/768 - 10675*t/3456 + 3847/2592)*h0 + (63/2048 - 27*t/2048)*h1
  norm_num at hh

private lemma cell_7_20 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/4)*h0
  norm_num at hh

private lemma cell_7_21 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) : ((0:ℝ):ℝ)=0 := by
  rfl

private lemma cell_7_22 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (h1 : (576*t:ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (1/576)*h1
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_7_23 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 10*t/3 + 8/9:ℝ)=0) (h1 : (16*t^8 - 656*t^7/3 + 9472*t^6/9 - 53888*t^5/27 + 53296*t^4/81 + 383824*t^3/243 - 361280*t^2/729 - 425024*t/2187 + 394240/6561:ℝ)=0) : False := by
  have hh : ((t-(1/3)))*(1:ℝ)=0 := by linear_combination (-t^6/96 + t^5/8 - 17*t^4/36 + 37*t^3/81 + 469*t^2/864 - 635*t/1944 - 8101/17496)*h0 + (1/768)*h1
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_7_24 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-16/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/16)*h0
  norm_num at hh

private lemma cell_7_25 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (h2 : (576*t:ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (1/576)*h2
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_7_26 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/2)*h0
  norm_num at hh

private lemma cell_7_27 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 16*t/3 + 14/9:ℝ)=0) (h2 : (16*t^8 - 272*t^7/3 + 160*t^6/9 + 14224*t^5/27 - 30128*t^4/81 - 237920*t^3/243 + 393568*t^2/729 + 1236544*t/2187 - 116480/6561:ℝ)=0) : (t - 7/3:ℝ)=0 := by
  have hh : (t - 7/3:ℝ)=0 := by linear_combination (t^6/12 - t^5/4 - 23*t^4/36 + 100*t^3/81 + 50*t^2/27 - 545*t/486 - 7081/4374)*h0 + (-1/96)*h2
  exact hh

private lemma cell_7_28 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 14*t/3 + 8/9:ℝ)=0) (h1 : (16*t^8 - 208*t^7/3 - 560*t^6/9 + 12704*t^5/27 - 1712*t^4/81 - 232816*t^3/243 + 128464*t^2/729 + 1142432*t/2187 - 116480/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-27*t^7/64 + 27*t^6/32 + 243*t^5/64 - 251*t^4/64 - 329*t^3/32 + 193*t^2/64 + 6013*t/864 + 9/8)*h0 + (27*t/512)*h1
  norm_num at hh

private lemma cell_7_29 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 10*t/3 + 8/9:ℝ)=0) (h2 : (16*t^8 - 656*t^7/3 + 9472*t^6/9 - 53888*t^5/27 + 53296*t^4/81 + 383824*t^3/243 - 361280*t^2/729 - 425024*t/2187 + 394240/6561:ℝ)=0) : False := by
  have hh : ((t-(1/3)))*(1:ℝ)=0 := by linear_combination (-t^6/96 + t^5/8 - 17*t^4/36 + 37*t^3/81 + 469*t^2/864 - 635*t/1944 - 8101/17496)*h0 + (1/768)*h2
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_7_30 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 16*t/3 + 14/9:ℝ)=0) (h1 : (16*t^8 - 272*t^7/3 + 160*t^6/9 + 14224*t^5/27 - 30128*t^4/81 - 237920*t^3/243 + 393568*t^2/729 + 1236544*t/2187 - 116480/6561:ℝ)=0) : (t - 7/3:ℝ)=0 := by
  have hh : (t - 7/3:ℝ)=0 := by linear_combination (t^6/12 - t^5/4 - 23*t^4/36 + 100*t^3/81 + 50*t^2/27 - 545*t/486 - 7081/4374)*h0 + (-1/96)*h1
  exact hh

private lemma cell_7_31 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 16*t/3 + 14/9:ℝ)=0) : (t - 7/3:ℝ)=0 := by
  have hh : ((t-(1/3)))*(t - 7/3:ℝ)=0 := by linear_combination (1/2)*h0
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  exact hv

private lemma cell_7_32 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-40/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/40)*h0
  norm_num at hh

private lemma cell_7_33 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-16/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/16)*h0
  norm_num at hh

private lemma cell_7_34 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-46/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/46)*h0
  norm_num at hh

private lemma cell_7_35 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 20*t/3 + 2/9:ℝ)=0) (h1 : (16*t^8 - 976*t^7/3 + 23440*t^6/9 - 284224*t^5/27 + 1851472*t^4/81 - 6422608*t^3/243 + 11394448*t^2/729 - 9336352*t/2187 + 2619904/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (189*t^7/9280 - 873*t^6/2320 + 24777*t^5/9280 - 17357*t^4/1856 + 242297*t^3/13920 - 488131*t^2/27840 + 230035*t/25056 - 26461/11745)*h0 + (279/74240 - 189*t/74240)*h1
  norm_num at hh

private lemma cell_7_36 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-16/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/16)*h0
  norm_num at hh

private lemma cell_7_37 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) : ((0:ℝ):ℝ)=0 := by
  rfl

private lemma cell_7_38 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/2)*h0
  norm_num at hh

private lemma cell_7_39 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 16*t/3 + 14/9:ℝ)=0) : (t - 7/3:ℝ)=0 := by
  have hh : ((t-(1/3)))*(t - 7/3:ℝ)=0 := by linear_combination (1/2)*h0
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  exact hv

private lemma cell_7_40 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-46/9:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9/46)*h0
  norm_num at hh

private lemma cell_7_41 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/2)*h0
  norm_num at hh

private lemma cell_7_42 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/6)*h0
  norm_num at hh

private lemma cell_7_43 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 22*t/3 + 2/9:ℝ)=0) (h1 : (16*t^8 - 1040*t^7/3 + 26848*t^6/9 - 354416*t^5/27 + 2564560*t^4/81 - 10205408*t^3/243 + 21715936*t^2/729 - 22715456*t/2187 + 8968960/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7/108 - 113*t^6/648 + 203*t^5/162 - 25783*t^4/5832 + 36319*t^3/4374 - 75547*t^2/8748 + 96538*t/19683 - 169259/118098)*h0 + (5/5184 - t/864)*h1
  norm_num at hh

private lemma cell_7_44 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 20*t/3 + 2/9:ℝ)=0) (h1 : (16*t^8 - 400*t^7/3 + 3136*t^6/9 - 6016*t^5/27 - 26576*t^4/81 + 111824*t^3/243 - 70400*t^2/729 - 323392*t/2187 + 394240/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (837*t^7/18560 - 54*t^6/145 + 891*t^5/928 - 2719*t^4/4640 - 17421*t^3/18560 + 5783*t^2/4640 - 29981*t/125280 - 365/783)*h0 + (2727/148480 - 837*t/148480)*h1
  norm_num at hh

private lemma cell_7_45 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 16*t/3 + 14/9:ℝ)=0) : (t - 7/3:ℝ)=0 := by
  have hh : ((t-(1/3)))*(t - 7/3:ℝ)=0 := by linear_combination (1/2)*h0
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  exact hv

private lemma cell_7_46 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 22*t/3 + 2/9:ℝ)=0) (h1 : (16*t^8 - 464*t^7/3 + 4240*t^6/9 - 9248*t^5/27 - 47600*t^4/81 + 174544*t^3/243 + 80080*t^2/729 - 469472*t/2187 + 267904/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7*t^7/108 - 101*t^6/162 + 305*t^5/162 - 1927*t^4/1458 - 21121*t^3/8748 + 12331*t^2/4374 + 20459*t/39366 - 104831/118098)*h0 + (19/648 - 7*t/864)*h1
  norm_num at hh

private lemma cell_7_47 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 28*t/3 + 26/9:ℝ)=0) (h1 : (16*t^8 - 848*t^7/3 + 17584*t^6/9 - 183200*t^5/27 + 1019056*t^4/81 - 2963696*t^3/243 + 4105744*t^2/729 - 2160416*t/2187 + 165760/6561:ℝ)=0) : False := by
  have hh : ((t-(1/3)))*(1:ℝ)=0 := by linear_combination (t^6/216 - 13*t^5/216 + 5*t^4/18 - 3383*t^3/5832 + 3103*t^2/5832 - 607*t/2916 - 4343/39366)*h0 + (-1/1728)*h1
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_7_48 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 - 112*t^7 + 176*t^6 + 224*t^5 - 592*t^4 - 16*t^3 + 400*t^2 - 96*t:ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6/96 - t^5/24 - t^4/96 + 11*t^3/96 - t^2/24 - 13*t/96 - 7/48)*h0 + (-1/768)*h1
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_7_49 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 14*t/3 + 8/9:ℝ)=0) (h1 : (16*t^8 - 208*t^7/3 + 592*t^6/9 + 1472*t^5/27 - 10352*t^4/81 + 31280*t^3/243 - 35696*t^2/729 - 182944*t/2187 + 413440/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (81*t^7/704 - 153*t^6/352 + 207*t^5/704 + 303*t^4/704 - 49*t^3/66 + 1343*t^2/2112 - 53*t/288 - 4901/7128)*h0 + (9/352 - 81*t/5632)*h1
  norm_num at hh

private lemma cell_7_50 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 20*t/3 + 2/9:ℝ)=0) (h1 : (16*t^8 - 400*t^7/3 + 2560*t^6/9 + 4784*t^5/27 - 74096*t^4/81 + 23840*t^3/243 + 530080*t^2/729 - 62464*t/2187 - 129920/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-567*t^7/4640 + 1179*t^6/1160 - 2493*t^5/1160 - 6603*t^4/4640 + 24259*t^3/3480 - 3701*t^2/6960 - 29309*t/5220 - 5/324)*h0 + (567*t/37120 - 1881/37120)*h1
  norm_num at hh

private lemma cell_7_51 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 - 240*t^7 + 1360*t^6 - 3648*t^5 + 4624*t^4 - 2160*t^3 - 240*t^2 + 288*t:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7/16 - 11*t^6/12 + 241*t^5/48 - 611*t^4/48 + 115*t^3/8 - 71*t^2/16 - 17*t/8 + 1/2)*h0 + (11/384 - t/128)*h1
  norm_num at hh

private lemma cell_7_52 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 14*t/3 + 8/9:ℝ)=0) (h1 : (16*t^8 - 208*t^7/3 - 560*t^6/9 + 12704*t^5/27 - 1712*t^4/81 - 232816*t^3/243 + 128464*t^2/729 + 1142432*t/2187 - 116480/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-27*t^7/64 + 27*t^6/32 + 243*t^5/64 - 251*t^4/64 - 329*t^3/32 + 193*t^2/64 + 6013*t/864 + 9/8)*h0 + (27*t/512)*h1
  norm_num at hh

private lemma cell_7_53 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 10*t/3 + 8/9:ℝ)=0) : False := by
  have hh : ((t-(1/3))*(t-(4/3)))*(1:ℝ)=0 := by linear_combination (1/2)*h0
  have hv := (mul_eq_zero.mp hh).resolve_left (mul_ne_zero hn1 hn2)
  norm_num at hv

private lemma cell_7_54 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 16*t/3 + 14/9:ℝ)=0) (h1 : (16*t^8 - 272*t^7/3 + 160*t^6/9 + 14224*t^5/27 - 30128*t^4/81 - 237920*t^3/243 + 393568*t^2/729 + 1236544*t/2187 - 116480/6561:ℝ)=0) : (t - 7/3:ℝ)=0 := by
  have hh : (t - 7/3:ℝ)=0 := by linear_combination (t^6/12 - t^5/4 - 23*t^4/36 + 100*t^3/81 + 50*t^2/27 - 545*t/486 - 7081/4374)*h0 + (-1/96)*h1
  exact hh

private lemma cell_7_55 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 16*t/3 + 14/9:ℝ)=0) (h2 : (16*t^8 + 112*t^7/3 - 1088*t^6/9 - 4928*t^5/27 + 33328*t^4/81 + 34000*t^3/243 - 379136*t^2/729 + 553216*t/2187 - 235520/6561:ℝ)=0) : False := by
  have hh : ((t-(1/3)))*(1:ℝ)=0 := by linear_combination (-t^6/480 - t^5/96 - t^4/96 + 53*t^3/12960 - 14*t^2/405 - 46*t/405 - 911/4374)*h0 + (1/3840)*h2
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_7_56 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 20*t/3 + 2/9:ℝ)=0) (h1 : (16*t^8 - 400*t^7/3 + 3136*t^6/9 - 6016*t^5/27 - 26576*t^4/81 + 111824*t^3/243 - 70400*t^2/729 - 323392*t/2187 + 394240/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (837*t^7/18560 - 54*t^6/145 + 891*t^5/928 - 2719*t^4/4640 - 17421*t^3/18560 + 5783*t^2/4640 - 29981*t/125280 - 365/783)*h0 + (2727/148480 - 837*t/148480)*h1
  norm_num at hh

private lemma cell_7_57 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 16*t/3 + 14/9:ℝ)=0) (h2 : (16*t^8 - 272*t^7/3 + 160*t^6/9 + 14224*t^5/27 - 30128*t^4/81 - 237920*t^3/243 + 393568*t^2/729 + 1236544*t/2187 - 116480/6561:ℝ)=0) : (t - 7/3:ℝ)=0 := by
  have hh : (t - 7/3:ℝ)=0 := by linear_combination (t^6/12 - t^5/4 - 23*t^4/36 + 100*t^3/81 + 50*t^2/27 - 545*t/486 - 7081/4374)*h0 + (-1/96)*h2
  exact hh

private lemma cell_7_58 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 22*t/3 + 2/9:ℝ)=0) (h1 : (16*t^8 - 464*t^7/3 + 4240*t^6/9 - 9248*t^5/27 - 47600*t^4/81 + 174544*t^3/243 + 80080*t^2/729 - 469472*t/2187 + 267904/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7*t^7/108 - 101*t^6/162 + 305*t^5/162 - 1927*t^4/1458 - 21121*t^3/8748 + 12331*t^2/4374 + 20459*t/39366 - 104831/118098)*h0 + (19/648 - 7*t/864)*h1
  norm_num at hh

private lemma cell_7_59 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 28*t/3 + 26/9:ℝ)=0) (h1 : (16*t^8 - 848*t^7/3 + 17584*t^6/9 - 183200*t^5/27 + 1019056*t^4/81 - 2963696*t^3/243 + 4105744*t^2/729 - 2160416*t/2187 + 165760/6561:ℝ)=0) (h2 : (16*t^8 - 272*t^7/3 + 160*t^6/9 + 14224*t^5/27 - 30128*t^4/81 - 237920*t^3/243 + 393568*t^2/729 + 1236544*t/2187 - 116480/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-t^13/2592 + 55*t^12/7776 - 193*t^11/3888 + 5453*t^10/34992 - 3095*t^9/26244 - 20021*t^8/34992 + 932647*t^7/629856 - 1040725*t^6/1889568 - 1005401*t^5/472392 + 67613825*t^4/25509168 + 2370253*t^3/19131876 - 81751435*t^2/38263752 + 136423741*t/172186884 + 93387529/258280326)*h0 + (t^7/20736 - t^6/3888 - t^5/31104 + 883*t^4/559872 - 125*t^3/209952 - 2645*t^2/839808 + 1091*t/1889568 + 21503/11337408)*h1 + (1/192)*h2
  norm_num at hh

private lemma cell_7_60 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 - 48*t^7 - 128*t^6 + 384*t^5 + 304*t^4 - 912*t^3 - 192*t^2 + 576*t:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (23*t^7/1248 - 21*t^6/416 - 67*t^5/416 + 499*t^4/1248 + 95*t^3/208 - 97*t^2/104 - 25*t/52 + 1/2)*h0 + (43/4992 - 23*t/9984)*h1
  norm_num at hh

private lemma cell_7_61 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 16*t/3 + 14/9:ℝ)=0) (h1 : (16*t^8 + 112*t^7/3 - 1088*t^6/9 - 4928*t^5/27 + 33328*t^4/81 + 34000*t^3/243 - 379136*t^2/729 + 553216*t/2187 - 235520/6561:ℝ)=0) : False := by
  have hh : ((t-(1/3)))*(1:ℝ)=0 := by linear_combination (-t^6/480 - t^5/96 - t^4/96 + 53*t^3/12960 - 14*t^2/405 - 46*t/405 - 911/4374)*h0 + (1/3840)*h1
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_7_62 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 28*t/3 + 26/9:ℝ)=0) (h1 : (16*t^8 - 272*t^7/3 + 160*t^6/9 + 14224*t^5/27 - 30128*t^4/81 - 237920*t^3/243 + 393568*t^2/729 + 1236544*t/2187 - 116480/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (73*t^7/7020 - 2339*t^6/42120 - 289*t^5/42120 + 129053*t^4/379080 - 73447*t^3/568620 - 387607*t^2/568620 + 302453*t/2558790 + 584669/1535274)*h0 + (1901/336960 - 73*t/56160)*h1
  norm_num at hh

private lemma cell_7_63 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 6*t:ℝ)=0) : False := by
  have hh : ((t-(1/3)))*(1:ℝ)=0 := by linear_combination (-1/6)*h0
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma pair_7_27_45 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 7/3:ℝ)=0) (h2 : (1296*t^8 - 9936*t^7 + 32112*t^6 - 57120*t^5 + 60784*t^4 - 116432*t^3/3 + 124432*t^2/9 - 61280*t/27 + 8320/81:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-27*t^7/160 + 9*t^6/10 - 333*t^5/160 + 413*t^4/160 - 227*t^3/120 + 307*t^2/480 - 133*t/432 - 137/324)*h0 + (1/7680)*h2
  norm_num at hh

private lemma pair_7_27_54 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 7/3:ℝ)=0) (h2 : (1296*t^8 - 9936*t^7 + 32112*t^6 - 57120*t^5 + 60784*t^4 - 116432*t^3/3 + 124432*t^2/9 - 61280*t/27 + 8320/81:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-27*t^7/160 + 9*t^6/10 - 333*t^5/160 + 413*t^4/160 - 227*t^3/120 + 307*t^2/480 - 133*t/432 - 137/324)*h0 + (1/7680)*h2
  norm_num at hh

private lemma pair_7_30_39 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 7/3:ℝ)=0) (h2 : (1296*t^8 - 9936*t^7 + 32112*t^6 - 57120*t^5 + 60784*t^4 - 116432*t^3/3 + 124432*t^2/9 - 61280*t/27 + 8320/81:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-27*t^7/160 + 9*t^6/10 - 333*t^5/160 + 413*t^4/160 - 227*t^3/120 + 307*t^2/480 - 133*t/432 - 137/324)*h0 + (1/7680)*h2
  norm_num at hh

private lemma pair_7_30_57 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 7/3:ℝ)=0) (h2 : (1296*t^8 - 9936*t^7 + 32112*t^6 - 57120*t^5 + 60784*t^4 - 116432*t^3/3 + 124432*t^2/9 - 61280*t/27 + 8320/81:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-27*t^7/160 + 9*t^6/10 - 333*t^5/160 + 413*t^4/160 - 227*t^3/120 + 307*t^2/480 - 133*t/432 - 137/324)*h0 + (1/7680)*h2
  norm_num at hh

private lemma pair_7_31_37 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 7/3:ℝ)=0) (h2 : (16*t^8 + 112*t^7/3 - 1088*t^6/9 - 4928*t^5/27 + 33328*t^4/81 + 34000*t^3/243 - 379136*t^2/729 + 553216*t/2187 - 235520/6561:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-t^7/480 - 7*t^6/720 - t^5/144 + 49*t^4/6480 - 1397*t^3/38880 - 124*t^2/1215 - 3727*t/21870 - 2825/6561)*h0 + (1/7680)*h2
  norm_num at hh

private lemma pair_7_39_57 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 7/3:ℝ)=0) (h2 : (1296*t^8 - 9936*t^7 + 32112*t^6 - 57120*t^5 + 60784*t^4 - 116432*t^3/3 + 124432*t^2/9 - 61280*t/27 + 8320/81:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-27*t^7/160 + 9*t^6/10 - 333*t^5/160 + 413*t^4/160 - 227*t^3/120 + 307*t^2/480 - 133*t/432 - 137/324)*h0 + (1/7680)*h2
  norm_num at hh

private lemma pair_7_45_54 (z t : ℝ) (_hf : 3*z - 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/3)≠0) (_hn2 : t-(4/3)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 7/3:ℝ)=0) (h2 : (1296*t^8 - 9936*t^7 + 32112*t^6 - 57120*t^5 + 60784*t^4 - 116432*t^3/3 + 124432*t^2/9 - 61280*t/27 + 8320/81:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-27*t^7/160 + 9*t^6/10 - 333*t^5/160 + 413*t^4/160 - 227*t^3/120 + 307*t^2/480 - 133*t/432 - 137/324)*h0 + (1/7680)*h2
  norm_num at hh

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_0 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 0) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_0 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_1 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 1) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_1 z t hf hn0 hn1 hn2 hn3
  · have hr : (-16/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_2 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 2) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_2 z t hf hn0 hn1 hn2 hn3
  · have hr : (-40/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_3 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 3) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_3 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 112*t^7 + 176*t^6 + 224*t^5 - 592*t^4 - 16*t^3 + 400*t^2 - 96*t:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_4 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 4) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_4 z t hf hn0 hn1 hn2 hn3
  · have hr : (-16/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_5 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 5) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_5 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_6 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 6) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_6 z t hf hn0 hn1 hn2 hn3
  · have hr : (-16/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_7 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 7) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_7 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 14*t/3 + 8/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 784*t^7/3 + 14560*t^6/9 - 128128*t^5/27 + 533680*t^4/81 - 854896*t^3/243 + 43360*t^2/729 + 677888*t/2187 - 68096/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_8 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 8) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_8 z t hf hn0 hn1 hn2 hn3
  · have hr : (-40/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_9 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 9) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_9 z t hf hn0 hn1 hn2 hn3
  · have hr : (-16/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_10 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 10) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_10 z t hf hn0 hn1 hn2 hn3
  · have hr : (-46/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_11 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 11) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_11 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 20*t/3 + 2/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 976*t^7/3 + 23440*t^6/9 - 284224*t^5/27 + 1851472*t^4/81 - 6422608*t^3/243 + 11394448*t^2/729 - 9336352*t/2187 + 2619904/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_12 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 12) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_12 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 112*t^7 + 176*t^6 + 224*t^5 - 592*t^4 - 16*t^3 + 400*t^2 - 96*t:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_13 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 13) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_13 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 14*t/3 + 8/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 208*t^7/3 + 592*t^6/9 + 1472*t^5/27 - 10352*t^4/81 + 31280*t^3/243 - 35696*t^2/729 - 182944*t/2187 + 413440/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_14 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 14) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_14 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 20*t/3 + 2/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 400*t^7/3 + 2560*t^6/9 + 4784*t^5/27 - 74096*t^4/81 + 23840*t^3/243 + 530080*t^2/729 - 62464*t/2187 - 129920/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_15 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 15) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_15 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 240*t^7 + 1360*t^6 - 3648*t^5 + 4624*t^4 - 2160*t^3 - 240*t^2 + 288*t:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_16 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 16) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_16 z t hf hn0 hn1 hn2 hn3
  · have hr : (-16/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_17 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 17) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_17 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_18 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 18) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_18 z t hf hn0 hn1 hn2 hn3
  · have hr : (-16/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_19 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 19) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_19 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 14*t/3 + 8/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 784*t^7/3 + 14560*t^6/9 - 128128*t^5/27 + 533680*t^4/81 - 854896*t^3/243 + 43360*t^2/729 + 677888*t/2187 - 68096/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_20 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 20) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_20 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_21 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (_hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 21) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : ((0:ℝ):ℝ)=0 := by
  apply cell_7_21 z t hf hn0 hn1 hn2 hn3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_22 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 22) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_22 z t hf hn0 hn1 hn2 hn3
  · have hr : (576*t:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_23 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 23) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_23 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 10*t/3 + 8/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 656*t^7/3 + 9472*t^6/9 - 53888*t^5/27 + 53296*t^4/81 + 383824*t^3/243 - 361280*t^2/729 - 425024*t/2187 + 394240/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_24 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 24) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_24 z t hf hn0 hn1 hn2 hn3
  · have hr : (-16/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_25 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 25) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_25 z t hf hn0 hn1 hn2 hn3
  · have hr : (576*t:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_26 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 26) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_26 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_27 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 27) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : (t - 7/3:ℝ)=0 := by
  apply cell_7_27 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 16*t/3 + 14/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 272*t^7/3 + 160*t^6/9 + 14224*t^5/27 - 30128*t^4/81 - 237920*t^3/243 + 393568*t^2/729 + 1236544*t/2187 - 116480/6561:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_28 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 28) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_28 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 14*t/3 + 8/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 208*t^7/3 - 560*t^6/9 + 12704*t^5/27 - 1712*t^4/81 - 232816*t^3/243 + 128464*t^2/729 + 1142432*t/2187 - 116480/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_29 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 29) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_29 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 10*t/3 + 8/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 656*t^7/3 + 9472*t^6/9 - 53888*t^5/27 + 53296*t^4/81 + 383824*t^3/243 - 361280*t^2/729 - 425024*t/2187 + 394240/6561:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_30 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 30) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : (t - 7/3:ℝ)=0 := by
  apply cell_7_30 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 16*t/3 + 14/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 272*t^7/3 + 160*t^6/9 + 14224*t^5/27 - 30128*t^4/81 - 237920*t^3/243 + 393568*t^2/729 + 1236544*t/2187 - 116480/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_31 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 31) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : (t - 7/3:ℝ)=0 := by
  apply cell_7_31 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 16*t/3 + 14/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_32 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 32) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_32 z t hf hn0 hn1 hn2 hn3
  · have hr : (-40/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_33 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 33) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_33 z t hf hn0 hn1 hn2 hn3
  · have hr : (-16/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_34 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 34) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_34 z t hf hn0 hn1 hn2 hn3
  · have hr : (-46/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_35 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 35) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_35 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 20*t/3 + 2/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 976*t^7/3 + 23440*t^6/9 - 284224*t^5/27 + 1851472*t^4/81 - 6422608*t^3/243 + 11394448*t^2/729 - 9336352*t/2187 + 2619904/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_36 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 36) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_36 z t hf hn0 hn1 hn2 hn3
  · have hr : (-16/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_37 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (_hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 37) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : ((0:ℝ):ℝ)=0 := by
  apply cell_7_37 z t hf hn0 hn1 hn2 hn3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_38 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 38) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_38 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_39 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 39) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : (t - 7/3:ℝ)=0 := by
  apply cell_7_39 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 16*t/3 + 14/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_40 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 40) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_40 z t hf hn0 hn1 hn2 hn3
  · have hr : (-46/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_41 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 41) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_41 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_42 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 42) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_42 z t hf hn0 hn1 hn2 hn3
  · have hr : (-6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_43 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 43) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_43 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 22*t/3 + 2/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 1040*t^7/3 + 26848*t^6/9 - 354416*t^5/27 + 2564560*t^4/81 - 10205408*t^3/243 + 21715936*t^2/729 - 22715456*t/2187 + 8968960/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_44 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 44) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_44 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 20*t/3 + 2/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 400*t^7/3 + 3136*t^6/9 - 6016*t^5/27 - 26576*t^4/81 + 111824*t^3/243 - 70400*t^2/729 - 323392*t/2187 + 394240/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_45 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 45) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : (t - 7/3:ℝ)=0 := by
  apply cell_7_45 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 16*t/3 + 14/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_46 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 46) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_46 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 22*t/3 + 2/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 464*t^7/3 + 4240*t^6/9 - 9248*t^5/27 - 47600*t^4/81 + 174544*t^3/243 + 80080*t^2/729 - 469472*t/2187 + 267904/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_47 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 47) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_47 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 28*t/3 + 26/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 848*t^7/3 + 17584*t^6/9 - 183200*t^5/27 + 1019056*t^4/81 - 2963696*t^3/243 + 4105744*t^2/729 - 2160416*t/2187 + 165760/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_48 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 48) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_48 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 112*t^7 + 176*t^6 + 224*t^5 - 592*t^4 - 16*t^3 + 400*t^2 - 96*t:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_49 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 49) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_49 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 14*t/3 + 8/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 208*t^7/3 + 592*t^6/9 + 1472*t^5/27 - 10352*t^4/81 + 31280*t^3/243 - 35696*t^2/729 - 182944*t/2187 + 413440/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_50 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 50) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_50 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 20*t/3 + 2/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 400*t^7/3 + 2560*t^6/9 + 4784*t^5/27 - 74096*t^4/81 + 23840*t^3/243 + 530080*t^2/729 - 62464*t/2187 - 129920/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_51 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 51) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_51 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 240*t^7 + 1360*t^6 - 3648*t^5 + 4624*t^4 - 2160*t^3 - 240*t^2 + 288*t:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_52 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 52) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_52 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 14*t/3 + 8/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 208*t^7/3 - 560*t^6/9 + 12704*t^5/27 - 1712*t^4/81 - 232816*t^3/243 + 128464*t^2/729 + 1142432*t/2187 - 116480/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_53 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 53) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_53 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 10*t/3 + 8/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_54 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 54) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : (t - 7/3:ℝ)=0 := by
  apply cell_7_54 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 16*t/3 + 14/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 272*t^7/3 + 160*t^6/9 + 14224*t^5/27 - 30128*t^4/81 - 237920*t^3/243 + 393568*t^2/729 + 1236544*t/2187 - 116480/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_55 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 55) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_55 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 16*t/3 + 14/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 112*t^7/3 - 1088*t^6/9 - 4928*t^5/27 + 33328*t^4/81 + 34000*t^3/243 - 379136*t^2/729 + 553216*t/2187 - 235520/6561:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_56 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 56) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_56 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 20*t/3 + 2/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 400*t^7/3 + 3136*t^6/9 - 6016*t^5/27 - 26576*t^4/81 + 111824*t^3/243 - 70400*t^2/729 - 323392*t/2187 + 394240/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_57 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 57) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : (t - 7/3:ℝ)=0 := by
  apply cell_7_57 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 16*t/3 + 14/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 272*t^7/3 + 160*t^6/9 + 14224*t^5/27 - 30128*t^4/81 - 237920*t^3/243 + 393568*t^2/729 + 1236544*t/2187 - 116480/6561:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_58 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 58) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_58 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 22*t/3 + 2/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 464*t^7/3 + 4240*t^6/9 - 9248*t^5/27 - 47600*t^4/81 + 174544*t^3/243 + 80080*t^2/729 - 469472*t/2187 + 267904/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_59 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 59) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_59 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 28*t/3 + 26/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 848*t^7/3 + 17584*t^6/9 - 183200*t^5/27 + 1019056*t^4/81 - 2963696*t^3/243 + 4105744*t^2/729 - 2160416*t/2187 + 165760/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 272*t^7/3 + 160*t^6/9 + 14224*t^5/27 - 30128*t^4/81 - 237920*t^3/243 + 393568*t^2/729 + 1236544*t/2187 - 116480/6561:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_60 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 60) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_60 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 48*t^7 - 128*t^6 + 384*t^5 + 304*t^4 - 912*t^3 - 192*t^2 + 576*t:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_61 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 61) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_61 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 16*t/3 + 14/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 112*t^7/3 - 1088*t^6/9 - 4928*t^5/27 + 33328*t^4/81 + 34000*t^3/243 - 379136*t^2/729 + 553216*t/2187 - 235520/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_62 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 62) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_62 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 28*t/3 + 26/9:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 272*t^7/3 + 160*t^6/9 + 14224*t^5/27 - 30128*t^4/81 - 237920*t^3/243 + 393568*t^2/729 + 1236544*t/2187 - 116480/6561:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_7_63 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/3) (4/3) t 63) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : False := by
  apply cell_7_63 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr


private def limit7 (_z t : ℝ) : Fin 64→Prop := ![False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,(((0:ℝ):ℝ)=0),False,False,False,False,False,((t - 7/3:ℝ)=0),False,False,((t - 7/3:ℝ)=0),((t - 7/3:ℝ)=0),False,False,False,False,False,(((0:ℝ):ℝ)=0),False,((t - 7/3:ℝ)=0),False,False,False,False,False,((t - 7/3:ℝ)=0),False,False,False,False,False,False,False,False,((t - 7/3:ℝ)=0),False,False,((t - 7/3:ℝ)=0),False,False,False,False,False,False]

private def hue7 : Fin 64→Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,3,1,0,0,0,0,0,1,0,3,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,3,0,0,0,0,0,0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_7_27_45 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit7 z t 27) (_hj : limit7 z t 45) (he : edge4 (1) (1) (1) (profile4 (1/3) (4/3) t 27) (profile4 (1/3) (4/3) t 45) (1/3) (4/3) t=0) : False := by
  apply pair_7_27_45 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (1296*t^8 - 9936*t^7 + 32112*t^6 - 57120*t^5 + 60784*t^4 - 116432*t^3/3 + 124432*t^2/9 - 61280*t/27 + 8320/81:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_7_27_54 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit7 z t 27) (_hj : limit7 z t 54) (he : edge4 (1) (1) (1) (profile4 (1/3) (4/3) t 27) (profile4 (1/3) (4/3) t 54) (1/3) (4/3) t=0) : False := by
  apply pair_7_27_54 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (1296*t^8 - 9936*t^7 + 32112*t^6 - 57120*t^5 + 60784*t^4 - 116432*t^3/3 + 124432*t^2/9 - 61280*t/27 + 8320/81:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_7_30_39 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit7 z t 30) (_hj : limit7 z t 39) (he : edge4 (1) (1) (1) (profile4 (1/3) (4/3) t 30) (profile4 (1/3) (4/3) t 39) (1/3) (4/3) t=0) : False := by
  apply pair_7_30_39 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (1296*t^8 - 9936*t^7 + 32112*t^6 - 57120*t^5 + 60784*t^4 - 116432*t^3/3 + 124432*t^2/9 - 61280*t/27 + 8320/81:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_7_30_57 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit7 z t 30) (_hj : limit7 z t 57) (he : edge4 (1) (1) (1) (profile4 (1/3) (4/3) t 30) (profile4 (1/3) (4/3) t 57) (1/3) (4/3) t=0) : False := by
  apply pair_7_30_57 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (1296*t^8 - 9936*t^7 + 32112*t^6 - 57120*t^5 + 60784*t^4 - 116432*t^3/3 + 124432*t^2/9 - 61280*t/27 + 8320/81:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_7_31_37 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit7 z t 31) (_hj : limit7 z t 37) (he : edge4 (1) (1) (1) (profile4 (1/3) (4/3) t 31) (profile4 (1/3) (4/3) t 37) (1/3) (4/3) t=0) : False := by
  apply pair_7_31_37 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (16*t^8 + 112*t^7/3 - 1088*t^6/9 - 4928*t^5/27 + 33328*t^4/81 + 34000*t^3/243 - 379136*t^2/729 + 553216*t/2187 - 235520/6561:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_7_39_57 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit7 z t 39) (_hj : limit7 z t 57) (he : edge4 (1) (1) (1) (profile4 (1/3) (4/3) t 39) (profile4 (1/3) (4/3) t 57) (1/3) (4/3) t=0) : False := by
  apply pair_7_39_57 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (1296*t^8 - 9936*t^7 + 32112*t^6 - 57120*t^5 + 60784*t^4 - 116432*t^3/3 + 124432*t^2/9 - 61280*t/27 + 8320/81:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_7_45_54 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit7 z t 45) (_hj : limit7 z t 54) (he : edge4 (1) (1) (1) (profile4 (1/3) (4/3) t 45) (profile4 (1/3) (4/3) t 54) (1/3) (4/3) t=0) : False := by
  apply pair_7_45_54 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (1296*t^8 - 9936*t^7 + 32112*t^6 - 57120*t^5 + 60784*t^4 - 116432*t^3/3 + 124432*t^2/9 - 61280*t/27 + 8320/81:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma exclude_field_7 (z t : ℝ) (hf : 3*z - 4=0) (hn0 : t-(1)≠0) (hn1 : t-(1/3)≠0) (hn2 : t-(4/3)≠0) (hn3 : t-((0:ℝ))≠0) (g : Fin 5→Fin 64) (hinj : Function.Injective g)
    (hc : ∀ i, cell (1) (1) (1) (profile4 (1/3) (4/3) t (g i)) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t)
    (he : ∀ i j : Fin 5, i≠j → edge4 (1) (1) (1) (profile4 (1/3) (4/3) t (g i)) (profile4 (1/3) (4/3) t (g j)) (1/3) (4/3) t=0) : False := by
  have row (k : Fin 64) (hh : cell (1) (1) (1) (profile4 (1/3) (4/3) t k) ((1/3),(1/3),(4/3)) ((1/3),(4/3),(1/3)) (1/3) (4/3) t) : limit7 z t k := by
    fin_cases k
    · exact row_7_0 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_1 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_2 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_3 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_4 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_5 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_6 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_7 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_8 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_9 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_10 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_11 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_12 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_13 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_14 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_15 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_16 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_17 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_18 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_19 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_20 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_21 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_22 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_23 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_24 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_25 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_26 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_27 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_28 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_29 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_30 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_31 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_32 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_33 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_34 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_35 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_36 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_37 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_38 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_39 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_40 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_41 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_42 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_43 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_44 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_45 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_46 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_47 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_48 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_49 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_50 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_51 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_52 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_53 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_54 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_55 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_56 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_57 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_58 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_59 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_60 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_61 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_62 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_7_63 z t hf hn0 hn1 hn2 hn3 hh
  have allowed (k : Fin 64) (hh : limit7 z t k) : k∈([21,27,30,31,37,39,45,54,57]:List (Fin 64)) := by
    fin_cases k <;> first | decide | exact False.elim hh
  have cert : ∀ i j : Fin 64, i∈([21,27,30,31,37,39,45,54,57]:List (Fin 64)) → j∈([21,27,30,31,37,39,45,54,57]:List (Fin 64)) → i<j → hue7 i=hue7 j → (i,j)∈([(27,45),(27,54),(30,39),(30,57),(31,37),(39,57),(45,54)]:List (Fin 64×Fin 64)) := by decide
  have bad (i j : Fin 64) (hi : limit7 z t i) (hj : limit7 z t j) (hlt : i<j) (hc : hue7 i=hue7 j) (hb : edge4 (1) (1) (1) (profile4 (1/3) (4/3) t i) (profile4 (1/3) (4/3) t j) (1/3) (4/3) t=0) : False := by
    have h := cert i j (allowed i hi) (allowed j hj) hlt hc
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact rowpair_7_27_45 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_7_27_54 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_7_30_39 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_7_30_57 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_7_31_37 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_7_39_57 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_7_45_54 z t hf hn0 hn1 hn2 hn3 hi hj hb
  have hi : Function.Injective (fun i : Fin 5 => hue7 (g i)) := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne (show g i≠g j from fun e => hne (hinj e)) with hl|hl
    · exact bad _ _ (row _ (hc i)) (row _ (hc j)) hl h (he i j hne)
    · exact bad _ _ (row _ (hc j)) (row _ (hc i)) hl h.symm (he j i (Ne.symm hne))
  have hh := Fintype.card_le_of_injective _ hi
  norm_num at hh

private lemma no_0001010221 (x y t : ℝ) (H : admissible ![0,0,0,1,0,1,0,2,2,1] x y) (E : hasExtension ![0,0,0,1,0,1,0,2,2,1] x y t)
    (t1 : t-1≠0) (tx : t-x≠0) (ty : t-y≠0) (t0 : t≠0) : False := by
  obtain ⟨h0,h1⟩ := shape_0001010221 x y H
  by_cases G0 : y^4 - 7*y^3 + 14*y^2 - 8*y + 1=0
  · have ex : x=y^3 - 6*y^2 + 9*y - 1 := by linear_combination (1)*h0
    obtain ⟨u,hu,hc,he⟩ := E
    change ∀ i, cell (1) (1) (1) (profile4 x y t (u i)) ((1),(x),(y)) ((x),(1),(y)) x y t at hc
    change ∀ i j, i≠j → edge4 (1) (1) (1) (profile4 x y t (u i)) (profile4 x y t (u j)) x y t=0 at he
    simp only [ex] at hc he tx ty
    apply exclude_field_5 y t (by linear_combination (1)*G0) t1 tx ty (by simpa using t0) u hu hc he
  apply G0
  linear_combination (1)*h1

private lemma no_0011012210 (x y t : ℝ) (H : admissible ![0,0,1,1,0,1,2,2,1,0] x y) (E : hasExtension ![0,0,1,1,0,1,2,2,1,0] x y t)
    (t1 : t-1≠0) (tx : t-x≠0) (ty : t-y≠0) (t0 : t≠0) : False := by
  obtain ⟨h0,h1⟩ := shape_0011012210 x y H
  by_cases G0 : 3*y - 4=0
  · have ex : x=1/3 := by linear_combination (1)*h0
    have ey : y=4/3 := by linear_combination (1/3)*G0
    obtain ⟨u,hu,hc,he⟩ := E
    change ∀ i, cell (1) (1) (1) (profile4 x y t (u i)) ((x),(x),(y)) ((x),(y),(x)) x y t at hc
    change ∀ i j, i≠j → edge4 (1) (1) (1) (profile4 x y t (u i)) (profile4 x y t (u j)) x y t=0 at he
    simp only [ex,ey] at hc he tx ty
    apply exclude_field_7 y t (by linear_combination (1)*G0) t1 tx ty (by simpa using t0) u hu hc he
  apply G0
  linear_combination (3)*h1

private lemma no_0011101122 (x y t : ℝ) (H : admissible ![0,0,1,1,1,0,1,1,2,2] x y) (E : hasExtension ![0,0,1,1,1,0,1,1,2,2] x y t)
    (t1 : t-1≠0) (tx : t-x≠0) (ty : t-y≠0) (t0 : t≠0) : False := by
  obtain ⟨h0,h1⟩ := shape_0011101122 x y H
  by_cases G0 : y^2 - 7*y + 1=0
  · have ex : x=y/3 + 1/3 := by linear_combination (1)*h0
    apply H.2.1 0 2 4 (by decide) (by decide)
    change area (1) (x) (y)=0
    simp only [ex,area]
    linear_combination (-4/9)*G0
  apply G0
  linear_combination (1)*h1

end Erdos1082Ten

open Erdos1082Ten EuclideanGeometry

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H3_R1.H1 := by
  intro A hn hA hd M hm B hBA hB hf hthree p r c hc hh
  obtain ⟨x,y,t,H,E,t1,tx,ty,t0⟩ := given_extension A B M hm hBA hA hB hd hthree hn hf p r c hc
  change colorCode c∈([835,3072,3203]:List ℕ) at hh
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with eq|eq|eq
  · have cc : c=![0,0,0,1,0,1,0,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact no_0001010221 x y t H E t1 tx ty t0
  · have cc : c=![0,0,1,1,0,1,2,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact no_0011012210 x y t H E t1 tx ty t0
  · have cc : c=![0,0,1,1,1,0,1,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact no_0011101122 x y t H E t1 tx ty t0
