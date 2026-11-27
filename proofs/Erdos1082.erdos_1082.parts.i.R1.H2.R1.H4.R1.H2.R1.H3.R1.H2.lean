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
private lemma base_0000011120 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : x^2 + x*y - 6*x - 2*y + (5:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -y^2 + 4*y≠0) (_n10 : (3:ℝ)≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : (x^2 - 4*x + (1:ℝ)=0) ∧ (y - (2:ℝ)=0) := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h3 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (-x*y/2 + x + y^2/2 - y)*h1 + (x^2/6 - 2*x/3 - y^2/6 + 2*y/3)*g1 + (-x^2/6 + x*y/6 + x/3 - y/3 + 1)*h2
  have h4 : y - (2:ℝ)=0 := by linear_combination (1 - y/2)*h1 + (x/6 + y/6 - 2/3)*g1 + (1/3 - x/6)*h2
  have h5 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1)*h3
  have h6 : y - (2:ℝ)=0 := by linear_combination (1)*h4
  exact ⟨h5, h6⟩



private lemma base_0000012211 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : -x^2 + 4*x*y - x - y^2 - 4*y + (2:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -y^2 + 4*y≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 4*x*y - y^2≠0) (n14 : 4*x*y - y^2≠0) : (x + y^2 - 5*y + (2:ℝ)=0) ∧ (y^3 - 6*y^2 + 9*y - (3:ℝ)=0) := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 4*x*y + x + y^2 + 4*y - (2:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x + y^3 - 5*y^2 + 4*y - (1:ℝ)=0 := by linear_combination (x/3 - y/3)*h2 + (-x/3 + 4*y/3 - 1)*h3
  have h5 : y^4 - 6*y^3 + 9*y^2 - 3*y=0 := by linear_combination (x*y/3 - x/3 - y^2/3 + y/3 + 1/3)*h2 + (-x*y/3 + x/3 + 4*y^2/3 - 7*y/3 + 2/3)*h3
  have h6 : x + y^3 - 5*y^2 + 4*y - (1:ℝ)=0 := by linear_combination (1)*h4
  have h8 : y≠0 := by
    intro he
    apply n14
    linear_combination (4*x - y)*he
  have h9 : ((y))*(y^3 - 6*y^2 + 9*y - 3)=0 := by linear_combination (1)*h5
  have h7 := (mul_eq_zero.mp h9).resolve_left h8
  have h10 : x + y^2 - 5*y + (2:ℝ)=0 := by linear_combination (1)*h6 + (-1)*h7
  exact ⟨h10, h7⟩



private lemma shape_0000011120 (x y : ℝ) (ha : admissible ![0,0,0,0,0,1,1,1,2,0] x y) : (x^2 - 4*x + 1=0) ∧ (y - 2=0) := by
  apply base_0000011120 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x 1 x y 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0000012211 (x y : ℝ) (ha : admissible ![0,0,0,0,0,1,2,2,1,1] x y) : (x + y^2 - 5*y + 2=0) ∧ (y^3 - 6*y^2 + 9*y - 3=0) := by
  apply base_0000012211 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y 1 y x x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 y x 1 y x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
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
  · have hn : area x y x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring

private lemma cell_0_0 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_0_1 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 3/4)*h0 + (-1/2)*hf
  norm_num at hh

private lemma cell_0_2 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_0_3 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) : (t - 3:ℝ)=0 := by
  have hh : ((t-((0:ℝ))))*(t - 3:ℝ)=0 := by linear_combination (1/2)*h0
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  exact hv

private lemma cell_0_4 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 3/4)*h0 + (-1/2)*hf
  norm_num at hh

private lemma cell_0_5 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (h1 : (2592*t*z:ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (1/648 - z/2592)*h1 + (t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_0_6 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (h2 : (2592*t*z:ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (1/648 - z/2592)*h2 + (t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_0_7 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 4*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 48) + t^6*(2032*z - 592) + t^5*(4448 - 14160*z) + t^4*(54080*z - 14736) + t^3*(29872 - 116656*z) + t^2*(137040*z - 36176) + t*(21600 - 77984*z) + 15232*z - 4096:ℝ)=0) (h2 : (16*t^8 - 304*t^7 + t^6*(2224 - 48*z) + t^5*(720*z - 7888) + t^4*(13792 - 3600*z) + t^3*(6384*z - 9952) + t^2*(-1440*z - 128) + t*(2432 - 1440*z) + 384*z - 512:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(13*z/52488 - 97/104976) + t^12*(241/13122 - 517*z/104976) + t^11*(23*z/648 - 257/1944) + t^10*(37079/104976 - 2503*z/26244) + t^9*(14683/52488 - 1849*z/26244) + t^8*(1619*z/1944 - 1369/432) + t^7*(131107/34992 - 34067*z/34992) + t^6*(184387/34992 - 3110*z/2187) + t^5*(5335*z/1944 - 13547/1296) + t^4*(39821*z/104976 - 117649/104976) + t^3*(677717/104976 - 187315*z/104976) + t^2*(1463*z/1944 - 604/243) + t*(5131/52488 - 4721*z/52488) - 8677*z/26244 + 9044/6561)*h0 + (t^7*(97/839808 - 13*z/419904) + t^6*(221*z/419904 - 1649/839808) + t^5*(1123/93312 - 301*z/93312) + t^4*(7085*z/839808 - 26437/839808) + t^3*(12445/419904 - 6667*z/839808) + t^2*(5*z/93312 - 5/23328) + t*(29*z/26244 - 869/209952) - 733*z/419904 + 1363/209952)*h1 + (1/1296 - z/5184)*h2 + (-91*t^14/26244 + 6269*t^13/52488 - 12007*t^12/6561 + 862309*t^11/52488 - 2510747*t^10/26244 + 4955311*t^9/13122 - 2241113*t^8/2187 + 33179401*t^7/17496 - 20245841*t^6/8748 + 89579089*t^5/52488 - 14103791*t^4/26244 - 5776171*t^3/26244 + 2106812*t^2/6561 - 1007393*t/6561 + 183617/6561)*hf
  norm_num at hh

private lemma cell_0_8 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_0_9 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h2 : (t*(2592*z - 7776) - 7776*z + 23328:ℝ)=0) : (t - 3:ℝ)=0 := by
  have hh : (t - 3:ℝ)=0 := by linear_combination (z/5184 - 1/5184)*h2 + (3/2 - t/2)*hf
  exact hh

private lemma cell_0_10 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/6)*h0
  norm_num at hh

private lemma cell_0_11 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 176) + t^6*(992*z + 624) + t^5*(-6144*z - 352) + t^4*(19264*z - 2992) + t^3*(8064 - 31664*z) + t^2*(24960*z - 8144) + t*(2800 - 6160*z) - 1120*z + 96:ℝ)=0) (h2 : (16*t^8 + t^7*(64*z - 432) + t^6*(4784 - 1088*z) + t^5*(7584*z - 28672) + t^4*(102288 - 28192*z) + t^3*(60848*z - 222752) + t^2*(288400 - 77088*z) + t*(53392*z - 201840) - 15392*z + 58016:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(z/52488 - 1/104976) + t^12*(2/6561 - 61*z/104976) + t^11*(43*z/5832 - 49/11664) + t^10*(863/26244 - 5257*z/104976) + t^9*(10111*z/52488 - 8549/52488) + t^8*(13/24 - 757*z/1944) + t^7*(3773*z/17496 - 44237/34992) + t^6*(22657*z/34992 + 9395/4374) + t^5*(-95*z/81 - 10289/3888) + t^4*(21365*z/104976 + 12845/6561) + t^3*(16895*z/26244 + 7457/26244) + t^2*(1549*z/5832 - 15863/5832) + t*(159907/52488 - 50651*z/52488) + 10805*z/26244 - 38251/26244)*h0 + (t^7*(1/839808 - z/419904) + t^6*(19*z/839808 - 17/839808) + t^5*(1/5832 - 7*z/93312) + t^4*(79*z/419904 - 781/839808) + t^3*(2711/839808 - 601*z/839808) + t^2*(85*z/46656 - 635/93312) + t*(6859/839808 - 1919*z/839808) + 527*z/419904 - 2011/419904)*h1 + (z/5184)*h2 + (-t^14/6561 + 25*t^13/6561 - 1099*t^12/26244 + 7121*t^11/26244 - 31613*t^10/26244 + 220627*t^9/52488 - 226213*t^8/17496 + 617269*t^7/17496 - 341011*t^6/4374 + 3330137*t^5/26244 - 3694199*t^4/26244 + 626300*t^3/6561 - 1495439*t^2/52488 - 134567*t/26244 + 28703/6561)*hf
  norm_num at hh

private lemma cell_0_12 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h2 : (16*t^8 + t^7*(16 - 128*z) + t^6*(1584*z - 576) + t^5*(2640 - 9168*z) + t^4*(29232*z - 7488) + t^3*(13104 - 50400*z) + t^2*(43200*z - 11664) + t*(3888 - 14256*z):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (-t^6/648 + t^5*(z/81 - 1/162) + t^4*(1/27 - 25*z/216) + t^3*(29*z/54 - 31/216) + t^2*(7/24 - 29*z/24) + t*(89*z/72 - 7/18) - 11*z/24 - 1/24)*h0 + (1/5184)*h2
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_0_13 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 4*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 48) + t^6*(2032*z - 592) + t^5*(4448 - 14160*z) + t^4*(54080*z - 14736) + t^3*(29872 - 116656*z) + t^2*(137040*z - 36176) + t*(21600 - 77984*z) + 15232*z - 4096:ℝ)=0) (h2 : (16*t^8 + t^7*(80 - 192*z) + t^6*(3072*z - 848) + t^5*(7520 - 27936*z) + t^4*(151680*z - 40592) + t^3*(134528 - 502032*z) + t^2*(987264*z - 264656) + t*(282032 - 1053840*z) + 467328*z - 125120:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(5*z/104976 - 19/104976) + t^12*(11*z/104976 - 19/104976) + t^11*(37/11664 - 29*z/11664) + t^10*(3071*z/104976 - 445/104976) + t^9*(4435/52488 - 4463*z/13122) + t^8*(5191*z/1944 - 1411/1944) + t^7*(137761/34992 - 514367*z/34992) + t^6*(2015563*z/34992 - 540857/34992) + t^5*(165787/3888 - 206315*z/1296) + t^4*(31932569*z/104976 - 8581135/104976) + t^3*(1348519/13122 - 2542783*z/6561) + t^2*(1834781*z/5832 - 61898/729) + t*(551251/13122 - 3994885*z/26244) + 487321*z/13122 - 235375/26244)*h0 + (t^7*(19/839808 - 5*z/839808) + t^6*(73/839808 - 23*z/839808) + t^5*(z/31104 + 11/93312) + t^4*(199/419904 - 275*z/419904) + t^3*(2105*z/839808 - 7/839808) + t^2*(317/93312 - 239*z/31104) + t*(8095*z/839808 - 53/839808) - 95*z/13122 + 2741/419904)*h1 + (1/5184 - z/5184)*h2 + (-35*t^14/52488 + 113*t^13/13122 - 1571*t^12/52488 - 7691*t^11/52488 + 13753*t^10/6561 - 670115*t^9/52488 + 957323*t^8/17496 - 1520035*t^7/8748 + 7061795*t^6/17496 - 35453705*t^5/52488 + 21305227*t^4/26244 - 37806797*t^3/52488 + 12818939*t^2/26244 - 6076421*t/26244 + 340340/6561)*hf
  norm_num at hh

private lemma cell_0_14 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 176) + t^6*(992*z + 624) + t^5*(-6144*z - 352) + t^4*(19264*z - 2992) + t^3*(8064 - 31664*z) + t^2*(24960*z - 8144) + t*(2800 - 6160*z) - 1120*z + 96:ℝ)=0) (h2 : (16*t^8 + t^7*(-128*z - 48) + t^6*(2032*z - 592) + t^5*(4448 - 14160*z) + t^4*(54080*z - 14736) + t^3*(29872 - 116656*z) + t^2*(137040*z - 36176) + t*(21600 - 77984*z) + 15232*z - 4096:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(7*z/52488 - 13/26244) + t^12*(337/52488 - 23*z/13122) + t^11*(49*z/5832 - 167/5832) + t^10*(1759/52488 - 971*z/52488) + t^9*(637*z/13122 + 3077/26244) + t^8*(-703*z/1944 - 221/648) + t^7*(31919*z/17496 - 1871/8748) + t^6*(38087/17496 - 11696*z/2187) + t^5*(533*z/54 - 1951/486) + t^4*(192163/52488 - 618785*z/52488) + t^3*(56600*z/6561 - 32725/26244) + t^2*(-4631*z/1458 - 2371/2916) + t*(13301*z/26244 - 6763/26244) - 3317*z/13122 + 5783/6561)*h0 + (t^7*(13/209952 - 7*z/419904) + t^6*(35*z/419904 - 127/419904) + t^5*(z/23328 - 1/3888) + t^4*(1015/419904 - 53*z/104976) + t^3*(-73*z/209952 - 37/209952) + t^2*(95*z/46656 - 29/5184) + t*(157/209952 - 29*z/52488) - 79*z/104976 + 607/209952)*h1 + (5/864 - z/648)*h2 + (-7*t^14/6561 + 287*t^13/13122 - 2393*t^12/13122 + 4976*t^11/6561 - 36521*t^10/26244 - 10423*t^9/26244 + 41191*t^8/8748 + 25799*t^7/8748 - 160909*t^6/4374 + 1423949*t^5/26244 + 353363*t^4/13122 - 4669057*t^3/26244 + 3006805*t^2/13122 - 824063*t/6561 + 148694/6561)*hf
  norm_num at hh

private lemma cell_0_15 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 48) + t^6*(2032*z - 592) + t^5*(4448 - 14160*z) + t^4*(54080*z - 14736) + t^3*(29872 - 116656*z) + t^2*(137040*z - 36176) + t*(21600 - 77984*z) + 15232*z - 4096:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(19/1458 - 5*z/1458) + t^6*(11*z/729 - 187/2916) + t^5*(11*z/243 - 61/972) + t^4*(427/729 - 1043*z/2916) + t^3*(2515*z/2916 - 863/2916) + t^2*(-1441*z/972 - 673/972) + t*(2791*z/1458 - 569/1458) - 766*z/729 + 1201/1458)*h0 + (t*(5*z/11664 - 19/11664) - 19*z/11664 + 145/23328)*h1 + (40*t^8/729 - 787*t^7/729 + 6838*t^6/729 - 33715*t^5/729 + 100675*t^4/729 - 181354*t^3/729 + 187105*t^2/729 - 97366*t/729 + 18088/729)*hf
  norm_num at hh

private lemma cell_0_16 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 3/4)*h0 + (-1/2)*hf
  norm_num at hh

private lemma cell_0_17 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(12960 - 49248*z) + 368064*z - 98496:ℝ)=0) (h2 : (t*(23328 - 85536*z) + 723168*z - 194400:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (19*z/15552 - 71/15552)*h1 + (11*z/15552 - 41/15552)*h2 + (362*t/3 - 5767/6)*hf
  norm_num at hh

private lemma cell_0_18 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(23328 - 85536*z) + 723168*z - 194400:ℝ)=0) (h2 : (t*(12960 - 49248*z) + 368064*z - 98496:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (11*z/15552 - 41/15552)*h1 + (19*z/15552 - 71/15552)*h2 + (362*t/3 - 5767/6)*hf
  norm_num at hh

private lemma cell_0_19 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 4*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 48) + t^6*(2416*z - 592) + t^5*(6752 - 24240*z) + t^4*(162080*z - 43824) + t^3*(200368 - 747184*z) + t^2*(2325840*z - 623120) + t*(1203840 - 4493888*z) + 4258144*z - 1140832:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(17/324 - 41*z/2916) + t^6*(157*z/1944 - 1757/5832) + t^5*(79/324 - 16*z/243) + t^4*(503/486 - 199*z/729) + t^3*(725*z/1944 - 8647/5832) + t^2*(7*z/486 + 5/18) + t*(155/486 - 827*z/2916) + 140*z/243 - 2051/1458)*h0 + (t*(41*z/23328 - 17/2592) - 235*z/46656 + 877/46656)*h1 + (287*t^8/1458 - 13627*t^7/2916 + 158389*t^6/2916 - 1187509*t^5/2916 + 6215227*t^4/2916 - 22898461*t^3/2916 + 57190129*t^2/2916 - 21955075*t/729 + 31267385/1458)*hf
  norm_num at hh

private lemma cell_0_20 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(12960 - 49248*z) + 368064*z - 98496:ℝ)=0) : (t - 2*z:ℝ)=0 := by
  have hh : (t - 2*z:ℝ)=0 := by linear_combination (19*z/15552 - 71/15552)*h1 + (361*t/6 - 1349/3)*hf
  exact hh

private lemma cell_0_21 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 6*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (11/4 - 3*z/4)*h0 + (-9/2)*hf
  norm_num at hh

private lemma cell_0_22 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3/8 - z/8)*h0 + (-1/2)*hf
  norm_num at hh

private lemma cell_0_23 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 4*z:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 192*z) + t^6*(3840*z - 1184) + t^5*(11056 - 40032*z) + t^4*(257856*z - 68720) + t^3*(279856 - 1047216*z) + t^2*(2609136*z - 699248) + t*(975904 - 3641088*z) + 2176512*z - 583232:ℝ)=0) : (t - 2*z:ℝ)=0 := by
  have hh : (t - 2*z:ℝ)=0 := by linear_combination (t^6*(71/1944 - 19*z/1944) + t^5*(z/162 - 2/81) + t^4*(19*z/162 - 67/162) + t^3*(287/1944 - 175*z/1944) + t^2*(98/81 - 8*z/81) + t*(113/324 - 53*z/81) + 871*z/972 - 863/972)*h0 + (19*z/15552 - 71/15552)*h1 + (95*t^7/486 - 2249*t^6/486 + 2665*t^5/54 - 153505*t^4/486 + 1243535*t^3/972 - 344501*t^2/108 + 1082455*t/243 - 647023/243)*hf
  exact hh

private lemma cell_0_24 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(23328 - 85536*z) + 723168*z - 194400:ℝ)=0) (h2 : (t*(2592 - 12960*z) + 75168*z - 18144:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7/1944 - 5*z/5184)*h1 + (13/7776 - 7*z/15552)*h2 + (2194/3 - 265*t/3)*hf
  norm_num at hh

private lemma cell_0_25 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3/8 - z/8)*h0 + (-1/2)*hf
  norm_num at hh

private lemma cell_0_26 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 2)*h0 + (1)*hf
  norm_num at hh

private lemma cell_0_27 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 6) + 2*z + 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 112) + t^6*(2672*z - 96) + t^5*(5824 - 27840*z) + t^4*(181360*z - 45760) + t^3*(205056 - 776656*z) + t^2*(2149824*z - 574352) + t*(945296 - 3527504*z) + 2635904*z - 706944:ℝ)=0) (h2 : (16*t^8 - 368*t^7 + t^6*(144*z + 3616) + t^5*(-2448*z - 20048) + t^4*(18864*z + 68416) + t^3*(-83232*z - 144752) + t^2*(223200*z + 176848) + t*(-346320*z - 96560) + 252000*z - 2720:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(2521/944784 - 1351*z/1889568) + t^12*(35947*z/1889568 - 33539/472392) + t^11*(134657/157464 - 144325*z/629856) + t^10*(395009*z/236196 - 11793539/1889568) + t^9*(29280949/944784 - 7845821*z/944784) + t^8*(6244033*z/209952 - 23302955/209952) + t^7*(186060517/629856 - 12463805*z/157464) + t^6*(99570947*z/629856 - 185797895/314928) + t^5*(183581387/209952 - 1537286*z/6561) + t^4*(467957515*z/1889568 - 873091903/944784) + t^3*(74756651/118098 - 160322123*z/944784) + t^2*(17721257*z/314928 - 16499659/78732) + t*(3414551*z/472392 - 1615202/59049) - 2180821*z/236196 + 8146889/236196)*h0 + (t^7*(1351*z/15116544 - 2521/7558272) + t^6*(104531/15116544 - 28009*z/15116544) + t^5*(27229*z/1679616 - 25405/419904) + t^4*(1112527/3779136 - 1192403*z/15116544) + t^3*(874841*z/3779136 - 6529901/7558272) + t^2*(639553/419904 - 685471*z/1679616) + t*(5990977*z/15116544 - 22358621/15116544) - 1200767*z/7558272 + 4481323/7558272)*h1 + (7/1944 - 5*z/5184)*h2 + (9457*t^14/944784 - 412391*t^13/944784 + 8519809*t^12/944784 - 110920609*t^11/944784 + 1017741545*t^10/944784 - 6955518049*t^9/944784 + 12144657011*t^8/314928 - 24696114887*t^7/157464 + 156244564385*t^6/314928 - 572043864749*t^5/472392 + 1057062070525*t^4/472392 - 2857818544801*t^3/944784 + 2659960254067*t^2/944784 - 758394001603*t/472392 + 24742837429/59049)*hf
  norm_num at hh

private lemma cell_0_28 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 4*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 48) + t^6*(2416*z - 592) + t^5*(6752 - 24240*z) + t^4*(162080*z - 43824) + t^3*(200368 - 747184*z) + t^2*(2325840*z - 623120) + t*(1203840 - 4493888*z) + 4258144*z - 1140832:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(17/324 - 41*z/2916) + t^6*(157*z/1944 - 1757/5832) + t^5*(79/324 - 16*z/243) + t^4*(503/486 - 199*z/729) + t^3*(725*z/1944 - 8647/5832) + t^2*(7*z/486 + 5/18) + t*(155/486 - 827*z/2916) + 140*z/243 - 2051/1458)*h0 + (t*(41*z/23328 - 17/2592) - 235*z/46656 + 877/46656)*h1 + (287*t^8/1458 - 13627*t^7/2916 + 158389*t^6/2916 - 1187509*t^5/2916 + 6215227*t^4/2916 - 22898461*t^3/2916 + 57190129*t^2/2916 - 21955075*t/729 + 31267385/1458)*hf
  norm_num at hh

private lemma cell_0_29 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 4*z:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 192*z) + t^6*(3840*z - 1184) + t^5*(11056 - 40032*z) + t^4*(257856*z - 68720) + t^3*(279856 - 1047216*z) + t^2*(2609136*z - 699248) + t*(975904 - 3641088*z) + 2176512*z - 583232:ℝ)=0) : (t - 2*z:ℝ)=0 := by
  have hh : (t - 2*z:ℝ)=0 := by linear_combination (t^6*(71/1944 - 19*z/1944) + t^5*(z/162 - 2/81) + t^4*(19*z/162 - 67/162) + t^3*(287/1944 - 175*z/1944) + t^2*(98/81 - 8*z/81) + t*(113/324 - 53*z/81) + 871*z/972 - 863/972)*h0 + (19*z/15552 - 71/15552)*h1 + (95*t^7/486 - 2249*t^6/486 + 2665*t^5/54 - 153505*t^4/486 + 1243535*t^3/972 - 344501*t^2/108 + 1082455*t/243 - 647023/243)*hf
  exact hh

private lemma cell_0_30 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 6) + 2*z + 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 112) + t^6*(2672*z - 96) + t^5*(5824 - 27840*z) + t^4*(181360*z - 45760) + t^3*(205056 - 776656*z) + t^2*(2149824*z - 574352) + t*(945296 - 3527504*z) + 2635904*z - 706944:ℝ)=0) : (t - z - 2:ℝ)=0 := by
  have hh : (t - z - 2:ℝ)=0 := by linear_combination (t^6*(13*z/972 - 97/1944) + t^5*(95/324 - 17*z/216) + t^4*(151*z/648 - 559/648) + t^3*(3155/1944 - 437*z/972) + t^2*(109*z/216 - 131/81) + t*(439/648 - 253*z/648) + 61*z/243 + 131/486)*h0 + (97/15552 - 13*z/7776)*h1 + (-91*t^7/486 + 4163*t^6/972 - 7439*t^5/162 + 293383*t^4/972 - 1260211*t^3/972 + 290977*t^2/81 - 5730947*t/972 + 1070714/243)*hf
  exact hh

private lemma cell_0_31 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 6*z:ℝ)=0) (h1 : (16*t^8 + t^7*(80 - 256*z) + t^6*(5904*z - 1776) + t^5*(19968 - 74640*z) + t^4*(573984*z - 153072) + t^3*(729648 - 2723760*z) + t^2*(7785936*z - 2086992) + t*(3290112 - 12277440*z) + 8193312*z - 2195424:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(511/972 - 137*z/972) + t^6*(55/108 - 43*z/324) + t^5*(527*z/324 - 2053/324) + t^4*(43*z/27 - 88/27) + t^3*(670/27 - 583*z/54) + t^2*(128*z/9 - 35/18) + t*(-173*z/9 - 164/9) + 107*z/6 - 4/3)*h0 + (t*(137*z/7776 - 511/7776) - 13*z/324 + 97/648)*h1 + (959*t^8/243 - 9232*t^7/81 + 14033*t^6/9 - 78665*t^5/6 + 3832139*t^4/54 - 4434121*t^3/18 + 4756898*t^2/9 - 636779*t + 328637)*hf
  norm_num at hh

private lemma cell_0_32 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_0_33 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h2 : (t*(2592 - 12960*z) + 75168*z - 18144:ℝ)=0) : (t - z - 2:ℝ)=0 := by
  have hh : (t - z - 2:ℝ)=0 := by linear_combination (5*z/15552 - 19/15552)*h2 + (25*t/6 - 145/6)*hf
  exact hh

private lemma cell_0_34 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/6)*h0
  norm_num at hh

private lemma cell_0_35 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 176) + t^6*(1184*z + 432) + t^5*(1808 - 9456*z) + t^4*(43456*z - 13072) + t^3*(36336 - 127040*z) + t^2*(238080*z - 63440) + t*(69616 - 261904*z) + 127520*z - 34080:ℝ)=0) (h2 : (16*t^8 + t^7*(64*z - 432) + t^6*(4592 - 896*z) + t^5*(5424*z - 25360) + t^4*(78960 - 17248*z) + t^3*(29984*z - 140336) + t^2*(137488 - 26976*z) + t*(10768*z - 67056) - 1952*z + 12320:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(71*z/1259712 - 265/1259712) + t^12*(8939/1259712 - 2395*z/1259712) + t^11*(11497*z/419904 - 42911/419904) + t^10*(1031831/1259712 - 276451*z/1259712) + t^9*(334991*z/314928 - 625187/157464) + t^8*(204107/17496 - 109355*z/34992) + t^7*(2093449*z/419904 - 7817339/419904) + t^6*(2717773/419904 - 724553*z/419904) + t^5*(4328701/139968 - 1162799*z/139968) + t^4*(18794975*z/1259712 - 69965143/1259712) + t^3*(21056701/629856 - 5672801*z/629856) + t^2*(131153/209952 - 28915*z/209952) + t*(133841*z/78732 - 986177/157464) + 349*z/157464 - 48893/157464)*h0 + (t^7*(265/10077696 - 71*z/10077696) + t^6*(911*z/5038848 - 425/629856) + t^5*(23419/3359232 - 6275*z/3359232) + t^4*(101051*z/10077696 - 377131/10077696) + t^3*(565093/5038848 - 151415*z/5038848) + t^2*(168667*z/3359232 - 629477/3359232) + t*(825719/5038848 - 3457*z/78732) + 41557*z/2519424 - 38771/629856)*h1 + (19/31104 - 5*z/31104)*h2 + (-71*t^14/157464 + 6271*t^13/314928 - 252089*t^12/629856 + 766723*t^11/157464 - 25326961*t^10/629856 + 150806425*t^9/629856 - 223461721*t^8/209952 + 755933365*t^7/209952 - 1959660763*t^6/209952 + 11628506473*t^5/629856 - 4314583867*t^4/157464 + 18603512149*t^3/629856 - 6876124477*t^2/314928 + 781096189*t/78732 - 82814675/39366)*hf
  norm_num at hh

private lemma cell_0_36 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) : ((0:ℝ):ℝ)=0 := by
  rfl

private lemma cell_0_37 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3/8 - z/8)*h0 + (-1/2)*hf
  norm_num at hh

private lemma cell_0_38 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 2)*h0 + (1)*hf
  norm_num at hh

private lemma cell_0_39 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 6) + 2*z + 4:ℝ)=0) : (t - z - 2:ℝ)=0 := by
  have hh : ((t-(1)))*(t - z - 2:ℝ)=0 := by linear_combination (1/2)*h0
  have hv := (mul_eq_zero.mp hh).resolve_left hn0
  exact hv

private lemma cell_0_40 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/6)*h0
  norm_num at hh

private lemma cell_0_41 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 2)*h0 + (1)*hf
  norm_num at hh

private lemma cell_0_42 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-10:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/10)*h0
  norm_num at hh

private lemma cell_0_43 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 10*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 240) + t^6*(1312*z + 1184) + t^5*(-11184*z - 1136) + t^4*(51728*z - 9408) + t^3*(37856 - 140816*z) + t^2*(225456*z - 63248) + t*(53280 - 194656*z) + 68224*z - 18304:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(29/1458 - 4*z/729) + t^6*(43*z/486 - 230/729) + t^5*(299/162 - 130*z/243) + t^4*(1097*z/729 - 3491/729) + t^3*(3436/729 - 53*z/27) + t^2*(515*z/486 + 119/162) + t*(-265*z/729 - 4297/1458) + 52*z/243 + 833/1458)*h0 + (t*(z/1458 - 29/11664) - 37*z/11664 + 23/1944)*h1 + (32*t^8/729 - 268*t^7/243 + 8626*t^6/729 - 51727*t^5/729 + 63343*t^4/243 - 438365*t^3/729 + 618695*t^2/729 - 53806*t/81 + 157768/729)*hf
  norm_num at hh

private lemma cell_0_44 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 176) + t^6*(1184*z + 432) + t^5*(1808 - 9456*z) + t^4*(43456*z - 13072) + t^3*(36336 - 127040*z) + t^2*(238080*z - 63440) + t*(69616 - 261904*z) + 127520*z - 34080:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(5/216 - z/162) + t^5*(4*z/81 - 121/648) + t^4*(101/324 - 25*z/324) + t^3*(65/162 - 31*z/216) + t^2*(115*z/324 - 553/648) + t*(-131*z/648 - 167/648) + 113*z/324 - 35/324)*h0 + (z/1296 - 5/1728)*h1 + (4*t^7/81 - 74*t^6/81 + 197*t^5/27 - 2716*t^4/81 + 7940*t^3/81 - 4960*t^2/27 + 16369*t/81 - 7970/81)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_0_45 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 6) + 2*z + 4:ℝ)=0) (h2 : (16*t^8 + t^7*(16 - 192*z) + t^6*(3648*z - 800) + t^5*(9616 - 36720*z) + t^4*(216528*z - 57344) + t^3*(206944 - 772944*z) + t^2*(1629936*z - 436016) + t*(499264 - 1861824*z) + 883776*z - 237248:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(137/23328 - 37*z/23328) + t^6*(29*z/11664 - 11/1458) + t^5*(29/486 - 89*z/3888) + t^4*(371*z/5832 - 247/5832) + t^3*(6505/23328 - 6743*z/23328) + t^2*(113*z/243 + 11/3888) + t*(1453/2916 - 1757*z/2916) + 29*z/2916 + 541/1458)*h0 + (t*(37*z/186624 - 137/186624) - 85*z/186624 + 317/186624)*h2 + (407*t^8/11664 - 9361*t^7/11664 + 103703*t^6/11664 - 346889*t^5/5832 + 2929511*t^4/11664 - 7857901*t^3/11664 + 12939599*t^2/11664 - 745024*t/729 + 1173707/2916)*hf
  norm_num at hh

private lemma cell_0_46 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 10*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 240) + t^6*(1312*z + 1184) + t^5*(-11184*z - 1136) + t^4*(51728*z - 9408) + t^3*(37856 - 140816*z) + t^2*(225456*z - 63248) + t*(53280 - 194656*z) + 68224*z - 18304:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(29/1458 - 4*z/729) + t^6*(43*z/486 - 230/729) + t^5*(299/162 - 130*z/243) + t^4*(1097*z/729 - 3491/729) + t^3*(3436/729 - 53*z/27) + t^2*(515*z/486 + 119/162) + t*(-265*z/729 - 4297/1458) + 52*z/243 + 833/1458)*h0 + (t*(z/1458 - 29/11664) - 37*z/11664 + 23/1944)*h1 + (32*t^8/729 - 268*t^7/243 + 8626*t^6/729 - 51727*t^5/729 + 63343*t^4/243 - 438365*t^3/729 + 618695*t^2/729 - 53806*t/81 + 157768/729)*hf
  norm_num at hh

private lemma cell_0_47 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 12*t + 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 176) + t^6*(2928*z + 144) + t^5*(6384 - 28752*z) + t^4*(155664*z - 42624) + t^3*(135648 - 495504*z) + t^2*(917568*z - 246240) + t*(242784 - 908064*z) + 368064*z - 98496:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(667/27216 - 179*z/27216) + t^6*(377*z/4536 - 467/1512) + t^5*(1423/1134 - 221*z/648) + t^4*(11*z/28 - 254/189) + t^3*(1349*z/3024 - 6355/3024) + t^2*(1601/504 - 323*z/504) + t*(313/252 - 61*z/126) + z/42 - 1/6)*h0 + (t*(179*z/217728 - 667/217728) - 325*z/72576 + 1213/72576)*h1 + (179*t^8/1701 - 13519*t^7/4536 + 20837*t^6/567 - 194087*t^5/756 + 92773*t^4/84 - 499507*t^3/168 + 174797*t^2/36 - 122331*t/28 + 23075/14)*hf
  norm_num at hh

private lemma cell_0_48 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(128*z - 304) + t^6*(1776 - 336*z) + t^5*(1392*z - 5088) + t^4*(5616 - 1728*z) + t^3*(432 - 432*z) + t^2*(-432*z - 3024) + t*(864*z + 864):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(317/7128 - 85*z/7128) + t^5*(49*z/297 - 61/99) + t^4*(3371/1188 - 226*z/297) + t^3*(973*z/792 - 3637/792) + t^2*(6/11 - 5*z/33) + t*(83/33 - 91*z/132) + 3*z/11 - 13/11)*h0 + (85*z/57024 - 317/57024)*h1 + (-170*t^7/891 + 595*t^6/1188 - 2465*t^5/1188 + 85*t^4/33 + 85*t^3/132 + 85*t^2/132 - 85*t/66)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_0_49 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 4*z:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 240) + t^6*(1184 - 320*z) + t^5*(672*z - 2320) + t^4*(720 - 256*z) + t^3*(2608 - 688*z) + t^2*(240*z - 1904) + t*(96 - 320*z) + 64*z + 128:ℝ)=0) (h2 : (16*t^8 - 112*t^7 + t^6*(144*z + 352) + t^5*(-720*z - 688) + t^4*(3600*z + 352) + t^3*(1136 - 8352*z) + t^2*(21312*z - 5456) + t*(6512 - 22320*z) + 31680*z - 9152:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(1351*z/314928 - 2521/157464) + t^12*(84001/314928 - 5627*z/78732) + t^11*(25753*z/52488 - 192223/104976) + t^10*(137266/19683 - 588485*z/314928) + t^9*(1411381*z/314928 - 5267345/314928) + t^8*(448783/17496 - 120251*z/17496) + t^7*(541535*z/104976 - 252629/13122) + t^6*(324449*z/104976 - 605423/52488) + t^5*(775819/17496 - 415753*z/34992) + t^4*(3756145*z/314928 - 7008925/157464) + t^3*(2298365/157464 - 615463*z/157464) + t^2*(2974787/104976 - 796951*z/104976) + t*(767207*z/157464 - 2855587/157464) + 160829*z/157464 - 596407/157464)*h0 + (t^7*(2521/1259712 - 1351*z/2519424) + t^6*(6755*z/2519424 - 12605/1259712) + t^5*(24221/839808 - 3245*z/419904) + t^4*(35443*z/2519424 - 132275/2519424) + t^3*(150349/2519424 - 20143*z/1259712) + t^2*(4157*z/839808 - 7757/419904) + t*(3449*z/2519424 - 6437/1259712) - 37969*z/2519424 + 141701/2519424)*h1 + (71/15552 - 19*z/15552)*h2 + (6755*t^14/157464 - 39625*t^13/78732 + 58657*t^12/19683 - 1734019*t^11/157464 + 2163041*t^10/78732 - 916535*t^9/19683 + 1247135*t^8/26244 - 211127*t^7/26244 - 1507639*t^6/26244 + 7339177*t^5/78732 - 2411105*t^4/39366 - 2809555*t^3/157464 + 11004647*t^2/157464 - 1953539*t/39366 + 700375/19683)*hf
  norm_num at hh

private lemma cell_0_50 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(128*z - 368) + t^6*(2976 - 784*z) + t^5*(3216*z - 12592) + t^4*(29312 - 7856*z) + t^3*(9856*z - 36624) + t^2*(22384 - 6720*z) + t*(2384*z - 4880) - 160*z - 288:ℝ)=0) : (t + z - 4:ℝ)=0 := by
  have hh : (t + z - 4:ℝ)=0 := by linear_combination (t^6*(5*z/324 - 14/243) + t^5*(236/243 - 253*z/972) + t^4*(1567*z/972 - 5849/972) + t^3*(16717/972 - 1120*z/243) + t^2*(6029*z/972 - 11255/486) + t*(12187/972 - 3275*z/972) + 44*z/243 - 131/162)*h0 + (7/972 - 5*z/2592)*h1 + (20*t^7/81 - 245*t^6/162 + 335*t^5/54 - 2455*t^4/162 + 1540*t^3/81 - 350*t^2/27 + 745*t/162 - 25/81)*hf
  exact hh

private lemma cell_0_51 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 240) + t^6*(1184 - 320*z) + t^5*(672*z - 2320) + t^4*(720 - 256*z) + t^3*(2608 - 688*z) + t^2*(240*z - 1904) + t*(96 - 320*z) + 64*z + 128:ℝ)=0) : (t + z - 4:ℝ)=0 := by
  have hh : (t + z - 4:ℝ)=0 := by linear_combination (t^6*(17/36 - 41*z/324) + t^5*(407*z/324 - 1519/324) + t^4*(4273/324 - 1145*z/324) + t^3*(124*z/81 - 463/81) + t^2*(365*z/81 - 1363/81) + t*(805/81 - 433*z/162) - 35*z/54 + 185/81)*h0 + (41*z/2592 - 17/288)*h1 + (-82*t^7/81 + 410*t^6/81 - 287*t^5/27 + 328*t^4/81 + 1763*t^3/162 - 205*t^2/54 + 410*t/81 - 82/81)*hf
  exact hh

private lemma cell_0_52 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 4*z:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 240) + t^6*(1184 - 320*z) + t^5*(672*z - 2320) + t^4*(720 - 256*z) + t^3*(2608 - 688*z) + t^2*(240*z - 1904) + t*(96 - 320*z) + 64*z + 128:ℝ)=0) : False := by
  have hh : ((t-(2)))*(1:ℝ)=0 := by linear_combination (t^6*(17/72 - 41*z/648) + t^5*(239*z/324 - 223/81) + t^4*(3187/324 - 427*z/162) + t^3*(451*z/216 - 5051/648) + t^2*(1157*z/324 - 4321/324) + t*(1571/162 - 845*z/324) - 185*z/324 + 647/324)*h0 + (41*z/5184 - 17/576)*h1 + (-205*t^7/324 + 115*t^6/27 - 731*t^5/54 + 5425*t^4/324 + 457*t^3/108 - 2311*t^2/108 + 1915*t/162 + 16/9)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_0_53 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 4*z:ℝ)=0) (h1 : (16*t^8 - 176*t^7 + t^6*(592 - 48*z) + t^5*(432*z - 320) + t^4*(-864*z - 1520) + t^3*(1840 - 1200*z) + t^2*(3024*z + 304) + t*(1728*z - 896) - 480*z + 160:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(8209/134136 - 2195*z/134136) + t^6*(23417*z/134136 - 87565/134136) + t^5*(44479/22356 - 5953*z/11178) + t^4*(1921*z/134136 - 5513/134136) + t^3*(246599*z/134136 - 923755/134136) + t^2*(805/243 - 875*z/972) + t*(202771/33534 - 107863*z/67068) - 2918*z/16767 + 12232/16767)*h0 + (t*(2195*z/1073088 - 8209/1073088) - 2609*z/1073088 + 9865/1073088)*h1 + (-2195*t^8/33534 + 57809*t^7/67068 - 128399*t^6/33534 + 335687*t^5/67068 + 513095*t^4/67068 - 336307*t^3/16767 + 66089*t^2/67068 + 366193*t/33534 - 15791/33534)*hf
  norm_num at hh

private lemma cell_0_54 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 6) + 2*z + 4:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 304) + t^6*(2256 - 640*z) + t^5*(2544*z - 8720) + t^4*(19280 - 5216*z) + t^3*(5984*z - 24432) + t^2*(16048 - 3840*z) + t*(1264*z - 3856) - 160*z - 288:ℝ)=0) (h2 : (16*t^8 - 176*t^7 + t^6*(592 - 48*z) + t^5*(432*z - 320) + t^4*(-864*z - 1520) + t^3*(1840 - 1200*z) + t^2*(3024*z + 304) + t*(1728*z - 896) - 480*z + 160:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(653*z/2309472 - 2437/2309472) + t^12*(60097/2309472 - 16103*z/2309472) + t^11*(6881*z/96228 - 102721/384912) + t^10*(1680347/1154736 - 450247*z/1154736) + t^9*(675437*z/577368 - 1260383/288684) + t^8*(382133/64152 - 204785*z/128304) + t^7*(2044855/769824 - 547913*z/769824) + t^6*(4250927*z/769824 - 15865249/769824) + t^5*(1460527/64152 - 195643*z/32076) + t^4*(707351/1154736 - 93605*z/577368) + t^3*(3449749*z/1154736 - 12915989/1154736) + t^2*(324727*z/384912 - 1227407/384912) + t*(1715491/288684 - 908563*z/577368) - 39901*z/288684 + 44579/72171)*h0 + (t^7*(2437/18475776 - 653*z/18475776) + t^6*(3265*z/9237888 - 12185/9237888) + t^5*(665/192456 - 2851*z/3079296) + t^4*(32731/18475776 - 8771*z/18475776) + t^3*(31357*z/9237888 - 117023/9237888) + t^2*(31*z/769824 - 461/3079296) + t*(83477/9237888 - 22369*z/9237888) - 13535*z/9237888 + 50503/9237888)*h1 + (1/648 - z/2592)*h2 + (3265*t^14/1154736 - 17249*t^13/288684 + 307349*t^12/577368 - 1482971*t^11/577368 + 4046701*t^10/577368 - 10663201*t^9/1154736 - 427223*t^8/192456 + 5282377*t^7/192456 - 14910259*t^6/384912 + 18918827*t^5/1154736 + 4966321*t^4/577368 - 691289*t^3/144342 - 40855*t^2/6561 + 2888009*t/577368 - 41333/288684)*hf
  norm_num at hh

private lemma cell_0_55 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 6*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 112) + 864*t^6*z + t^5*(1680 - 4800*z) + t^4*(14400*z - 5040) + t^3*(6768 - 25200*z) + t^2*(24624*z - 5616) + t*(2592 - 10368*z):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(73/486 - 10*z/243) + t^6*(11*z/36 - 347/324) + t^5*(419/324 - 163*z/324) + t^4*(443/108 - 43*z/108) + t^3*(-z/18 - 58/9) + t^2*(65*z/18 - 77/18) + t*(107/18 - 55*z/18) - z/6 + 2/3)*h0 + (t*(5*z/972 - 73/3888) - 23*z/2592 + 77/2592)*h1 + (40*t^8/243 - 287*t^7/81 + 4619*t^6/162 - 6223*t^5/54 + 14017*t^4/54 - 671*t^3/2 + 4283*t^2/18 - 223*t/3 + 1)*hf
  norm_num at hh

private lemma cell_0_56 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(128*z - 368) + t^6*(2976 - 784*z) + t^5*(3216*z - 12592) + t^4*(29312 - 7856*z) + t^3*(9856*z - 36624) + t^2*(22384 - 6720*z) + t*(2384*z - 4880) - 160*z - 288:ℝ)=0) : (t + z - 4:ℝ)=0 := by
  have hh : (t + z - 4:ℝ)=0 := by linear_combination (t^6*(5*z/324 - 14/243) + t^5*(236/243 - 253*z/972) + t^4*(1567*z/972 - 5849/972) + t^3*(16717/972 - 1120*z/243) + t^2*(6029*z/972 - 11255/486) + t*(12187/972 - 3275*z/972) + 44*z/243 - 131/162)*h0 + (7/972 - 5*z/2592)*h1 + (20*t^7/81 - 245*t^6/162 + 335*t^5/54 - 2455*t^4/162 + 1540*t^3/81 - 350*t^2/27 + 745*t/162 - 25/81)*hf
  exact hh

private lemma cell_0_57 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 6) + 2*z + 4:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 304) + t^6*(2256 - 640*z) + t^5*(2544*z - 8720) + t^4*(19280 - 5216*z) + t^3*(5984*z - 24432) + t^2*(16048 - 3840*z) + t*(1264*z - 3856) - 160*z - 288:ℝ)=0) (h2 : (16*t^8 - 176*t^7 + t^6*(1168 - 48*z) + t^5*(432*z - 5072) + t^4*(16192 - 2160*z) + t^3*(6576*z - 36896) + t^2*(62080 - 13824*z) + t*(17280*z - 66560) - 13440*z + 44800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(z/72171 - 239/4618944) + t^12*(2947/2309472 - 1579*z/4618944) + t^11*(6167*z/1539648 - 23017/1539648) + t^10*(518129/4618944 - 8677*z/288684) + t^9*(186877*z/1154736 - 348715/577368) + t^8*(1263271/513216 - 169249*z/256608) + t^7*(3213797*z/1539648 - 11994109/1539648) + t^6*(29719801/1539648 - 3981355*z/769824) + t^5*(2556745*z/256608 - 19089841/513216) + t^4*(249746195/4618944 - 66866089*z/4618944) + t^3*(34137809*z/2309472 - 127638943/2309472) + t^2*(13151575/384912 - 3509339*z/384912) + t*(1255145*z/577368 - 1184017/144342) + 93749*z/288684 - 90061/72171)*h0 + (t^7*(239/36951552 - z/577368) + t^6*(5*z/288684 - 1195/18475776) + t^5*(4955/12317184 - 1327*z/12317184) + t^4*(1981*z/4618944 - 29585/18475776) + t^3*(87029/18475776 - 46625*z/36951552) + t^2*(7831*z/3079296 - 29231/3079296) + t*(130313/9237888 - 34915*z/9237888) + 27055*z/9237888 - 100967/9237888)*h1 + (1/10368 - z/10368)*h2 + (10*t^14/72171 - 6763*t^13/2309472 + 17945*t^12/577368 - 502589*t^11/2309472 + 2572315*t^10/2309472 - 2526809*t^9/577368 + 5205461*t^8/384912 - 25541297*t^7/769824 + 49543543*t^6/769824 - 223154741*t^5/2309472 + 124284131*t^4/1154736 - 5962675*t^3/72171 + 988859*t^2/26244 - 3659509*t/577368 - 426443/288684)*hf
  norm_num at hh

private lemma cell_0_58 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 10*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(128*z - 432) + t^6*(4304 - 1232*z) + t^5*(5808*z - 22160) + t^4*(64128 - 16624*z) + t^3*(28144*z - 104608) + t^2*(92128 - 26112*z) + t*(11744*z - 39072) - 1856*z + 5696:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(59/34263 - 101*z/68526) + t^6*(274*z/34263 - 2839/68526) + t^5*(11039/22842 - 1274*z/11421) + t^4*(27140*z/34263 - 96892/34263) + t^3*(598721/68526 - 168985*z/68526) + t^2*(43196*z/11421 - 163483/11421) + t*(802813/68526 - 96439*z/34263) + 27802*z/34263 - 268669/68526)*h0 + (t*(101*z/548208 - 59/274104) - 307*z/274104 + 1051/548208)*h1 + (-808*t^8/34263 + 12689*t^7/34263 - 83941*t^6/34263 + 327821*t^5/34263 - 815605*t^4/34263 + 1244858*t^3/34263 - 1076182*t^2/34263 + 462392*t/34263 - 71224/34263)*hf
  norm_num at hh

private lemma cell_0_59 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 12*t + 6:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 368) + t^6*(3264 - 768*z) + t^5*(3792*z - 14640) + t^4*(35712 - 9648*z) + t^3*(13104*z - 46944) + t^2*(30672 - 9072*z) + t*(2592*z - 7776):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(17*z/3888 - 23/1944) + t^6*(161/648 - 49*z/648) + t^5*(47*z/81 - 1343/648) + t^4*(3751/432 - 1015*z/432) + t^3*(2195*z/432 - 1031/54) + t^2*(997/48 - 87*z/16) + t*(53*z/24 - 71/8) + 1/6)*h0 + (t*(23/15552 - 17*z/31104) + 31*z/10368 - 7/864)*h1 + (17*t^8/486 - 11*t^7/18 + 2831*t^6/648 - 299*t^5/18 + 3889*t^4/108 - 1589*t^3/36 + 685*t^2/24 - 31*t/4)*hf
  norm_num at hh

private lemma cell_0_60 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 240) + t^6*(1184 - 320*z) + t^5*(672*z - 2320) + t^4*(720 - 256*z) + t^3*(2608 - 688*z) + t^2*(240*z - 1904) + t*(96 - 320*z) + 64*z + 128:ℝ)=0) (h2 : (16*t^8 + t^7*(16 - 64*z) + t^6*(416*z - 288) + t^5*(368 - 1104*z) + t^4*(1552*z + 128) + t^3*(-848*z - 96) + t^2*(-1104*z - 80) + t*(2048*z - 320) - 832*z + 192:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(5*z/629856 - 19/629856) + t^12*(119/629856 - 31*z/629856) + t^11*(37/209952 - 11*z/209952) + t^10*(101*z/157464 - 373/157464) + t^9*(1163/629856 - 301*z/629856) + t^8*(643/69984 - 179*z/69984) + t^7*(619*z/209952 - 2147/209952) + t^6*(17*z/6561 - 469/104976) + t^5*(17981/34992 - 5389*z/34992) + t^4*(262405*z/314928 - 452197/157464) + t^3*(807259/314928 - 126949*z/157464) + t^2*(391739/104976 - 96823*z/104976) + t*(66877*z/78732 - 56096/19683) - 1565*z/78732 - 44105/78732)*h0 + (t^7*(19/5038848 - 5*z/5038848) + t^6*(35/2519424 - 5*z/1259712) + t^5*(1/104976 - z/839808) + t^4*(139/2519424 - 47*z/2519424) + t^3*(1655/5038848 - 415*z/5038848) + t^2*(971/839808 - 131*z/419904) + t*(5323/1259712 - 1433*z/1259712) - 2665*z/629856 + 4981/314928)*h1 + (1/15552 - 7*z/31104)*h2 + (5*t^14/78732 - 5*t^13/78732 - 83*t^12/157464 + 127*t^11/39366 - 503*t^10/314928 + 1055*t^9/314928 + 613*t^8/26244 + 1763*t^7/26244 - 65933*t^6/104976 + 662255*t^5/314928 - 230971*t^4/157464 - 460331*t^3/157464 + 66601*t^2/157464 - 16145*t/19683 + 3289/39366)*hf
  norm_num at hh

private lemma cell_0_61 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 6*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 112) + 864*t^6*z + t^5*(1680 - 4800*z) + t^4*(14400*z - 5040) + t^3*(6768 - 25200*z) + t^2*(24624*z - 5616) + t*(2592 - 10368*z):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(73/486 - 10*z/243) + t^6*(11*z/36 - 347/324) + t^5*(419/324 - 163*z/324) + t^4*(443/108 - 43*z/108) + t^3*(-z/18 - 58/9) + t^2*(65*z/18 - 77/18) + t*(107/18 - 55*z/18) - z/6 + 2/3)*h0 + (t*(5*z/972 - 73/3888) - 23*z/2592 + 77/2592)*h1 + (40*t^8/243 - 287*t^7/81 + 4619*t^6/162 - 6223*t^5/54 + 14017*t^4/54 - 671*t^3/2 + 4283*t^2/18 - 223*t/3 + 1)*hf
  norm_num at hh

private lemma cell_0_62 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 12*t + 6:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 368) + t^6*(3264 - 768*z) + t^5*(3792*z - 14640) + t^4*(35712 - 9648*z) + t^3*(13104*z - 46944) + t^2*(30672 - 9072*z) + t*(2592*z - 7776):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(17*z/3888 - 23/1944) + t^6*(161/648 - 49*z/648) + t^5*(47*z/81 - 1343/648) + t^4*(3751/432 - 1015*z/432) + t^3*(2195*z/432 - 1031/54) + t^2*(997/48 - 87*z/16) + t*(53*z/24 - 71/8) + 1/6)*h0 + (t*(23/15552 - 17*z/31104) + 31*z/10368 - 7/864)*h1 + (17*t^8/486 - 11*t^7/18 + 2831*t^6/648 - 299*t^5/18 + 3889*t^4/108 - 1589*t^3/36 + 685*t^2/24 - 31*t/4)*hf
  norm_num at hh

private lemma cell_0_63 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 6*t:ℝ)=0) (h1 : (t*(288*z + 96) - 832*z + 192:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7/6 - z/3)*h0 + (85/2112 - 23*z/2112)*h1 + (69*t/22 - 299/33)*hf
  norm_num at hh

private lemma pair_0_3_9 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 3:ℝ)=0) (h2 : (16*t^8 + t^7*(16 - 128*z) + t^6*(1584*z - 576) + t^5*(2640 - 9168*z) + t^4*(29232*z - 7488) + t^3*(13104 - 50400*z) + t^2*(43200*z - 11664) + t*(3888 - 14256*z):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-t^7/972 + t^6*(2*z/243 - 1/243) + t^5*(2/81 - 25*z/324) + t^4*(29*z/81 - 31/324) + t^3*(7/36 - 29*z/36) + t^2*(89*z/108 - 7/27) + t*(-11*z/36 - 1/36) - 1/3)*h0 + (1/15552)*h2
  norm_num at hh

private lemma pair_0_3_23 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 3:ℝ)=0) (h1 : (t - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z/11 - 5/11)*h0 + (5/11 - 2*z/11)*h1 + (-4/11)*hf
  norm_num at hh

private lemma pair_0_3_30 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 3:ℝ)=0) (h1 : (t - z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 3/2)*h0 + (3/2 - z/2)*h1 + (-1/2)*hf
  norm_num at hh

private lemma pair_0_3_33 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 3:ℝ)=0) (h1 : (t - z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 3/2)*h0 + (3/2 - z/2)*h1 + (-1/2)*hf
  norm_num at hh

private lemma pair_0_3_36 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 3:ℝ)=0) (h2 : (16*t^8 + t^7*(64*z - 176) + t^6*(624 - 192*z) + t^5*(192*z - 960) + 432*t^4 + t^3*(864 - 432*z) - 1296*t^2 + t*(432*z + 432):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(13/486 - 7*z/972) + t^6*(4*z/81 - 5/27) + t^5*(65/162 - 35*z/324) + t^4*(z/12 - 17/54) + t^3*(z/18 - 2/9) + t^2*(7/12 - z/6) + t*(z/12 - 5/12) - 1/3)*h0 + (7*z/15552 - 13/7776)*h2 + (-7*t^7/243 + 7*t^6/81 - 7*t^5/81 + 7*t^3/36 - 7*t/36)*hf
  norm_num at hh

private lemma pair_0_9_23 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 3:ℝ)=0) (h1 : (t - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z/11 - 5/11)*h0 + (5/11 - 2*z/11)*h1 + (-4/11)*hf
  norm_num at hh

private lemma pair_0_9_30 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 3:ℝ)=0) (h1 : (t - z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 3/2)*h0 + (3/2 - z/2)*h1 + (-1/2)*hf
  norm_num at hh

private lemma pair_0_9_33 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 3:ℝ)=0) (h1 : (t - z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 3/2)*h0 + (3/2 - z/2)*h1 + (-1/2)*hf
  norm_num at hh

private lemma pair_0_9_36 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 3:ℝ)=0) (h2 : (t*(2592 - 12960*z) + 75168*z - 18144:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 3/2)*h0 + (7*z/15552 - 13/7776)*h2 + (35*t/6 - 203/6)*hf
  norm_num at hh

private lemma pair_0_20_39 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z:ℝ)=0) (h1 : (t - z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2/3 - z/3)*h0 + (z/3 - 2/3)*h1 + (-1/3)*hf
  norm_num at hh

private lemma pair_0_20_50 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z:ℝ)=0) (h1 : (t + z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (8/23 - 3*z/23)*h0 + (3*z/23 - 8/23)*h1 + (-9/23)*hf
  norm_num at hh

private lemma pair_0_23_30 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z:ℝ)=0) (h1 : (t - z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2/3 - z/3)*h0 + (z/3 - 2/3)*h1 + (-1/3)*hf
  norm_num at hh

private lemma pair_0_23_33 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z:ℝ)=0) (h1 : (t - z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2/3 - z/3)*h0 + (z/3 - 2/3)*h1 + (-1/3)*hf
  norm_num at hh

private lemma pair_0_23_36 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z - 48) + t^6*(544*z - 112) + t^5*(592 - 1680*z) + t^4*(1760*z - 720) + t^3*(1120*z - 16) + t^2*(688 - 3072*z) + t*(1328*z - 528) + 64*z + 128:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(377*z/3564 - 469/1188) + t^6*(4975/3564 - 1333*z/3564) + t^5*(z/44 - 101/1188) + t^4*(1693*z/1782 - 39/11) + t^3*(15073/3564 - 4039*z/3564) + t^2*(503*z/396 - 5635/1188) + t*(943/1188 - 775*z/3564) - 1150*z/891 + 8345/1782)*h0 + (469/19008 - 377*z/57024)*h2 + (-377*t^7/1782 + 94*t^6/33 - 13141*t^5/1188 + 24121*t^4/1782 + 1526*t^3/297 - 10555*t^2/594 + 29741*t/3564 - 641/297)*hf
  norm_num at hh

private lemma pair_0_29_51 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z:ℝ)=0) (h1 : (t + z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (8/23 - 3*z/23)*h0 + (3*z/23 - 8/23)*h1 + (-9/23)*hf
  norm_num at hh

private lemma pair_0_30_33 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z - 2:ℝ)=0) (h2 : (16*t^8 - 176*t^7 + t^6*(1168 - 48*z) + t^5*(432*z - 5072) + t^4*(16192 - 2160*z) + t^3*(6576*z - 36896) + t^2*(62080 - 13824*z) + t*(17280*z - 66560) - 13440*z + 44800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(61*z/277992 - 229/277992) + t^6*(250/34749 - 89*z/46332) + t^5*(89*z/7722 - 500/11583) + t^4*(21871/138996 - 2927*z/69498) + t^3*(3689*z/30888 - 124321/277992) + t^2*(9215/11583 - 92*z/429) + t*(10898*z/34749 - 41735/34749) - 2014*z/11583 + 16477/34749)*h0 + (229/4447872 - 61*z/4447872)*h2 + (61*t^7/277992 - 239*t^6/92664 + 49*t^5/2808 - 1813*t^4/25272 + 2428*t^3/11583 - 40*t^2/99 + 19133*t/34749 - 461/1287)*hf
  norm_num at hh

private lemma pair_0_30_36 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z - 2:ℝ)=0) (h2 : (16*t^8 + t^7*(16 - 192*z) + t^6*(3648*z - 800) + t^5*(9616 - 36720*z) + t^4*(216528*z - 57344) + t^3*(206944 - 772944*z) + t^2*(1629936*z - 436016) + t*(499264 - 1861824*z) + 883776*z - 237248:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-t^7/1944 + t^6*(11*z/1944 - 1/648) + t^5*(11/648 - 55*z/648) + t^4*(223*z/324 - 185/972) + t^3*(251/324 - 5875*z/1944) + t^2*(4855*z/648 - 1349/648) + t*(574/243 - 772*z/81) + 2447*z/486 - 97/54)*h0 + (1/31104)*h2 + (11*t^6/1944 - 55*t^5/648 + 223*t^4/324 - 5875*t^3/1944 + 4855*t^2/648 - 772*t/81 + 2447/486)*hf
  norm_num at hh

private lemma pair_0_33_36 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z - 2:ℝ)=0) (h2 : (t*(12960 - 49248*z) + 368064*z - 98496:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/3 - 2/3)*h0 + (11*z/15552 - 41/15552)*h2 + (209*t/6 - 260)*hf
  norm_num at hh

private lemma pair_0_39_50 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z)≠0) (_hn2 : t-(2)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z - 2:ℝ)=0) (h1 : (t + z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3/4 - z/4)*h0 + (z/4 - 3/4)*h1 + (-1/2)*hf
  norm_num at hh

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_0 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 0) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_0 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_1 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 1) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_1 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_2 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 2) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_2 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_3 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 3) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : (t - 3:ℝ)=0 := by
  apply cell_0_3 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_4 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 4) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_4 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_5 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 5) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_5 z t hf hn0 hn1 hn2 hn3
  · have hr : (2592*t*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_6 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 6) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_6 z t hf hn0 hn1 hn2 hn3
  · have hr : (2592*t*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_7 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 7) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_7 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 448*t^6*z^2 + 240*t^6*z - 144*t^6 - 896*t^5*z^3 - 432*t^5*z^2 + 1008*t^5*z + 432*t^5 + 1120*t^4*z^4 + 240*t^4*z^3 - 2736*t^4*z^2 - 1296*t^4*z + 288*t^4 - 896*t^3*z^5 + 240*t^3*z^4 + 3744*t^3*z^3 + 864*t^3*z^2 - 2448*t^3*z - 864*t^3 + 448*t^2*z^6 - 432*t^2*z^5 - 2736*t^2*z^4 + 864*t^2*z^3 + 4320*t^2*z^2 + 864*t^2*z - 128*t*z^7 + 240*t*z^6 + 1008*t*z^5 - 1296*t*z^4 - 2448*t*z^3 + 864*t*z^2 + 2592*t*z + 16*z^8 - 48*z^7 - 144*z^6 + 432*z^5 + 288*z^4 - 864*z^3:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 4016*t^5 - 1120*t^4*z^2 - 4720*t^4*z - 15024*t^4 + 896*t^3*z^3 + 3344*t^3*z^2 + 8736*t^3*z + 30736*t^3 - 448*t^2*z^4 - 1360*t^2*z^3 - 2256*t^2*z^2 - 8528*t^2*z - 36176*t^2 + 128*t*z^5 + 272*t*z^4 - 48*t*z^3 + 832*t*z^2 + 5824*t*z + 21600*t - 16*z^6 - 16*z^5 + 96*z^4 - 32*z^3 - 512*z^2 - 1152*z - 4096)*hf
  · have hr : (16*t^8 - 304*t^7 - 48*t^6*z + 2224*t^6 + 720*t^5*z - 7888*t^5 - 3600*t^4*z + 13792*t^4 + 6384*t^3*z - 9952*t^3 - 1440*t^2*z - 128*t^2 - 1440*t*z + 2432*t + 384*z - 512:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_8 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 8) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_8 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_9 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 9) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : (t - 3:ℝ)=0 := by
  apply cell_0_9 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^6 + 16848*t*z^5 - 84240*t*z^4 + 203472*t*z^3 - 246240*t*z^2 + 142560*t*z - 31104*t + 1296*z^8 - 22032*z^7 + 156816*z^6 - 607824*z^5 + 1397088*z^4 - 1941408*z^3 + 1586304*z^2 - 694656*z + 124416:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^4 - 11664*t*z^3 + 36288*t*z^2 - 46656*t*z + 23328*t - 1296*z^6 + 16848*z^5 - 88128*z^4 + 238464*z^3 - 355104*z^2 + 282528*z - 101088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_10 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 10) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_10 z t hf hn0 hn1 hn2 hn3
  · have hr : (-6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_11 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 11) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_11 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z - 176*t^7 + 160*t^6*z^2 + 352*t^6*z + 784*t^6 - 256*t^5*z^3 - 528*t^5*z^2 - 192*t^5*z - 1904*t^5 + 304*t^4*z^4 + 176*t^4*z^3 + 384*t^4*z^2 - 1936*t^4*z + 2656*t^4 - 256*t^3*z^5 + 176*t^3*z^4 + 992*t^3*z^3 - 1904*t^3*z^2 + 4720*t^3*z - 1568*t^3 + 160*t^2*z^6 - 528*t^2*z^5 + 384*t^2*z^4 - 1904*t^2*z^3 + 5424*t^2*z^2 - 4128*t^2*z - 704*t^2 - 64*t*z^7 + 352*t*z^6 - 192*t*z^5 - 1936*t*z^4 + 4720*t*z^3 - 4128*t*z^2 - 160*t*z + 1408*t + 16*z^8 - 176*z^7 + 784*z^6 - 1904*z^5 + 2656*z^4 - 1568*z^3 - 704*z^2 + 1408*z - 512:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 1552*t^5 - 304*t^4*z^2 - 1392*t^4*z - 5648*t^4 + 256*t^3*z^3 + 848*t^3*z^2 + 2144*t^3*z + 9632*t^3 - 160*t^2*z^4 - 112*t^2*z^3 - 672*t^2*z^2 - 672*t^2*z - 7440*t^2 + 64*t*z^5 - 96*t*z^4 - 256*t*z^3 + 1008*t*z^2 - 432*t*z + 1392*t - 16*z^6 + 112*z^5 - 320*z^4 + 512*z^3 - 288*z^2 - 96*z + 608)*hf
  · have hr : (16*t^8 + 64*t^7*z - 432*t^7 + 160*t^6*z^2 - 1728*t^6*z + 4944*t^6 + 256*t^5*z^3 - 3888*t^5*z^2 + 19296*t^5*z - 31536*t^5 + 304*t^4*z^4 - 5616*t^4*z^3 + 38592*t^4*z^2 - 115344*t^4*z + 122976*t^4 + 256*t^3*z^5 - 5616*t^3*z^4 + 48000*t^3*z^3 - 199152*t^3*z^2 + 398448*t^3*z - 299808*t^3 + 160*t^2*z^6 - 3888*t^2*z^5 + 38592*t^2*z^4 - 199152*t^2*z^3 + 557712*t^2*z^2 - 794016*t^2*z + 444096*t^2 + 64*t*z^7 - 1728*t*z^6 + 19296*t*z^5 - 115344*t*z^4 + 398448*t*z^3 - 794016*t*z^2 + 840672*t*z - 362880*t + 16*z^8 - 432*z^7 + 4944*z^6 - 31536*z^5 + 122976*z^4 - 299808*z^3 + 444096*z^2 - 362880*z + 124416:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 2864*t^5 - 304*t^4*z^2 + 4400*t^4*z - 20688*t^4 - 256*t^3*z^3 + 4592*t^3*z^2 - 29376*t^3*z + 77056*t^3 - 160*t^2*z^4 + 3248*t^2*z^3 - 25440*t^2*z^2 + 94144*t^2*z - 155696*t^2 - 64*t*z^5 + 1472*t*z^4 - 13344*t*z^3 + 60496*t*z^2 - 143120*t*z + 161040*t - 16*z^6 + 368*z^5 - 3456*z^4 + 17344*z^3 - 50144*z^2 + 81888*z - 66400)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_12 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 12) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_12 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z + 16*t^7 + 448*t^6*z^2 - 208*t^6*z - 128*t^6 - 896*t^5*z^3 + 912*t^5*z^2 + 624*t^5*z - 32*t^5 + 1120*t^4*z^4 - 2000*t^4*z^3 - 1056*t^4*z^2 + 736*t^4*z + 256*t^4 - 896*t^3*z^5 + 2480*t^3*z^4 + 544*t^3*z^3 - 2336*t^3*z^2 - 832*t^3*z - 32*t^3 + 448*t^2*z^6 - 1776*t^2*z^5 + 384*t^2*z^4 + 2912*t^2*z^3 + 96*t^2*z^2 - 624*t^2*z + 16*t^2 - 128*t*z^7 + 688*t*z^6 - 528*t*z^5 - 1600*t*z^4 + 1280*t*z^3 + 336*t*z^2 + 1120*t*z - 272*t + 16*z^8 - 112*z^7 + 160*z^6 + 320*z^5 - 800*z^4 + 320*z^3 + 304*z^2 - 688*z + 160:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 2672*t^5 - 1120*t^4*z^2 - 2480*t^4*z - 7744*t^4 + 896*t^3*z^3 + 1104*t^3*z^2 + 2976*t^3*z + 13136*t^3 - 448*t^2*z^4 - 16*t^2*z^3 - 2896*t^2*z - 11680*t^2 + 128*t*z^5 - 176*t*z^4 - 304*t*z^3 + 560*t*z^2 + 1264*t*z + 4160*t - 16*z^6 + 48*z^5 + 48*z^4 - 176*z^3 + 48*z^2 + 48*z - 160)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_13 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 13) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_13 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 448*t^6*z^2 + 240*t^6*z - 144*t^6 - 896*t^5*z^3 - 432*t^5*z^2 + 1008*t^5*z + 432*t^5 + 1120*t^4*z^4 + 240*t^4*z^3 - 2736*t^4*z^2 - 1296*t^4*z + 288*t^4 - 896*t^3*z^5 + 240*t^3*z^4 + 3744*t^3*z^3 + 864*t^3*z^2 - 2448*t^3*z - 864*t^3 + 448*t^2*z^6 - 432*t^2*z^5 - 2736*t^2*z^4 + 864*t^2*z^3 + 4320*t^2*z^2 + 864*t^2*z - 128*t*z^7 + 240*t*z^6 + 1008*t*z^5 - 1296*t*z^4 - 2448*t*z^3 + 864*t*z^2 + 2592*t*z + 16*z^8 - 48*z^7 - 144*z^6 + 432*z^5 + 288*z^4 - 864*z^3:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 4016*t^5 - 1120*t^4*z^2 - 4720*t^4*z - 15024*t^4 + 896*t^3*z^3 + 3344*t^3*z^2 + 8736*t^3*z + 30736*t^3 - 448*t^2*z^4 - 1360*t^2*z^3 - 2256*t^2*z^2 - 8528*t^2*z - 36176*t^2 + 128*t*z^5 + 272*t*z^4 - 48*t*z^3 + 832*t*z^2 + 5824*t*z + 21600*t - 16*z^6 - 16*z^5 + 96*z^4 - 32*z^3 - 512*z^2 - 1152*z - 4096)*hf
  · have hr : (16*t^8 - 192*t^7*z + 80*t^7 + 1056*t^6*z^2 - 1152*t^6*z + 208*t^6 - 3456*t^5*z^3 + 6768*t^5*z^2 - 3168*t^5*z + 464*t^5 + 7344*t^4*z^4 - 22032*t^4*z^3 + 19296*t^4*z^2 - 6288*t^4*z + 736*t^4 - 10368*t^3*z^5 + 43632*t^3*z^4 - 60480*t^3*z^3 + 34512*t^3*z^2 - 9360*t^3*z + 992*t^3 + 9504*t^2*z^6 - 53136*t^2*z^5 + 106272*t^2*z^4 - 95472*t^2*z^3 + 42192*t^2*z^2 - 8352*t^2*z + 448*t^2 - 5184*t*z^7 + 37152*t*z^6 - 101088*t*z^5 + 131760*t*z^4 - 86832*t*z^3 + 27936*t*z^2 - 2208*t*z - 640*t + 1296*z^8 - 11664*z^7 + 41904*z^6 - 76464*z^5 + 73440*z^4 - 31968*z^3 + 192*z^2 + 3456*z - 512:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6 + 3456*t^5*z + 7056*t^5 - 7344*t^4*z^2 - 7344*t^4*z - 41328*t^4 + 10368*t^3*z^3 - 2160*t^3*z^2 + 41472*t^3*z + 133536*t^3 - 9504*t^2*z^4 + 15120*t^2*z^3 - 36288*t^2*z^2 - 64800*t^2*z - 265104*t^2 + 5184*t*z^5 - 16416*t*z^4 + 30240*t*z^3 + 5616*t*z^2 + 79056*t*z + 282672*t - 1296*z^6 + 6480*z^5 - 14688*z^4 + 11232*z^3 - 13824*z^2 - 34560*z - 124608)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_14 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 14) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_14 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z - 176*t^7 + 160*t^6*z^2 + 352*t^6*z + 784*t^6 - 256*t^5*z^3 - 528*t^5*z^2 - 192*t^5*z - 1904*t^5 + 304*t^4*z^4 + 176*t^4*z^3 + 384*t^4*z^2 - 1936*t^4*z + 2656*t^4 - 256*t^3*z^5 + 176*t^3*z^4 + 992*t^3*z^3 - 1904*t^3*z^2 + 4720*t^3*z - 1568*t^3 + 160*t^2*z^6 - 528*t^2*z^5 + 384*t^2*z^4 - 1904*t^2*z^3 + 5424*t^2*z^2 - 4128*t^2*z - 704*t^2 - 64*t*z^7 + 352*t*z^6 - 192*t*z^5 - 1936*t*z^4 + 4720*t*z^3 - 4128*t*z^2 - 160*t*z + 1408*t + 16*z^8 - 176*z^7 + 784*z^6 - 1904*z^5 + 2656*z^4 - 1568*z^3 - 704*z^2 + 1408*z - 512:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 1552*t^5 - 304*t^4*z^2 - 1392*t^4*z - 5648*t^4 + 256*t^3*z^3 + 848*t^3*z^2 + 2144*t^3*z + 9632*t^3 - 160*t^2*z^4 - 112*t^2*z^3 - 672*t^2*z^2 - 672*t^2*z - 7440*t^2 + 64*t*z^5 - 96*t*z^4 - 256*t*z^3 + 1008*t*z^2 - 432*t*z + 1392*t - 16*z^6 + 112*z^5 - 320*z^4 + 512*z^3 - 288*z^2 - 96*z + 608)*hf
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 448*t^6*z^2 + 240*t^6*z - 144*t^6 - 896*t^5*z^3 - 432*t^5*z^2 + 1008*t^5*z + 432*t^5 + 1120*t^4*z^4 + 240*t^4*z^3 - 2736*t^4*z^2 - 1296*t^4*z + 288*t^4 - 896*t^3*z^5 + 240*t^3*z^4 + 3744*t^3*z^3 + 864*t^3*z^2 - 2448*t^3*z - 864*t^3 + 448*t^2*z^6 - 432*t^2*z^5 - 2736*t^2*z^4 + 864*t^2*z^3 + 4320*t^2*z^2 + 864*t^2*z - 128*t*z^7 + 240*t*z^6 + 1008*t*z^5 - 1296*t*z^4 - 2448*t*z^3 + 864*t*z^2 + 2592*t*z + 16*z^8 - 48*z^7 - 144*z^6 + 432*z^5 + 288*z^4 - 864*z^3:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 4016*t^5 - 1120*t^4*z^2 - 4720*t^4*z - 15024*t^4 + 896*t^3*z^3 + 3344*t^3*z^2 + 8736*t^3*z + 30736*t^3 - 448*t^2*z^4 - 1360*t^2*z^3 - 2256*t^2*z^2 - 8528*t^2*z - 36176*t^2 + 128*t*z^5 + 272*t*z^4 - 48*t*z^3 + 832*t*z^2 + 5824*t*z + 21600*t - 16*z^6 - 16*z^5 + 96*z^4 - 32*z^3 - 512*z^2 - 1152*z - 4096)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_15 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 15) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_15 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 448*t^6*z^2 + 240*t^6*z - 144*t^6 - 896*t^5*z^3 - 432*t^5*z^2 + 1008*t^5*z + 432*t^5 + 1120*t^4*z^4 + 240*t^4*z^3 - 2736*t^4*z^2 - 1296*t^4*z + 288*t^4 - 896*t^3*z^5 + 240*t^3*z^4 + 3744*t^3*z^3 + 864*t^3*z^2 - 2448*t^3*z - 864*t^3 + 448*t^2*z^6 - 432*t^2*z^5 - 2736*t^2*z^4 + 864*t^2*z^3 + 4320*t^2*z^2 + 864*t^2*z - 128*t*z^7 + 240*t*z^6 + 1008*t*z^5 - 1296*t*z^4 - 2448*t*z^3 + 864*t*z^2 + 2592*t*z + 16*z^8 - 48*z^7 - 144*z^6 + 432*z^5 + 288*z^4 - 864*z^3:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 4016*t^5 - 1120*t^4*z^2 - 4720*t^4*z - 15024*t^4 + 896*t^3*z^3 + 3344*t^3*z^2 + 8736*t^3*z + 30736*t^3 - 448*t^2*z^4 - 1360*t^2*z^3 - 2256*t^2*z^2 - 8528*t^2*z - 36176*t^2 + 128*t*z^5 + 272*t*z^4 - 48*t*z^3 + 832*t*z^2 + 5824*t*z + 21600*t - 16*z^6 - 16*z^5 + 96*z^4 - 32*z^3 - 512*z^2 - 1152*z - 4096)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_16 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 16) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_16 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_17 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 17) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_17 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^6 + 9072*t*z^5 - 20736*t*z^4 + 14256*t*z^3 + 3888*t*z^2 - 2592*t*z + 1296*z^8 - 11664*z^7 + 40176*z^6 - 64800*z^5 + 45360*z^4 - 3888*z^3 - 9072*z^2 + 2592*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^4 - 3888*t*z^3 + 3888*t*z^2 + 5184*t*z + 12960*t - 1296*z^6 + 6480*z^5 - 12960*z^4 + 6480*z^3 - 6480*z^2 - 28512*z - 98496)*hf
  · have hr : (-3072*t*z^6 + 25344*t*z^5 - 78336*t*z^4 + 111360*t*z^3 - 72288*t*z^2 + 19296*t*z - 1344*t + 4096*z^8 - 44032*z^7 + 196096*z^6 - 468736*z^5 + 650368*z^4 - 526528*z^3 + 234784*z^2 - 49504*z + 3136:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(3072*t*z^4 - 13056*t*z^3 + 23040*t*z^2 - 6144*t*z + 24672*t - 4096*z^6 + 27648*z^5 - 81408*z^4 + 115456*z^3 - 107136*z^2 - 17472*z - 197536)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_18 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 18) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_18 z t hf hn0 hn1 hn2 hn3
  · have hr : (-3072*t*z^6 + 25344*t*z^5 - 78336*t*z^4 + 111360*t*z^3 - 72288*t*z^2 + 19296*t*z - 1344*t + 4096*z^8 - 44032*z^7 + 196096*z^6 - 468736*z^5 + 650368*z^4 - 526528*z^3 + 234784*z^2 - 49504*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(3072*t*z^4 - 13056*t*z^3 + 23040*t*z^2 - 6144*t*z + 24672*t - 4096*z^6 + 27648*z^5 - 81408*z^4 + 115456*z^3 - 107136*z^2 - 17472*z - 197536)*hf
  · have hr : (-1296*t*z^6 + 9072*t*z^5 - 20736*t*z^4 + 14256*t*z^3 + 3888*t*z^2 - 2592*t*z + 1296*z^8 - 11664*z^7 + 40176*z^6 - 64800*z^5 + 45360*z^4 - 3888*z^3 - 9072*z^2 + 2592*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^4 - 3888*t*z^3 + 3888*t*z^2 + 5184*t*z + 12960*t - 1296*z^6 + 6480*z^5 - 12960*z^4 + 6480*z^3 - 6480*z^2 - 28512*z - 98496)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_19 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 19) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_19 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 640*t^6*z^2 - 144*t^6*z + 48*t^6 - 2048*t^5*z^3 + 1440*t^5*z^2 + 720*t^5*z + 4864*t^4*z^4 - 7680*t^4*z^3 + 1440*t^4*z^2 - 864*t^4*z - 144*t^4 - 8192*t^3*z^5 + 19584*t^3*z^4 - 7872*t^3*z^3 - 3456*t^3*z^2 + 144*t^3*z + 432*t^3 + 10240*t^2*z^6 - 36864*t^2*z^5 + 40320*t^2*z^4 - 15552*t^2*z^3 + 4320*t^2*z^2 + 1296*t^2*z - 432*t^2 - 8192*t*z^7 + 38400*t*z^6 - 57600*t*z^5 + 24192*t*z^4 + 5760*t*z^3 - 1728*t*z + 4096*z^8 - 27648*z^7 + 72192*z^6 - 89856*z^5 + 49536*z^4 - 1728*z^3 - 9504*z^2 + 2592*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-640*t^6 + 2048*t^5*z + 6752*t^5 - 4864*t^4*z^2 - 11776*t^4*z - 43680*t^4 + 8192*t^3*z^3 + 13184*t^3*z^2 + 52416*t^3*z + 199936*t^3 - 10240*t^2*z^4 - 4096*t^2*z^3 - 46464*t^2*z^2 - 166208*t^2*z - 622688*t^2 + 8192*t*z^5 - 5632*t*z^4 + 26880*t*z^3 + 88960*t*z^2 + 323200*t*z + 1203840*t - 4096*z^6 + 11264*z^5 - 23040*z^4 - 13568*z^3 - 80768*z^2 - 307776*z - 1140832)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_20 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 20) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : (t - 2*z:ℝ)=0 := by
  apply cell_0_20 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^6 + 9072*t*z^5 - 20736*t*z^4 + 14256*t*z^3 + 3888*t*z^2 - 2592*t*z + 1296*z^8 - 11664*z^7 + 40176*z^6 - 64800*z^5 + 45360*z^4 - 3888*z^3 - 9072*z^2 + 2592*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^4 - 3888*t*z^3 + 3888*t*z^2 + 5184*t*z + 12960*t - 1296*z^6 + 6480*z^5 - 12960*z^4 + 6480*z^3 - 6480*z^2 - 28512*z - 98496)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_21 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 21) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_21 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_22 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 22) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_22 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 12*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_23 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 23) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : (t - 2*z:ℝ)=0 := by
  apply cell_0_23 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 192*t^7*z + 16*t^7 + 1056*t^6*z^2 - 384*t^6*z - 128*t^6 - 3456*t^5*z^3 + 2736*t^5*z^2 + 864*t^5*z - 32*t^5 + 7344*t^4*z^4 - 9936*t^4*z^3 - 1440*t^4*z^2 + 1392*t^4*z + 256*t^4 - 10368*t^3*z^5 + 21168*t^3*z^4 - 2592*t^3*z^3 - 6432*t^3*z^2 - 1104*t^3*z - 32*t^3 + 9504*t^2*z^6 - 27216*t^2*z^5 + 12960*t^2*z^4 + 11232*t^2*z^3 - 2304*t^2*z^2 - 864*t^2*z + 16*t^2 - 5184*t*z^7 + 19872*t*z^6 - 18144*t*z^5 - 7344*t*z^4 + 9936*t*z^3 + 576*t*z^2 + 1392*t*z - 272*t + 1296*z^8 - 6480*z^7 + 9504*z^6 - 9504*z^4 + 5184*z^3 + 624*z^2 - 1104*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6 + 3456*t^5*z + 11088*t^5 - 7344*t^4*z^2 - 19440*t^4*z - 68976*t^4 + 10368*t^3*z^3 + 20304*t^3*z^2 + 73440*t^3*z + 279888*t^3 - 9504*t^2*z^4 - 10800*t^2*z^3 - 46656*t^2*z^2 - 187056*t^2*z - 699264*t^2 + 5184*t*z^5 + 864*t*z^4 + 16416*t*z^3 + 72144*t*z^2 + 262224*t*z + 976176*t - 1296*z^6 + 1296*z^5 - 3024*z^4 - 13392*z^3 - 41040*z^2 - 155952*z - 583392)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_24 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 24) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_24 z t hf hn0 hn1 hn2 hn3
  · have hr : (-3072*t*z^6 + 25344*t*z^5 - 78336*t*z^4 + 111360*t*z^3 - 72288*t*z^2 + 19296*t*z - 1344*t + 4096*z^8 - 44032*z^7 + 196096*z^6 - 468736*z^5 + 650368*z^4 - 526528*z^3 + 234784*z^2 - 49504*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(3072*t*z^4 - 13056*t*z^3 + 23040*t*z^2 - 6144*t*z + 24672*t - 4096*z^6 + 27648*z^5 - 81408*z^4 + 115456*z^3 - 107136*z^2 - 17472*z - 197536)*hf
  · have hr : (-1296*t*z^6 + 12960*t*z^5 - 50544*t*z^4 + 97200*t*z^3 - 95904*t*z^2 + 45360*t*z - 7776*t + 1296*z^8 - 16848*z^7 + 93312*z^6 - 287712*z^5 + 539136*z^4 - 624672*z^3 + 431568*z^2 - 159408*z + 23328:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^4 - 7776*t*z^3 + 18144*t*z^2 - 16848*t*z + 10368*t - 1296*z^6 + 11664*z^5 - 45360*z^4 + 94608*z^3 - 115344*z^2 + 68688*z - 41472)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_25 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 25) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_25 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 12*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_26 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 26) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_26 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 10*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_27 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 27) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_27 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 6*t + 2*z^2 - 6*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 128*t^7*z - 112*t^7 + 640*t^6*z^2 + 112*t^6*z + 544*t^6 - 2048*t^5*z^3 + 672*t^5*z^2 + 192*t^5*z - 1696*t^5 + 4864*t^4*z^4 - 7168*t^4*z^3 + 5568*t^4*z^2 - 5776*t^4*z + 4096*t^4 - 8192*t^3*z^5 + 20608*t^3*z^4 - 14336*t^3*z^3 - 4768*t^3*z^2 + 15536*t^3*z - 6688*t^3 + 10240*t^2*z^6 - 43008*t^2*z^5 + 72960*t^2*z^4 - 77504*t^2*z^3 + 66912*t^2*z^2 - 39552*t^2*z + 8656*t^2 - 8192*t*z^7 + 46592*t*z^6 - 98304*t*z^5 + 81664*t*z^4 + 11840*t*z^3 - 66720*t*z^2 + 39280*t*z - 6160*t + 4096*z^8 - 35840*z^7 + 136192*z^6 - 293888*z^5 + 391936*z^4 - 325952*z^3 + 160192*z^2 - 39872*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-640*t^6 + 2048*t^5*z + 7520*t^5 - 4864*t^4*z^2 - 12288*t^4*z - 49856*t^4 + 8192*t^3*z^3 + 12160*t^3*z^2 + 54784*t^3*z + 211744*t^3 - 10240*t^2*z^4 + 2048*t^2*z^3 - 54528*t^2*z^2 - 142656*t^2*z - 583008*t^2 + 8192*t*z^5 - 13824*t*z^4 + 34816*t*z^3 + 71424*t*z^2 + 239040*t*z + 951456*t - 4096*z^6 + 19456*z^5 - 54272*z^4 + 57344*z^3 - 108288*z^2 - 164544*z - 710080)*hf
  · have hr : (16*t^8 - 368*t^7 + 192*t^6*z^2 - 624*t^6*z + 3808*t^6 - 3312*t^5*z^2 + 10800*t^5*z - 23360*t^5 + 864*t^4*z^4 - 5616*t^4*z^3 + 33984*t^4*z^2 - 81216*t^4*z + 92896*t^4 - 9936*t^3*z^4 + 64800*t^3*z^3 - 210336*t^3*z^2 + 342528*t^3*z - 244928*t^3 + 1728*t^2*z^6 - 16848*t^2*z^5 + 101088*t^2*z^4 - 362016*t^2*z^3 + 754560*t^2*z^2 - 852336*t^2*z + 417328*t^2 - 9936*t*z^6 + 97200*t*z^5 - 420768*t*z^4 + 1023840*t*z^3 - 1472976*t*z^2 + 1186272*t*z - 419120*t + 1296*z^8 - 16848*z^7 + 100224*z^6 - 355104*z^5 + 817344*z^4 - 1248480*z^3 + 1233552*z^2 - 719472*z + 189280:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6 + 3312*t^5 - 864*t^4*z^2 + 2160*t^4*z - 24480*t^4 + 9936*t^3*z^2 - 25056*t^3*z + 100176*t^3 - 1728*t^2*z^4 + 9936*t^2*z^3 - 59616*t^2*z^2 + 113616*t^2*z - 240480*t^2 + 9936*t*z^4 - 57456*t*z^3 + 181008*t*z^2 - 242352*t*z + 322560*t - 1296*z^6 + 11664*z^5 - 52272*z^4 + 134352*z^3 - 227664*z^2 + 203472*z - 192000)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_28 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 28) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_28 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 640*t^6*z^2 - 144*t^6*z + 48*t^6 - 2048*t^5*z^3 + 1440*t^5*z^2 + 720*t^5*z + 4864*t^4*z^4 - 7680*t^4*z^3 + 1440*t^4*z^2 - 864*t^4*z - 144*t^4 - 8192*t^3*z^5 + 19584*t^3*z^4 - 7872*t^3*z^3 - 3456*t^3*z^2 + 144*t^3*z + 432*t^3 + 10240*t^2*z^6 - 36864*t^2*z^5 + 40320*t^2*z^4 - 15552*t^2*z^3 + 4320*t^2*z^2 + 1296*t^2*z - 432*t^2 - 8192*t*z^7 + 38400*t*z^6 - 57600*t*z^5 + 24192*t*z^4 + 5760*t*z^3 - 1728*t*z + 4096*z^8 - 27648*z^7 + 72192*z^6 - 89856*z^5 + 49536*z^4 - 1728*z^3 - 9504*z^2 + 2592*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-640*t^6 + 2048*t^5*z + 6752*t^5 - 4864*t^4*z^2 - 11776*t^4*z - 43680*t^4 + 8192*t^3*z^3 + 13184*t^3*z^2 + 52416*t^3*z + 199936*t^3 - 10240*t^2*z^4 - 4096*t^2*z^3 - 46464*t^2*z^2 - 166208*t^2*z - 622688*t^2 + 8192*t*z^5 - 5632*t*z^4 + 26880*t*z^3 + 88960*t*z^2 + 323200*t*z + 1203840*t - 4096*z^6 + 11264*z^5 - 23040*z^4 - 13568*z^3 - 80768*z^2 - 307776*z - 1140832)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_29 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 29) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : (t - 2*z:ℝ)=0 := by
  apply cell_0_29 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 192*t^7*z + 16*t^7 + 1056*t^6*z^2 - 384*t^6*z - 128*t^6 - 3456*t^5*z^3 + 2736*t^5*z^2 + 864*t^5*z - 32*t^5 + 7344*t^4*z^4 - 9936*t^4*z^3 - 1440*t^4*z^2 + 1392*t^4*z + 256*t^4 - 10368*t^3*z^5 + 21168*t^3*z^4 - 2592*t^3*z^3 - 6432*t^3*z^2 - 1104*t^3*z - 32*t^3 + 9504*t^2*z^6 - 27216*t^2*z^5 + 12960*t^2*z^4 + 11232*t^2*z^3 - 2304*t^2*z^2 - 864*t^2*z + 16*t^2 - 5184*t*z^7 + 19872*t*z^6 - 18144*t*z^5 - 7344*t*z^4 + 9936*t*z^3 + 576*t*z^2 + 1392*t*z - 272*t + 1296*z^8 - 6480*z^7 + 9504*z^6 - 9504*z^4 + 5184*z^3 + 624*z^2 - 1104*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6 + 3456*t^5*z + 11088*t^5 - 7344*t^4*z^2 - 19440*t^4*z - 68976*t^4 + 10368*t^3*z^3 + 20304*t^3*z^2 + 73440*t^3*z + 279888*t^3 - 9504*t^2*z^4 - 10800*t^2*z^3 - 46656*t^2*z^2 - 187056*t^2*z - 699264*t^2 + 5184*t*z^5 + 864*t*z^4 + 16416*t*z^3 + 72144*t*z^2 + 262224*t*z + 976176*t - 1296*z^6 + 1296*z^5 - 3024*z^4 - 13392*z^3 - 41040*z^2 - 155952*z - 583392)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_30 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 30) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : (t - z - 2:ℝ)=0 := by
  apply cell_0_30 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 6*t + 2*z^2 - 6*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 128*t^7*z - 112*t^7 + 640*t^6*z^2 + 112*t^6*z + 544*t^6 - 2048*t^5*z^3 + 672*t^5*z^2 + 192*t^5*z - 1696*t^5 + 4864*t^4*z^4 - 7168*t^4*z^3 + 5568*t^4*z^2 - 5776*t^4*z + 4096*t^4 - 8192*t^3*z^5 + 20608*t^3*z^4 - 14336*t^3*z^3 - 4768*t^3*z^2 + 15536*t^3*z - 6688*t^3 + 10240*t^2*z^6 - 43008*t^2*z^5 + 72960*t^2*z^4 - 77504*t^2*z^3 + 66912*t^2*z^2 - 39552*t^2*z + 8656*t^2 - 8192*t*z^7 + 46592*t*z^6 - 98304*t*z^5 + 81664*t*z^4 + 11840*t*z^3 - 66720*t*z^2 + 39280*t*z - 6160*t + 4096*z^8 - 35840*z^7 + 136192*z^6 - 293888*z^5 + 391936*z^4 - 325952*z^3 + 160192*z^2 - 39872*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-640*t^6 + 2048*t^5*z + 7520*t^5 - 4864*t^4*z^2 - 12288*t^4*z - 49856*t^4 + 8192*t^3*z^3 + 12160*t^3*z^2 + 54784*t^3*z + 211744*t^3 - 10240*t^2*z^4 + 2048*t^2*z^3 - 54528*t^2*z^2 - 142656*t^2*z - 583008*t^2 + 8192*t*z^5 - 13824*t*z^4 + 34816*t*z^3 + 71424*t*z^2 + 239040*t*z + 951456*t - 4096*z^6 + 19456*z^5 - 54272*z^4 + 57344*z^3 - 108288*z^2 - 164544*z - 710080)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_31 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 31) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_31 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 256*t^7*z + 80*t^7 + 1792*t^6*z^2 - 1264*t^6*z + 16*t^6 - 7168*t^5*z^3 + 8448*t^5*z^2 - 912*t^5*z - 256*t^5 + 17920*t^4*z^4 - 31040*t^4*z^3 + 8448*t^4*z^2 + 2272*t^4*z + 16*t^4 - 28672*t^3*z^5 + 67840*t^3*z^4 - 33664*t^3*z^3 - 6784*t^3*z^2 + 1744*t^3*z + 176*t^3 + 28672*t^2*z^6 - 88320*t^2*z^5 + 68352*t^2*z^4 + 6656*t^2*z^3 - 11712*t^2*z^2 - 48*t^2*z - 272*t^2 - 16384*t*z^7 + 63488*t*z^6 - 69888*t*z^5 + 2560*t*z^4 + 25408*t*z^3 - 5952*t*z^2 + 1664*t*z - 64*t + 4096*z^8 - 19456*z^7 + 28672*z^6 - 5632*z^5 - 18176*z^4 + 10688*z^3 + 640*z^2 - 1312*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1792*t^6 + 7168*t^5*z + 20224*t^5 - 17920*t^4*z^2 - 40640*t^4*z - 153088*t^4 + 28672*t^3*z^3 + 46848*t^3*z^2 + 192384*t^3*z + 729472*t^3 - 28672*t^2*z^4 - 26368*t^2*z^3 - 145152*t^2*z^2 - 560896*t^2*z - 2086720*t^2 + 16384*t*z^5 + 2048*t*z^4 + 61696*t*z^3 + 242176*t*z^2 + 881600*t*z + 3290176*t - 4096*z^6 + 3072*z^5 - 12288*z^4 - 46592*z^3 - 155904*z^2 - 587712*z - 2195584)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_32 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 32) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_32 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_33 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 33) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : (t - z - 2:ℝ)=0 := by
  apply cell_0_33 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^6 + 12960*t*z^5 - 50544*t*z^4 + 97200*t*z^3 - 95904*t*z^2 + 45360*t*z - 7776*t + 1296*z^8 - 16848*z^7 + 93312*z^6 - 287712*z^5 + 539136*z^4 - 624672*z^3 + 431568*z^2 - 159408*z + 23328:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^4 - 7776*t*z^3 + 18144*t*z^2 - 16848*t*z + 10368*t - 1296*z^6 + 11664*z^5 - 45360*z^4 + 94608*z^3 - 115344*z^2 + 68688*z - 41472)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_34 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 34) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_34 z t hf hn0 hn1 hn2 hn3
  · have hr : (-6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_35 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 35) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_35 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z - 176*t^7 + 160*t^6*z^2 + 544*t^6*z + 592*t^6 - 256*t^5*z^3 - 1104*t^5*z^2 - 1200*t^5*z - 320*t^5 + 304*t^4*z^4 + 1328*t^4*z^3 + 1680*t^4*z^2 - 208*t^4*z - 1520*t^4 - 256*t^3*z^5 - 1168*t^3*z^4 - 976*t^3*z^3 + 1264*t^3*z^2 + 1456*t^3*z + 1840*t^3 + 160*t^2*z^6 + 624*t^2*z^5 + 240*t^2*z^4 - 1616*t^2*z^3 - 1776*t^2*z^2 + 768*t^2*z + 304*t^2 - 64*t*z^7 - 224*t*z^6 + 240*t*z^5 + 1088*t*z^4 - 608*t*z^3 - 1104*t*z^2 + 1568*t*z - 896*t + 16*z^8 + 16*z^7 - 128*z^6 - 32*z^5 + 256*z^4 - 32*z^3 + 16*z^2 - 272*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 2128*t^5 - 304*t^4*z^2 - 2544*t^4*z - 11552*t^4 + 256*t^3*z^3 + 2192*t^3*z^2 + 9488*t^3*z + 34496*t^3 - 160*t^2*z^4 - 1264*t^2*z^3 - 5136*t^2*z^2 - 17664*t^2*z - 63744*t^2 + 64*t*z^5 + 480*t*z^4 + 1616*t*z^3 + 4896*t*z^2 + 18576*t*z + 70512*t - 16*z^6 - 80*z^5 - 176*z^4 - 592*z^3 - 2448*z^2 - 9168*z - 34240)*hf
  · have hr : (16*t^8 + 64*t^7*z - 432*t^7 + 160*t^6*z^2 - 1536*t^6*z + 4752*t^6 + 256*t^5*z^3 - 3312*t^5*z^2 + 14832*t^5*z - 27648*t^5 + 304*t^4*z^4 - 4464*t^4*z^3 + 26640*t^4*z^2 - 73872*t^4*z + 92304*t^4 + 256*t^3*z^5 - 4272*t^3*z^4 + 28944*t^3*z^3 - 104976*t^3*z^2 + 201456*t^3*z - 179280*t^3 + 160*t^2*z^6 - 2736*t^2*z^5 + 20592*t^2*z^4 - 85104*t^2*z^3 + 209520*t^2*z^2 - 294624*t^2*z + 195696*t^2 + 64*t*z^7 - 1152*t*z^6 + 8784*t*z^5 - 38880*t*z^4 + 109440*t*z^3 - 197424*t*z^2 + 212544*t*z - 108864*t + 16*z^8 - 240*z^7 + 1728*z^6 - 7776*z^5 + 23616*z^4 - 49248*z^3 + 68688*z^2 - 58320*z + 23328:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 2288*t^5 - 304*t^4*z^2 + 3248*t^4*z - 13344*t^4 - 256*t^3*z^3 + 3248*t^3*z^2 - 15696*t^3*z + 38944*t^3 - 160*t^2*z^4 + 2096*t^2*z^3 - 12048*t^2*z^2 + 34816*t^2*z - 58208*t^2 - 64*t*z^5 + 896*t*z^4 - 5136*t*z^3 + 17440*t*z^2 - 34544*t*z + 41808*t - 16*z^6 + 176*z^5 - 1008*z^4 + 3568*z^3 - 8336*z^2 + 12336*z - 11008)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_36 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (_hc : cell (1) (1) (1) (profile4 (z) (2) t 36) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : ((0:ℝ):ℝ)=0 := by
  apply cell_0_36 z t hf hn0 hn1 hn2 hn3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_37 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 37) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_37 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 12*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_38 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 38) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_38 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 10*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_39 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 39) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : (t - z - 2:ℝ)=0 := by
  apply cell_0_39 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 6*t + 2*z^2 - 6*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_40 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 40) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_40 z t hf hn0 hn1 hn2 hn3
  · have hr : (-6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_41 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 41) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_41 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 10*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_42 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 42) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_42 z t hf hn0 hn1 hn2 hn3
  · have hr : (-10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_43 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 43) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_43 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 10*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z - 240*t^7 + 160*t^6*z^2 + 672*t^6*z + 1344*t^6 - 256*t^5*z^3 - 1296*t^5*z^2 - 2160*t^5*z - 3456*t^5 + 304*t^4*z^4 + 1392*t^4*z^3 + 3024*t^4*z^2 + 1728*t^4*z + 3744*t^4 - 256*t^3*z^5 - 1104*t^3*z^4 - 1200*t^3*z^3 - 2160*t^3*z^2 + 1152*t^3*z + 160*t^2*z^6 + 432*t^2*z^5 + 432*t^2*z^4 - 1296*t^2*z^3 + 1296*t^2*z^2 + 432*t^2*z - 3024*t^2 - 64*t*z^7 - 96*t*z^6 + 432*t*z^5 - 432*t*z^4 - 144*t*z^3 + 864*t*z^2 - 864*t*z + 1296*t + 16*z^8 - 48*z^7 + 48*z^6 - 144*z^4 + 432*z^3 - 432*z^2:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 2320*t^5 - 304*t^4*z^2 - 2608*t^4*z - 13152*t^4 + 256*t^3*z^3 + 2128*t^3*z^2 + 9456*t^3*z + 37856*t^3 - 160*t^2*z^4 - 1072*t^2*z^3 - 4560*t^2*z^2 - 15872*t^2*z - 60224*t^2 + 64*t*z^5 + 352*t*z^4 + 912*t*z^3 + 3728*t*z^2 + 14144*t*z + 51984*t - 16*z^6 - 16*z^5 - 96*z^4 - 368*z^3 - 1232*z^2 - 4992*z - 18304)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_44 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 44) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_44 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z - 176*t^7 + 160*t^6*z^2 + 544*t^6*z + 592*t^6 - 256*t^5*z^3 - 1104*t^5*z^2 - 1200*t^5*z - 320*t^5 + 304*t^4*z^4 + 1328*t^4*z^3 + 1680*t^4*z^2 - 208*t^4*z - 1520*t^4 - 256*t^3*z^5 - 1168*t^3*z^4 - 976*t^3*z^3 + 1264*t^3*z^2 + 1456*t^3*z + 1840*t^3 + 160*t^2*z^6 + 624*t^2*z^5 + 240*t^2*z^4 - 1616*t^2*z^3 - 1776*t^2*z^2 + 768*t^2*z + 304*t^2 - 64*t*z^7 - 224*t*z^6 + 240*t*z^5 + 1088*t*z^4 - 608*t*z^3 - 1104*t*z^2 + 1568*t*z - 896*t + 16*z^8 + 16*z^7 - 128*z^6 - 32*z^5 + 256*z^4 - 32*z^3 + 16*z^2 - 272*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 2128*t^5 - 304*t^4*z^2 - 2544*t^4*z - 11552*t^4 + 256*t^3*z^3 + 2192*t^3*z^2 + 9488*t^3*z + 34496*t^3 - 160*t^2*z^4 - 1264*t^2*z^3 - 5136*t^2*z^2 - 17664*t^2*z - 63744*t^2 + 64*t*z^5 + 480*t*z^4 + 1616*t*z^3 + 4896*t*z^2 + 18576*t*z + 70512*t - 16*z^6 - 80*z^5 - 176*z^4 - 592*z^3 - 2448*z^2 - 9168*z - 34240)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_45 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 45) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_45 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 6*t + 2*z^2 - 6*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 192*t^7*z + 16*t^7 + 1056*t^6*z^2 - 576*t^6*z + 256*t^6 - 3456*t^5*z^3 + 4464*t^5*z^2 - 2736*t^5*z + 256*t^5 + 7344*t^4*z^4 - 16848*t^4*z^3 + 16272*t^4*z^2 - 7104*t^4*z + 1696*t^4 - 10368*t^3*z^5 + 36720*t^3*z^4 - 54000*t^3*z^3 + 40656*t^3*z^2 - 14976*t^3*z + 1792*t^3 + 9504*t^2*z^6 - 47952*t^2*z^5 + 102384*t^2*z^4 - 118800*t^2*z^3 + 79344*t^2*z^2 - 30096*t^2*z + 4912*t^2 - 5184*t*z^7 + 35424*t*z^6 - 104976*t*z^5 + 174096*t*z^4 - 171504*t*z^3 + 97344*t*z^2 - 28128*t*z + 3472*t + 1296*z^8 - 11664*z^7 + 47088*z^6 - 111456*z^5 + 168048*z^4 - 162864*z^3 + 96528*z^2 - 30240*z + 3136:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6 + 3456*t^5*z + 9360*t^5 - 7344*t^4*z^2 - 12528*t^4*z - 59040*t^4 + 10368*t^3*z^3 + 4752*t^3*z^2 + 62640*t^3*z + 205152*t^3 - 9504*t^2*z^4 + 9936*t^2*z^3 - 53136*t^2*z^2 - 103680*t^2*z - 440928*t^2 + 5184*t*z^5 - 14688*t*z^4 + 41040*t*z^3 + 4752*t*z^2 + 149472*t*z + 495792*t - 1296*z^6 + 6480*z^5 - 19872*z^4 + 25488*z^3 - 46224*z^2 - 47520*z - 240384)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_46 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 46) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_46 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 10*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z - 240*t^7 + 160*t^6*z^2 + 672*t^6*z + 1344*t^6 - 256*t^5*z^3 - 1296*t^5*z^2 - 2160*t^5*z - 3456*t^5 + 304*t^4*z^4 + 1392*t^4*z^3 + 3024*t^4*z^2 + 1728*t^4*z + 3744*t^4 - 256*t^3*z^5 - 1104*t^3*z^4 - 1200*t^3*z^3 - 2160*t^3*z^2 + 1152*t^3*z + 160*t^2*z^6 + 432*t^2*z^5 + 432*t^2*z^4 - 1296*t^2*z^3 + 1296*t^2*z^2 + 432*t^2*z - 3024*t^2 - 64*t*z^7 - 96*t*z^6 + 432*t*z^5 - 432*t*z^4 - 144*t*z^3 + 864*t*z^2 - 864*t*z + 1296*t + 16*z^8 - 48*z^7 + 48*z^6 - 144*z^4 + 432*z^3 - 432*z^2:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 2320*t^5 - 304*t^4*z^2 - 2608*t^4*z - 13152*t^4 + 256*t^3*z^3 + 2128*t^3*z^2 + 9456*t^3*z + 37856*t^3 - 160*t^2*z^4 - 1072*t^2*z^3 - 4560*t^2*z^2 - 15872*t^2*z - 60224*t^2 + 64*t*z^5 + 352*t*z^4 + 912*t*z^3 + 3728*t*z^2 + 14144*t*z + 51984*t - 16*z^6 - 16*z^5 - 96*z^4 - 368*z^3 - 1232*z^2 - 4992*z - 18304)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_47 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 47) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_47 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 12*t + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z - 176*t^7 + 448*t^6*z^2 + 1136*t^6*z + 592*t^6 - 896*t^5*z^3 - 3120*t^5*z^2 - 2832*t^5*z - 320*t^5 + 1120*t^4*z^4 + 4720*t^4*z^3 + 5424*t^4*z^2 + 448*t^4*z - 1520*t^4 - 896*t^3*z^5 - 4240*t^3*z^4 - 5216*t^3*z^3 + 832*t^3*z^2 + 4112*t^3*z + 1840*t^3 + 448*t^2*z^6 + 2256*t^2*z^5 + 2544*t^2*z^4 - 1984*t^2*z^3 - 3648*t^2*z^2 - 1488*t^2*z + 304*t^2 - 128*t*z^7 - 656*t*z^6 - 528*t*z^5 + 1280*t*z^4 + 1040*t*z^3 - 528*t*z^2 + 1408*t*z - 896*t + 16*z^8 + 80*z^7 + 16*z^6 - 256*z^5 + 16*z^4 + 176*z^3 - 272*z^2 - 64*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 6704*t^5 - 1120*t^4*z^2 - 9200*t^4*z - 41104*t^4 + 896*t^3*z^3 + 7824*t^3*z^2 + 35616*t^3*z + 133808*t^3 - 448*t^2*z^4 - 4048*t^2*z^3 - 18288*t^2*z^2 - 67120*t^2*z - 246544*t^2 + 128*t*z^5 + 1168*t*z^4 + 5072*t*z^3 + 17840*t*z^2 + 65248*t*z + 243680*t - 16*z^6 - 144*z^5 - 576*z^4 - 1904*z^3 - 7056*z^2 - 26496*z - 98656)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_48 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 48) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_48 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z - 304*t^7 + 448*t^6*z^2 - 2128*t^6*z + 2224*t^6 + 896*t^5*z^3 - 6384*t^5*z^2 + 13488*t^5*z - 7888*t^5 + 1120*t^4*z^4 - 10640*t^4*z^3 + 33936*t^4*z^2 - 40592*t^4*z + 13792*t^4 + 896*t^3*z^5 - 10640*t^3*z^4 + 45344*t^3*z^3 - 82336*t^3*z^2 + 57328*t^3*z - 9952*t^3 + 448*t^2*z^6 - 6384*t^2*z^5 + 33936*t^2*z^4 - 82336*t^2*z^3 + 87072*t^2*z^2 - 29280*t^2*z - 128*t^2 + 128*t*z^7 - 2128*t*z^6 + 13488*t*z^5 - 40592*t*z^4 + 57328*t*z^3 - 29280*t*z^2 - 544*t*z + 2432*t + 16*z^8 - 304*z^7 + 2224*z^6 - 7888*z^5 + 13792*z^4 - 9952*z^3 - 128*z^2 + 2432*z - 512:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 - 896*t^5*z + 2800*t^5 - 1120*t^4*z^2 + 6160*t^4*z - 8176*t^4 - 896*t^3*z^3 + 7056*t^3*z^2 - 16224*t^3*z + 10384*t^3 - 448*t^2*z^4 + 4592*t^2*z^3 - 15120*t^2*z^2 + 17264*t^2*z - 2896*t^2 - 128*t*z^5 + 1616*t*z^4 - 6896*t*z^3 + 11392*t*z^2 - 4864*t*z - 1568*t - 16*z^6 + 240*z^5 - 1248*z^4 + 2656*z^3 - 1920*z^2 - 384*z + 512)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_49 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 49) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_49 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 + 64*t^7*z - 240*t^7 + 160*t^6*z^2 - 960*t^6*z + 1344*t^6 + 256*t^5*z^3 - 2160*t^5*z^2 + 5472*t^5*z - 3456*t^5 + 304*t^4*z^4 - 3120*t^4*z^3 + 10944*t^4*z^2 - 14256*t^4*z + 3744*t^4 + 256*t^3*z^5 - 3120*t^3*z^4 + 13728*t^3*z^3 - 25056*t^3*z^2 + 14832*t^3*z + 160*t^2*z^6 - 2160*t^2*z^5 + 10944*t^2*z^4 - 25056*t^2*z^3 + 22464*t^2*z^2 - 3024*t^2 + 64*t*z^7 - 960*t*z^6 + 5472*t*z^5 - 14256*t*z^4 + 14832*t*z^3 - 5616*t*z + 1296*t + 16*z^8 - 240*z^7 + 1344*z^6 - 3456*z^5 + 3744*z^4 - 3024*z^2 + 1296*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 1136*t^5 - 304*t^4*z^2 + 1904*t^4*z - 3024*t^4 - 256*t^3*z^3 + 2096*t^3*z^2 - 5088*t^3*z + 2608*t^3 - 160*t^2*z^4 + 1520*t^2*z^3 - 4704*t^2*z^2 + 4720*t^2*z + 1120*t^2 - 64*t*z^5 + 704*t*z^4 - 2592*t*z^3 + 3184*t*z^2 + 496*t*z - 1200*t - 16*z^6 + 176*z^5 - 624*z^4 + 784*z^3 + 16*z^2 - 720*z + 128)*hf
  · have hr : (16*t^8 - 112*t^7 + 192*t^6*z^2 - 624*t^6*z + 544*t^6 - 1008*t^5*z^2 + 3312*t^5*z - 1696*t^5 + 864*t^4*z^4 - 5616*t^4*z^3 + 13248*t^4*z^2 - 13536*t^4*z + 4096*t^4 - 3024*t^3*z^4 + 19872*t^3*z^3 - 41952*t^3*z^2 + 30720*t^3*z - 6688*t^3 + 1728*t^2*z^6 - 16848*t^2*z^5 + 64800*t^2*z^4 - 125280*t^2*z^3 + 125568*t^2*z^2 - 57168*t^2*z + 8656*t^2 - 3024*t*z^6 + 29808*t*z^5 - 110592*t*z^4 + 190944*t*z^3 - 154800*t*z^2 + 54720*t*z - 6160*t + 1296*z^8 - 16848*z^7 + 89856*z^6 - 254016*z^5 + 410400*z^4 - 380160*z^3 + 190704*z^2 - 44688*z + 3136:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6 + 1008*t^5 - 864*t^4*z^2 + 2160*t^4*z - 3744*t^4 + 3024*t^3*z^2 - 7776*t^3*z + 7824*t^3 - 1728*t^2*z^4 + 9936*t^2*z^3 - 23328*t^2*z^2 + 22032*t^2*z - 14112*t^2 + 3024*t*z^4 - 17712*t*z^3 + 36720*t*z^2 - 26352*t*z + 12672*t - 1296*z^6 + 11664*z^5 - 41904*z^4 + 74736*z^3 - 69552*z^2 + 27216*z - 12288)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_50 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 50) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : (t + z - 4:ℝ)=0 := by
  apply cell_0_50 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z - 368*t^7 + 448*t^6*z^2 - 2576*t^6*z + 3424*t^6 + 896*t^5*z^3 - 7728*t^5*z^2 + 20688*t^5*z - 16736*t^5 + 1120*t^4*z^4 - 12880*t^4*z^3 + 51936*t^4*z^2 - 85120*t^4*z + 46528*t^4 + 896*t^3*z^5 - 12880*t^3*z^4 + 69344*t^3*z^3 - 171680*t^3*z^2 + 190432*t^3*z - 73952*t^3 + 448*t^2*z^6 - 7728*t^2*z^5 + 51936*t^2*z^4 - 171680*t^2*z^3 + 287808*t^2*z^2 - 225456*t^2*z + 63376*t^2 + 128*t*z^7 - 2576*t*z^6 + 20688*t*z^5 - 85120*t*z^4 + 190432*t*z^3 - 225456*t*z^2 + 127328*t*z - 25424*t + 16*z^8 - 368*z^7 + 3424*z^6 - 16736*z^5 + 46528*z^4 - 73952*z^3 + 63376*z^2 - 25424*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 - 896*t^5*z + 4144*t^5 - 1120*t^4*z^2 + 8400*t^4*z - 17216*t^4 - 896*t^3*z^3 + 9296*t^3*z^2 - 31264*t^3*z + 37328*t^3 - 448*t^2*z^4 + 5936*t^2*z^3 - 27744*t^2*z^2 + 54768*t^2*z - 40992*t^2 - 128*t*z^5 + 2064*t*z^4 - 12304*t*z^3 + 33840*t*z^2 - 42768*t*z + 20544*t - 16*z^6 + 304*z^5 - 2192*z^4 + 7664*z^3 - 13680*z^2 + 11568*z - 3424)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_51 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 51) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : (t + z - 4:ℝ)=0 := by
  apply cell_0_51 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 240*t^7 + 160*t^6*z^2 - 960*t^6*z + 1344*t^6 + 256*t^5*z^3 - 2160*t^5*z^2 + 5472*t^5*z - 3456*t^5 + 304*t^4*z^4 - 3120*t^4*z^3 + 10944*t^4*z^2 - 14256*t^4*z + 3744*t^4 + 256*t^3*z^5 - 3120*t^3*z^4 + 13728*t^3*z^3 - 25056*t^3*z^2 + 14832*t^3*z + 160*t^2*z^6 - 2160*t^2*z^5 + 10944*t^2*z^4 - 25056*t^2*z^3 + 22464*t^2*z^2 - 3024*t^2 + 64*t*z^7 - 960*t*z^6 + 5472*t*z^5 - 14256*t*z^4 + 14832*t*z^3 - 5616*t*z + 1296*t + 16*z^8 - 240*z^7 + 1344*z^6 - 3456*z^5 + 3744*z^4 - 3024*z^2 + 1296*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 1136*t^5 - 304*t^4*z^2 + 1904*t^4*z - 3024*t^4 - 256*t^3*z^3 + 2096*t^3*z^2 - 5088*t^3*z + 2608*t^3 - 160*t^2*z^4 + 1520*t^2*z^3 - 4704*t^2*z^2 + 4720*t^2*z + 1120*t^2 - 64*t*z^5 + 704*t*z^4 - 2592*t*z^3 + 3184*t*z^2 + 496*t*z - 1200*t - 16*z^6 + 176*z^5 - 624*z^4 + 784*z^3 + 16*z^2 - 720*z + 128)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_52 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 52) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_52 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 + 64*t^7*z - 240*t^7 + 160*t^6*z^2 - 960*t^6*z + 1344*t^6 + 256*t^5*z^3 - 2160*t^5*z^2 + 5472*t^5*z - 3456*t^5 + 304*t^4*z^4 - 3120*t^4*z^3 + 10944*t^4*z^2 - 14256*t^4*z + 3744*t^4 + 256*t^3*z^5 - 3120*t^3*z^4 + 13728*t^3*z^3 - 25056*t^3*z^2 + 14832*t^3*z + 160*t^2*z^6 - 2160*t^2*z^5 + 10944*t^2*z^4 - 25056*t^2*z^3 + 22464*t^2*z^2 - 3024*t^2 + 64*t*z^7 - 960*t*z^6 + 5472*t*z^5 - 14256*t*z^4 + 14832*t*z^3 - 5616*t*z + 1296*t + 16*z^8 - 240*z^7 + 1344*z^6 - 3456*z^5 + 3744*z^4 - 3024*z^2 + 1296*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 1136*t^5 - 304*t^4*z^2 + 1904*t^4*z - 3024*t^4 - 256*t^3*z^3 + 2096*t^3*z^2 - 5088*t^3*z + 2608*t^3 - 160*t^2*z^4 + 1520*t^2*z^3 - 4704*t^2*z^2 + 4720*t^2*z + 1120*t^2 - 64*t*z^5 + 704*t*z^4 - 2592*t*z^3 + 3184*t*z^2 + 496*t*z - 1200*t - 16*z^6 + 176*z^5 - 624*z^4 + 784*z^3 + 16*z^2 - 720*z + 128)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_53 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 53) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_53 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 176*t^7 - 48*t^6*z + 592*t^6 + 432*t^5*z - 320*t^5 - 864*t^4*z - 1520*t^4 - 1200*t^3*z + 1840*t^3 + 3024*t^2*z + 304*t^2 + 1728*t*z - 896*t - 480*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_54 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 54) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_54 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 6*t + 2*z^2 - 6*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 + 64*t^7*z - 304*t^7 + 160*t^6*z^2 - 1280*t^6*z + 2416*t^6 + 256*t^5*z^3 - 2928*t^5*z^2 + 10416*t^5*z - 10624*t^5 + 304*t^4*z^4 - 4336*t^4*z^3 + 21840*t^4*z^2 - 44560*t^4*z + 28336*t^4 + 256*t^3*z^5 - 4400*t^3*z^4 + 28432*t^3*z^3 - 83920*t^3*z^2 + 108080*t^3*z - 46288*t^3 + 160*t^2*z^6 - 3120*t^2*z^5 + 23856*t^2*z^4 - 90032*t^2*z^3 + 171312*t^2*z^2 - 147264*t^2*z + 43792*t^2 + 64*t*z^7 - 1408*t*z^6 + 12432*t*z^5 - 56096*t*z^4 + 136064*t*z^3 - 171408*t*z^2 + 100960*t*z - 20608*t + 16*z^8 - 368*z^7 + 3424*z^6 - 16736*z^5 + 46528*z^4 - 73952*z^3 + 63376*z^2 - 25424*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 1904*t^5 - 304*t^4*z^2 + 3120*t^4*z - 9056*t^4 - 256*t^3*z^3 + 3376*t^3*z^2 - 14672*t^3*z + 21856*t^3 - 160*t^2*z^4 + 2480*t^2*z^3 - 13776*t^2*z^2 + 32448*t^2*z - 27744*t^2 - 64*t*z^5 + 1152*t*z^4 - 7760*t*z^3 + 23904*t*z^2 - 32688*t*z + 16752*t - 16*z^6 + 304*z^5 - 2192*z^4 + 7664*z^3 - 13680*z^2 + 11568*z - 3424)*hf
  · have hr : (16*t^8 - 176*t^7 - 48*t^6*z + 592*t^6 + 432*t^5*z - 320*t^5 - 864*t^4*z - 1520*t^4 - 1200*t^3*z + 1840*t^3 + 3024*t^2*z + 304*t^2 + 1728*t*z - 896*t - 480*z + 160:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_55 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 55) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_55 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 112*t^7 + 160*t^6*z^2 + 224*t^6*z + 160*t^6 - 256*t^5*z^3 - 336*t^5*z^2 + 384*t^5*z + 320*t^5 + 304*t^4*z^4 + 112*t^4*z^3 - 768*t^4*z^2 - 1232*t^4*z - 800*t^4 - 256*t^3*z^5 + 112*t^3*z^4 + 1472*t^3*z^3 + 320*t^3*z^2 - 1328*t^3*z + 320*t^3 + 160*t^2*z^6 - 336*t^2*z^5 - 768*t^2*z^4 + 320*t^2*z^3 + 1536*t^2*z^2 + 2112*t^2*z + 304*t^2 - 64*t*z^7 + 224*t*z^6 + 384*t*z^5 - 1232*t*z^4 - 1328*t*z^3 + 2112*t*z^2 + 1424*t*z - 688*t + 16*z^8 - 112*z^7 + 160*z^6 + 320*z^5 - 800*z^4 + 320*z^3 + 304*z^2 - 688*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 1360*t^5 - 304*t^4*z^2 - 1328*t^4*z - 4240*t^4 + 256*t^3*z^3 + 912*t^3*z^2 + 1920*t^3*z + 6448*t^3 - 160*t^2*z^4 - 304*t^2*z^3 - 288*t^2*z^2 - 1168*t^2*z - 5920*t^2 + 64*t*z^5 + 32*t*z^4 - 320*t*z^3 - 80*t*z^2 + 1328*t*z + 3280*t - 16*z^6 + 48*z^5 + 48*z^4 - 176*z^3 + 48*z^2 + 48*z - 160)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_56 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 56) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : (t + z - 4:ℝ)=0 := by
  apply cell_0_56 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z - 368*t^7 + 448*t^6*z^2 - 2576*t^6*z + 3424*t^6 + 896*t^5*z^3 - 7728*t^5*z^2 + 20688*t^5*z - 16736*t^5 + 1120*t^4*z^4 - 12880*t^4*z^3 + 51936*t^4*z^2 - 85120*t^4*z + 46528*t^4 + 896*t^3*z^5 - 12880*t^3*z^4 + 69344*t^3*z^3 - 171680*t^3*z^2 + 190432*t^3*z - 73952*t^3 + 448*t^2*z^6 - 7728*t^2*z^5 + 51936*t^2*z^4 - 171680*t^2*z^3 + 287808*t^2*z^2 - 225456*t^2*z + 63376*t^2 + 128*t*z^7 - 2576*t*z^6 + 20688*t*z^5 - 85120*t*z^4 + 190432*t*z^3 - 225456*t*z^2 + 127328*t*z - 25424*t + 16*z^8 - 368*z^7 + 3424*z^6 - 16736*z^5 + 46528*z^4 - 73952*z^3 + 63376*z^2 - 25424*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 - 896*t^5*z + 4144*t^5 - 1120*t^4*z^2 + 8400*t^4*z - 17216*t^4 - 896*t^3*z^3 + 9296*t^3*z^2 - 31264*t^3*z + 37328*t^3 - 448*t^2*z^4 + 5936*t^2*z^3 - 27744*t^2*z^2 + 54768*t^2*z - 40992*t^2 - 128*t*z^5 + 2064*t*z^4 - 12304*t*z^3 + 33840*t*z^2 - 42768*t*z + 20544*t - 16*z^6 + 304*z^5 - 2192*z^4 + 7664*z^3 - 13680*z^2 + 11568*z - 3424)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_57 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 57) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_57 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 6*t + 2*z^2 - 6*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 + 64*t^7*z - 304*t^7 + 160*t^6*z^2 - 1280*t^6*z + 2416*t^6 + 256*t^5*z^3 - 2928*t^5*z^2 + 10416*t^5*z - 10624*t^5 + 304*t^4*z^4 - 4336*t^4*z^3 + 21840*t^4*z^2 - 44560*t^4*z + 28336*t^4 + 256*t^3*z^5 - 4400*t^3*z^4 + 28432*t^3*z^3 - 83920*t^3*z^2 + 108080*t^3*z - 46288*t^3 + 160*t^2*z^6 - 3120*t^2*z^5 + 23856*t^2*z^4 - 90032*t^2*z^3 + 171312*t^2*z^2 - 147264*t^2*z + 43792*t^2 + 64*t*z^7 - 1408*t*z^6 + 12432*t*z^5 - 56096*t*z^4 + 136064*t*z^3 - 171408*t*z^2 + 100960*t*z - 20608*t + 16*z^8 - 368*z^7 + 3424*z^6 - 16736*z^5 + 46528*z^4 - 73952*z^3 + 63376*z^2 - 25424*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 1904*t^5 - 304*t^4*z^2 + 3120*t^4*z - 9056*t^4 - 256*t^3*z^3 + 3376*t^3*z^2 - 14672*t^3*z + 21856*t^3 - 160*t^2*z^4 + 2480*t^2*z^3 - 13776*t^2*z^2 + 32448*t^2*z - 27744*t^2 - 64*t*z^5 + 1152*t*z^4 - 7760*t*z^3 + 23904*t*z^2 - 32688*t*z + 16752*t - 16*z^6 + 304*z^5 - 2192*z^4 + 7664*z^3 - 13680*z^2 + 11568*z - 3424)*hf
  · have hr : (16*t^8 - 176*t^7 + 192*t^6*z^2 - 816*t^6*z + 1360*t^6 - 1584*t^5*z^2 + 6768*t^5*z - 6656*t^5 + 864*t^4*z^4 - 7344*t^4*z^3 + 25776*t^4*z^2 - 43488*t^4*z + 25552*t^4 - 4752*t^3*z^4 + 40608*t^3*z^3 - 123072*t^3*z^2 + 155856*t^3*z - 68816*t^3 + 1728*t^2*z^6 - 22032*t^2*z^5 + 117936*t^2*z^4 - 340416*t^2*z^3 + 549792*t^2*z^2 - 454320*t^2*z + 146608*t^2 - 4752*t*z^6 + 60912*t*z^5 - 309312*t*z^4 + 791856*t*z^3 - 1072944*t*z^2 + 728640*t*z - 193856*t + 1296*z^8 - 22032*z^7 + 158544*z^6 - 629856*z^5 + 1508112*z^4 - 2222640*z^3 + 1961904*z^2 - 944736*z + 189280:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6 + 1584*t^5 - 864*t^4*z^2 + 3888*t^4*z - 9360*t^4 + 4752*t^3*z^2 - 21600*t^3*z + 31920*t^3 - 1728*t^2*z^4 + 15120*t^2*z^3 - 55728*t^2*z^2 + 102384*t^2*z - 84528*t^2 + 4752*t*z^4 - 41904*t*z^3 + 136944*t*z^2 - 202176*t*z + 127296*t - 1296*z^6 + 16848*z^5 - 89856*z^4 + 253584*z^3 - 403920*z^2 + 353376*z - 144480)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_58 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 58) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_58 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 10*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z - 432*t^7 + 448*t^6*z^2 - 3024*t^6*z + 4752*t^6 + 896*t^5*z^3 - 9072*t^5*z^2 + 28656*t^5*z - 27648*t^5 + 1120*t^4*z^4 - 15120*t^4*z^3 + 71856*t^4*z^2 - 139968*t^4*z + 92304*t^4 + 896*t^3*z^5 - 15120*t^3*z^4 + 95904*t^3*z^3 - 281664*t^3*z^2 + 375696*t^3*z - 179280*t^3 + 448*t^2*z^6 - 9072*t^2*z^5 + 71856*t^2*z^4 - 281664*t^2*z^3 + 566784*t^2*z^2 - 545616*t^2*z + 195696*t^2 + 128*t*z^7 - 3024*t*z^6 + 28656*t*z^5 - 139968*t*z^4 + 375696*t*z^3 - 545616*t*z^2 + 393984*t*z - 108864*t + 16*z^8 - 432*z^7 + 4752*z^6 - 27648*z^5 + 92304*z^4 - 179280*z^3 + 195696*z^2 - 108864*z + 23328:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 - 896*t^5*z + 5488*t^5 - 1120*t^4*z^2 + 10640*t^4*z - 28176*t^4 - 896*t^3*z^3 + 11536*t^3*z^2 - 48864*t^3*z + 74672*t^3 - 448*t^2*z^4 + 7280*t^2*z^3 - 42288*t^2*z^2 + 105232*t^2*z - 103568*t^2 - 128*t*z^5 + 2512*t*z^4 - 18480*t*z^3 + 63536*t*z^2 - 103072*t*z + 69792*t - 16*z^6 + 368*z^5 - 3264*z^4 + 14224*z^3 - 32144*z^2 + 36480*z - 17632)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_59 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 59) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_59 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 12*t + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 368*t^7 + 160*t^6*z^2 - 1408*t^6*z + 3424*t^6 + 256*t^5*z^3 - 3120*t^5*z^2 + 12432*t^5*z - 16736*t^5 + 304*t^4*z^4 - 4400*t^4*z^3 + 23856*t^4*z^2 - 56096*t^4*z + 46528*t^4 + 256*t^3*z^5 - 4336*t^3*z^4 + 28432*t^3*z^3 - 90032*t^3*z^2 + 136064*t^3*z - 73952*t^3 + 160*t^2*z^6 - 2928*t^2*z^5 + 21840*t^2*z^4 - 83920*t^2*z^3 + 171312*t^2*z^2 - 171408*t^2*z + 63376*t^2 + 64*t*z^7 - 1280*t*z^6 + 10416*t*z^5 - 44560*t*z^4 + 108080*t*z^3 - 147264*t*z^2 + 100960*t*z - 25424*t + 16*z^8 - 304*z^7 + 2416*z^6 - 10624*z^5 + 28336*z^4 - 46288*z^3 + 43792*z^2 - 20608*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 2096*t^5 - 304*t^4*z^2 + 3184*t^4*z - 10816*t^4 - 256*t^3*z^3 + 3312*t^3*z^2 - 14928*t^3*z + 27008*t^3 - 160*t^2*z^4 + 2288*t^2*z^3 - 12528*t^2*z^2 + 31520*t^2*z - 32704*t^2 - 64*t*z^5 + 1024*t*z^4 - 6256*t*z^3 + 18512*t*z^2 - 27776*t*z + 17648*t - 16*z^6 + 240*z^5 - 1440*z^4 + 4624*z^3 - 8400*z^2 + 8064*z - 3136)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_60 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 60) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_60 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 240*t^7 + 160*t^6*z^2 - 960*t^6*z + 1344*t^6 + 256*t^5*z^3 - 2160*t^5*z^2 + 5472*t^5*z - 3456*t^5 + 304*t^4*z^4 - 3120*t^4*z^3 + 10944*t^4*z^2 - 14256*t^4*z + 3744*t^4 + 256*t^3*z^5 - 3120*t^3*z^4 + 13728*t^3*z^3 - 25056*t^3*z^2 + 14832*t^3*z + 160*t^2*z^6 - 2160*t^2*z^5 + 10944*t^2*z^4 - 25056*t^2*z^3 + 22464*t^2*z^2 - 3024*t^2 + 64*t*z^7 - 960*t*z^6 + 5472*t*z^5 - 14256*t*z^4 + 14832*t*z^3 - 5616*t*z + 1296*t + 16*z^8 - 240*z^7 + 1344*z^6 - 3456*z^5 + 3744*z^4 - 3024*z^2 + 1296*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 1136*t^5 - 304*t^4*z^2 + 1904*t^4*z - 3024*t^4 - 256*t^3*z^3 + 2096*t^3*z^2 - 5088*t^3*z + 2608*t^3 - 160*t^2*z^4 + 1520*t^2*z^3 - 4704*t^2*z^2 + 4720*t^2*z + 1120*t^2 - 64*t*z^5 + 704*t*z^4 - 2592*t*z^3 + 3184*t*z^2 + 496*t*z - 1200*t - 16*z^6 + 176*z^5 - 624*z^4 + 784*z^3 + 16*z^2 - 720*z + 128)*hf
  · have hr : (16*t^8 - 64*t^7*z + 16*t^7 + 160*t^6*z^2 - 224*t^6*z - 128*t^6 - 256*t^5*z^3 + 624*t^5*z^2 + 240*t^5*z - 32*t^5 + 304*t^4*z^4 - 1168*t^4*z^3 + 240*t^4*z^2 + 1088*t^4*z + 256*t^4 - 256*t^3*z^5 + 1328*t^3*z^4 - 976*t^3*z^3 - 1616*t^3*z^2 - 608*t^3*z - 32*t^3 + 160*t^2*z^6 - 1104*t^2*z^5 + 1680*t^2*z^4 + 1264*t^2*z^3 - 1776*t^2*z^2 - 1104*t^2*z + 16*t^2 - 64*t*z^7 + 544*t*z^6 - 1200*t*z^5 - 208*t*z^4 + 1456*t*z^3 + 768*t*z^2 + 1568*t*z - 272*t + 16*z^8 - 176*z^7 + 592*z^6 - 320*z^5 - 1520*z^4 + 1840*z^3 + 304*z^2 - 896*z + 160:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 400*t^5 - 304*t^4*z^2 - 48*t^4*z - 128*t^4 + 256*t^3*z^3 - 304*t^3*z^2 - 496*t^3*z - 64*t^3 - 160*t^2*z^4 + 464*t^2*z^3 + 336*t^2*z^2 - 384*t^2*z - 96*t^2 + 64*t*z^5 - 288*t*z^4 - 16*t*z^3 + 432*t*z^2 + 288*t*z - 48*t - 16*z^6 + 112*z^5 - 128*z^4 - 304*z^3 + 432*z^2 + 192*z + 32)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_61 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 61) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_61 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 112*t^7 + 160*t^6*z^2 + 224*t^6*z + 160*t^6 - 256*t^5*z^3 - 336*t^5*z^2 + 384*t^5*z + 320*t^5 + 304*t^4*z^4 + 112*t^4*z^3 - 768*t^4*z^2 - 1232*t^4*z - 800*t^4 - 256*t^3*z^5 + 112*t^3*z^4 + 1472*t^3*z^3 + 320*t^3*z^2 - 1328*t^3*z + 320*t^3 + 160*t^2*z^6 - 336*t^2*z^5 - 768*t^2*z^4 + 320*t^2*z^3 + 1536*t^2*z^2 + 2112*t^2*z + 304*t^2 - 64*t*z^7 + 224*t*z^6 + 384*t*z^5 - 1232*t*z^4 - 1328*t*z^3 + 2112*t*z^2 + 1424*t*z - 688*t + 16*z^8 - 112*z^7 + 160*z^6 + 320*z^5 - 800*z^4 + 320*z^3 + 304*z^2 - 688*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 1360*t^5 - 304*t^4*z^2 - 1328*t^4*z - 4240*t^4 + 256*t^3*z^3 + 912*t^3*z^2 + 1920*t^3*z + 6448*t^3 - 160*t^2*z^4 - 304*t^2*z^3 - 288*t^2*z^2 - 1168*t^2*z - 5920*t^2 + 64*t*z^5 + 32*t*z^4 - 320*t*z^3 - 80*t*z^2 + 1328*t*z + 3280*t - 16*z^6 + 48*z^5 + 48*z^4 - 176*z^3 + 48*z^2 + 48*z - 160)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_62 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 62) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_62 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 12*t + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 368*t^7 + 160*t^6*z^2 - 1408*t^6*z + 3424*t^6 + 256*t^5*z^3 - 3120*t^5*z^2 + 12432*t^5*z - 16736*t^5 + 304*t^4*z^4 - 4400*t^4*z^3 + 23856*t^4*z^2 - 56096*t^4*z + 46528*t^4 + 256*t^3*z^5 - 4336*t^3*z^4 + 28432*t^3*z^3 - 90032*t^3*z^2 + 136064*t^3*z - 73952*t^3 + 160*t^2*z^6 - 2928*t^2*z^5 + 21840*t^2*z^4 - 83920*t^2*z^3 + 171312*t^2*z^2 - 171408*t^2*z + 63376*t^2 + 64*t*z^7 - 1280*t*z^6 + 10416*t*z^5 - 44560*t*z^4 + 108080*t*z^3 - 147264*t*z^2 + 100960*t*z - 25424*t + 16*z^8 - 304*z^7 + 2416*z^6 - 10624*z^5 + 28336*z^4 - 46288*z^3 + 43792*z^2 - 20608*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 2096*t^5 - 304*t^4*z^2 + 3184*t^4*z - 10816*t^4 - 256*t^3*z^3 + 3312*t^3*z^2 - 14928*t^3*z + 27008*t^3 - 160*t^2*z^4 + 2288*t^2*z^3 - 12528*t^2*z^2 + 31520*t^2*z - 32704*t^2 - 64*t*z^5 + 1024*t*z^4 - 6256*t*z^3 + 18512*t*z^2 - 27776*t*z + 17648*t - 16*z^6 + 240*z^5 - 1440*z^4 + 4624*z^3 - 8400*z^2 + 8064*z - 3136)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_0_63 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z) (2) t 63) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : False := by
  apply cell_0_63 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (-48*t*z^6 + 432*t*z^5 - 864*t*z^4 - 1200*t*z^3 + 3024*t*z^2 + 1728*t*z - 480*t + 16*z^8 - 176*z^7 + 592*z^6 - 320*z^5 - 1520*z^4 + 1840*z^3 + 304*z^2 - 896*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t*z^4 - 240*t*z^3 - 144*t*z^2 + 864*t*z + 576*t - 16*z^6 + 112*z^5 - 128*z^4 - 304*z^3 + 432*z^2 + 192*z + 32)*hf


private def limit0 (z t : ℝ) : Fin 64→Prop := ![False,False,False,((t - 3:ℝ)=0),False,False,False,False,False,((t - 3:ℝ)=0),False,False,False,False,False,False,False,False,False,False,((t - 2*z:ℝ)=0),False,False,((t - 2*z:ℝ)=0),False,False,False,False,False,((t - 2*z:ℝ)=0),((t - z - 2:ℝ)=0),False,False,((t - z - 2:ℝ)=0),False,False,(((0:ℝ):ℝ)=0),False,False,((t - z - 2:ℝ)=0),False,False,False,False,False,False,False,False,False,False,((t + z - 4:ℝ)=0),((t + z - 4:ℝ)=0),False,False,False,False,((t + z - 4:ℝ)=0),False,False,False,False,False,False,False]

private def hue0 : Fin 64→Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,1,2,0,0,0,0,3,0,0,0,0,0,0,0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_3_9 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 3) (_hj : limit0 z t 9) (he : edge4 (1) (1) (1) (profile4 (z) (2) t 3) (profile4 (z) (2) t 9) (z) (2) t=0) : False := by
  apply pair_0_3_9 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (16*t^8 - 128*t^7*z + 16*t^7 + 448*t^6*z^2 - 208*t^6*z - 128*t^6 - 896*t^5*z^3 + 912*t^5*z^2 + 624*t^5*z - 32*t^5 + 1120*t^4*z^4 - 2000*t^4*z^3 - 1056*t^4*z^2 + 736*t^4*z + 256*t^4 - 896*t^3*z^5 + 2480*t^3*z^4 + 544*t^3*z^3 - 2336*t^3*z^2 - 832*t^3*z - 32*t^3 + 448*t^2*z^6 - 1776*t^2*z^5 + 384*t^2*z^4 + 2912*t^2*z^3 + 96*t^2*z^2 - 624*t^2*z + 16*t^2 - 128*t*z^7 + 688*t*z^6 - 528*t*z^5 - 1600*t*z^4 + 1280*t*z^3 + 336*t*z^2 + 1120*t*z - 272*t + 16*z^8 - 112*z^7 + 160*z^6 + 320*z^5 - 800*z^4 + 320*z^3 + 304*z^2 - 688*z + 160:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-448*t^6 + 896*t^5*z + 2672*t^5 - 1120*t^4*z^2 - 2480*t^4*z - 7744*t^4 + 896*t^3*z^3 + 1104*t^3*z^2 + 2976*t^3*z + 13136*t^3 - 448*t^2*z^4 - 16*t^2*z^3 - 2896*t^2*z - 11680*t^2 + 128*t*z^5 - 176*t*z^4 - 304*t*z^3 + 560*t*z^2 + 1264*t*z + 4160*t - 16*z^6 + 48*z^5 + 48*z^4 - 176*z^3 + 48*z^2 + 48*z - 160)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_3_23 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 3) (hj : limit0 z t 23) (_he : edge4 (1) (1) (1) (profile4 (z) (2) t 3) (profile4 (z) (2) t 23) (z) (2) t=0) : False := by
  apply pair_0_3_23 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_3_30 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 3) (hj : limit0 z t 30) (_he : edge4 (1) (1) (1) (profile4 (z) (2) t 3) (profile4 (z) (2) t 30) (z) (2) t=0) : False := by
  apply pair_0_3_30 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_3_33 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 3) (hj : limit0 z t 33) (_he : edge4 (1) (1) (1) (profile4 (z) (2) t 3) (profile4 (z) (2) t 33) (z) (2) t=0) : False := by
  apply pair_0_3_33 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_3_36 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 3) (_hj : limit0 z t 36) (he : edge4 (1) (1) (1) (profile4 (z) (2) t 3) (profile4 (z) (2) t 36) (z) (2) t=0) : False := by
  apply pair_0_3_36 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (16*t^8 + 64*t^7*z - 176*t^7 + 160*t^6*z^2 - 832*t^6*z + 784*t^6 + 256*t^5*z^3 - 1968*t^5*z^2 + 4224*t^5*z - 1904*t^5 + 304*t^4*z^4 - 3056*t^4*z^3 + 9888*t^4*z^2 - 10736*t^4*z + 2656*t^4 + 256*t^3*z^5 - 3184*t^3*z^4 + 13984*t^3*z^3 - 24944*t^3*z^2 + 14384*t^3*z - 1568*t^3 + 160*t^2*z^6 - 2352*t^2*z^5 + 12768*t^2*z^4 - 30928*t^2*z^3 + 31056*t^2*z^2 - 8544*t^2*z - 704*t^2 + 64*t*z^7 - 1088*t*z^6 + 7104*t*z^5 - 22096*t*z^4 + 31856*t*z^3 - 15360*t*z^2 - 992*t*z + 1408*t + 16*z^8 - 304*z^7 + 2224*z^6 - 7888*z^5 + 13792*z^4 - 9952*z^3 - 128*z^2 + 2432*z - 512:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-160*t^6 - 256*t^5*z + 944*t^5 - 304*t^4*z^2 + 1840*t^4*z - 2224*t^4 - 256*t^3*z^3 + 2160*t^3*z^2 - 5088*t^3*z + 2432*t^3 - 160*t^2*z^4 + 1712*t^2*z^3 - 5760*t^2*z^2 + 6176*t^2*z - 592*t^2 - 64*t*z^5 + 832*t*z^4 - 3712*t*z^3 + 6416*t*z^2 - 2480*t*z - 976*t - 16*z^6 + 240*z^5 - 1248*z^4 + 2656*z^3 - 1920*z^2 - 384*z + 512)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_9_23 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 9) (hj : limit0 z t 23) (_he : edge4 (1) (1) (1) (profile4 (z) (2) t 9) (profile4 (z) (2) t 23) (z) (2) t=0) : False := by
  apply pair_0_9_23 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_9_30 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 9) (hj : limit0 z t 30) (_he : edge4 (1) (1) (1) (profile4 (z) (2) t 9) (profile4 (z) (2) t 30) (z) (2) t=0) : False := by
  apply pair_0_9_30 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_9_33 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 9) (hj : limit0 z t 33) (_he : edge4 (1) (1) (1) (profile4 (z) (2) t 9) (profile4 (z) (2) t 33) (z) (2) t=0) : False := by
  apply pair_0_9_33 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_9_36 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 9) (_hj : limit0 z t 36) (he : edge4 (1) (1) (1) (profile4 (z) (2) t 9) (profile4 (z) (2) t 36) (z) (2) t=0) : False := by
  apply pair_0_9_36 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (-1296*t*z^6 + 12960*t*z^5 - 50544*t*z^4 + 97200*t*z^3 - 95904*t*z^2 + 45360*t*z - 7776*t + 1296*z^8 - 16848*z^7 + 93312*z^6 - 287712*z^5 + 539136*z^4 - 624672*z^3 + 431568*z^2 - 159408*z + 23328:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(1296*t*z^4 - 7776*t*z^3 + 18144*t*z^2 - 16848*t*z + 10368*t - 1296*z^6 + 11664*z^5 - 45360*z^4 + 94608*z^3 - 115344*z^2 + 68688*z - 41472)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_20_39 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 20) (hj : limit0 z t 39) (_he : edge4 (1) (1) (1) (profile4 (z) (2) t 20) (profile4 (z) (2) t 39) (z) (2) t=0) : False := by
  apply pair_0_20_39 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_20_50 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 20) (hj : limit0 z t 50) (_he : edge4 (1) (1) (1) (profile4 (z) (2) t 20) (profile4 (z) (2) t 50) (z) (2) t=0) : False := by
  apply pair_0_20_50 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_23_30 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 23) (hj : limit0 z t 30) (_he : edge4 (1) (1) (1) (profile4 (z) (2) t 23) (profile4 (z) (2) t 30) (z) (2) t=0) : False := by
  apply pair_0_23_30 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_23_33 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 23) (hj : limit0 z t 33) (_he : edge4 (1) (1) (1) (profile4 (z) (2) t 23) (profile4 (z) (2) t 33) (z) (2) t=0) : False := by
  apply pair_0_23_33 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_23_36 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 23) (_hj : limit0 z t 36) (he : edge4 (1) (1) (1) (profile4 (z) (2) t 23) (profile4 (z) (2) t 36) (z) (2) t=0) : False := by
  apply pair_0_23_36 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (16*t^8 - 64*t^7*z - 48*t^7 + 160*t^6*z^2 - 96*t^6*z + 48*t^6 - 256*t^5*z^3 + 432*t^5*z^2 + 432*t^5*z + 304*t^4*z^4 - 1104*t^4*z^3 + 432*t^4*z^2 - 432*t^4*z - 144*t^4 - 256*t^3*z^5 + 1392*t^3*z^4 - 1200*t^3*z^3 - 1296*t^3*z^2 - 144*t^3*z + 432*t^3 + 160*t^2*z^6 - 1296*t^2*z^5 + 3024*t^2*z^4 - 2160*t^2*z^3 + 1296*t^2*z^2 + 864*t^2*z - 432*t^2 - 64*t*z^7 + 672*t*z^6 - 2160*t*z^5 + 1728*t*z^4 + 1152*t*z^3 + 432*t*z^2 - 864*t*z + 16*z^8 - 240*z^7 + 1344*z^6 - 3456*z^5 + 3744*z^4 - 3024*z^2 + 1296*z:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-160*t^6 + 256*t^5*z + 592*t^5 - 304*t^4*z^2 - 112*t^4*z - 576*t^4 + 256*t^3*z^3 - 368*t^3*z^2 - 528*t^3*z - 448*t^3 - 160*t^2*z^4 + 656*t^2*z^3 - 240*t^2*z^2 + 544*t^2*z + 1120*t^2 + 64*t*z^5 - 416*t*z^4 + 432*t*z^3 + 416*t*z^2 + 80*t*z - 528*t - 16*z^6 + 176*z^5 - 624*z^4 + 784*z^3 + 16*z^2 - 720*z + 128)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_29_51 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 29) (hj : limit0 z t 51) (_he : edge4 (1) (1) (1) (profile4 (z) (2) t 29) (profile4 (z) (2) t 51) (z) (2) t=0) : False := by
  apply pair_0_29_51 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_30_33 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 30) (_hj : limit0 z t 33) (he : edge4 (1) (1) (1) (profile4 (z) (2) t 30) (profile4 (z) (2) t 33) (z) (2) t=0) : False := by
  apply pair_0_30_33 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (16*t^8 - 176*t^7 + 192*t^6*z^2 - 816*t^6*z + 1360*t^6 - 1584*t^5*z^2 + 6768*t^5*z - 6656*t^5 + 864*t^4*z^4 - 7344*t^4*z^3 + 25776*t^4*z^2 - 43488*t^4*z + 25552*t^4 - 4752*t^3*z^4 + 40608*t^3*z^3 - 123072*t^3*z^2 + 155856*t^3*z - 68816*t^3 + 1728*t^2*z^6 - 22032*t^2*z^5 + 117936*t^2*z^4 - 340416*t^2*z^3 + 549792*t^2*z^2 - 454320*t^2*z + 146608*t^2 - 4752*t*z^6 + 60912*t*z^5 - 309312*t*z^4 + 791856*t*z^3 - 1072944*t*z^2 + 728640*t*z - 193856*t + 1296*z^8 - 22032*z^7 + 158544*z^6 - 629856*z^5 + 1508112*z^4 - 2222640*z^3 + 1961904*z^2 - 944736*z + 189280:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-192*t^6 + 1584*t^5 - 864*t^4*z^2 + 3888*t^4*z - 9360*t^4 + 4752*t^3*z^2 - 21600*t^3*z + 31920*t^3 - 1728*t^2*z^4 + 15120*t^2*z^3 - 55728*t^2*z^2 + 102384*t^2*z - 84528*t^2 + 4752*t*z^4 - 41904*t*z^3 + 136944*t*z^2 - 202176*t*z + 127296*t - 1296*z^6 + 16848*z^5 - 89856*z^4 + 253584*z^3 - 403920*z^2 + 353376*z - 144480)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_30_36 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 30) (_hj : limit0 z t 36) (he : edge4 (1) (1) (1) (profile4 (z) (2) t 30) (profile4 (z) (2) t 36) (z) (2) t=0) : False := by
  apply pair_0_30_36 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (16*t^8 - 192*t^7*z + 16*t^7 + 1056*t^6*z^2 - 576*t^6*z + 256*t^6 - 3456*t^5*z^3 + 4464*t^5*z^2 - 2736*t^5*z + 256*t^5 + 7344*t^4*z^4 - 16848*t^4*z^3 + 16272*t^4*z^2 - 7104*t^4*z + 1696*t^4 - 10368*t^3*z^5 + 36720*t^3*z^4 - 54000*t^3*z^3 + 40656*t^3*z^2 - 14976*t^3*z + 1792*t^3 + 9504*t^2*z^6 - 47952*t^2*z^5 + 102384*t^2*z^4 - 118800*t^2*z^3 + 79344*t^2*z^2 - 30096*t^2*z + 4912*t^2 - 5184*t*z^7 + 35424*t*z^6 - 104976*t*z^5 + 174096*t*z^4 - 171504*t*z^3 + 97344*t*z^2 - 28128*t*z + 3472*t + 1296*z^8 - 11664*z^7 + 47088*z^6 - 111456*z^5 + 168048*z^4 - 162864*z^3 + 96528*z^2 - 30240*z + 3136:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-1056*t^6 + 3456*t^5*z + 9360*t^5 - 7344*t^4*z^2 - 12528*t^4*z - 59040*t^4 + 10368*t^3*z^3 + 4752*t^3*z^2 + 62640*t^3*z + 205152*t^3 - 9504*t^2*z^4 + 9936*t^2*z^3 - 53136*t^2*z^2 - 103680*t^2*z - 440928*t^2 + 5184*t*z^5 - 14688*t*z^4 + 41040*t*z^3 + 4752*t*z^2 + 149472*t*z + 495792*t - 1296*z^6 + 6480*z^5 - 19872*z^4 + 25488*z^3 - 46224*z^2 - 47520*z - 240384)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_33_36 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 33) (_hj : limit0 z t 36) (he : edge4 (1) (1) (1) (profile4 (z) (2) t 33) (profile4 (z) (2) t 36) (z) (2) t=0) : False := by
  apply pair_0_33_36 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (-1296*t*z^6 + 9072*t*z^5 - 20736*t*z^4 + 14256*t*z^3 + 3888*t*z^2 - 2592*t*z + 1296*z^8 - 11664*z^7 + 40176*z^6 - 64800*z^5 + 45360*z^4 - 3888*z^3 - 9072*z^2 + 2592*z:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(1296*t*z^4 - 3888*t*z^3 + 3888*t*z^2 + 5184*t*z + 12960*t - 1296*z^6 + 6480*z^5 - 12960*z^4 + 6480*z^3 - 6480*z^2 - 28512*z - 98496)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_0_39_50 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit0 z t 39) (hj : limit0 z t 50) (_he : edge4 (1) (1) (1) (profile4 (z) (2) t 39) (profile4 (z) (2) t 50) (z) (2) t=0) : False := by
  apply pair_0_39_50 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma exclude_field_0 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z)≠0) (hn2 : t-(2)≠0) (hn3 : t-((0:ℝ))≠0) (g : Fin 5→Fin 64) (hinj : Function.Injective g)
    (hc : ∀ i, cell (1) (1) (1) (profile4 (z) (2) t (g i)) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t)
    (he : ∀ i j : Fin 5, i≠j → edge4 (1) (1) (1) (profile4 (z) (2) t (g i)) (profile4 (z) (2) t (g j)) (z) (2) t=0) : False := by
  have row (k : Fin 64) (hh : cell (1) (1) (1) (profile4 (z) (2) t k) ((1),(z),(z)) ((1),(z),(2)) (z) (2) t) : limit0 z t k := by
    fin_cases k
    · exact row_0_0 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_1 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_2 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_3 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_4 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_5 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_6 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_7 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_8 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_9 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_10 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_11 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_12 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_13 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_14 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_15 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_16 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_17 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_18 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_19 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_20 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_21 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_22 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_23 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_24 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_25 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_26 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_27 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_28 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_29 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_30 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_31 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_32 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_33 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_34 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_35 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_36 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_37 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_38 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_39 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_40 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_41 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_42 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_43 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_44 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_45 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_46 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_47 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_48 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_49 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_50 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_51 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_52 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_53 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_54 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_55 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_56 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_57 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_58 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_59 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_60 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_61 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_62 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_0_63 z t hf hn0 hn1 hn2 hn3 hh
  have allowed (k : Fin 64) (hh : limit0 z t k) : k∈([3,9,20,23,29,30,33,36,39,50,51,56]:List (Fin 64)) := by
    fin_cases k <;> first | decide | exact False.elim hh
  have cert : ∀ i j : Fin 64, i∈([3,9,20,23,29,30,33,36,39,50,51,56]:List (Fin 64)) → j∈([3,9,20,23,29,30,33,36,39,50,51,56]:List (Fin 64)) → i<j → hue0 i=hue0 j → (i,j)∈([(3,9),(3,23),(3,30),(3,33),(3,36),(9,23),(9,30),(9,33),(9,36),(20,39),(20,50),(23,30),(23,33),(23,36),(29,51),(30,33),(30,36),(33,36),(39,50)]:List (Fin 64×Fin 64)) := by decide
  have bad (i j : Fin 64) (hi : limit0 z t i) (hj : limit0 z t j) (hlt : i<j) (hc : hue0 i=hue0 j) (hb : edge4 (1) (1) (1) (profile4 (z) (2) t i) (profile4 (z) (2) t j) (z) (2) t=0) : False := by
    have h := cert i j (allowed i hi) (allowed j hj) hlt hc
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact rowpair_0_3_9 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_3_23 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_3_30 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_3_33 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_3_36 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_9_23 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_9_30 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_9_33 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_9_36 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_20_39 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_20_50 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_23_30 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_23_33 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_23_36 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_29_51 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_30_33 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_30_36 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_33_36 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_0_39_50 z t hf hn0 hn1 hn2 hn3 hi hj hb
  have hi : Function.Injective (fun i : Fin 5 => hue0 (g i)) := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne (show g i≠g j from fun e => hne (hinj e)) with hl|hl
    · exact bad _ _ (row _ (hc i)) (row _ (hc j)) hl h (he i j hne)
    · exact bad _ _ (row _ (hc j)) (row _ (hc i)) hl h.symm (he j i (Ne.symm hne))
  have hh := Fintype.card_le_of_injective _ hi
  norm_num at hh

private lemma cell_1_0 (z t : ℝ) (_hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_1_1 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z^2 + 8*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-z^2/2 + 5*z/2 - 5/2)*h0 + (3 - z)*hf
  norm_num at hh

private lemma cell_1_2 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 6*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/6 - 1/2)*h0 + (-1/3)*hf
  norm_num at hh

private lemma cell_1_3 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z^2 + 192*z - 240) + t^6*(768*z^2 - 1968*z + 1344) + t^5*(-4320*z^2 + 9936*z - 4608) + t^4*(13536*z^2 - 29664*z + 11376) + t^3*(-23184*z^2 + 50112*z - 18144) + t^2*(19872*z^2 - 43200*z + 15552) + t*(-6480*z^2 + 14256*z - 5184):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(z^2/162 - 5*z/162 + 2/81) + t^5*(-2*z^2/81 + 4*z/27 - 4/27) + t^4*(-z^2/54 - 7*z/54 + 13/54) + t^3*(z^2/3 - 2*z/3 + 1/9) + t^2*(-5*z^2/6 + 35*z/18 - 7/9) + t*(8*z^2/9 - 13*z/6 + 5/6) - z^2/3 + 5*z/6 - 1/2)*h0 + (-z^2/1296 + 5*z/1296 - 1/324)*h1 + (-4*t^7*z/81 + 8*t^7/81 + 16*t^6*z/27 - 25*t^6/27 - 10*t^5*z/3 + 13*t^5/3 + 94*t^4*z/9 - 112*t^4/9 - 161*t^3*z/9 + 187*t^3/9 + 46*t^2*z/3 - 18*t^2 - 5*t*z + 6*t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_1_4 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z^2 + 8*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-z^2/2 + 5*z/2 - 5/2)*h0 + (3 - z)*hf
  norm_num at hh

private lemma cell_1_5 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^2/2 - 5*z/2 + 2)*h0 + (1)*hf
  norm_num at hh

private lemma cell_1_6 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h1 : (t*(-1296*z^2 + 9072*z - 3888):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (13*z^2/3888 - z/54 + 7/324)*h1 + (13*t*z/3 - 85*t/3)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_1_7 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z^2 - 10*z) - 4*z^2 + 18*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 48) + t^6*(496*z^2 + 48) + t^5*(-6240*z^2 + 11232*z - 3696) + t^4*(29952*z^2 - 66336*z + 24048) + t^3*(-68496*z^2 + 153504*z - 56880) + t^2*(78768*z^2 - 165024*z + 60192) + t*(-47088*z^2 + 97776*z - 35424) + 10512*z^2 - 22464*z + 8208:ℝ)=0) : (t + z^2 - 4*z:ℝ)=0 := by
  have hh : (t + z^2 - 4*z:ℝ)=0 := by linear_combination (t^6*(11*z^2/162 - 61*z/162 + 71/162) + t^5*(-25*z^2/81 + 31*z/18 - 109/54) + t^4*(-5*z^2/54 + 11*z/27 - 7/18) + t^3*(29*z^2/27 - 148*z/27 + 335/54) + t^2*(-7*z^2/54 - 5*z/9 + 7/6) + t*(z^2/18 + 25*z/18 - 8/3) - 7*z^2/18 + 3*z/2 - 31/18)*h0 + (-11*z^2/1296 + 61*z/1296 - 71/1296)*h1 + (-11*t^7*z/81 - 38*t^7/81 + 413*t^6*z/81 - 163*t^6/81 - 4375*t^5*z/81 + 227*t^5/3 + 6796*t^4*z/27 - 11815*t^4/27 - 15574*t^3*z/27 + 27662*t^3/27 + 18034*t^2*z/27 - 3308*t^2/3 - 1196*t*z/3 + 5867*t/9 + 263*z/3 - 1318/9)*hf
  exact hh

private lemma cell_1_8 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 6*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/6 - 1/2)*h0 + (-1/3)*hf
  norm_num at hh

private lemma cell_1_9 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h2 : (t*(-1296*z^2 + 9072*z - 3888):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (13*z^2/3888 - z/54 + 7/324)*h2 + (13*t*z/3 - 85*t/3)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_1_10 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 8*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 1)*h0 + (-1)*hf
  norm_num at hh

private lemma cell_1_11 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 2*z^2 - 4*z + 2:ℝ)=0) (h2 : (16*t^8 + t^7*(128*z^2 - 640*z + 208) + t^6*(-2032*z^2 + 9664*z - 4112) + t^5*(14448*z^2 - 65712*z + 27856) + t^4*(-55552*z^2 + 244496*z - 102272) + t^3*(116432*z^2 - 502832*z + 209488) + t^2*(-126480*z^2 + 545088*z - 227312) + t*(63488*z^2 - 275680*z + 115168) - 9856*z^2 + 43456*z - 18176:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(74*z^2/729 - 91*z/162 + 211/324) + t^6*(-1127*z^2/2916 + 347*z/162 - 2419/972) + t^5*(-289*z^2/972 + 521*z/324 - 193/108) + t^4*(5375*z^2/2916 - 3239*z/324 + 299/27) + t^3*(-1757*z^2/2916 + 851*z/324 - 1051/972) + t^2*(-587*z^2/972 + 1579*z/324 - 59/6) + t*(-970*z^2/729 + 463*z/81 - 341/162) + 829*z^2/729 - 295*z/54 + 1007/243)*h0 + (t*(-37*z^2/2916 + 91*z/1296 - 211/2592) + 689*z^2/23328 - 1271*z/7776 + 737/3888)*h2 + (1184*t^8*z/729 - 580*t^8/81 - 21700*t^7*z/729 + 61859*t^7/486 + 177959*t^6*z/729 - 81614*t^6/81 - 824506*t^5*z/729 + 40667*t^5/9 + 4540825*t^4*z/1458 - 5902123*t^4/486 - 3675988*t^3*z/729 + 1572674*t^3/81 + 3311417*t^2*z/729 - 1416605*t^2/81 - 1456204*t*z/729 + 1886473*t/243 + 210554*z/729 - 30943/27)*hf
  norm_num at hh

private lemma cell_1_12 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(128*z^2 - 576*z + 144) + t^6*(-1872*z^2 + 8304*z - 3360) + t^5*(11520*z^2 - 50544*z + 21312) + t^4*(-37008*z^2 + 161280*z - 67680) + t^3*(63216*z^2 - 274320*z + 114480) + t^2*(-54000*z^2 + 233280*z - 97200) + t*(18144*z^2 - 77760*z + 32400):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(z^2/162 - z/54 + 1/81) + t^5*(-4*z^2/81 + 4*z/27 - 2/27) + t^4*(2*z^2/9 - 41*z/54 + 8/27) + t^3*(-13*z^2/18 + 26*z/9 - 7/6) + t^2*(4*z^2/3 - 53*z/9 + 22/9) + t*(-19*z^2/18 + 16*z/3 - 7/3) + z^2/6 - 3*z/2 + 1/2)*h0 + (-z^2/1296 + z/432 - 1/648)*h1 + (8*t^7*z/81 - 4*t^7/27 - 13*t^6*z/9 + 56*t^6/27 + 80*t^5*z/9 - 37*t^5/3 - 257*t^4*z/9 + 349*t^4/9 + 439*t^3*z/9 - 196*t^3/3 - 125*t^2*z/3 + 55*t^2 + 14*t*z - 18*t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_1_13 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z^2 - 10*z) - 4*z^2 + 18*z - 6:ℝ)=0) (h2 : (16*t^8 + t^7*(-128*z - 48) + t^6*(496*z^2 + 48) + t^5*(-6240*z^2 + 11232*z - 3696) + t^4*(29952*z^2 - 66336*z + 24048) + t^3*(-68496*z^2 + 153504*z - 56880) + t^2*(78768*z^2 - 165024*z + 60192) + t*(-47088*z^2 + 97776*z - 35424) + 10512*z^2 - 22464*z + 8208:ℝ)=0) : (t + z^2 - 4*z:ℝ)=0 := by
  have hh : (t + z^2 - 4*z:ℝ)=0 := by linear_combination (t^6*(11*z^2/162 - 61*z/162 + 71/162) + t^5*(-25*z^2/81 + 31*z/18 - 109/54) + t^4*(-5*z^2/54 + 11*z/27 - 7/18) + t^3*(29*z^2/27 - 148*z/27 + 335/54) + t^2*(-7*z^2/54 - 5*z/9 + 7/6) + t*(z^2/18 + 25*z/18 - 8/3) - 7*z^2/18 + 3*z/2 - 31/18)*h0 + (-11*z^2/1296 + 61*z/1296 - 71/1296)*h2 + (-11*t^7*z/81 - 38*t^7/81 + 413*t^6*z/81 - 163*t^6/81 - 4375*t^5*z/81 + 227*t^5/3 + 6796*t^4*z/27 - 11815*t^4/27 - 15574*t^3*z/27 + 27662*t^3/27 + 18034*t^2*z/27 - 3308*t^2/3 - 1196*t*z/3 + 5867*t/9 + 263*z/3 - 1318/9)*hf
  exact hh

private lemma cell_1_14 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(128*z^2 - 640*z + 208) + t^6*(-2032*z^2 + 9664*z - 4112) + t^5*(14448*z^2 - 65712*z + 27856) + t^4*(-55552*z^2 + 244496*z - 102272) + t^3*(116432*z^2 - 502832*z + 209488) + t^2*(-126480*z^2 + 545088*z - 227312) + t*(63488*z^2 - 275680*z + 115168) - 9856*z^2 + 43456*z - 18176:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(74*z^2/729 - 91*z/162 + 211/324) + t^6*(-1127*z^2/2916 + 347*z/162 - 2419/972) + t^5*(-289*z^2/972 + 521*z/324 - 193/108) + t^4*(5375*z^2/2916 - 3239*z/324 + 299/27) + t^3*(-1757*z^2/2916 + 851*z/324 - 1051/972) + t^2*(-587*z^2/972 + 1579*z/324 - 59/6) + t*(-970*z^2/729 + 463*z/81 - 341/162) + 829*z^2/729 - 295*z/54 + 1007/243)*h0 + (t*(-37*z^2/2916 + 91*z/1296 - 211/2592) + 689*z^2/23328 - 1271*z/7776 + 737/3888)*h1 + (1184*t^8*z/729 - 580*t^8/81 - 21700*t^7*z/729 + 61859*t^7/486 + 177959*t^6*z/729 - 81614*t^6/81 - 824506*t^5*z/729 + 40667*t^5/9 + 4540825*t^4*z/1458 - 5902123*t^4/486 - 3675988*t^3*z/729 + 1572674*t^3/81 + 3311417*t^2*z/729 - 1416605*t^2/81 - 1456204*t*z/729 + 1886473*t/243 + 210554*z/729 - 30943/27)*hf
  norm_num at hh

private lemma cell_1_15 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z^2 - 384*z + 80) + t^6*(-704*z^2 + 4512*z - 1904) + t^5*(3072*z^2 - 21888*z + 9824) + t^4*(-6688*z^2 + 55824*z - 24896) + t^3*(7136*z^2 - 76224*z + 33920) + t^2*(-2112*z^2 + 46800*z - 21296) + t*(-2432*z^2 - 816*z + 944) + 1792*z^2 - 8160*z + 3424:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(23*z^2/486 - 64*z/243 + 25/81) + t^6*(-109*z^2/486 + 619*z/486 - 125/81) + t^5*(-2*z^2/27 + 23*z/162 + 1/3) + t^4*(685*z^2/486 - 1634*z/243 + 491/81) + t^3*(-388*z^2/243 + 1603*z/243 - 779/162) + t^2*(4*z^2/27 + 124*z/81 - 32/9) + t*(41*z^2/486 - 737*z/486 + 133/81) + 31*z^2/243 - 151*z/243 + 137/162)*h0 + (t*(-23*z^2/3888 + 8*z/243 - 25/648) + 11*z^2/486 - 487*z/3888 + 47/324)*h1 + (92*t^8*z/243 - 512*t^8/243 - 1364*t^7*z/243 + 7994*t^7/243 + 8288*t^6*z/243 - 52556*t^6/243 - 26510*t^5*z/243 + 188579*t^5/243 + 47042*t^4*z/243 - 395006*t^4/243 - 42284*t^3*z/243 + 466901*t^3/243 + 8120*t^2*z/243 - 254681*t^2/243 + 15952*t*z/243 + 110*t/243 - 9856*z/243 + 40288/243)*hf
  norm_num at hh

private lemma cell_1_16 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z^2 + 8*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-z^2/2 + 5*z/2 - 5/2)*h0 + (3 - z)*hf
  norm_num at hh

private lemma cell_1_17 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^2/2 - 5*z/2 + 2)*h0 + (1)*hf
  norm_num at hh

private lemma cell_1_18 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(36288*z^2 - 158112*z + 66096) - 233280*z^2 + 1014768*z - 423792:ℝ)=0) (h2 : (t*(3888*z^2 - 34992*z + 15552) - 11664*z^2 + 163296*z - 73872:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-89*z^2/3888 + 41*z/324 - 95/648)*h1 + (173*z^2/3888 - 319*z/1296 + 1109/3888)*h2 + (1973*t*z/3 - 5254*t/3 - 4821*z + 13686)*hf
  norm_num at hh

private lemma cell_1_19 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z^2 - 10*z) - 4*z^2 + 18*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 48) + t^6*(112*z^2 + 1728*z - 528) + t^5*(-1920*z^2 - 9936*z + 4512) + t^4*(8784*z^2 + 51168*z - 25200) + t^3*(-12192*z^2 - 216288*z + 103392) + t^2*(-61632*z^2 + 756432*z - 340272) + t*(244512*z^2 - 1548144*z + 670896) - 398592*z^2 + 1933200*z - 817344:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-3881*z^2/49572 + 199*z/459 - 24919/49572) + t^6*(25081*z^2/49572 - 139415*z/49572 + 17989/5508) + t^5*(-7151*z^2/5508 + 13493*z/1836 - 71045/8262) + t^4*(10837*z^2/5508 - 99089*z/8262 + 59663/4131) + t^3*(-1727*z^2/1377 + 46213*z/4131 - 27617/1836) + t^2*(-2387*z^2/1836 - 988*z/459 + 9694/1377) + t*(7681*z^2/2754 - 25247*z/5508 + 301/2754) - 593*z^2/324 + 1625*z/324 - 127/36)*h0 + (t*(3881*z^2/396576 - 199*z/3672 + 24919/396576) - 1217*z^2/66096 + 20203*z/198288 - 15611/132192)*h1 + (3881*t^8*z/24786 + 1493*t^8/2754 - 1765*t^7*z/729 - 344447*t^7/24786 + 631355*t^6*z/24786 + 489050*t^6/4131 - 179620*t^5*z/1377 - 2884510*t^5/4131 + 1203893*t^4*z/4131 + 8629247*t^4/2754 + 1036177*t^3*z/2754 - 15376756*t^3/1377 - 4872439*t^2*z/1377 + 4443691*t^2/162 + 2575801*t*z/306 - 119878999*t/2754 - 10116049*z/1377 + 29542183/918)*hf
  norm_num at hh

private lemma cell_1_20 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^2/2 - 5*z/2 + 2)*h0 + (1)*hf
  norm_num at hh

private lemma cell_1_21 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z^2 - 30*z + 14:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (15*z^2/74 - 42*z/37 + 47/37)*h0 + (207/37 - 45*z/37)*hf
  norm_num at hh

private lemma cell_1_22 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 12*z + 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^2/3 - 11*z/6 + 2)*h0 + (11/3 - 2*z/3)*hf
  norm_num at hh

private lemma cell_1_23 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(4*z^2 - 20*z + 6) - 4*z^2 + 18*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z^2 - 448*z + 144) + t^6*(-416*z^2 + 4848*z - 2208) + t^5*(-1248*z^2 - 21456*z + 10464) + t^4*(23424*z^2 + 37920*z - 22896) + t^3*(-108336*z^2 + 34560*z + 7488) + t^2*(243360*z^2 - 260928*z + 68832) + t*(-272016*z^2 + 404208*z - 129600) + 120672*z^2 - 213408*z + 73440:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-367*z^2/8262 + 677*z/2754 - 2357/8262) + t^6*(536*z^2/4131 - 2972*z/4131 + 43/51) + t^5*(461*z^2/2754 - 2521*z/2754 + 887/918) + t^4*(-776*z^2/1377 + 8521*z/2754 - 4223/1377) + t^3*(229*z^2/918 - 3851*z/2754 - 49/918) + t^2*(-242*z^2/459 + 52*z/17 - 19/51) + t*(436*z^2/459 - 4985*z/918 + 1418/459) - 103*z^2/918 + 623*z/918 + 7/17)*h0 + (t*(367*z^2/66096 - 677*z/22032 + 2357/66096) - 89*z^2/16524 + 989*z/33048 - 193/5508)*h1 + (-734*t^8*z/4131 + 232*t^8/153 + 2696*t^7*z/1377 - 34462*t^7/1377 + 18748*t^6*z/4131 + 204311*t^6/1377 - 61442*t^5*z/459 - 554215*t^5/1377 + 36947*t^4*z/51 + 166255*t^4/459 - 2659904*t^3*z/1377 + 112019*t^3/153 + 1292191*t^2*z/459 - 357604*t^2/153 - 978080*t*z/459 + 7144*t/3 + 99374*z/153 - 131417/153)*hf
  norm_num at hh

private lemma cell_1_24 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(3888*z^2 - 34992*z + 15552) - 11664*z^2 + 163296*z - 73872:ℝ)=0) (h2 : (t*(36288*z^2 - 158112*z + 66096) - 233280*z^2 + 1014768*z - 423792:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (173*z^2/3888 - 319*z/1296 + 1109/3888)*h1 + (-89*z^2/3888 + 41*z/324 - 95/648)*h2 + (1973*t*z/3 - 5254*t/3 - 4821*z + 13686)*hf
  norm_num at hh

private lemma cell_1_25 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 12*z + 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^2/3 - 11*z/6 + 2)*h0 + (11/3 - 2*z/3)*hf
  norm_num at hh

private lemma cell_1_26 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z^2 - 11*z + 25/2)*h0 + (8)*hf
  norm_num at hh

private lemma cell_1_27 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z^2 - 12*z + 2) - 2*z^2 + 12*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 192*z) + t^6*(720*z^2 + 912*z - 512) + t^5*(-11808*z^2 + 9360*z - 1760) + t^4*(84528*z^2 - 111072*z + 33376) + t^3*(-331632*z^2 + 495120*z - 158960) + t^2*(728496*z^2 - 1103616*z + 356848) + t*(-827136*z^2 + 1161888*z - 362576) + 349056*z^2 - 324096*z + 75232:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-7652*z^2/2187 + 9407*z/486 - 32707/1458) + t^6*(30461*z^2/2187 - 37447*z/486 + 65099/729) + t^5*(-5143*z^2/729 + 2107*z/54 - 10987/243) + t^4*(-51577*z^2/4374 + 31739*z/486 - 110425/1458) + t^3*(26150*z^2/2187 - 32299*z/486 + 112603/1458) + t^2*(-21979*z^2/1458 + 757*z/9 - 47623/486) + t*(1486*z^2/2187 - 2221*z/486 + 4363/729) + 11761*z^2/4374 - 7069*z/486 + 23851/1458)*h0 + (t*(1913*z^2/4374 - 9407*z/3888 + 32707/11664) - 14605*z^2/34992 + 6733*z/2916 - 31213/11664)*h1 + (15304*t^8*z/2187 + 32995*t^8/729 - 764906*t^7*z/2187 - 316049*t^7/729 + 12043357*t^6*z/2187 - 1011899*t^6/729 - 91608803*t^5*z/2187 + 23931418*t^5/729 + 394260346*t^4*z/2187 - 129954593*t^4/729 - 999406022*t^3*z/2187 + 346402009*t^3/729 + 1456066930*t^2*z/2187 - 478999517*t^2/729 - 1088900933*t*z/2187 + 287037502*t/729 + 318634441*z/2187 - 48937319/729)*hf
  norm_num at hh

private lemma cell_1_28 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z^2 - 10*z) - 4*z^2 + 18*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(192*z^2 - 896*z + 336) + t^6*(-3680*z^2 + 16608*z - 6960) + t^5*(36384*z^2 - 161424*z + 67584) + t^4*(-220032*z^2 + 968592*z - 405072) + t^3*(842880*z^2 - 3695472*z + 1544688) + t^2*(-2002176*z^2 + 8760096*z - 3660624) + t*(2695680*z^2 - 11781792*z + 4922640) - 1570176*z^2 + 6862320*z - 2867184:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-109*z^2/243 + 3619*z/1458 - 1399/486) + t^6*(685*z^2/729 - 47*z/9 + 991/162) + t^5*(142*z^2/243 - 1399*z/486 + 385/162) + t^4*(-1369*z^2/486 + 6169*z/486 - 371/54) + t^3*(3055*z^2/243 - 8981*z/162 + 2101/81) + t^2*(-5927*z^2/162 + 13058*z/81 - 4049/54) + t*(4535*z^2/81 - 39437*z/162 + 5515/54) - 6151*z^2/162 + 4456*z/27 - 3737/54)*h0 + (t*(109*z^2/1944 - 3619*z/11664 + 1399/3888) - 275*z^2/2916 + 2029*z/3888 - 2353/3888)*h1 + (-2398*t^8*z/243 + 29999*t^8/729 + 160942*t^7*z/729 - 72514*t^7/81 - 579436*t^6*z/243 + 2306891*t^6/243 + 1277891*t^5*z/81 - 15116138*t^5/243 - 16535488*t^4*z/243 + 21623126*t^4/81 + 15541883*t^3*z/81 - 60803297*t^3/81 - 9186068*t^2*z/27 + 1328998*t^2 + 9249169*t*z/27 - 4011457*t/3 - 1334078*z/9 + 1735621/3)*hf
  norm_num at hh

private lemma cell_1_29 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(4*z^2 - 20*z + 6) - 4*z^2 + 18*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(256*z^2 - 1216*z + 528) + t^6*(-5744*z^2 + 25872*z - 10944) + t^5*(67296*z^2 - 296784*z + 124080) + t^4*(-464736*z^2 + 2032608*z - 849168) + t^3*(1952448*z^2 - 8509104*z + 3554064) + t^2*(-4900464*z^2 + 21323520*z - 8904672) + t*(6742800*z^2 - 29319984*z + 12242880) - 3905568*z^2 + 16978032*z - 7089120:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(z^2/81 - 11*z/162 + 19/243) + t^6*(z^2/27 - 52*z/243 + 43/162) + t^5*(2*z^2/27 - 8*z/27 + 11/162) + t^4*(-76*z^2/81 + 695*z/162 - 208/81) + t^3*(97*z^2/27 - 1253*z/81 + 157/27) + t^2*(-32*z^2/3 + 1252*z/27 - 1015/54) + t*(454*z^2/27 - 1988*z/27 + 1721/54) - 92*z^2/9 + 1196*z/27 - 107/6)*h0 + (t*(-z^2/648 + 11*z/1296 - 19/1944) - z^2/486 + 11*z/972 - 17/1296)*h1 + (28*t^8*z/81 - 118*t^8/81 - 2050*t^7*z/243 + 2735*t^7/81 + 22328*t^6*z/243 - 29038*t^6/81 - 1724*t^5*z/3 + 180028*t^5/81 + 6116*t^4*z/3 - 636788*t^4/81 - 282530*t^3*z/81 + 120983*t^3/9 + 5734*t^2*z/27 - 7753*t^2/9 + 71596*t*z/9 - 824444*t/27 - 218080*z/27 + 31032)*hf
  norm_num at hh

private lemma cell_1_30 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z^2 - 12*z + 2) - 2*z^2 + 12*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(192*z^2 - 960*z + 400) + t^6*(-3840*z^2 + 18096*z - 7712) + t^5*(40464*z^2 - 183456*z + 77008) + t^4*(-255120*z^2 + 1131024*z - 473264) + t^3*(988752*z^2 - 4331136*z + 1810096) + t^2*(-2312784*z^2 + 10075824*z - 4208240) + t*(2998128*z^2 - 13036416*z + 5443456) - 1652784*z^2 + 7183680*z - 2999456:ℝ)=0) (h2 : (16*t^8 + t^7*(16 - 192*z) + t^6*(720*z^2 + 912*z - 512) + t^5*(-11808*z^2 + 9360*z - 1760) + t^4*(84528*z^2 - 111072*z + 33376) + t^3*(-331632*z^2 + 495120*z - 158960) + t^2*(728496*z^2 - 1103616*z + 356848) + t*(-827136*z^2 + 1161888*z - 362576) + 349056*z^2 - 324096*z + 75232:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(-8329*z^2/13122 + 69115*z/19683 - 53401/13122) + t^12*(8011*z^2/4374 - 199420*z/19683 + 51359/4374) + t^11*(9092*z^2/2187 - 50324*z/2187 + 38891/1458) + t^10*(-139769*z^2/13122 + 1163414*z/19683 - 900083/13122) + t^9*(-40181*z^2/4374 + 964972*z/19683 - 122326/2187) + t^8*(12985*z^2/729 - 126205*z/1458 + 2549/27) + t^7*(-54467*z^2/4374 + 175147*z/13122 + 52255/4374) + t^6*(83045*z^2/1458 - 889232*z/6561 + 49898/729) + t^5*(-80650*z^2/729 + 17218*z/81 - 11962/243) + t^4*(1107224*z^2/6561 - 13534601*z/39366 + 705419/6561) + t^3*(-697069*z^2/4374 + 13680371*z/39366 - 305101/2187) + t^2*(140038*z^2/2187 - 243844*z/2187 + 14467/1458) + t*(-27961*z^2/13122 - 78157*z/39366 + 116339/13122) - 17965*z^2/4374 + 71282*z/19683 + 10876/2187)*h0 + (t^7*(8329*z^2/104976 - 69115*z/157464 + 53401/104976) + t^6*(-11179*z^2/34992 + 556577*z/314928 - 215015/104976) + t^5*(4489*z^2/26244 - 99271*z/104976 + 355/324) + t^4*(14155*z^2/52488 - 471389*z/314928 + 91181/52488) + t^3*(-14497*z^2/52488 + 244111*z/157464 - 189767/104976) + t^2*(17563*z^2/52488 - 200249*z/104976 + 544/243) + t*(-151*z^2/11664 + 22997*z/157464 - 10813/52488) - 2077*z^2/26244 + 125543*z/314928 - 46469/104976)*h1 + (-311*z^2/1944 + 1147*z/1296 - 997/972)*h2 + (-91619*t^14*z/6561 + 1220686*t^14/19683 + 2369042*t^13*z/6561 - 30388739*t^13/19683 - 9786304*t^12*z/2187 + 362855887*t^12/19683 + 221785019*t^11*z/6561 - 2667819808*t^11/19683 - 1087742300*t^10*z/6561 + 12864725849*t^10/19683 + 43005095*t^9*z/81 - 40794409495*t^9/19683 - 2328169099*t^8*z/2187 + 27103182314*t^8/6561 + 2479469854*t^7*z/2187 - 28676766790*t^7/6561 - 42286823*t^6*z/729 + 992199695*t^6/6561 - 9828429457*t^5*z/6561 + 117407125070*t^5/19683 + 13479344986*t^4*z/6561 - 161860272154*t^4/19683 - 3203706584*t^3*z/2187 + 117032888915*t^3/19683 + 3447736882*t^2*z/6561 - 41593053548*t^2/19683 + 548237933*t*z/6561 - 9315479174*t/19683 - 6072643*z/81 + 8204927929/19683)*hf
  norm_num at hh

private lemma cell_1_31 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(4*z^2 - 20*z + 4) - 6*z^2 + 28*z - 10:ℝ)=0) (h1 : (16*t^8 + t^7*(192*z^2 - 1024*z + 464) + t^6*(-3680*z^2 + 18944*z - 8144) + t^5*(39744*z^2 - 198192*z + 83936) + t^4*(-260064*z^2 + 1261072*z - 532976) + t^3*(1047008*z^2 - 4954160*z + 2088944) + t^2*(-2530080*z^2 + 11725728*z - 4932752) + t*(3353856*z^2 - 15282208*z + 6416432) - 1867904*z^2 + 8397872*z - 3520496:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-2689*z^2/972 + 3719*z/243 - 5747/324) + t^6*(-2965*z^2/486 + 16399*z/486 - 12667/324) + t^5*(1259*z^2/108 - 20861*z/324 + 4021/54) + t^4*(5503*z^2/243 - 61255*z/486 + 11930/81) + t^3*(-12547*z^2/972 + 36239*z/486 - 14863/162) + t^2*(-220*z^2/9 + 41377*z/324 - 14527/108) + t*(2816*z^2/243 - 26501*z/486 + 7289/162) - 2711*z^2/972 + 2522*z/243 - 661/324)*h0 + (t*(2689*z^2/7776 - 3719*z/1944 + 5747/2592) - 4621*z^2/7776 + 6391*z/1944 - 823/216)*h1 + (-13445*t^8*z/243 + 66313*t^8/243 + 225905*t^7*z/162 - 1592050*t^7/243 - 3891379*t^6*z/243 + 35334953*t^6/486 + 55175539*t^5*z/486 - 243302729*t^5/486 - 41830231*t^4*z/81 + 539480188*t^4/243 + 727610447*t^3*z/486 - 3061107497*t^3/486 - 647234981*t^2*z/243 + 5349689741*t^2/486 + 213766561*t*z/81 - 5225135021*t/486 - 539482157*z/486 + 2173029299/486)*hf
  norm_num at hh

private lemma cell_1_32 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 6*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/6 - 1/2)*h0 + (-1/3)*hf
  norm_num at hh

private lemma cell_1_33 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(3888*z^2 - 34992*z + 15552) - 11664*z^2 + 163296*z - 73872:ℝ)=0) (h2 : (t*(-33696*z^2 + 73872*z - 27216) + 270864*z^2 - 575424*z + 209952:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-157*z^2/5832 + 193*z/1296 - 671/3888)*h1 + (-113*z^2/3888 + 625*z/3888 - 181/972)*h2 + (-2624*t*z/3 + 2384*t/3 + 22675*z/3 - 26348/3)*hf
  norm_num at hh

private lemma cell_1_34 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 8*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 1)*h0 + (-1)*hf
  norm_num at hh

private lemma cell_1_35 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z^2 + 128*z - 176) + t^6*(1376*z^2 - 2720*z + 1360) + t^5*(-15360*z^2 + 31632*z - 12032) + t^4*(104960*z^2 - 220432*z + 80656) + t^3*(-462208*z^2 + 977776*z - 356432) + t^2*(1293504*z^2 - 2743008*z + 1000144) + t*(-2109952*z^2 + 4477376*z - 1632944) + 1538240*z^2 - 3266384*z + 1191568:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-5*z^2/81 + 83*z/243 - 289/729) + t^6*(727*z^2/1458 - 2008*z/729 + 2329/729) + t^5*(-719*z^2/486 + 3935*z/486 - 4549/486) + t^4*(581*z^2/243 - 2003*z/162 + 20347/1458) + t^3*(-2278*z^2/729 + 17917*z/1458 - 17299/1458) + t^2*(2639*z^2/486 - 2992*z/243 + 2719/486) + t*(-2429*z^2/243 + 9365*z/486 - 3310/729) + 13423*z^2/1458 - 26627*z/1458 + 7115/1458)*h0 + (t*(5*z^2/648 - 83*z/1944 + 289/5832) - 215*z^2/11664 + 595*z/5832 - 691/5832)*h1 + (40*t^8*z/81 - 214*t^8/243 - 8510*t^7*z/729 + 13597*t^7/729 + 34721*t^6*z/243 - 166609*t^6/729 - 264881*t^5*z/243 + 431258*t^5/243 + 4006834*t^4*z/729 - 6593222*t^4/729 - 1498036*t^3*z/81 + 22292261*t^3/729 + 9747341*t^2*z/243 - 16149892*t^2/243 - 36990506*t*z/729 + 61356694*t/729 + 6885559*z/243 - 34305100/729)*hf
  norm_num at hh

private lemma cell_1_36 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(-33696*z^2 + 73872*z - 27216) + 270864*z^2 - 575424*z + 209952:ℝ)=0) (h2 : (t*(3888*z^2 - 34992*z + 15552) - 11664*z^2 + 163296*z - 73872:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-113*z^2/3888 + 625*z/3888 - 181/972)*h1 + (-157*z^2/5832 + 193*z/1296 - 671/3888)*h2 + (-2624*t*z/3 + 2384*t/3 + 22675*z/3 - 26348/3)*hf
  norm_num at hh

private lemma cell_1_37 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 12*z + 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^2/3 - 11*z/6 + 2)*h0 + (11/3 - 2*z/3)*hf
  norm_num at hh

private lemma cell_1_38 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z^2 - 11*z + 25/2)*h0 + (8)*hf
  norm_num at hh

private lemma cell_1_39 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z^2 - 12*z + 2) - 2*z^2 + 12*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 192*z) + t^6*(1104*z^2 - 624*z + 64) + t^5*(-18432*z^2 + 34128*z - 11696) + t^4*(138240*z^2 - 290496*z + 105520) + t^3*(-597216*z^2 + 1274928*z - 465968) + t^2*(1555920*z^2 - 3306528*z + 1206592) + t*(-2281392*z^2 + 4838352*z - 1764416) + 1438944*z^2 - 3051120*z + 1112608:ℝ)=0) (h2 : (16*t^8 + t^7*(192*z^2 - 960*z + 400) + t^6*(-3648*z^2 + 17520*z - 7520) + t^5*(35424*z^2 - 166608*z + 70240) + t^4*(-201696*z^2 + 941376*z - 396080) + t^3*(687696*z^2 - 3213696*z + 1353088) + t^2*(-1367712*z^2 + 6459552*z - 2723168) + t*(1439184*z^2 - 6969840*z + 2946208) - 597216*z^2 + 3060960*z - 1301504:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(9031*z^2/118098 - 5551*z/13122 + 6433/13122) + t^12*(-26107*z^2/118098 + 48121*z/39366 - 18571/13122) + t^11*(-37061*z^2/39366 + 3805*z/729 - 79781/13122) + t^10*(125818*z^2/59049 - 156451*z/13122 + 62051/4374) + t^9*(339608*z^2/59049 - 606395*z/19683 + 216259/6561) + t^8*(-153901*z^2/13122 + 262723*z/4374 - 123572/2187) + t^7*(-12530*z^2/19683 + 39362*z/2187 - 131776/2187) + t^6*(-219280*z^2/19683 + 242947*z/6561 + 17551/729) + t^5*(356257*z^2/13122 - 300280*z/2187 + 270785/2187) + t^4*(2642501*z^2/118098 - 1230725*z/13122 + 182431/6561) + t^3*(-6647507*z^2/118098 + 4996309*z/19683 - 1825433/13122) + t^2*(1071701*z^2/39366 - 512003*z/4374 + 305746/6561) + t*(-300811*z^2/59049 + 130550*z/6561 - 3653/1458) + 289246*z^2/59049 - 419260*z/19683 + 62999/6561)*h0 + (t^7*(-9031*z^2/944784 + 5551*z/104976 - 6433/104976) + t^6*(-1235*z^2/944784 + 2293*z/314928 - 25/2916) + t^5*(5575*z^2/78732 - 20599*z/52488 + 23977/52488) + t^4*(22655*z^2/944784 - 6673*z/52488 + 13891/104976) + t^3*(-143921*z^2/944784 + 128993*z/157464 - 92947/104976) + t^2*(475*z^2/39366 - 1111*z/104976 - 14753/104976) + t*(-7819*z^2/944784 - 2537*z/104976 + 7639/34992) + 34321*z^2/944784 - 26149*z/157464 + 10237/104976)*h1 + (-113*z^2/3888 + 625*z/3888 - 181/972)*h2 + (-9031*t^14*z/59049 - 19471*t^14/19683 + 658277*t^13*z/59049 - 89896*t^13/19683 - 10233421*t^12*z/59049 + 4904282*t^12/19683 + 71626201*t^11*z/59049 - 40876742*t^11/19683 - 251342681*t^10*z/59049 + 145625029*t^10/19683 + 292199419*t^9*z/59049 - 155573135*t^9/19683 + 321957019*t^8*z/19683 - 198170504*t^8/6561 - 1255083734*t^7*z/19683 + 754868008*t^7/6561 + 651467929*t^6*z/19683 - 566592683*t^6/6561 + 11803289920*t^5*z/59049 - 4723757552*t^5/19683 - 24592554977*t^4*z/59049 + 9985290793*t^4/19683 + 17780659984*t^3*z/59049 - 5055267788*t^3/19683 - 7821114511*t^2*z/59049 + 544804079*t^2/19683 + 8065651850*t*z/59049 - 3134630938*t/19683 - 4110980956*z/59049 + 2301714461/19683)*hf
  norm_num at hh

private lemma cell_1_40 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 8*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 1)*h0 + (-1)*hf
  norm_num at hh

private lemma cell_1_41 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z^2 - 11*z + 25/2)*h0 + (8)*hf
  norm_num at hh

private lemma cell_1_42 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 6*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-9*z^2/34 + 3*z/2 - 32/17)*h0 + (-27/17)*hf
  norm_num at hh

private lemma cell_1_43 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z^2 + 64*z - 112) + t^6*(2112*z^2 - 3920*z + 1504) + t^5*(-28080*z^2 + 58080*z - 20944) + t^4*(208528*z^2 - 440944*z + 160432) + t^3*(-939504*z^2 + 1993568*z - 727024) + t^2*(2543760*z^2 - 5398224*z + 1968976) + t*(-3798640*z^2 + 8058880*z - 2939200) + 2400336*z^2 - 5091200*z + 1856704:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(167*z^2/162 - 2771*z/486 + 535/81) + t^6*(-1475*z^2/243 + 8156*z/243 - 3148/81) + t^5*(1259*z^2/162 - 3473*z/81 + 1337/27) + t^4*(1031*z^2/162 - 17461*z/486 + 6841/162) + t^3*(-3232*z^2/243 + 18715*z/243 - 14761/162) + t^2*(131*z^2/162 - 1208*z/81 + 599/27) + t*(367*z^2/54 - 4915*z/243 + 2513/162) - 1361*z^2/243 + 9229*z/486 - 1348/81)*h0 + (t*(-167*z^2/1296 + 2771*z/3888 - 535/648) + 455*z^2/1944 - 629*z/486 + 971/648)*h1 + (-668*t^8*z/81 + 2066*t^8/243 + 69271*t^7*z/243 - 98786*t^7/243 - 996425*t^6*z/243 + 1575701*t^6/243 + 902534*t^5*z/27 - 13284548*t^5/243 - 41281342*t^4*z/243 + 68117360*t^4/243 + 133092239*t^3*z/243 - 219933650*t^3/243 - 87873886*t^2*z/81 + 435541847*t^2/243 + 291204868*t*z/243 - 480907271*t/243 - 136516388*z/243 + 225354671/243)*hf
  norm_num at hh

private lemma cell_1_44 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(128*z^2 - 640*z + 208) + t^6*(-1840*z^2 + 9280*z - 3920) + t^5*(11712*z^2 - 61392*z + 26272) + t^4*(-35824*z^2 + 216992*z - 93776) + t^3*(26912*z^2 - 372320*z + 168352) + t^2*(169152*z^2 + 34896*z - 53360) + t*(-561472*z^2 + 945008*z - 319280) + 741728*z^2 - 1517456*z + 547648:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(32711*z^2/166212 - 20105*z/18468 + 69889/55404) + t^6*(-125795*z^2/166212 + 231835*z/55404 - 134161/27702) + t^5*(2293*z^2/13851 - 5485*z/6156 + 17827/18468) + t^4*(105361*z^2/83106 - 131749*z/18468 + 119032/13851) + t^3*(-111047*z^2/166212 + 109931*z/27702 - 295325/55404) + t^2*(1508*z^2/13851 - 4985*z/6156 + 13495/9234) + t*(-3301*z^2/41553 + 965*z/3078 + 5053/55404) - 1271*z^2/8748 + 2947*z/2916 - 1430/729)*h0 + (t*(-32711*z^2/1329696 + 20105*z/147744 - 69889/443232) + 76493*z^2/1329696 - 11755*z/36936 + 20437/55404)*h1 + (130844*t^8*z/41553 - 128129*t^8/9234 - 2203210*t^7*z/41553 + 6636089*t^7/27702 + 16433471*t^6*z/41553 - 25785569*t^6/13851 - 129260321*t^5*z/83106 + 25069843*t^5/3078 + 226077007*t^4*z/83106 - 282079061*t^4/13851 + 217270513*t^3*z/83106 + 650977505*t^3/27702 - 978298252*t^2*z/41553 + 4966889*t^2/486 + 2100361049*t*z/41553 - 1884833653*t/27702 - 3546038345*z/83106 + 932667451/13851)*hf
  norm_num at hh

private lemma cell_1_45 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z^2 - 12*z + 2) - 2*z^2 + 12*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(192*z^2 - 960*z + 400) + t^6*(-3648*z^2 + 17520*z - 7520) + t^5*(35424*z^2 - 166608*z + 70240) + t^4*(-201696*z^2 + 941376*z - 396080) + t^3*(687696*z^2 - 3213696*z + 1353088) + t^2*(-1367712*z^2 + 6459552*z - 2723168) + t*(1439184*z^2 - 6969840*z + 2946208) - 597216*z^2 + 3060960*z - 1301504:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-2084*z^2/2187 + 427*z/81 - 4454/729) + t^6*(-1295*z^2/4374 + 265*z/162 - 1378/729) + t^5*(10153*z^2/1458 - 3118*z/81 + 21643/486) + t^4*(12047*z^2/4374 - 1252*z/81 + 26981/1458) + t^3*(-24322*z^2/2187 + 3371*z/54 - 54505/729) + t^2*(-8875*z^2/1458 + 2563*z/81 - 15199/486) + t*(11950*z^2/2187 - 754*z/27 + 38465/1458) - 2927*z^2/4374 + 443*z/162 - 1283/1458)*h0 + (t*(521*z^2/4374 - 427*z/648 + 2227/2916) - 3469*z^2/34992 + 6397*z/11664 - 3707/5832)*h1 + (-45848*t^8*z/2187 + 67874*t^8/729 + 989059*t^7*z/2187 - 1430707*t^7/729 - 10050638*t^6*z/2187 + 14229374*t^6/729 + 60240586*t^5*z/2187 - 84425629*t^5/729 - 222814331*t^4*z/2187 + 312218915*t^4/729 + 505368046*t^3*z/2187 - 714300016*t^3/729 - 671495015*t^2*z/2187 + 967425884*t^2/729 + 467634676*t*z/2187 - 696629899*t/729 - 129486821*z/2187 + 201028751/729)*hf
  norm_num at hh

private lemma cell_1_46 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(128*z^2 - 704*z + 272) + t^6*(-1872*z^2 + 10384*z - 4544) + t^5*(12960*z^2 - 73968*z + 31904) + t^4*(-48848*z^2 + 297536*z - 128384) + t^3*(95376*z^2 - 672496*z + 293648) + t^2*(-75024*z^2 + 800256*z - 358064) + t*(-15712*z^2 - 412544*z + 196496) + 38496*z^2 + 36832*z - 25664:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(4075*z^2/1539 - 135259*z/9234 + 52253/3078) + t^6*(-20458*z^2/4617 + 113167*z/4617 - 29143/1026) + t^5*(-16855*z^2/1026 + 46633*z/513 - 36041/342) + t^4*(9712*z^2/513 - 484195*z/4617 + 187313/1539) + t^3*(122974*z^2/4617 - 1355867*z/9234 + 87056/513) + t^2*(-19543*z^2/1026 + 53476*z/513 - 20543/171) + t*(-29057*z^2/3078 + 495665*z/9234 - 96416/1539) + 8819*z^2/4617 - 105283*z/9234 + 6763/513)*h0 + (t*(-4075*z^2/12312 + 135259*z/73872 - 52253/24624) + 21667*z^2/36936 - 119863*z/36936 + 92611/24624)*h1 + (65200*t^8*z/1539 - 935372*t^8/4617 - 3231772*t^7*z/4617 + 16229552*t^7/4617 + 24915494*t^6*z/4617 - 129882440*t^6/4617 - 36531565*t^5*z/1539 + 603767747*t^5/4617 + 277870336*t^4*z/4617 - 1702627457*t^4/4617 - 373205972*t^3*z/4617 + 2869758848*t^3/4617 + 59786371*t^2*z/1539 - 2714397026*t^2/4617 + 101467859*t*z/4617 + 1220936093*t/4617 - 104279242*z/4617 - 148509005/4617)*hf
  norm_num at hh

private lemma cell_1_47 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 2*z^2 - 2*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z^2 - 512*z + 208) + t^6*(192*z^2 + 4352*z - 2192) + t^5*(-14208*z^2 + 336*z + 3040) + t^4*(149056*z^2 - 206384*z + 64144) + t^3*(-774240*z^2 + 1403216*z - 487184) + t^2*(2232096*z^2 - 4440576*z + 1589008) + t*(-3419360*z^2 + 7071808*z - 2560304) + 2176896*z^2 - 4577872*z + 1665424:ℝ)=0) : (t - z^2 + 2*z - 1:ℝ)=0 := by
  have hh : (t - z^2 + 2*z - 1:ℝ)=0 := by linear_combination (t^6*(z^2/54 - 19*z/243 + 2/81) + t^5*(-79*z^2/162 + 172*z/81 - 73/81) + t^4*(241*z^2/54 - 1571*z/81 + 1315/162) + t^3*(-1654*z^2/81 + 43087*z/486 - 2996/81) + t^2*(3989*z^2/81 - 17299*z/81 + 14435/162) + t*(-179*z^2/3 + 41815*z/162 - 8732/81) + 2323*z^2/81 - 59861*z/486 + 307/6)*h0 + (-z^2/432 + 19*z/1944 - 1/324)*h1 + (4*t^7*z/27 - 206*t^7/243 + 11*t^6*z/27 + 2159*t^6/243 - 2585*t^5*z/81 - 3176*t^5/81 + 3025*t^4*z/9 + 11698*t^4/243 - 141862*t^3*z/81 + 69470*t^3/243 + 410540*t^2*z/81 - 113200*t^2/81 - 210488*t*z/27 + 605953*t/243 + 403522*z/81 - 407986/243)*hf
  exact hh

private lemma cell_1_48 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z^2 + 384*z - 432) + t^6*(480*z^2 - 2592*z + 2832) + t^5*(-1440*z^2 + 7776*z - 8928) + t^4*(2304*z^2 - 12816*z + 15264) + t^3*(-2016*z^2 + 11232*z - 13824) + t^2*(864*z^2 - 5616*z + 6480) + t*(1296*z - 1296):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(-25*z^2/306 + 415*z/918 - 722/1377) + t^5*(1538*z^2/1377 - 2836*z/459 + 3286/459) + t^4*(-1673*z^2/306 + 3085*z/102 - 16090/459) + t^3*(3751*z^2/306 - 6917*z/102 + 1336/17) + t^2*(-2018*z^2/153 + 11164*z/153 - 25885/306) + t*(994*z^2/153 - 611*z/17 + 4243/102) - 20*z^2/17 + 332*z/51 - 131/17)*h0 + (25*z^2/2448 - 415*z/7344 + 361/5508)*h1 + (100*t^7*z/153 - 1660*t^7/459 - 250*t^6*z/51 + 3700*t^6/153 + 250*t^5*z/17 - 3700*t^5/51 - 400*t^4*z/17 + 6115*t^4/51 + 350*t^3*z/17 - 5360*t^3/51 - 150*t^2*z/17 + 905*t^2/17 - 225*t/17)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_1_49 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z^2 - 10*z) - 4*z^2 + 18*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 240) + t^6*(-176*z^2 + 336*z + 960) + t^5*(960*z^2 - 3312*z - 1536) + t^4*(-5040*z^2 + 21504*z - 4608) + t^3*(14448*z^2 - 62352*z + 22320) + t^2*(-36144*z^2 + 154656*z - 62928) + t*(42336*z^2 - 181728*z + 75600) - 49536*z^2 + 215136*z - 89856:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-77*z^2/243 + 2557*z/1458 - 494/243) + t^6*(6101*z^2/1458 - 625*z/27 + 2173/81) + t^5*(-10387*z^2/486 + 28726*z/243 - 22193/162) + t^4*(26831*z^2/486 - 148433*z/486 + 9557/27) + t^3*(-37543*z^2/486 + 69253*z/162 - 80269/162) + t^2*(8941*z^2/162 - 24733*z/81 + 9554/27) + t*(-1102*z^2/81 + 6062*z/81 - 4667/54) - 295*z^2/162 + 557*z/54 - 328/27)*h0 + (t*(77*z^2/1944 - 2557*z/11664 + 247/972) - 505*z^2/5832 + 233*z/486 - 2161/3888)*h1 + (154*t^8*z/243 - 3943*t^8/729 - 1943*t^7*z/729 + 1040*t^7/27 + 1511*t^6*z/243 - 30532*t^6/243 + 2345*t^5*z/27 - 39386*t^5/243 - 153907*t^4*z/243 + 184058*t^4/81 + 183329*t^3*z/81 - 691109*t^3/81 - 13676*t^2*z/3 + 468359*t^2/27 + 50195*t*z/9 - 193004*t/9 - 12890*z/3 + 50015/3)*hf
  norm_num at hh

private lemma cell_1_50 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z^2 + 320*z - 368) + t^6*(320*z^2 - 1808*z + 2080) + t^5*(-816*z^2 + 4992*z - 5840) + t^4*(1424*z^2 - 7984*z + 9040) + t^3*(-1744*z^2 + 7552*z - 7664) + t^2*(1104*z^2 - 4272*z + 3376) + t*(656*z^2 - 1696*z + 544) - 304*z^2 + 736*z - 320:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z^2 + 320*z - 368) + t^6*(512*z^2 - 2384*z + 2272) + t^5*(-1248*z^2 + 5712*z - 5696) + t^4*(1856*z^2 - 6400*z + 6736) + t^3*(-2128*z^2 + 4672*z - 3872) + t^2*(6720*z^2 - 15360*z + 5824) + t*(-6256*z^2 + 15728*z - 5792) + 8960*z^2 - 20000*z + 7360:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(-1261*z^2/39366 + 3488*z/19683 - 2695/13122) + t^12*(15271*z^2/19683 - 168961*z/39366 + 65273/13122) + t^11*(-104603*z^2/13122 + 64297*z/1458 - 223553/4374) + t^10*(898118*z^2/19683 - 9936937*z/39366 + 1919420/6561) + t^9*(-3164065*z^2/19683 + 35007781*z/39366 - 6762109/6561) + t^8*(1588109*z^2/4374 - 1464260*z/729 + 1697020/729) + t^7*(-6944963*z^2/13122 + 38420153*z/13122 - 7421242/2187) + t^6*(3175643*z^2/6561 - 35135915*z/13122 + 13573753/4374) + t^5*(-551923*z^2/2187 + 1017751*z/729 - 2359025/1458) + t^4*(1017092*z^2/19683 - 11252821*z/39366 + 4346035/13122) + t^3*(384019*z^2/39366 - 2121851*z/39366 + 817783/13122) + t^2*(-26039*z^2/6561 + 31933*z/1458 - 109483/4374) + t*(-25573*z^2/39366 + 141523*z/39366 - 53455/13122) + 3451*z^2/19683 - 14864*z/19683 + 3737/13122)*h0 + (t^7*(1261*z^2/314928 - 436*z/19683 + 2695/104976) + t^6*(-15347*z^2/314928 + 84901*z/314928 - 10933/34992) + t^5*(2665*z^2/13122 - 14743*z/13122 + 3797/2916) + t^4*(-54841*z^2/157464 + 303385*z/157464 - 234407/104976) + t^3*(34721*z^2/157464 - 96041*z/78732 + 49471/34992) + t^2*(-2195*z^2/104976 + 12143*z/104976 - 391/2916) + t*(-6941*z^2/314928 + 19189*z/157464 - 14825/104976) - 367*z^2/157464 + 1991*z/157464 - 169/11664)*h1 + (-5*z^2/1296 + 85*z/3888 - 13/486)*h2 + (5044*t^14*z/19683 - 24121*t^14/19683 - 3161*t^13*z/729 + 437519*t^13/19683 + 596549*t^12*z/19683 - 3380437*t^12/19683 - 2299045*t^11*z/19683 + 14931487*t^11/19683 + 604496*t^10*z/2187 - 42181769*t^10/19683 - 8133104*t^9*z/19683 + 79527124*t^9/19683 + 2364359*t^8*z/6561 - 33361946*t^8/6561 - 46876*t^7*z/729 + 26638702*t^7/6561 - 2181647*t^6*z/6561 - 10284911*t^6/6561 + 10623098*t^5*z/19683 - 8572955*t^5/19683 - 261526*t^4*z/729 + 14205808*t^4/19683 + 1442692*t^3*z/19683 - 3745598*t^3/19683 + 876646*t^2*z/19683 - 1783375*t^2/19683 - 61253*t*z/2187 + 1200353*t/19683 + 659552*z/19683 - 1264084/19683)*hf
  norm_num at hh

private lemma cell_1_51 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z^2 + 576*z - 496) + t^6*(496*z^2 - 2352*z + 2560) + t^5*(-1248*z^2 + 6192*z - 7456) + t^4*(2288*z^2 - 11520*z + 12832) + t^3*(-1840*z^2 + 10128*z - 11152) + t^2*(912*z^2 - 6336*z + 5488) + t*(-608*z^2 + 4320*z - 2224) + 256*z^2 - 1344*z + 544:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-2*z^2/81 + 35*z/243 - 29/162) + t^6*(25*z^2/54 - 1253*z/486 + 238/81) + t^5*(-215*z^2/81 + 1207*z/81 - 470/27) + t^4*(631*z^2/81 - 10625*z/243 + 4156/81) + t^3*(-986*z^2/81 + 16480*z/243 - 12761/162) + t^2*(1505*z^2/162 - 8269*z/162 + 1585/27) + t*(-181*z^2/54 + 8137*z/486 - 2801/162) + 61*z^2/81 - 619*z/243 + 119/162)*h0 + (t*(z^2/324 - 35*z/1944 + 29/1296) - 5*z^2/432 + 263*z/3888 - 109/1296)*h1 + (32*t^8*z/81 - 416*t^8/243 - 244*t^7*z/81 + 3266*t^7/243 + 259*t^6*z/27 - 10886*t^6/243 - 1742*t^5*z/81 + 25223*t^5/243 + 2605*t^4*z/81 - 38765*t^4/243 - 217*t^3*z/9 + 32318*t^3/243 + 1007*t^2*z/81 - 20585*t^2/243 - 634*t*z/81 + 12860*t/243 + 80*z/27 - 3668/243)*hf
  norm_num at hh

private lemma cell_1_52 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z^2 - 10*z) - 4*z^2 + 18*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 240) + t^6*(208*z^2 - 1200*z + 1536) + t^5*(-1056*z^2 + 5328*z - 4560) + t^4*(1440*z^2 - 7008*z + 5328) + t^3*(1344*z^2 - 5616*z + 1584) + t^2*(-2448*z^2 + 10368*z - 4608) + t*(-2160*z^2 + 8784*z - 3456) + 576*z^2 - 2160*z + 864:ℝ)=0) (h2 : (16*t^8 + t^7*(64*z - 240) + t^6*(-176*z^2 + 336*z + 960) + t^5*(960*z^2 - 3312*z - 1536) + t^4*(-5040*z^2 + 21504*z - 4608) + t^3*(14448*z^2 - 62352*z + 22320) + t^2*(-36144*z^2 + 154656*z - 62928) + t*(42336*z^2 - 181728*z + 75600) - 49536*z^2 + 215136*z - 89856:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(-24541*z^2/39366 + 135763*z/39366 - 26224/6561) + t^12*(551765*z^2/39366 - 339157*z/4374 + 1179209/13122) + t^11*(-876970*z^2/6561 + 4851476*z/6561 - 3748447/4374) + t^10*(9316697*z^2/13122 - 25770398*z/6561 + 9955627/2187) + t^9*(-30426023*z^2/13122 + 28053244*z/2187 - 32512610/2187) + t^8*(2347319*z^2/486 - 19478366*z/729 + 15049775/486) + t^7*(-9298843*z^2/1458 + 8573671*z/243 - 19873097/486) + t^6*(1210061*z^2/243 - 4462777*z/162 + 15516551/486) + t^5*(-15457*z^2/9 + 2308753*z/243 - 891917/81) + t^4*(-493925*z^2/1458 + 2732465*z/1458 - 527804/243) + t^3*(646945*z^2/1458 - 132547*z/54 + 691247/243) + t^2*(-43297*z^2/486 + 239489*z/486 - 46264/81) + t*(-553*z^2/243 + 5977*z/486 - 1141/81) + 163*z^2/243 - 575*z/162 + 667/162)*h0 + (t^7*(24541*z^2/314928 - 135763*z/314928 + 3278/6561) + t^6*(-35203*z^2/39366 + 519323*z/104976 - 66875/11664) + t^5*(396353*z^2/104976 - 548165*z/26244 + 847069/34992) + t^4*(-815125*z^2/104976 + 281834*z/6561 - 1742051/34992) + t^3*(877123*z^2/104976 - 539147*z/11664 + 1874551/34992) + t^2*(-145985*z^2/34992 + 403801*z/17496 - 311993/11664) + t*(128*z^2/243 - 6373*z/2187 + 1459/432) + 1301*z^2/17496 - 4799*z/11664 + 1391/2916)*h1 + (-41*z^2/1944 + 455*z/3888 - 11/81)*h2 + (24541*t^14*z/19683 - 209386*t^14/19683 - 919880*t^13*z/19683 + 7567*t^13/27 + 3882056*t^12*z/6561 - 6652867*t^12/2187 - 24909124*t^11*z/6561 + 13171546*t^11/729 + 31192304*t^10*z/2187 - 142356311*t^10/2187 - 23996135*t^9*z/729 + 35703488*t^9/243 + 33426385*t^8*z/729 - 49436894*t^8/243 - 25015831*t^7*z/729 + 113157314*t^7/729 + 2024342*t^6*z/243 - 10333388*t^6/243 + 191285*t^5*z/729 - 2058032*t^5/729 + 6665669*t^4*z/729 - 6843775*t^4/243 - 2521574*t^3*z/243 + 2802422*t^3/81 + 633928*t^2*z/243 - 674993*t^2/81 + 59912*t*z/81 - 240644*t/81 - 9764*z/9 + 113302/27)*hf
  norm_num at hh

private lemma cell_1_53 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(4*z^2 - 20*z + 6) - 4*z^2 + 18*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z^2 - 256*z - 48) + t^6*(-704*z^2 + 2880*z - 720) + t^5*(2784*z^2 - 11664*z + 4416) + t^4*(-4512*z^2 + 19632*z - 8496) + t^3*(1536*z^2 - 7920*z + 3888) + t^2*(3168*z^2 - 12960*z + 5328) + t*(-2880*z^2 + 13248*z - 5616) + 576*z^2 - 3024*z + 1296:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(359*z^2/27702 - 721*z/9234 + 977/9234) + t^6*(-368*z^2/4617 + 4999*z/9234 - 4115/4617) + t^5*(-905*z^2/9234 - 130*z/1539 + 5615/3078) + t^4*(12907*z^2/9234 - 9055*z/1539 + 851/513) + t^3*(-401*z^2/162 + 617*z/54 - 574/81) + t^2*(199*z^2/3078 - 235*z/513 + 1313/1026) + t*(6725*z^2/3078 - 5087*z/513 + 5533/1026) - 631*z^2/1026 + 1219*z/513 - 185/513)*h0 + (t*(-359*z^2/221616 + 721*z/73872 - 977/73872) - 25*z^2/9234 + 233*z/24624 + 49/18468)*h1 + (718*t^8*z/13851 - 724*t^8/4617 - 34*t^7*z/57 + 10867*t^7/4617 + 4120*t^6*z/1539 - 1099*t^6/81 - 26570*t^5*z/4617 + 55874*t^5/1539 + 8872*t^4*z/1539 - 63548*t^4/1539 - 446*t^3*z/513 + 427*t^3/1539 - 2344*t^2*z/513 + 2135*t^2/57 + 2224*t*z/513 - 3794*t/171 - 154*z/171 + 787/513)*hf
  norm_num at hh

private lemma cell_1_54 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z^2 - 12*z + 2) - 2*z^2 + 12*z - 4:ℝ)=0) (h1 : (16*t^8 - 176*t^7 + t^6*(48*z^2 - 288*z + 784) + t^5*(-432*z^2 + 2592*z - 2048) + t^4*(1008*z^2 - 5904*z + 2656) + t^3*(192*z^2 - 2160*z + 1600) + t^2*(-1728*z^2 + 11664*z - 5312) + t*(-576*z^2 + 4608*z - 2048) + 192*z^2 - 1440*z + 640:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(11551*z^2/53946 - 21301*z/17982 + 24691/17982) + t^6*(-60860*z^2/26973 + 74821*z/5994 - 130094/8991) + t^5*(139765*z^2/17982 - 128869*z/2997 + 298739/5994) + t^4*(-235240*z^2/26973 + 433771*z/8991 - 1005095/17982) + t^3*(-154285*z^2/53946 + 15815*z/999 - 165428/8991) + t^2*(65734*z^2/8991 - 242413*z/5994 + 140273/2997) + t*(33679*z^2/53946 - 31139*z/8991 + 36791/8991) - 1717*z^2/53946 + 1007*z/5994 - 1363/17982)*h0 + (t*(-11551*z^2/431568 + 21301*z/143856 - 24691/143856) + 6497*z^2/215784 - 23965*z/143856 + 27799/143856)*h1 + (-11551*t^8*z/26973 + 21301*t^8/8991 + 167924*t^7*z/26973 - 309667*t^7/8991 - 891874*t^6*z/26973 + 548233*t^6/2997 + 53198*t^5*z/729 - 3595121*t^5/8991 - 996205*t^4*z/26973 + 1555502*t^4/8991 - 1952125*t^3*z/26973 + 464972*t^3/999 + 1348241*t^2*z/26973 - 2559959*t^2/8991 + 641792*t*z/26973 - 1564813*t/8991 - 157645*z/26973 + 122855/2997)*hf
  norm_num at hh

private lemma cell_1_55 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(4*z^2 - 20*z + 4) - 6*z^2 + 28*z - 10:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 112) + t^6*(208*z^2 - 16*z + 352) + t^5*(-2304*z^2 + 4848*z - 2032) + t^4*(9120*z^2 - 23072*z + 8464) + t^3*(-15712*z^2 + 36976*z - 13456) + t^2*(12528*z^2 - 21216*z + 7168) + t*(-6864*z^2 + 13712*z - 4960) + 928*z^2 - 2608*z + 1024:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(5594*z^2/17253 - 61903*z/34506 + 11959/5751) + t^6*(-15013*z^2/5751 + 249253*z/17253 - 96319/5751) + t^5*(67243*z^2/11502 - 186241*z/5751 + 72002/1917) + t^4*(-20216*z^2/17253 + 115064*z/17253 - 89903/11502) + t^3*(-27515*z^2/3834 + 1352113*z/34506 - 259961/5751) + t^2*(19976*z^2/5751 - 105478*z/5751 + 79819/3834) + t*(42439*z^2/34506 - 259975*z/34506 + 52633/5751) - 377*z^2/5751 + 8128*z/17253 - 6245/11502)*h0 + (t*(-2797*z^2/69012 + 61903*z/276048 - 11959/46008) + 221*z^2/3834 - 88085*z/276048 + 17027/46008)*h1 + (-22376*t^8*z/17253 + 56678*t^8/17253 + 359164*t^7*z/17253 - 837428*t^7/17253 - 830540*t^6*z/5751 + 5524085*t^6/17253 + 9354539*t^5*z/17253 - 19837268*t^5/17253 - 19682482*t^4*z/17253 + 37778732*t^4/17253 + 7801057*t^3*z/5751 - 36170888*t^3/17253 - 16984058*t^2*z/17253 + 21677774*t^2/17253 + 7606993*t*z/17253 - 12626312*t/17253 - 103298*z/1917 + 2204930/17253)*hf
  norm_num at hh

private lemma cell_1_56 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z^2 + 320*z - 368) + t^6*(512*z^2 - 2384*z + 2272) + t^5*(-1248*z^2 + 5712*z - 5696) + t^4*(1856*z^2 - 6400*z + 6736) + t^3*(-2128*z^2 + 4672*z - 3872) + t^2*(6720*z^2 - 15360*z + 5824) + t*(-6256*z^2 + 15728*z - 5792) + 8960*z^2 - 20000*z + 7360:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-34*z^2/729 + 7*z/27 - 443/1458) + t^6*(175*z^2/243 - 2905*z/729 + 6737/1458) + t^5*(-223*z^2/54 + 11093*z/486 - 12829/486) + t^4*(16171*z^2/1458 - 29809*z/486 + 51776/729) + t^3*(-2257*z^2/162 + 56261*z/729 - 65399/729) + t^2*(13*z^2/2 - 17543*z/486 + 10256/243) + t*(313*z^2/1458 - 617*z/486 + 1271/729) - 130*z^2/243 + 4681*z/1458 - 3197/729)*h0 + (t*(17*z^2/2916 - 7*z/216 + 443/11664) - 13*z^2/729 + 1157*z/11664 - 679/5832)*h1 + (272*t^8*z/729 - 436*t^8/243 - 980*t^7*z/243 + 13912*t^7/729 + 10910*t^6*z/729 - 54427*t^6/729 - 18091*t^5*z/729 + 32618*t^5/243 + 1889*t^4*z/81 - 84080*t^4/729 - 35911*t^3*z/729 + 79520*t^3/729 + 104471*t^2*z/729 - 67180*t^2/243 - 39907*t*z/243 + 236902*t/729 + 117260*z/729 - 210601/729)*hf
  norm_num at hh

private lemma cell_1_57 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z^2 - 12*z + 2) - 2*z^2 + 12*z - 4:ℝ)=0) (h1 : (16*t^8 - 176*t^7 + t^6*(-144*z^2 + 672*z + 400) + t^5*(1152*z^2 - 5328*z + 1120) + t^4*(-4464*z^2 + 20160*z - 7856) + t^3*(10080*z^2 - 44256*z + 18784) + t^2*(-14976*z^2 + 64080*z - 27056) + t*(12672*z^2 - 53424*z + 22288) - 4320*z^2 + 18096*z - 7520:ℝ)=0) (h2 : (16*t^8 - 176*t^7 + t^6*(48*z^2 - 288*z + 784) + t^5*(-432*z^2 + 2592*z - 2048) + t^4*(1008*z^2 - 5904*z + 2656) + t^3*(192*z^2 - 2160*z + 1600) + t^2*(-1728*z^2 + 11664*z - 5312) + t*(-576*z^2 + 4608*z - 2048) + 192*z^2 - 1440*z + 640:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(99301*z^2/4015332 - 3391*z/24786 + 106111/669222) + t^12*(-113387*z^2/236196 + 209089*z/78732 - 121163/39366) + t^11*(1682513*z^2/446148 - 775651*z/37179 + 399533/16524) + t^10*(-60937153*z^2/4015332 + 1387283*z/16524 - 130232357/1338444) + t^9*(31837333*z^2/1003833 - 234835961*z/1338444 + 68041430/334611) + t^8*(-3887383*z^2/148716 + 3584225*z/24786 - 8307953/49572) + t^7*(-20970667*z^2/1338444 + 1432243*z/16524 - 44817755/446148) + t^6*(25732103*z^2/669222 - 94901555*z/446148 + 27496742/111537) + t^5*(-178583*z^2/24786 + 987919*z/24786 - 572420/12393) + t^4*(-50404795*z^2/4015332 + 860624*z/12393 - 26927858/334611) + t^3*(1547971*z^2/4015332 - 1422583*z/669222 + 3232751/1338444) + t^2*(241643*z^2/223074 - 891047*z/148716 + 171077/24786) + t*(5162971*z^2/4015332 - 19613*z/2754 + 5579623/669222) + 688487*z^2/4015332 - 640895*z/669222 + 1644625/1338444)*h0 + (t^7*(-99301*z^2/32122656 + 3391*z/198288 - 106111/5353776) + t^6*(496505*z^2/16061328 - 16955*z/99144 + 530555/2676888) + t^5*(-516935*z^2/5353776 + 1906487*z/3569184 - 276193/446148) + t^4*(2668757*z^2/32122656 - 820211*z/1784592 + 2851775/5353776) + t^3*(490081*z^2/8030664 - 602483*z/1784592 + 4189535/10707552) + t^2*(-163169*z^2/2676888 + 1203553*z/3569184 - 697433/1784592) + t*(-128581*z^2/8030664 + 19759*z/223074 - 1099211/10707552) - 12586*z^2/1003833 + 61891*z/892296 - 860779/10707552)*h1 + (13*z^2/3888 - z/54 + 7/324)*h2 + (-99301*t^14*z/2007666 + 3391*t^14/12393 + 1133171*t^13*z/2007666 - 828935*t^13/223074 - 491717*t^12*z/1003833 + 1510409*t^12/111537 - 51036419*t^11*z/2007666 + 5872228*t^11/111537 + 199328834*t^10*z/1003833 - 75251551*t^10/111537 - 1526090141*t^9*z/2007666 + 319490600*t^9/111537 + 1168629445*t^8*z/669222 - 504537215*t^8/74358 - 1643908061*t^7*z/669222 + 236141819*t^7/24786 + 609609641*t^6*z/334611 - 56869393*t^6/8262 + 27206719*t^5*z/2007666 - 17322535*t^5/74358 - 1255894729*t^4*z/1003833 + 1069997033*t^4/223074 + 1848281677*t^3*z/2007666 - 768105523*t^3/223074 - 487512373*t^2*z/2007666 + 200962381*t^2/223074 + 94226602*t*z/1003833 - 40706714*t/111537 - 109343425*z/2007666 + 22770061/111537)*hf
  norm_num at hh

private lemma cell_1_58 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z^2 + 256*z - 304) + t^6*(480*z^2 - 1856*z + 1648) + t^5*(-1152*z^2 + 4368*z - 3520) + t^4*(448*z^2 - 2224*z + 2224) + t^3*(1728*z^2 - 4624*z + 1904) + t^2*(-1440*z^2 + 4224*z - 2096) + t*(-352*z^2 + 832*z - 208) + 384*z^2 - 1040*z + 400:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(179*z^2/486 - 494*z/243 + 190/81) + t^6*(-707*z^2/162 + 5860*z/243 - 1507/54) + t^5*(329*z^2/18 - 1819*z/18 + 3163/27) + t^4*(-15695*z^2/486 + 86815*z/486 - 33581/162) + t^3*(1544*z^2/81 - 51335*z/486 + 3310/27) + t^2*(109*z^2/18 - 599*z/18 + 2105/54) + t*(-3535*z^2/486 + 19673*z/486 - 3845/81) + 7*z^2/9 - 1049*z/243 + 29/6)*h0 + (t*(-179*z^2/3888 + 247*z/972 - 95/324) + 89*z^2/1296 - 733*z/1944 + 559/1296)*h1 + (-716*t^8*z/243 + 2878*t^8/243 + 6259*t^7*z/243 - 25882*t^7/243 - 6259*t^6*z/81 + 84097*t^6/243 + 15353*t^5*z/243 - 103381*t^5/243 + 27551*t^4*z/243 - 14645*t^4/243 - 18070*t^3*z/81 + 122156*t^3/243 + 17149*t^2*z/243 - 53501*t^2/243 + 13705*t*z/243 - 25240*t/243 - 754*z/27 + 14677/243)*hf
  norm_num at hh

private lemma cell_1_59 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 2*z^2 - 2*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z^2 + 448*z - 368) + t^6*(1392*z^2 - 3856*z + 2272) + t^5*(-9312*z^2 + 20784*z - 9056) + t^4*(45328*z^2 - 95264*z + 35488) + t^3*(-145200*z^2 + 307088*z - 111632) + t^2*(282768*z^2 - 602400*z + 219568) + t*(-303104*z^2 + 646048*z - 235856) + 136608*z^2 - 290560*z + 106048:ℝ)=0) (h2 : (16*t^8 + t^7*(64*z^2 - 320*z + 16) + t^6*(-864*z^2 + 4112*z - 1472) + t^5*(4944*z^2 - 22272*z + 9232) + t^4*(-15248*z^2 + 65680*z - 27632) + t^3*(25776*z^2 - 109024*z + 45616) + t^2*(-21360*z^2 + 92112*z - 38480) + t*(5680*z^2 - 26048*z + 10912) + 1584*z^2 - 6400*z + 2656:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(-16411*z^2/27702 + 408542*z/124659 - 2840905/747954) + t^12*(261157*z^2/27702 - 39008081*z/747954 + 45208837/747954) + t^11*(-14633345*z^2/249318 + 80952965*z/249318 - 31273771/83106) + t^10*(1168586*z^2/6561 - 12929443*z/13122 + 22477076/19683) + t^9*(-1151938*z^2/4617 + 1032364907*z/747954 - 598235183/373977) + t^8*(1542520*z^2/41553 - 17066687*z/83106 + 2197733/9234) + t^7*(27129953*z^2/83106 - 75042674*z/41553 + 521829103/249318) + t^6*(-529462*z^2/1539 + 474502703*z/249318 - 274964555/124659) + t^5*(1106234*z^2/41553 - 12237991*z/83106 + 4726693/27702) + t^4*(5603288*z^2/41553 - 186025819*z/249318 + 646978513/747954) + t^3*(-1561753*z^2/27702 + 233854289*z/747954 - 135869222/373977) + t^2*(-3461839*z^2/249318 + 9282254*z/124659 - 6994241/83106) + t*(1280008*z^2/124659 - 13180847*z/249318 + 21898591/373977) + 133*z^2/486 - 84331*z/19683 + 251167/39366)*h0 + (t^7*(16411*z^2/221616 - 204271*z/498636 + 2840905/5983632) + t^6*(-1595003*z^2/2991816 + 17647397*z/5983632 - 10226321/2991816) + t^5*(132856*z^2/124659 - 2939885*z/498636 + 851803/124659) + t^4*(-384737*z^2/1994544 + 2128403*z/1994544 - 7400237/5983632) + t^3*(-3459041*z^2/2991816 + 4783927*z/747954 - 2772187/373977) + t^2*(1616873*z^2/1994544 - 8944669*z/1994544 + 10366481/1994544) + t*(-7799*z^2/249318 + 86291*z/498636 - 600019/2991816) - 6281*z^2/39366 + 277997*z/314928 - 161099/157464)*h1 + (-5743*z^2/36936 + 7061*z/8208 - 24557/24624)*h2 + (131288*t^14*z/13851 - 204110*t^14/6561 - 63626390*t^13*z/373977 + 179994434*t^13/373977 + 193126147*t^12*z/124659 - 1332584180*t^12/373977 - 1210672534*t^11*z/124659 + 2291430032*t^11/124659 + 16681710386*t^10*z/373977 - 28300407149*t^10/373977 - 18230302265*t^9*z/124659 + 89852266463*t^9/373977 + 13492818736*t^8*z/41553 - 22196100643*t^8/41553 - 55067063944*t^7*z/124659 + 91334984932*t^7/124659 + 3411111178*t^6*z/13851 - 51364209724*t^6/124659 + 10023542021*t^5*z/41553 - 49962162784*t^5/124659 - 206907902563*t^4*z/373977 + 345931180648*t^4/373977 + 49047215819*t^3*z/124659 - 247764442288*t^3/373977 - 9773158361*t^2*z/124659 + 17112626359*t^2/124659 - 16165355558*t*z/373977 + 26083853744*t/373977 + 2747744201*z/124659 - 13853740202/373977)*hf
  norm_num at hh

private lemma cell_1_60 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z^2 - 192*z - 112) + t^6*(-416*z^2 + 1584*z + 160) + t^5*(1632*z^2 - 6768*z + 1184) + t^4*(-3520*z^2 + 14880*z - 4688) + t^3*(3248*z^2 - 14112*z + 5504) + t^2*(-96*z^2 - 288*z - 128) + t*(-2288*z^2 + 11184*z - 4576) + 1504*z^2 - 6624*z + 2752:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(85*z^2/243 - 313*z/162 + 181/81) + t^6*(-649*z^2/162 + 3589*z/162 - 692/27) + t^5*(1348*z^2/81 - 14897*z/162 + 2870/27) + t^4*(-7576*z^2/243 + 4648*z/27 - 32195/162) + t^3*(2006*z^2/81 - 2459*z/18 + 8491/54) + t^2*(-337*z^2/162 + 1825*z/162 - 337/27) + t*(-3361*z^2/486 + 3062*z/81 - 6997/162) + 157*z^2/81 - 818*z/81 + 581/54)*h0 + (t*(-85*z^2/1944 + 313*z/1296 - 181/648) + 211*z^2/1296 - 583*z/648 + 25/24)*h1 + (680*t^8*z/243 - 572*t^8/81 - 6952*t^7*z/243 + 7040*t^7/81 + 11266*t^6*z/81 - 39505*t^6/81 - 101966*t^5*z/243 + 125813*t^5/81 + 173770*t^4*z/243 - 218729*t^4/81 - 533*t^3*z + 164620*t^3/81 - 20512*t^2*z/243 + 40147*t^2/81 + 106499*t*z/243 - 154111*t/81 - 19834*z/81 + 77954/81)*hf
  norm_num at hh

private lemma cell_1_61 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(4*z^2 - 20*z + 4) - 6*z^2 + 28*z - 10:ℝ)=0) (h1 : (16*t^8 + t^7*(192*z^2 - 832*z + 272) + t^6*(-3392*z^2 + 14672*z - 6080) + t^5*(29088*z^2 - 126192*z + 52832) + t^4*(-150912*z^2 + 656224*z - 274160) + t^3*(490736*z^2 - 2134688*z + 891392) + t^2*(-971712*z^2 + 4224768*z - 1764032) + t*(1064976*z^2 - 4628464*z + 1932512) - 492128*z^2 + 2138816*z - 893024:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-1831*z^2/5994 + 30413*z/17982 - 11753/5994) + t^6*(87*z^2/74 - 58514*z/8991 + 22606/2997) + t^5*(271*z^2/2997 - 533*z/999 + 659/999) + t^4*(-7594*z^2/2997 + 127520*z/8991 - 100183/5994) + t^3*(1676*z^2/2997 - 30658*z/8991 + 30061/5994) + t^2*(8999*z^2/5994 - 14995*z/1998 + 11527/1998) + t*(-149*z^2/81 + 4037*z/486 - 385/81) + 4229*z^2/2997 - 112561*z/17982 + 11275/2997)*h0 + (t*(1831*z^2/47952 - 30413*z/143856 + 11753/47952) - 1261*z^2/23976 + 42007*z/143856 - 5417/15984)*h1 + (-18310*t^8*z/2997 + 205256*t^8/8991 + 398849*t^7*z/2997 - 4589264*t^7/8991 - 3843365*t^6*z/2997 + 44665451*t^6/8991 + 21886990*t^5*z/2997 - 255238532*t^5/8991 - 79998373*t^4*z/2997 + 933839639*t^4/8991 + 62848204*t^3*z/999 - 2201277101*t^3/8991 - 274990246*t^2*z/2997 + 3211048763*t^2/8991 + 74711582*t*z/999 - 2618622674*t/8991 - 2095846*z/81 + 906917567/8991)*hf
  norm_num at hh

private lemma cell_1_62 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 2*z^2 - 2*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z^2 - 320*z + 16) + t^6*(-864*z^2 + 4112*z - 1472) + t^5*(4944*z^2 - 22272*z + 9232) + t^4*(-15248*z^2 + 65680*z - 27632) + t^3*(25776*z^2 - 109024*z + 45616) + t^2*(-21360*z^2 + 92112*z - 38480) + t*(5680*z^2 - 26048*z + 10912) + 1584*z^2 - 6400*z + 2656:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-7268*z^2/13851 + 8935*z/3078 - 15532/4617) + t^6*(52340*z^2/13851 - 96521*z/4617 + 37286/1539) + t^5*(-34871*z^2/4617 + 128639*z/3078 - 149119/3078) + t^4*(36851*z^2/27702 - 3802*z/513 + 80455/9234) + t^3*(231253*z^2/27702 - 424957*z/9234 + 81313/1539) + t^2*(-27970*z^2/4617 + 102109*z/3078 - 57625/1539) + t*(6919*z^2/13851 - 3701*z/1539 + 8699/4617) + 797*z^2/729 - 2947*z/486 + 383/54)*h0 + (t*(1817*z^2/27702 - 8935*z/24624 + 3883/9234) - 19283*z^2/110808 + 23711*z/24624 - 1718/1539)*h1 + (-58144*t^8*z/13851 + 78148*t^8/4617 + 953744*t^7*z/13851 - 1288735*t^7/4617 - 6678868*t^6*z/13851 + 8903167*t^6/4617 + 1367312*t^5*z/729 - 33783215*t^5/4617 - 60207745*t^4*z/13851 + 76579247*t^4/4617 + 81304133*t^3*z/13851 - 102872336*t^3/4617 - 2972530*t^2*z/729 + 73065505*t^2/4617 + 12238028*t*z/13851 - 17065804*t/4617 + 3787748*z/13851 - 4542716/4617)*hf
  norm_num at hh

private lemma cell_1_63 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 6*t:ℝ)=0) (h1 : (t*(-144*z^2 + 432*z - 192) + 272*z^2 - 768*z + 304:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^2/3 - 11*z/6 + 2)*h0 + (-67*z^2/816 + 373*z/816 - 73/136)*h1 + (-201*t*z/17 + 516*t/17 + 67*z/3 - 2723/51)*hf
  norm_num at hh

private lemma pair_1_7_13 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + z^2 - 4*z:ℝ)=0) (h2 : (1296*t^8 + t^7*(10368*z^2 - 51840*z + 19440) + t^6*(-151632*z^2 + 720576*z - 304560) + t^5*(1118448*z^2 - 5128272*z + 2157840) + t^4*(-4883328*z^2 + 21888144*z - 9173088) + t^3*(13020912*z^2 - 57554064*z + 24078384) + t^2*(-20796912*z^2 + 91176192*z - 38108880) + t*(18271008*z^2 - 79742880*z + 33312384) - 6785856*z^2 + 29548800*z - 12340512:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(z/6 - 1/3) + t^6*(-4*z^2/3 + 4*z - 3/2) + t^5*(73*z^2/6 - 39*z + 95/6) + t^4*(-117*z^2/2 + 1181*z/6 - 159/2) + t^3*(985*z^2/6 - 1744*z/3 + 1415/6) + t^2*(-1615*z^2/6 + 6017*z/6 - 821/2) + t*(719*z^2/3 - 935*z + 1154/3) - 90*z^2 + 1097*z/3 - 152)*h0 + (1/3888 - z/7776)*h2 + (7*t^7/6 + 4*t^6*z/3 - 125*t^6/6 - 73*t^5*z/6 + 317*t^5/2 + 117*t^4*z/2 - 4247*t^4/6 - 985*t^3*z/6 + 3855*t^3/2 + 1615*t^2*z/6 - 3139*t^2 - 719*t*z/3 + 8416*t/3 + 90*z - 3175/3)*hf
  norm_num at hh

private lemma pair_1_7_47 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + z^2 - 4*z:ℝ)=0) (h1 : (t - z^2 + 2*z - 1:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-2*z^2/37 + 18*z/37 - 35/37)*h0 + (2*z^2/37 - 18*z/37 + 35/37)*h1 + (4*z/37 - 24/37)*hf
  norm_num at hh

private lemma pair_1_13_47 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(-z^2 + 5*z - 2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + z^2 - 4*z:ℝ)=0) (h1 : (t - z^2 + 2*z - 1:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-2*z^2/37 + 18*z/37 - 35/37)*h0 + (2*z^2/37 - 18*z/37 + 35/37)*h1 + (4*z/37 - 24/37)*hf
  norm_num at hh

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_0 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 0) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_0 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_1 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 1) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_1 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 20*z^3 + 64*z^2 - 70*z + 20:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_2 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 2) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_2 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_3 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 3) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_3 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z^2 + 192*t^7*z - 240*t^7 + 160*t^6*z^4 - 1152*t^6*z^3 + 3360*t^6*z^2 - 4176*t^6*z + 1920*t^6 - 256*t^5*z^6 + 2880*t^5*z^5 - 13680*t^5*z^4 + 34560*t^5*z^3 - 49104*t^5*z^2 + 36288*t^5*z - 10080*t^5 + 304*t^4*z^8 - 4800*t^4*z^7 + 33072*t^4*z^6 - 128736*t^4*z^5 + 306864*t^4*z^4 - 453312*t^4*z^3 + 400896*t^4*z^2 - 192096*t^4*z + 36864*t^4 - 256*t^3*z^10 + 5184*t^3*z^9 - 46704*t^3*z^8 + 245664*t^3*z^7 - 832944*t^3*z^6 + 1895904*t^3*z^5 - 2919744*t^3*z^4 + 2977488*t^3*z^3 - 1894176*t^3*z^2 + 664416*t^3*z - 95904*t^3 + 160*t^2*z^12 - 4032*t^2*z^11 + 45936*t^2*z^10 - 311904*t^2*z^9 + 1400688*t^2*z^8 - 4363632*t^2*z^7 + 9619632*t^2*z^6 - 15029712*t^2*z^5 + 16411680*t^2*z^4 - 12133584*t^2*z^3 + 5719680*t^2*z^2 - 1525824*t^2*z + 172368*t^2 - 64*t*z^14 + 1920*t*z^13 - 26304*t*z^12 + 217728*t*z^11 - 1214208*t*z^10 + 4816224*t*z^9 - 13979952*t*z^8 + 30078576*t*z^7 - 48012768*t*z^6 + 56268864*t*z^5 - 47292768*t*z^4 + 27370656*t*z^3 - 10200816*t*z^2 + 2172096*t*z - 198288*t + 16*z^16 - 576*z^15 + 9552*z^14 - 96624*z^13 + 665472*z^12 - 3298464*z^11 + 12127248*z^10 - 33598224*z^9 + 70557840*z^8 - 112123008*z^7 + 133673760*z^6 - 117713520*z^5 + 74729952*z^4 - 32946912*z^3 + 9486720*z^2 - 1590192*z + 116640:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z + 192*t^6 + 256*t^5*z^3 - 1344*t^5*z^2 + 3312*t^5*z - 1824*t^5 - 304*t^4*z^5 + 2976*t^4*z^4 - 12480*t^4*z^3 + 26160*t^4*z^2 - 28656*t^4*z + 8496*t^4 + 256*t^3*z^7 - 3648*t^3*z^6 + 22512*t^3*z^5 - 76992*t^3*z^4 + 157440*t^3*z^3 - 190800*t^3*z^2 + 127008*t^3*z - 25920*t^3 - 160*t^2*z^9 + 3072*t^2*z^8 - 26064*t^2*z^7 + 127392*t^2*z^6 - 392544*t^2*z^5 + 783648*t^2*z^4 - 1002672*t^2*z^3 + 783216*t^2*z^2 - 337392*t^2*z + 52272*t^2 + 64*t*z^11 - 1536*t*z^10 + 16512*t*z^9 - 104640*t*z^8 + 433152*t*z^7 - 1226016*t*z^6 + 2411568*t*z^5 - 3275568*t*z^4 + 2977200*t*z^3 - 1690848*t*z^2 + 526176*t*z - 64368*t - 16*z^13 + 480*z^12 - 6528*z^11 + 53088*z^10 - 286752*z^9 + 1080576*z^8 - 2903760*z^7 + 5590224*z^6 - 7640928*z^5 + 7254144*z^4 - 4609872*z^3 + 1844208*z^2 - 413424*z + 38880)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_4 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 4) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_4 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 20*z^3 + 64*z^2 - 70*z + 20:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_5 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 5) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_5 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 20*z^3 + 66*z^2 - 80*z + 26:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_6 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 6) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_6 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^3 + 6480*t*z^2 - 2592*t*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_7 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 7) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : (t + z^2 - 4*z:ℝ)=0 := by
  apply cell_1_7 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z + 2*z^4 - 20*z^3 + 62*z^2 - 60*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 496*t^6*z^2 + 48*t^6 - 1184*t^5*z^3 + 864*t^5*z^2 + 576*t^5*z - 144*t^5 + 1840*t^4*z^4 - 2928*t^4*z^3 - 2160*t^4*z^2 + 1152*t^4*z - 288*t^4 - 1856*t^3*z^5 + 4752*t^3*z^4 + 2352*t^3*z^3 - 4896*t^3*z^2 - 576*t^3*z + 864*t^3 + 1168*t^2*z^6 - 4320*t^2*z^5 - 144*t^2*z^4 + 7920*t^2*z^3 - 432*t^2*z^2 - 864*t^2*z - 416*t*z^7 + 2112*t*z^6 - 1296*t*z^5 - 5040*t*z^4 + 2448*t*z^3 + 5616*t*z^2 - 2592*t*z + 64*z^8 - 432*z^7 + 624*z^6 + 1008*z^5 - 2448*z^4 + 864*z^3:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1184*t^5 - 1840*t^4*z - 8112*t^4 + 1856*t^3*z^2 + 6384*t^3*z + 19248*t^3 - 1168*t^2*z^3 - 2688*t^2*z^2 - 5472*t^2*z - 20064*t^2 + 416*t*z^4 + 384*t*z^3 - 144*t*z^2 + 1968*t*z + 11808*t - 64*z^5 + 48*z^4 + 240*z^3 - 192*z^2 - 720*z - 2736)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_8 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 8) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_8 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_9 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 9) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_9 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^3 + 6480*t*z^2 - 2592*t*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_10 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 10) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_10 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_11 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 11) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_11 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z^2 - 640*t^7*z + 208*t^7 + 448*t^6*z^4 - 4480*t^6*z^3 + 12752*t^6*z^2 - 7808*t^6*z + 1264*t^6 + 896*t^5*z^6 - 13440*t^5*z^5 + 72144*t^5*z^4 - 161728*t^5*z^3 + 133632*t^5*z^2 - 43392*t^5*z + 4720*t^5 + 1120*t^4*z^8 - 22400*t^4*z^7 + 176720*t^4*z^6 - 691520*t^4*z^5 + 1385344*t^4*z^4 - 1351888*t^4*z^3 + 644048*t^4*z^2 - 142912*t^4*z + 11680*t^4 + 896*t^3*z^10 - 22400*t^3*z^9 + 233200*t^3*z^8 - 1304960*t^3*z^7 + 4230336*t^3*z^6 - 8016512*t^3*z^5 + 8686704*t^3*z^4 - 5306000*t^3*z^3 + 1775456*t^3*z^2 - 300224*t^3*z + 19936*t^3 + 448*t^2*z^12 - 13440*t^2*z^11 + 173808*t^2*z^10 - 1265920*t^2*z^9 + 5696304*t^2*z^8 - 16372128*t^2*z^7 + 30164624*t^2*z^6 - 35197440*t^2*z^5 + 25601712*t^2*z^4 - 11341136*t^2*z^3 + 2931984*t^2*z^2 - 403296*t^2*z + 22912*t^2 + 128*t*z^14 - 4480*t*z^13 + 69232*t*z^12 - 621248*t*z^11 + 3582400*t*z^10 - 13885312*t*z^9 + 36821728*t*z^8 - 66920528*t*z^7 + 82678496*t*z^6 - 68485168*t*z^5 + 37279760*t*z^4 - 12932336*t*z^3 + 2713904*t*z^2 - 310048*t*z + 14464*t + 16*z^16 - 640*z^15 + 11504*z^14 - 122688*z^13 + 863456*z^12 - 4221200*z^11 + 14704480*z^10 - 36886176*z^9 + 66680560*z^8 - 86329056*z^7 + 79113952*z^6 - 50417872*z^5 + 21748208*z^4 - 6078624*z^3 + 1019072*z^2 - 87680*z + 2560:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6*z + 1792*t^6 - 896*t^5*z^3 + 8064*t^5*z^2 - 15696*t^5*z - 7712*t^5 - 1120*t^4*z^5 + 15680*t^4*z^4 - 72560*t^4*z^3 + 111680*t^4*z^2 - 15184*t^4*z + 37984*t^4 - 896*t^3*z^7 + 17024*t^3*z^6 - 122992*t^3*z^5 + 411104*t^3*z^4 - 605712*t^3*z^3 + 313328*t^3*z^2 - 122016*t^3*z - 63184*t^3 - 448*t^2*z^9 + 10752*t^2*z^8 - 105264*t^2*z^7 + 536224*t^2*z^6 - 1499328*t^2*z^5 + 2234352*t^2*z^4 - 1655888*t^2*z^3 + 654960*t^2*z^2 - 65904*t^2*z + 83408*t^2 - 128*t*z^11 + 3712*t*z^10 - 45808*t*z^9 + 312608*t*z^8 - 1283344*t*z^7 + 3234352*t*z^6 - 4927696*t*z^5 + 4395152*t*z^4 - 2255264*t*z^3 + 614128*t*z^2 - 112160*t*z - 33568*t - 16*z^13 + 544*z^12 - 8096*z^11 + 69168*z^10 - 373952*z^9 + 1330688*z^8 - 3147280*z^7 + 4904448*z^6 - 4936288*z^5 + 3129456*z^4 - 1197280*z^3 + 260224*z^2 - 22976*z + 6912)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_12 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 12) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_12 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z^2 - 576*t^7*z + 144*t^7 + 448*t^6*z^4 - 4032*t^6*z^3 + 10224*t^6*z^2 - 5136*t^6*z + 672*t^6 + 896*t^5*z^6 - 12096*t^5*z^5 + 58320*t^5*z^4 - 116352*t^5*z^3 + 82512*t^5*z^2 - 22464*t^5*z + 2016*t^5 + 1120*t^4*z^8 - 20160*t^4*z^7 + 143280*t^4*z^6 - 504720*t^4*z^5 + 905904*t^4*z^4 - 780768*t^4*z^3 + 322272*t^4*z^2 - 60768*t^4*z + 4032*t^4 + 896*t^3*z^10 - 20160*t^3*z^9 + 189360*t^3*z^8 - 958080*t^3*z^7 + 2811936*t^3*z^6 - 4821696*t^3*z^5 + 4704624*t^3*z^4 - 2556432*t^3*z^3 + 747936*t^3*z^2 - 108000*t^3*z + 6048*t^3 + 448*t^2*z^12 - 12096*t^2*z^11 + 141264*t^2*z^10 - 932400*t^2*z^9 + 3815424*t^2*z^8 - 10005120*t^2*z^7 + 16856928*t^2*z^6 - 17978976*t^2*z^5 + 11880864*t^2*z^4 - 4724784*t^2*z^3 + 1080000*t^2*z^2 - 129600*t^2*z + 6480*t^2 + 128*t*z^14 - 4032*t*z^13 + 56304*t*z^12 - 458496*t*z^11 + 2410128*t*z^10 - 8555904*t*z^9 + 20878992*t*z^8 - 35063568*t*z^7 + 40119984*t*z^6 - 30729888*t*z^5 + 15370128*t*z^4 - 4847040*t*z^3 + 913680*t*z^2 - 93312*t*z + 3888*t + 16*z^16 - 576*z^15 + 9360*z^14 - 90672*z^13 + 582576*z^12 - 2614176*z^11 + 8406432*z^10 - 19580256*z^9 + 33047280*z^8 - 40120272*z^7 + 34547472*z^6 - 20656944*z^5 + 8302176*z^4 - 2122848*z^3 + 309744*z^2 - 19440*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6*z + 1344*t^6 - 896*t^5*z^3 + 6720*t^5*z^2 - 9936*t^5*z - 6432*t^5 - 1120*t^4*z^5 + 13440*t^4*z^4 - 52560*t^4*z^3 + 65040*t^4*z^2 - 2304*t^4*z + 23904*t^4 - 896*t^3*z^7 + 14784*t^3*z^6 - 92592*t^3*z^5 + 266784*t^3*z^4 - 333552*t^3*z^3 + 141552*t^3*z^2 - 52992*t^3*z - 36144*t^3 - 448*t^2*z^9 + 9408*t^2*z^8 - 80784*t^2*z^7 + 361680*t^2*z^6 - 890064*t^2*z^5 + 1167264*t^2*z^4 - 757728*t^2*z^3 + 257040*t^2*z^2 - 17280*t^2*z + 34560*t^2 - 128*t*z^11 + 3264*t*z^10 - 35568*t*z^9 + 215328*t*z^8 - 788256*t*z^7 + 1781712*t*z^6 - 2448432*t*z^5 + 1972800*t*z^4 - 902160*t*z^3 + 216432*t*z^2 - 33696*t*z - 9504*t - 16*z^13 + 480*z^12 - 6336*z^11 + 48288*z^10 - 234384*z^9 + 754272*z^8 - 1626480*z^7 + 2329776*z^6 - 2167488*z^5 + 1267920*z^4 - 443232*z^3 + 83808*z^2 - 6480*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_13 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 13) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : (t + z^2 - 4*z:ℝ)=0 := by
  apply cell_1_13 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z + 2*z^4 - 20*z^3 + 62*z^2 - 60*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 496*t^6*z^2 + 48*t^6 - 1184*t^5*z^3 + 864*t^5*z^2 + 576*t^5*z - 144*t^5 + 1840*t^4*z^4 - 2928*t^4*z^3 - 2160*t^4*z^2 + 1152*t^4*z - 288*t^4 - 1856*t^3*z^5 + 4752*t^3*z^4 + 2352*t^3*z^3 - 4896*t^3*z^2 - 576*t^3*z + 864*t^3 + 1168*t^2*z^6 - 4320*t^2*z^5 - 144*t^2*z^4 + 7920*t^2*z^3 - 432*t^2*z^2 - 864*t^2*z - 416*t*z^7 + 2112*t*z^6 - 1296*t*z^5 - 5040*t*z^4 + 2448*t*z^3 + 5616*t*z^2 - 2592*t*z + 64*z^8 - 432*z^7 + 624*z^6 + 1008*z^5 - 2448*z^4 + 864*z^3:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1184*t^5 - 1840*t^4*z - 8112*t^4 + 1856*t^3*z^2 + 6384*t^3*z + 19248*t^3 - 1168*t^2*z^3 - 2688*t^2*z^2 - 5472*t^2*z - 20064*t^2 + 416*t*z^4 + 384*t*z^3 - 144*t*z^2 + 1968*t*z + 11808*t - 64*z^5 + 48*z^4 + 240*z^3 - 192*z^2 - 720*z - 2736)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_14 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 14) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_14 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z^2 - 640*t^7*z + 208*t^7 + 448*t^6*z^4 - 4480*t^6*z^3 + 12752*t^6*z^2 - 7808*t^6*z + 1264*t^6 + 896*t^5*z^6 - 13440*t^5*z^5 + 72144*t^5*z^4 - 161728*t^5*z^3 + 133632*t^5*z^2 - 43392*t^5*z + 4720*t^5 + 1120*t^4*z^8 - 22400*t^4*z^7 + 176720*t^4*z^6 - 691520*t^4*z^5 + 1385344*t^4*z^4 - 1351888*t^4*z^3 + 644048*t^4*z^2 - 142912*t^4*z + 11680*t^4 + 896*t^3*z^10 - 22400*t^3*z^9 + 233200*t^3*z^8 - 1304960*t^3*z^7 + 4230336*t^3*z^6 - 8016512*t^3*z^5 + 8686704*t^3*z^4 - 5306000*t^3*z^3 + 1775456*t^3*z^2 - 300224*t^3*z + 19936*t^3 + 448*t^2*z^12 - 13440*t^2*z^11 + 173808*t^2*z^10 - 1265920*t^2*z^9 + 5696304*t^2*z^8 - 16372128*t^2*z^7 + 30164624*t^2*z^6 - 35197440*t^2*z^5 + 25601712*t^2*z^4 - 11341136*t^2*z^3 + 2931984*t^2*z^2 - 403296*t^2*z + 22912*t^2 + 128*t*z^14 - 4480*t*z^13 + 69232*t*z^12 - 621248*t*z^11 + 3582400*t*z^10 - 13885312*t*z^9 + 36821728*t*z^8 - 66920528*t*z^7 + 82678496*t*z^6 - 68485168*t*z^5 + 37279760*t*z^4 - 12932336*t*z^3 + 2713904*t*z^2 - 310048*t*z + 14464*t + 16*z^16 - 640*z^15 + 11504*z^14 - 122688*z^13 + 863456*z^12 - 4221200*z^11 + 14704480*z^10 - 36886176*z^9 + 66680560*z^8 - 86329056*z^7 + 79113952*z^6 - 50417872*z^5 + 21748208*z^4 - 6078624*z^3 + 1019072*z^2 - 87680*z + 2560:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6*z + 1792*t^6 - 896*t^5*z^3 + 8064*t^5*z^2 - 15696*t^5*z - 7712*t^5 - 1120*t^4*z^5 + 15680*t^4*z^4 - 72560*t^4*z^3 + 111680*t^4*z^2 - 15184*t^4*z + 37984*t^4 - 896*t^3*z^7 + 17024*t^3*z^6 - 122992*t^3*z^5 + 411104*t^3*z^4 - 605712*t^3*z^3 + 313328*t^3*z^2 - 122016*t^3*z - 63184*t^3 - 448*t^2*z^9 + 10752*t^2*z^8 - 105264*t^2*z^7 + 536224*t^2*z^6 - 1499328*t^2*z^5 + 2234352*t^2*z^4 - 1655888*t^2*z^3 + 654960*t^2*z^2 - 65904*t^2*z + 83408*t^2 - 128*t*z^11 + 3712*t*z^10 - 45808*t*z^9 + 312608*t*z^8 - 1283344*t*z^7 + 3234352*t*z^6 - 4927696*t*z^5 + 4395152*t*z^4 - 2255264*t*z^3 + 614128*t*z^2 - 112160*t*z - 33568*t - 16*z^13 + 544*z^12 - 8096*z^11 + 69168*z^10 - 373952*z^9 + 1330688*z^8 - 3147280*z^7 + 4904448*z^6 - 4936288*z^5 + 3129456*z^4 - 1197280*z^3 + 260224*z^2 - 22976*z + 6912)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_15 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 15) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_15 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z^2 - 384*t^7*z + 80*t^7 + 160*t^6*z^4 - 1728*t^6*z^3 + 5344*t^6*z^2 - 2880*t^6*z + 400*t^6 + 256*t^5*z^6 - 4032*t^5*z^5 + 22704*t^5*z^4 - 52848*t^5*z^3 + 41808*t^5*z^2 - 11808*t^5*z + 1040*t^5 + 304*t^4*z^8 - 6144*t^4*z^7 + 49328*t^4*z^6 - 197136*t^4*z^5 + 402000*t^4*z^4 - 389664*t^4*z^3 + 176048*t^4*z^2 - 35616*t^4*z + 2464*t^4 + 256*t^3*z^10 - 6336*t^3*z^9 + 65584*t^3*z^8 - 366768*t^3*z^7 + 1193824*t^3*z^6 - 2276064*t^3*z^5 + 2464736*t^3*z^4 - 1467504*t^3*z^3 + 460448*t^3*z^2 - 70272*t^3*z + 4256*t^3 + 160*t^2*z^12 - 4608*t^2*z^11 + 57648*t^2*z^10 - 409392*t^2*z^9 + 1811184*t^2*z^8 - 5162688*t^2*z^7 + 9509440*t^2*z^6 - 11142288*t^2*z^5 + 8102544*t^2*z^4 - 3543408*t^2*z^3 + 891120*t^2*z^2 - 117216*t^2*z + 6208*t^2 + 64*t*z^14 - 2112*t*z^13 + 30944*t*z^12 - 265104*t*z^11 + 1471728*t*z^10 - 5544720*t*z^9 + 14443264*t*z^8 - 26055456*t*z^7 + 32217200*t*z^6 - 26783712*t*z^5 + 14576640*t*z^4 - 5017680*t*z^3 + 1044304*t*z^2 - 121632*t*z + 6272*t + 16*z^16 - 576*z^15 + 9424*z^14 - 92592*z^13 + 608224*z^12 - 2815056*z^11 + 9429088*z^10 - 23128272*z^9 + 41611840*z^8 - 54576144*z^7 + 51510448*z^6 - 34301088*z^5 + 15653680*z^4 - 4679424*z^3 + 847360*z^2 - 79488*z + 2560:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z + 768*t^6 - 256*t^5*z^3 + 2496*t^5*z^2 - 5424*t^5*z - 2928*t^5 - 304*t^4*z^5 + 4320*t^4*z^4 - 20672*t^4*z^3 + 33312*t^4*z^2 - 3120*t^4*z + 9120*t^4 - 256*t^3*z^7 + 4800*t^3*z^6 - 34480*t^3*z^5 + 115920*t^3*z^4 - 173584*t^3*z^3 + 87840*t^3*z^2 - 27680*t^3*z - 9888*t^3 - 160*t^2*z^9 + 3648*t^2*z^8 - 34320*t^2*z^7 + 170160*t^2*z^6 - 470400*t^2*z^5 + 705888*t^2*z^4 - 530032*t^2*z^3 + 197904*t^2*z^2 - 27168*t^2*z + 9168*t^2 - 64*t*z^11 + 1728*t*z^10 - 20000*t*z^9 + 129360*t*z^8 - 510384*t*z^7 + 1258176*t*z^6 - 1912672*t*z^5 + 1724688*t*z^4 - 880496*t*z^3 + 240528*t*z^2 - 34944*t*z + 1776*t - 16*z^13 + 480*z^12 - 6400*z^11 + 49824*z^10 - 250240*z^9 + 846000*z^8 - 1951456*z^7 + 3054816*z^6 - 3181840*z^5 + 2137392*z^4 - 885088*z^3 + 208512*z^2 - 24640*z - 288)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_16 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 16) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_16 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 20*z^3 + 64*z^2 - 70*z + 20:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_17 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 17) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_17 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 20*z^3 + 66*z^2 - 80*z + 26:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_18 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 18) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_18 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^12 + 38880*t*z^11 - 510624*t*z^10 + 3856896*t*z^9 - 18523728*t*z^8 + 59127408*t*z^7 - 127656000*t*z^6 + 186767856*t*z^5 - 183356784*t*z^4 + 117886752*t*z^3 - 47253456*t*z^2 + 10650528*t*z - 1026432*t + 1296*z^16 - 51840*z^15 + 939600*z^14 - 10207296*z^13 + 74100096*z^12 - 379597104*z^11 + 1413468144*z^10 - 3886701408*z^9 + 7948907136*z^8 - 12103084800*z^7 + 13662120960*z^6 - 11319288624*z^5 + 6759202464*z^4 - 2819015136*z^3 + 776616336*z^2 - 126647712*z + 9237888:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^9 - 31104*t*z^8 + 312336*t*z^7 - 1699056*t*z^6 + 5425056*t*z^5 - 10348560*t*z^4 + 11641968*t*z^3 - 7503840*t*z^2 + 2510352*t*z - 364176*t - 1296*z^13 + 44064*z^12 - 663552*z^11 + 5825520*z^10 - 33042816*z^9 + 126919872*z^8 - 337087008*z^7 + 622772064*z^6 - 797732064*z^5 + 700482816*z^4 - 411319296*z^3 + 153831312*z^2 - 32892480*z + 3220560)*hf
  · have hr : (-1296*t*z^12 + 34992*t*z^11 - 417312*t*z^10 + 2888784*t*z^9 - 12836880*t*z^8 + 38282544*t*z^7 - 77963472*t*z^6 + 108527040*t*z^5 - 102045744*t*z^4 + 63095760*t*z^3 - 24362208*t*z^2 + 5287680*t*z - 489888*t + 1296*z^16 - 46656*z^15 + 765936*z^14 - 7585488*z^13 + 50534928*z^12 - 239183280*z^11 + 828517248*z^10 - 2133851040*z^9 + 4114478592*z^8 - 5942311632*z^7 + 6395806656*z^6 - 5073824448*z^5 + 2910114864*z^4 - 1168251984*z^3 + 310176864*z^2 - 48771072*z + 3429216:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^9 - 27216*t*z^8 + 242352*t*z^7 - 1185840*t*z^6 + 3459024*t*z^5 - 6128784*t*z^4 + 6502032*t*z^3 - 3978720*t*z^2 + 1268784*t*z - 168480*t - 1296*z^13 + 38880*z^12 - 520992*z^11 + 4105728*z^10 - 21094992*z^9 + 74098800*z^8 - 181752336*z^7 + 313162848*z^6 - 377434080*z^5 + 313984512*z^4 - 175504320*z^3 + 62635680*z^2 - 12808368*z + 1167696)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_19 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 19) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_19 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z + 2*z^4 - 20*z^3 + 62*z^2 - 60*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 192*t^6*z^4 - 1920*t^6*z^3 + 6448*t^6*z^2 - 5760*t^6*z + 1776*t^6 - 1152*t^5*z^5 + 11088*t^5*z^4 - 32576*t^5*z^3 + 22032*t^5*z^2 + 3168*t^5*z - 4032*t^5 + 864*t^4*z^8 - 17280*t^4*z^7 + 143280*t^4*z^6 - 621504*t^4*z^5 + 1477840*t^4*z^4 - 1895952*t^4*z^3 + 1326672*t^4*z^2 - 486144*t^4*z + 73584*t^4 - 3456*t^3*z^9 + 67824*t^3*z^8 - 539520*t^3*z^7 + 2202720*t^3*z^6 - 4815872*t^3*z^5 + 5354496*t^3*z^4 - 2534352*t^3*z^3 - 96480*t^3*z^2 + 476352*t^3*z - 111888*t^3 + 1728*t^2*z^12 - 51840*t^2*z^11 + 685584*t^2*z^10 - 5232384*t^2*z^9 + 25369488*t^2*z^8 - 81285408*t^2*z^7 + 174388192*t^2*z^6 - 250644672*t^2*z^5 + 240203520*t^2*z^4 - 151137648*t^2*z^3 + 59972832*t^2*z^2 - 13619232*t^2*z + 1349136*t^2 - 3456*t*z^13 + 102384*t*z^12 - 1325376*t*z^11 + 9819792*t*z^10 - 45832032*t*z^9 + 139881024*t*z^8 - 280987760*t*z^7 + 365078400*t*z^6 - 291369312*t*z^5 + 121172688*t*z^4 - 3782304*t*z^3 - 19679328*t*z^2 + 7952256*t*z - 1026432*t + 1296*z^16 - 51840*z^15 + 941328*z^14 - 10259136*z^13 + 74781360*z^12 - 384745680*z^11 + 1438184784*z^10 - 3965411136*z^9 + 8117998384*z^8 - 12348649296*z^7 + 13901257344*z^6 - 11472093792*z^5 + 6820348752*z^4 - 2832858144*z^3 + 777965472*z^2 - 126647712*z + 9237888:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6*z + 768*t^6 + 1152*t^5*z^2 - 4176*t^5*z - 2848*t^5 - 864*t^4*z^5 + 12096*t^4*z^4 - 62928*t^4*z^3 + 132480*t^4*z^2 - 80320*t^4*z + 32928*t^4 + 3456*t^3*z^6 - 47088*t^3*z^5 + 225888*t^3*z^4 - 413232*t^3*z^3 + 162224*t^3*z^2 + 15600*t^3*z - 71760*t^3 - 1728*t^2*z^9 + 41472*t^2*z^8 - 421200*t^2*z^7 + 2326752*t^2*z^6 - 7493760*t^2*z^5 + 14118480*t^2*z^4 - 15253216*t^2*z^3 + 9577776*t^2*z^2 - 3102480*t^2*z + 563136*t^2 + 3456*t*z^10 - 81648*t*z^9 + 804384*t*z^8 - 4248288*t*z^7 + 12857904*t*z^6 - 22085856*t*z^5 + 20006624*t*z^4 - 7692240*t*z^3 - 1101312*t*z^2 + 1469472*t*z - 565776*t - 1296*z^13 + 44064*z^12 - 665280*z^11 + 5866992*z^10 - 33459696*z^9 + 129188736*z^8 - 344314128*z^7 + 636448656*z^6 - 812913088*z^5 + 710190480*z^4 - 414550704*z^3 + 154335984*z^2 - 32805072*z + 3351744)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_20 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 20) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_20 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 20*z^3 + 66*z^2 - 80*z + 26:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_21 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 21) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_21 z t hf hn0 hn1 hn2 hn3
  · have hr : (6*z^2 - 30*z + 14:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_22 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 22) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_22 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 16*z^3 + 44*z^2 - 54*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_23 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 23) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_23 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 4*t*z^2 - 20*t*z + 6*t + 2*z^4 - 20*z^3 + 62*z^2 - 60*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8 + 64*t^7*z^2 - 448*t^7*z + 144*t^7 + 160*t^6*z^4 - 2048*t^6*z^3 + 7552*t^6*z^2 - 5424*t^6*z + 1056*t^6 + 256*t^5*z^6 - 4800*t^5*z^5 + 32304*t^5*z^4 - 90688*t^5*z^3 + 90576*t^5*z^2 - 35136*t^5*z + 4608*t^5 + 304*t^4*z^8 - 7360*t^4*z^7 + 70800*t^4*z^6 - 339616*t^4*z^5 + 835600*t^4*z^4 - 995616*t^4*z^3 + 582048*t^4*z^2 - 161568*t^4*z + 16992*t^4 + 256*t^3*z^10 - 7616*t^3*z^9 + 94768*t^3*z^8 - 636832*t^3*z^7 + 2489936*t^3*z^6 - 5710048*t^3*z^5 + 7507104*t^3*z^4 - 5609136*t^3*z^3 + 2330208*t^3*z^2 - 499680*t^3*z + 43200*t^3 + 160*t^2*z^12 - 5568*t^2*z^11 + 84048*t^2*z^10 - 718880*t^2*z^9 + 3821712*t^2*z^8 - 13057584*t^2*z^7 + 28793392*t^2*z^6 - 40570128*t^2*z^5 + 36145728*t^2*z^4 - 20030256*t^2*z^3 + 6651936*t^2*z^2 - 1207872*t^2*z + 92016*t^2 + 64*t*z^14 - 2560*t*z^13 + 45408*t*z^12 - 469952*t*z^11 + 3142208*t*z^10 - 14204640*t*z^9 + 44224432*t*z^8 - 95113744*t*z^7 + 140512608*t*z^6 - 141216768*t*z^5 + 95153184*t*z^4 - 41930208*t*z^3 + 11533104*t*z^2 - 1793664*t*z + 120528*t + 16*z^16 - 704*z^15 + 14032*z^14 - 167312*z^13 + 1327840*z^12 - 7387328*z^11 + 29579536*z^10 - 86265872*z^9 + 183775312*z^8 - 285131328*z^7 + 319903104*z^6 - 256532400*z^5 + 144282528*z^4 - 55137888*z^3 + 13532832*z^2 - 1909008*z + 116640:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z + 1088*t^6 - 256*t^5*z^3 + 3264*t^5*z^2 - 10416*t^5*z - 1952*t^5 - 304*t^4*z^5 + 5536*t^4*z^4 - 34848*t^4*z^3 + 79792*t^4*z^2 - 26608*t^4*z + 13296*t^4 - 256*t^3*z^7 + 6080*t^3*z^6 - 55984*t^3*z^5 + 245440*t^3*z^4 - 495200*t^3*z^3 + 361936*t^3*z^2 - 142368*t^3*z + 11904*t^3 - 160*t^2*z^9 + 4608*t^2*z^8 - 54960*t^2*z^7 + 347168*t^2*z^6 - 1230240*t^2*z^5 + 2386752*t^2*z^4 - 2359216*t^2*z^3 + 1243344*t^2*z^2 - 292464*t^2*z + 7728*t^2 - 64*t*z^11 + 2176*t*z^10 - 31776*t*z^9 + 259520*t*z^8 - 1292576*t*z^7 + 4018176*t*z^6 - 7703632*t*z^5 + 8850640*t*z^4 - 6021552*t*z^3 + 2320800*t*z^2 - 482496*t*z + 83376*t - 16*z^13 + 608*z^12 - 10240*z^11 + 100352*z^10 - 631744*z^9 + 2662976*z^8 - 7614928*z^7 + 14714288*z^6 - 18966304*z^5 + 16060128*z^4 - 8702736*z^3 + 2875920*z^2 - 522000*z + 14400)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_24 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 24) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_24 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^12 + 34992*t*z^11 - 417312*t*z^10 + 2888784*t*z^9 - 12836880*t*z^8 + 38282544*t*z^7 - 77963472*t*z^6 + 108527040*t*z^5 - 102045744*t*z^4 + 63095760*t*z^3 - 24362208*t*z^2 + 5287680*t*z - 489888*t + 1296*z^16 - 46656*z^15 + 765936*z^14 - 7585488*z^13 + 50534928*z^12 - 239183280*z^11 + 828517248*z^10 - 2133851040*z^9 + 4114478592*z^8 - 5942311632*z^7 + 6395806656*z^6 - 5073824448*z^5 + 2910114864*z^4 - 1168251984*z^3 + 310176864*z^2 - 48771072*z + 3429216:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^9 - 27216*t*z^8 + 242352*t*z^7 - 1185840*t*z^6 + 3459024*t*z^5 - 6128784*t*z^4 + 6502032*t*z^3 - 3978720*t*z^2 + 1268784*t*z - 168480*t - 1296*z^13 + 38880*z^12 - 520992*z^11 + 4105728*z^10 - 21094992*z^9 + 74098800*z^8 - 181752336*z^7 + 313162848*z^6 - 377434080*z^5 + 313984512*z^4 - 175504320*z^3 + 62635680*z^2 - 12808368*z + 1167696)*hf
  · have hr : (-1296*t*z^12 + 38880*t*z^11 - 510624*t*z^10 + 3856896*t*z^9 - 18523728*t*z^8 + 59127408*t*z^7 - 127656000*t*z^6 + 186767856*t*z^5 - 183356784*t*z^4 + 117886752*t*z^3 - 47253456*t*z^2 + 10650528*t*z - 1026432*t + 1296*z^16 - 51840*z^15 + 939600*z^14 - 10207296*z^13 + 74100096*z^12 - 379597104*z^11 + 1413468144*z^10 - 3886701408*z^9 + 7948907136*z^8 - 12103084800*z^7 + 13662120960*z^6 - 11319288624*z^5 + 6759202464*z^4 - 2819015136*z^3 + 776616336*z^2 - 126647712*z + 9237888:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^9 - 31104*t*z^8 + 312336*t*z^7 - 1699056*t*z^6 + 5425056*t*z^5 - 10348560*t*z^4 + 11641968*t*z^3 - 7503840*t*z^2 + 2510352*t*z - 364176*t - 1296*z^13 + 44064*z^12 - 663552*z^11 + 5825520*z^10 - 33042816*z^9 + 126919872*z^8 - 337087008*z^7 + 622772064*z^6 - 797732064*z^5 + 700482816*z^4 - 411319296*z^3 + 153831312*z^2 - 32892480*z + 3220560)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_25 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 25) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_25 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 16*z^3 + 44*z^2 - 54*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_26 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 26) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_26 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 16*z^3 + 42*z^2 - 46*z + 14:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_27 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 27) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_27 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 12*t*z + 2*t + 2*z^4 - 18*z^3 + 52*z^2 - 48*z + 14:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(6 - 2*z)*hf
  · have hr : (16*t^8 - 192*t^7*z + 16*t^7 + 192*t^6*z^4 - 1728*t^6*z^3 + 5904*t^6*z^2 - 4848*t^6*z + 1216*t^6 - 1728*t^5*z^5 + 15696*t^5*z^4 - 48384*t^5*z^3 + 46512*t^5*z^2 - 14400*t^5*z + 832*t^5 + 864*t^4*z^8 - 15552*t^4*z^7 + 120528*t^4*z^6 - 498096*t^4*z^5 + 1132560*t^4*z^4 - 1360512*t^4*z^3 + 861696*t^4*z^2 - 275232*t^4*z + 35104*t^4 - 5184*t^3*z^9 + 93744*t^3*z^8 - 705024*t^3*z^7 + 2808864*t^3*z^6 - 6295104*t^3*z^5 + 7908240*t^3*z^4 - 5499216*t^3*z^3 + 2014560*t^3*z^2 - 337056*t^3*z + 16000*t^3 + 1728*t^2*z^12 - 46656*t^2*z^11 + 563760*t^2*z^10 - 3977424*t^2*z^9 + 17975520*t^2*z^8 - 53932608*t^2*z^7 + 108387936*t^2*z^6 - 145265184*t^2*z^5 + 128628288*t^2*z^4 - 73852560*t^2*z^3 + 26367264*t^2*z^2 - 5311296*t^2*z + 460528*t^2 - 5184*t*z^13 + 140400*t*z^12 - 1679616*t*z^11 + 11647152*t*z^10 - 51694848*t*z^9 + 153288720*t*z^8 - 308667888*t*z^7 + 422752176*t*z^6 - 390815712*t*z^5 + 239461200*t*z^4 - 93850560*t*z^3 + 21977712*t*z^2 - 2668224*t*z + 115216*t + 1296*z^16 - 46656*z^15 + 765936*z^14 - 7580304*z^13 + 50391504*z^12 - 237422016*z^11 + 815889024*z^10 - 2075284800*z^9 + 3930282864*z^8 - 5540708016*z^7 + 5783773680*z^6 - 4422421584*z^5 + 2430922944*z^4 - 930543264*z^3 + 234541008*z^2 - 34872144*z + 2310400:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6*z + 576*t^6 + 1728*t^5*z^2 - 5328*t^5*z + 864*t^5 - 864*t^4*z^5 + 10368*t^4*z^4 - 50544*t^4*z^3 + 98928*t^4*z^2 - 52992*t^4*z + 576*t^4 + 5184*t^3*z^6 - 62640*t^3*z^5 + 282528*t^3*z^4 - 534384*t^3*z^3 + 358128*t^3*z^2 - 102432*t^3*z + 58320*t^3 - 1728*t^2*z^9 + 36288*t^2*z^8 - 330480*t^2*z^7 + 1662768*t^2*z^6 - 4915728*t^2*z^5 + 8481888*t^2*z^4 - 8266752*t^2*z^3 + 4580496*t^2*z^2 - 1298880*t^2*z + 34560*t^2 + 5184*t*z^10 - 109296*t*z^9 + 977184*t*z^8 - 4784832*t*z^7 + 13863312*t*z^6 - 24113808*t*z^5 + 24860736*t*z^4 - 14973552*t*z^3 + 4886352*t*z^2 - 798912*t*z + 159264*t - 1296*z^13 + 38880*z^12 - 520992*z^11 + 4100544*z^10 - 20982672*z^9 + 73058112*z^8 - 176394672*z^7 + 296445744*z^6 - 344882016*z^5 + 274220208*z^4 - 145177056*z^3 + 48731328*z^2 - 9280848*z + 745056)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_28 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 28) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_28 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z + 2*z^4 - 20*z^3 + 62*z^2 - 60*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8 + 192*t^7*z^2 - 896*t^7*z + 336*t^7 + 1056*t^6*z^4 - 9984*t^6*z^3 + 27712*t^6*z^2 - 19392*t^6*z + 3984*t^6 + 3456*t^5*z^6 - 49536*t^5*z^5 + 258480*t^5*z^4 - 584672*t^5*z^3 + 539856*t^5*z^2 - 213984*t^5*z + 30528*t^5 + 7344*t^4*z^8 - 141696*t^4*z^7 + 1091088*t^4*z^6 - 4247232*t^4*z^5 + 8764336*t^4*z^4 - 9414960*t^4*z^3 + 5316480*t^4*z^2 - 1502208*t^4*z + 167760*t^4 + 10368*t^3*z^10 - 252288*t^3*z^9 + 2578608*t^3*z^8 - 14338464*t^3*z^7 + 47036400*t^3*z^6 - 92872064*t^3*z^5 + 109840080*t^3*z^4 - 77667024*t^3*z^3 + 32078016*t^3*z^2 - 7130304*t^3*z + 658800*t^3 + 9504*t^2*z^12 - 279936*t^2*z^11 + 3578256*t^2*z^10 - 25980480*t^2*z^9 + 117879696*t^2*z^8 - 347222736*t^2*z^7 + 671553664*t^2*z^6 - 852055056*t^2*z^5 + 706348224*t^2*z^4 - 377107344*t^2*z^3 + 124648848*t^2*z^2 - 23183712*t^2*z + 1854576*t^2 + 5184*t*z^14 - 179712*t*z^13 + 2765664*t*z^12 - 24873696*t*z^11 + 144908784*t*z^10 - 573370560*t*z^9 + 1574372640*t*z^8 - 3022606256*t*z^7 + 4058004144*t*z^6 - 3794835168*t*z^5 + 2446118064*t*z^4 - 1061714016*t*z^3 + 295655616*t*z^2 - 47640960*t*z + 3374784*t + 1296*z^16 - 51840*z^15 + 936144*z^14 - 10082880*z^13 + 72110304*z^12 - 360969264*z^11 + 1300192752*z^10 - 3416875680*z^9 + 6588479296*z^8 - 9327170112*z^7 + 9665381184*z^6 - 7275487248*z^5 + 3917238336*z^4 - 1465744896*z^3 + 361250928*z^2 - 52635744*z + 3429216:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6*z + 3648*t^6 - 3456*t^5*z^3 + 28800*t^5*z^2 - 54576*t^5*z - 12352*t^5 - 7344*t^4*z^5 + 97632*t^4*z^4 - 439200*t^4*z^3 + 711312*t^4*z^2 - 250768*t^4*z + 190944*t^4 - 10368*t^3*z^7 + 190080*t^3*z^6 - 1344816*t^3*z^5 + 4527744*t^3*z^4 - 7196352*t^3*z^3 + 4909808*t^3*z^2 - 2030832*t^3*z - 295296*t^3 - 9504*t^2*z^9 + 222912*t^2*z^8 - 2155248*t^2*z^7 + 11014272*t^2*z^6 - 31728096*t^2*z^5 + 51259968*t^2*z^4 - 45398176*t^2*z^3 + 23142000*t^2*z^2 - 5132736*t^2*z + 1838400*t^2 - 5184*t*z^11 + 148608*t*z^10 - 1827360*t*z^9 + 12556512*t*z^8 - 52677648*t*z^7 + 138813984*t*z^6 - 229720368*t*z^5 + 236925248*t*z^4 - 152527392*t*z^3 + 58182480*t*z^2 - 13500912*t*z - 515952*t - 1296*z^13 + 44064*z^12 - 660096*z^11 + 5721840*z^10 - 31706208*z^9 + 117255168*z^8 - 294140352*z^7 + 501618432*z^6 - 579740032*z^5 + 451742976*z^4 - 232407744*z^3 + 76133904*z^2 - 13536288*z + 2098800)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_29 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 29) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_29 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 4*t*z^2 - 20*t*z + 6*t + 2*z^4 - 20*z^3 + 62*z^2 - 60*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8 + 256*t^7*z^2 - 1216*t^7*z + 528*t^7 + 1792*t^6*z^4 - 17024*t^6*z^3 + 48016*t^6*z^2 - 35952*t^6*z + 7872*t^6 + 7168*t^5*z^6 - 102144*t^5*z^5 + 531840*t^5*z^4 - 1210576*t^5*z^3 + 1147968*t^5*z^2 - 470304*t^5*z + 69408*t^5 + 17920*t^4*z^8 - 340480*t^4*z^7 + 2585280*t^4*z^6 - 9948640*t^4*z^5 + 20390416*t^4*z^4 - 21924528*t^4*z^3 + 12443760*t^4*z^2 - 3535488*t^4*z + 396288*t^4 + 28672*t^3*z^10 - 680960*t^3*z^9 + 6795520*t^3*z^8 - 36918400*t^3*z^7 + 118464128*t^3*z^6 - 229232464*t^3*z^5 + 266380800*t^3*z^4 - 185409024*t^3*z^3 + 75429360*t^3*z^2 - 16510464*t^3*z + 1500768*t^3 + 28672*t^2*z^12 - 817152*t^2*z^11 + 10104576*t^2*z^10 - 70960640*t^2*z^9 + 311362944*t^2*z^8 - 886830432*t^2*z^7 + 1658327488*t^2*z^6 - 2033955216*t^2*z^5 + 1629295920*t^2*z^4 - 839800800*t^2*z^3 + 267607152*t^2*z^2 - 47887200*t^2*z + 3676752*t^2 + 16384*t*z^14 - 544768*t*z^13 + 8036352*t*z^12 - 69234944*t*z^11 + 386049536*t*z^10 - 1460492736*t*z^9 + 3829388032*t*z^8 - 7009356880*t*z^7 + 8955612816*t*z^6 - 7954886016*t*z^5 + 4861172448*t*z^4 - 1996406640*t*z^3 + 524968128*t*z^2 - 79706592*t*z + 5307120*t + 4096*z^16 - 155648*z^15 + 2667520*z^14 - 27233792*z^13 + 184344832*z^12 - 871780736*z^11 + 2959633408*z^10 - 7309597280*z^9 + 13199234752*z^8 - 17426938272*z^7 + 16765676880*z^6 - 11660048064*z^5 + 5771447568*z^4 - 1975216752*z^3 + 442980576*z^2 - 58432752*z + 3429216:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1792*t^6*z + 6272*t^6 - 7168*t^5*z^3 + 59136*t^5*z^2 - 112512*t^5*z - 18224*t^5 - 17920*t^4*z^5 + 232960*t^4*z^4 - 1026240*t^4*z^3 + 1640800*t^4*z^2 - 610576*t^4*z + 415152*t^4 - 28672*t^3*z^7 + 508928*t^3*z^6 - 3483904*t^3*z^5 + 11348608*t^3*z^4 - 17490560*t^3*z^3 + 11699920*t^3*z^2 - 4720416*t^3*z - 684432*t^3 - 28672*t^2*z^9 + 645120*t^2*z^8 - 5975808*t^2*z^7 + 29213696*t^2*z^6 - 80363136*t^2*z^5 + 123800928*t^2*z^4 - 104612608*t^2*z^3 + 50981808*t^2*z^2 - 10488816*t^2*z + 4193808*t^2 - 16384*t*z^11 + 446464*t*z^10 - 5210112*t*z^9 + 33906944*t*z^8 - 134377472*t*z^7 + 333435072*t*z^6 - 517659520*t*z^5 + 499351696*t*z^4 - 300261744*t*z^3 + 106171728*t*z^2 - 23731296*t*z - 2311920*t - 4096*z^13 + 131072*z^12 - 1844224*z^11 + 14976512*z^10 - 77494528*z^9 + 266492288*z^8 - 618299392*z^7 + 968886752*z^6 - 1021742848*z^5 + 721602240*z^4 - 333717552*z^3 + 98094048*z^2 - 14618592*z + 3506112)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_30 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 30) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_30 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 12*t*z + 2*t + 2*z^4 - 18*z^3 + 52*z^2 - 48*z + 14:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(6 - 2*z)*hf
  · have hr : (16*t^8 + 192*t^7*z^2 - 960*t^7*z + 400*t^7 + 1056*t^6*z^4 - 10560*t^6*z^3 + 31008*t^6*z^2 - 23088*t^6*z + 4960*t^6 + 3456*t^5*z^6 - 51840*t^5*z^5 + 282672*t^5*z^4 - 667152*t^5*z^3 + 641376*t^5*z^2 - 262944*t^5*z + 38560*t^5 + 7344*t^4*z^8 - 146880*t^4*z^7 + 1170288*t^4*z^6 - 4704048*t^4*z^5 + 9996768*t^4*z^4 - 11015568*t^4*z^3 + 6346704*t^4*z^2 - 1818240*t^4*z + 204544*t^4 + 10368*t^3*z^10 - 259200*t^3*z^9 + 2716848*t^3*z^8 - 15460848*t^3*z^7 + 51779952*t^3*z^6 - 104058864*t^3*z^5 + 124766400*t^3*z^4 - 89035104*t^3*z^3 + 36936624*t^3*z^2 - 8209344*t^3*z + 755296*t^3 + 9504*t^2*z^12 - 285120*t^2*z^11 + 3705264*t^2*z^10 - 27296784*t^2*z^9 + 125385408*t^2*z^8 - 372922272*t^2*z^7 + 725954832*t^2*z^6 - 923519232*t^2*z^5 + 764320608*t^2*z^4 - 405504000*t^2*z^3 + 132561072*t^2*z^2 - 24267744*t^2*z + 1901968*t^2 + 5184*t*z^14 - 181440*t*z^13 + 2814048*t*z^12 - 25457328*t*z^11 + 148865040*t*z^10 - 589837248*t*z^9 + 1617421392*t*z^8 - 3091310352*t*z^7 + 4116635136*t*z^6 - 3803359968*t*z^5 + 2412101088*t*z^4 - 1025795664*t*z^3 + 278751936*t*z^2 - 43662624*t*z + 2995312*t + 1296*z^16 - 51840*z^15 + 934416*z^14 - 10025856*z^13 + 71275248*z^12 - 353815776*z^11 + 1260376848*z^10 - 3265451280*z^9 + 6184852416*z^8 - 8564117040*z^7 + 8638921296*z^6 - 6296826816*z^5 + 3264377088*z^4 - 1169100336*z^3 + 274093968*z^2 - 37752240*z + 2310400:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6*z + 4224*t^6 - 3456*t^5*z^3 + 31104*t^5*z^2 - 64944*t^5*z - 12816*t^5 - 7344*t^4*z^5 + 102816*t^4*z^4 - 487296*t^4*z^3 + 832896*t^4*z^2 - 305280*t^4*z + 225936*t^4 - 10368*t^3*z^7 + 196992*t^3*z^6 - 1441584*t^3*z^5 + 5007312*t^3*z^4 - 8170848*t^3*z^3 + 5643216*t^3*z^2 - 2347536*t^3*z - 351600*t^3 - 9504*t^2*z^9 + 228096*t^2*z^8 - 2251152*t^2*z^7 + 11708496*t^2*z^6 - 34189776*t^2*z^5 + 55653696*t^2*z^4 - 49199184*t^2*z^3 + 24871536*t^2*z^2 - 5337648*t^2*z + 2036736*t^2 - 5184*t*z^11 + 150336*t*z^10 - 1865376*t*z^9 + 12896496*t*z^8 - 54246672*t*z^7 + 142692624*t*z^6 - 234356112*t*z^5 + 238200048*t*z^4 - 150151968*t*z^3 + 55579392*t*z^2 - 12656880*t*z - 816048*t - 1296*z^13 + 44064*z^12 - 658368*z^11 + 5675184*z^10 - 31166640*z^9 + 113764176*z^8 - 280266480*z^7 + 466474896*z^6 - 522312192*z^5 + 391170384*z^4 - 191664576*z^3 + 59369328*z^2 - 9668784*z + 1769952)*hf
  · have hr : (16*t^8 - 192*t^7*z + 16*t^7 + 192*t^6*z^4 - 1728*t^6*z^3 + 5904*t^6*z^2 - 4848*t^6*z + 1216*t^6 - 1728*t^5*z^5 + 15696*t^5*z^4 - 48384*t^5*z^3 + 46512*t^5*z^2 - 14400*t^5*z + 832*t^5 + 864*t^4*z^8 - 15552*t^4*z^7 + 120528*t^4*z^6 - 498096*t^4*z^5 + 1132560*t^4*z^4 - 1360512*t^4*z^3 + 861696*t^4*z^2 - 275232*t^4*z + 35104*t^4 - 5184*t^3*z^9 + 93744*t^3*z^8 - 705024*t^3*z^7 + 2808864*t^3*z^6 - 6295104*t^3*z^5 + 7908240*t^3*z^4 - 5499216*t^3*z^3 + 2014560*t^3*z^2 - 337056*t^3*z + 16000*t^3 + 1728*t^2*z^12 - 46656*t^2*z^11 + 563760*t^2*z^10 - 3977424*t^2*z^9 + 17975520*t^2*z^8 - 53932608*t^2*z^7 + 108387936*t^2*z^6 - 145265184*t^2*z^5 + 128628288*t^2*z^4 - 73852560*t^2*z^3 + 26367264*t^2*z^2 - 5311296*t^2*z + 460528*t^2 - 5184*t*z^13 + 140400*t*z^12 - 1679616*t*z^11 + 11647152*t*z^10 - 51694848*t*z^9 + 153288720*t*z^8 - 308667888*t*z^7 + 422752176*t*z^6 - 390815712*t*z^5 + 239461200*t*z^4 - 93850560*t*z^3 + 21977712*t*z^2 - 2668224*t*z + 115216*t + 1296*z^16 - 46656*z^15 + 765936*z^14 - 7580304*z^13 + 50391504*z^12 - 237422016*z^11 + 815889024*z^10 - 2075284800*z^9 + 3930282864*z^8 - 5540708016*z^7 + 5783773680*z^6 - 4422421584*z^5 + 2430922944*z^4 - 930543264*z^3 + 234541008*z^2 - 34872144*z + 2310400:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6*z + 576*t^6 + 1728*t^5*z^2 - 5328*t^5*z + 864*t^5 - 864*t^4*z^5 + 10368*t^4*z^4 - 50544*t^4*z^3 + 98928*t^4*z^2 - 52992*t^4*z + 576*t^4 + 5184*t^3*z^6 - 62640*t^3*z^5 + 282528*t^3*z^4 - 534384*t^3*z^3 + 358128*t^3*z^2 - 102432*t^3*z + 58320*t^3 - 1728*t^2*z^9 + 36288*t^2*z^8 - 330480*t^2*z^7 + 1662768*t^2*z^6 - 4915728*t^2*z^5 + 8481888*t^2*z^4 - 8266752*t^2*z^3 + 4580496*t^2*z^2 - 1298880*t^2*z + 34560*t^2 + 5184*t*z^10 - 109296*t*z^9 + 977184*t*z^8 - 4784832*t*z^7 + 13863312*t*z^6 - 24113808*t*z^5 + 24860736*t*z^4 - 14973552*t*z^3 + 4886352*t*z^2 - 798912*t*z + 159264*t - 1296*z^13 + 38880*z^12 - 520992*z^11 + 4100544*z^10 - 20982672*z^9 + 73058112*z^8 - 176394672*z^7 + 296445744*z^6 - 344882016*z^5 + 274220208*z^4 - 145177056*z^3 + 48731328*z^2 - 9280848*z + 745056)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_31 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 31) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_31 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 4*t*z^2 - 20*t*z + 4*t + 2*z^4 - 20*z^3 + 60*z^2 - 50*z + 14:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8 + 192*t^7*z^2 - 1024*t^7*z + 464*t^7 + 1056*t^6*z^4 - 11136*t^6*z^3 + 34624*t^6*z^2 - 27424*t^6*z + 6256*t^6 + 3456*t^5*z^6 - 54144*t^5*z^5 + 309168*t^5*z^4 - 765760*t^5*z^3 + 772656*t^5*z^2 - 332256*t^5*z + 51008*t^5 + 7344*t^4*z^8 - 152064*t^4*z^7 + 1256976*t^4*z^6 - 5250720*t^4*z^5 + 11605648*t^4*z^4 - 13288208*t^4*z^3 + 7946976*t^4*z^2 - 2359712*t^4*z + 274672*t^4 + 10368*t^3*z^10 - 266112*t^3*z^9 + 2868912*t^3*z^8 - 16818240*t^3*z^7 + 58083024*t^3*z^6 - 120380416*t^3*z^5 + 148694032*t^3*z^4 - 109173712*t^3*z^3 + 46535168*t^3*z^2 - 10610816*t^3*z + 999920*t^3 + 9504*t^2*z^12 - 290304*t^2*z^11 + 3847824*t^2*z^10 - 28955232*t^2*z^9 + 136010736*t^2*z^8 - 413903664*t^2*z^7 + 824214688*t^2*z^6 - 1071394896*t^2*z^5 + 904749216*t^2*z^4 - 489023536*t^2*z^3 + 162606480*t^2*z^2 - 30229248*t^2*z + 2401936*t^2 + 5184*t*z^14 - 183168*t*z^13 + 2872800*t*z^12 - 26320896*t*z^11 + 156072528*t*z^10 - 627572160*t*z^9 + 1746854688*t*z^8 - 3387485968*t*z^7 + 4571731088*t*z^6 - 4274041632*t*z^5 + 2738148784*t*z^4 - 1174193312*t*z^3 + 321155712*t*z^2 - 50534464*t*z + 3475328*t + 1296*z^16 - 51840*z^15 + 936144*z^14 - 10079424*z^13 + 72003168*z^12 - 359511696*z^11 + 1288759440*z^10 - 3359685504*z^9 + 6397575904*z^8 - 8893119328*z^7 + 8987780704*z^6 - 6548424496*z^5 + 3385060672*z^4 - 1205787232*z^3 + 280465840*z^2 - 38232256*z + 2310400:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6*z + 4800*t^6 - 3456*t^5*z^3 + 33408*t^5*z^2 - 77616*t^5*z - 10976*t^5 - 7344*t^4*z^5 + 108000*t^4*z^4 - 542880*t^4*z^3 + 999408*t^4*z^2 - 399280*t^4*z + 269216*t^4 - 10368*t^3*z^7 + 203904*t^3*z^6 - 1552176*t^3*z^5 + 5638944*t^3*z^4 - 9668064*t^3*z^3 + 6965008*t^3*z^2 - 2974576*t^3*z - 363008*t^3 - 9504*t^2*z^9 + 233280*t^2*z^8 - 2362608*t^2*z^7 + 12651552*t^2*z^6 - 38138112*t^2*z^5 + 64123200*t^2*z^4 - 58277824*t^2*z^3 + 30204816*t^2*z^2 - 6650304*t^2*z + 2444896*t^2 - 5184*t*z^11 + 152064*t*z^10 - 1913760*t*z^9 + 13454208*t*z^8 - 57667248*t*z^7 + 154739520*t*z^6 - 259049712*t*z^5 + 267530272*t*z^4 - 170883488*t*z^3 + 63819120*t*z^2 - 14691856*t*z - 980368*t - 1296*z^13 + 44064*z^12 - 660096*z^11 + 5718384*z^10 - 31619808*z^9 + 116347104*z^8 - 288943392*z^7 + 484041792*z^6 - 543793312*z^5 + 407153152*z^4 - 198596608*z^3 + 61086544*z^2 - 9712480*z + 1943632)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_32 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 32) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_32 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_33 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 33) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_33 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^12 + 34992*t*z^11 - 417312*t*z^10 + 2888784*t*z^9 - 12836880*t*z^8 + 38282544*t*z^7 - 77963472*t*z^6 + 108527040*t*z^5 - 102045744*t*z^4 + 63095760*t*z^3 - 24362208*t*z^2 + 5287680*t*z - 489888*t + 1296*z^16 - 46656*z^15 + 765936*z^14 - 7585488*z^13 + 50534928*z^12 - 239183280*z^11 + 828517248*z^10 - 2133851040*z^9 + 4114478592*z^8 - 5942311632*z^7 + 6395806656*z^6 - 5073824448*z^5 + 2910114864*z^4 - 1168251984*z^3 + 310176864*z^2 - 48771072*z + 3429216:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^9 - 27216*t*z^8 + 242352*t*z^7 - 1185840*t*z^6 + 3459024*t*z^5 - 6128784*t*z^4 + 6502032*t*z^3 - 3978720*t*z^2 + 1268784*t*z - 168480*t - 1296*z^13 + 38880*z^12 - 520992*z^11 + 4105728*z^10 - 21094992*z^9 + 74098800*z^8 - 181752336*z^7 + 313162848*z^6 - 377434080*z^5 + 313984512*z^4 - 175504320*z^3 + 62635680*z^2 - 12808368*z + 1167696)*hf
  · have hr : (-2592*t*z^6 + 22032*t*z^5 - 67392*t*z^4 + 88128*t*z^3 - 45360*t*z^2 + 7776*t*z + 2592*z^8 - 27216*z^7 + 114048*z^6 - 244944*z^5 + 289008*z^4 - 186624*z^3 + 60912*z^2 - 7776*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2592*t*z^3 - 6480*t*z^2 + 5184*t*z + 9072*t - 2592*z^5 + 11664*z^4 - 20736*z^3 + 7776*z^2 - 20736*z - 69984)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_34 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 34) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_34 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_35 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 35) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_35 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z^2 + 128*t^7*z - 176*t^7 + 160*t^6*z^4 - 1024*t^6*z^3 + 3200*t^6*z^2 - 3776*t^6*z + 1552*t^6 - 256*t^5*z^6 + 2688*t^5*z^5 - 12528*t^5*z^4 + 29792*t^5*z^3 - 41328*t^5*z^2 + 30624*t^5*z - 8384*t^5 + 304*t^4*z^8 - 4736*t^4*z^7 + 33392*t^4*z^6 - 134336*t^4*z^5 + 332944*t^4*z^4 - 499312*t^4*z^3 + 434048*t^4*z^2 - 200320*t^4*z + 37072*t^4 - 256*t^3*z^10 + 5248*t^3*z^9 - 48560*t^3*z^8 + 262048*t^3*z^7 - 904848*t^3*z^6 + 2078080*t^3*z^5 - 3229872*t^3*z^4 + 3344944*t^3*z^3 - 2167744*t^3*z^2 + 773440*t^3*z - 113552*t^3 + 160*t^2*z^12 - 4224*t^2*z^11 + 51120*t^2*z^10 - 371392*t^2*z^9 + 1789872*t^2*z^8 - 5974608*t^2*z^7 + 14012864*t^2*z^6 - 22978896*t^2*z^5 + 25886976*t^2*z^4 - 19437968*t^2*z^3 + 9216720*t^2*z^2 - 2472288*t^2*z + 283120*t^2 - 64*t*z^14 + 2048*t*z^13 - 30080*t*z^12 + 266848*t*z^11 - 1588112*t*z^10 + 6675968*t*z^9 - 20378048*t*z^8 + 45821488*t*z^7 - 76243408*t*z^6 + 93245792*t*z^5 - 82043056*t*z^4 + 49895776*t*z^3 - 19628032*t*z^2 + 4437248*t*z - 433472*t + 16*z^16 - 640*z^15 + 11888*z^14 - 135360*z^13 + 1051520*z^12 - 5874416*z^11 + 24259024*z^10 - 75031776*z^9 + 174453088*z^8 - 303932064*z^7 + 393280768*z^6 - 372535696*z^5 + 252705056*z^4 - 118605120*z^3 + 36347120*z^2 - 6507488*z + 513760:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z + 64*t^6 + 256*t^5*z^3 - 1152*t^5*z^2 + 3312*t^5*z + 1216*t^5 - 304*t^4*z^5 + 2912*t^4*z^4 - 13184*t^4*z^3 + 28112*t^4*z^2 - 36880*t^4*z - 14528*t^4 + 256*t^3*z^7 - 3712*t^3*z^6 + 23984*t^3*z^5 - 83968*t^3*z^4 + 174048*t^3*z^3 - 206128*t^3*z^2 + 174768*t^3*z + 80960*t^3 - 160*t^2*z^9 + 3264*t^2*z^8 - 30096*t^2*z^7 + 160960*t^2*z^6 - 543456*t^2*z^5 + 1174944*t^2*z^4 - 1589216*t^2*z^3 + 1238736*t^2*z^2 - 626784*t^2*z - 239008*t^2 + 64*t*z^11 - 1664*t*z^10 + 19520*t*z^9 - 134560*t*z^8 + 600080*t*z^7 - 1805888*t*z^6 + 3738320*t*z^5 - 5338336*t*z^4 + 5150848*t*z^3 - 3080720*t*z^2 + 1186096*t*z + 399824*t - 16*z^13 + 544*z^12 - 8480*z^11 + 79536*z^10 - 496352*z^9 + 2155040*z^8 - 6623008*z^7 + 14409312*z^6 - 21925024*z^5 + 22829088*z^4 - 15753088*z^3 + 6780304*z^2 - 1758176*z - 225936)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_36 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 36) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_36 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2592*t*z^6 + 22032*t*z^5 - 67392*t*z^4 + 88128*t*z^3 - 45360*t*z^2 + 7776*t*z + 2592*z^8 - 27216*z^7 + 114048*z^6 - 244944*z^5 + 289008*z^4 - 186624*z^3 + 60912*z^2 - 7776*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2592*t*z^3 - 6480*t*z^2 + 5184*t*z + 9072*t - 2592*z^5 + 11664*z^4 - 20736*z^3 + 7776*z^2 - 20736*z - 69984)*hf
  · have hr : (-1296*t*z^12 + 34992*t*z^11 - 417312*t*z^10 + 2888784*t*z^9 - 12836880*t*z^8 + 38282544*t*z^7 - 77963472*t*z^6 + 108527040*t*z^5 - 102045744*t*z^4 + 63095760*t*z^3 - 24362208*t*z^2 + 5287680*t*z - 489888*t + 1296*z^16 - 46656*z^15 + 765936*z^14 - 7585488*z^13 + 50534928*z^12 - 239183280*z^11 + 828517248*z^10 - 2133851040*z^9 + 4114478592*z^8 - 5942311632*z^7 + 6395806656*z^6 - 5073824448*z^5 + 2910114864*z^4 - 1168251984*z^3 + 310176864*z^2 - 48771072*z + 3429216:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^9 - 27216*t*z^8 + 242352*t*z^7 - 1185840*t*z^6 + 3459024*t*z^5 - 6128784*t*z^4 + 6502032*t*z^3 - 3978720*t*z^2 + 1268784*t*z - 168480*t - 1296*z^13 + 38880*z^12 - 520992*z^11 + 4105728*z^10 - 21094992*z^9 + 74098800*z^8 - 181752336*z^7 + 313162848*z^6 - 377434080*z^5 + 313984512*z^4 - 175504320*z^3 + 62635680*z^2 - 12808368*z + 1167696)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_37 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 37) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_37 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 16*z^3 + 44*z^2 - 54*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_38 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 38) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_38 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 16*z^3 + 42*z^2 - 46*z + 14:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_39 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 39) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_39 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 12*t*z + 2*t + 2*z^4 - 18*z^3 + 52*z^2 - 48*z + 14:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(6 - 2*z)*hf
  · have hr : (16*t^8 - 192*t^7*z + 16*t^7 + 1104*t^6*z^2 - 624*t^6*z + 64*t^6 - 3888*t^5*z^3 + 4896*t^5*z^2 - 864*t^5*z - 32*t^5 + 9072*t^4*z^4 - 19152*t^4*z^3 + 8208*t^4*z^2 - 192*t^4*z - 320*t^4 - 14256*t^3*z^5 + 44064*t^3*z^4 - 34848*t^3*z^3 + 4560*t^3*z^2 + 960*t^3*z + 160*t^3 + 14688*t^2*z^6 - 61776*t^2*z^5 + 78192*t^2*z^4 - 29376*t^2*z^3 + 720*t^2*z^2 + 864*t^2*z + 16*t^2 - 9072*t*z^7 + 49680*t*z^6 - 91584*t*z^5 + 63936*t*z^4 - 12816*t*z^3 + 2592*t*z^2 - 2208*t*z + 304*t + 2592*z^8 - 18144*z^7 + 47088*z^6 - 55296*z^5 + 26352*z^4 + 1584*z^3 - 6528*z^2 + 2256*z - 224:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(3888*t^5 - 9072*t^4*z - 35280*t^4 + 14256*t^3*z^2 + 41472*t^3*z + 155376*t^3 - 14688*t^2*z^3 - 26352*t^2*z^2 - 104112*t^2*z - 402192*t^2 + 9072*t*z^4 + 4752*t*z^3 + 38448*t*z^2 + 151200*t*z + 588240*t - 2592*z^5 + 2592*z^4 - 8208*z^3 - 25056*z^2 - 95040*z - 370944)*hf
  · have hr : (16*t^8 + 192*t^7*z^2 - 960*t^7*z + 400*t^7 + 1056*t^6*z^4 - 10368*t^6*z^3 + 30048*t^6*z^2 - 21936*t^6*z + 4576*t^6 + 3456*t^5*z^6 - 50112*t^5*z^5 + 265392*t^5*z^4 - 609984*t^5*z^3 + 568080*t^5*z^2 - 224064*t^5*z + 31360*t^5 + 7344*t^4*z^8 - 139968*t^4*z^7 + 1067472*t^4*z^6 - 4122144*t^4*z^5 + 8429040*t^4*z^4 - 8909280*t^4*z^3 + 4897632*t^4*z^2 - 1330080*t^4*z + 140896*t^4 + 10368*t^3*z^10 - 243648*t^3*z^9 + 2410992*t^3*z^8 - 13004064*t^3*z^7 + 41405904*t^3*z^6 - 79215840*t^3*z^5 + 90276384*t^3*z^4 - 60998256*t^3*z^3 + 23837280*t^3*z^2 - 4962144*t^3*z + 425152*t^3 + 9504*t^2*z^12 - 264384*t^2*z^11 + 3199824*t^2*z^10 - 22044960*t^2*z^9 + 95044752*t^2*z^8 - 266076144*t^2*z^7 + 488199312*t^2*z^6 - 584956080*t^2*z^5 + 454734720*t^2*z^4 - 225661680*t^2*z^3 + 68652576*t^2*z^2 - 11633472*t^2*z + 839536*t^2 + 5184*t*z^14 - 165888*t*z^13 + 2363040*t*z^12 - 19719936*t*z^11 + 106805952*t*z^10 - 393343776*t*z^9 + 1005219504*t*z^8 - 1793033712*t*z^7 + 2227831776*t*z^6 - 1916571456*t*z^5 + 1127821248*t*z^4 - 442966176*t*z^3 + 110566704*t*z^2 - 15811584*t*z + 983632*t + 1296*z^16 - 46656*z^15 + 760752*z^14 - 7419600*z^13 + 48161088*z^12 - 219163968*z^11 + 718083792*z^10 - 1715329872*z^9 + 2998959120*z^8 - 3831775200*z^7 + 3559335264*z^6 - 2380381776*z^5 + 1126541280*z^4 - 366000480*z^3 + 77262144*z^2 - 9499152*z + 513760:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6*z + 4032*t^6 - 3456*t^5*z^3 + 29376*t^5*z^2 - 58032*t^5*z - 12960*t^5 - 7344*t^4*z^5 + 95904*t^4*z^4 - 425952*t^4*z^3 + 681264*t^4*z^2 - 220176*t^4*z + 178992*t^4 - 10368*t^3*z^7 + 181440*t^3*z^6 - 1229040*t^3*z^5 + 3965760*t^3*z^4 - 6005664*t^3*z^3 + 3802896*t^3*z^2 - 1510752*t^3*z - 309312*t^3 - 9504*t^2*z^9 + 207360*t^2*z^8 - 1870128*t^2*z^7 + 8929440*t^2*z^6 - 24014880*t^2*z^5 + 36011520*t^2*z^4 - 29207952*t^2*z^3 + 13560048*t^2*z^2 - 2468304*t^2*z + 1187568*t^2 - 5184*t*z^11 + 134784*t*z^10 - 1507680*t*z^9 + 9445248*t*z^8 - 36160992*t*z^7 + 86847552*t*z^6 - 130349520*t*z^5 + 120825648*t*z^4 - 69189552*t*z^3 + 22954752*t*z^2 - 4909824*t*z - 654192*t - 1296*z^13 + 38880*z^12 - 515808*z^11 + 3970944*z^10 - 19576512*z^9 + 64418976*z^8 - 143468496*z^7 + 216018576*z^6 - 218374272*z^5 + 146956896*z^4 - 64169712*z^3 + 17628624*z^2 - 2371440*z + 605088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_40 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 40) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_40 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_41 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 41) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_41 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 16*z^3 + 42*z^2 - 46*z + 14:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_42 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 42) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_42 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_43 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 43) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_43 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z^2 + 64*t^7*z - 112*t^7 + 160*t^6*z^4 - 704*t^6*z^3 + 2016*t^6*z^2 - 2096*t^6*z + 736*t^6 - 256*t^5*z^6 + 1920*t^5*z^5 - 7152*t^5*z^4 + 13456*t^5*z^3 - 15936*t^5*z^2 + 11424*t^5*z - 2848*t^5 + 304*t^4*z^8 - 3520*t^4*z^7 + 19792*t^4*z^6 - 66064*t^4*z^5 + 142432*t^4*z^4 - 190384*t^4*z^3 + 146032*t^4*z^2 - 58816*t^4*z + 9280*t^4 - 256*t^3*z^10 + 3968*t^3*z^9 - 28848*t^3*z^8 + 125232*t^3*z^7 - 355344*t^3*z^6 + 683184*t^3*z^5 - 913152*t^3*z^4 + 847872*t^3*z^3 - 506352*t^3*z^2 + 163328*t^3*z - 20704*t^3 + 160*t^2*z^12 - 3264*t^2*z^11 + 31440*t^2*z^10 - 186416*t^2*z^9 + 751392*t^2*z^8 - 2147040*t^2*z^7 + 4400016*t^2*z^6 - 6394752*t^2*z^5 + 6408576*t^2*z^4 - 4254560*t^2*z^3 + 1762320*t^2*z^2 - 405024*t^2*z + 38608*t^2 - 64*t*z^14 + 1600*t*z^13 - 18688*t*z^12 + 133808*t*z^11 - 651536*t*z^10 + 2270144*t*z^9 - 5819568*t*z^8 + 11149584*t*z^7 - 16084032*t*z^6 + 17407328*t*z^5 - 13804640*t*z^4 + 7612688*t*z^3 - 2677600*t*z^2 + 524320*t*z - 42448*t + 16*z^16 - 512*z^15 + 7728*z^14 - 72544*z^13 + 471152*z^12 - 2231040*z^11 + 7914928*z^10 - 21300752*z^9 + 43586208*z^8 - 67423088*z^7 + 77838256*z^6 - 65750016*z^5 + 39512192*z^4 - 16221328*z^3 + 4266672*z^2 - 638960*z + 40768:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z - 256*t^6 + 256*t^5*z^3 - 384*t^5*z^2 + 2544*t^5*z + 6032*t^5 - 304*t^4*z^5 + 1696*t^4*z^4 - 6880*t^4*z^3 + 8608*t^4*z^2 - 23776*t^4*z - 50384*t^4 + 256*t^3*z^7 - 2432*t^3*z^6 + 11952*t^3*z^5 - 30864*t^3*z^4 + 55296*t^3*z^3 - 37776*t^3*z^2 + 96240*t^3*z + 235440*t^3 - 160*t^2*z^9 + 2304*t^2*z^8 - 16176*t^2*z^7 + 68144*t^2*z^6 - 190032*t^2*z^5 + 345024*t^2*z^4 - 415152*t^2*z^3 + 228528*t^2*z^2 - 265968*t^2*z - 643456*t^2 + 64*t*z^11 - 1216*t*z^10 + 10816*t*z^9 - 57776*t*z^8 + 203888*t*z^7 - 494384*t*z^6 + 844944*t*z^5 - 1018800*t*z^4 + 883584*t*z^3 - 401792*t*z^2 + 385232*t*z + 965584*t - 16*z^13 + 416*z^12 - 5088*z^11 + 38224*z^10 - 194768*z^9 + 703152*z^8 - 1828432*z^7 + 3417488*z^6 - 4515936*z^5 + 4084784*z^4 - 2433664*z^3 + 837168*z^2 - 331856*z - 605312)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_44 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 44) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_44 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z^2 - 640*t^7*z + 208*t^7 + 448*t^6*z^4 - 4480*t^6*z^3 + 12944*t^6*z^2 - 8192*t^6*z + 1456*t^6 + 896*t^5*z^6 - 13440*t^5*z^5 + 73296*t^5*z^4 - 169792*t^5*z^3 + 148176*t^5*z^2 - 52896*t^5*z + 6592*t^5 + 1120*t^4*z^8 - 22400*t^4*z^7 + 179600*t^4*z^6 - 726080*t^4*z^5 + 1528912*t^4*z^4 - 1600144*t^4*z^3 + 843056*t^4*z^2 - 214912*t^4*z + 21040*t^4 + 896*t^3*z^10 - 22400*t^3*z^9 + 237040*t^3*z^8 - 1370240*t^3*z^7 + 4663008*t^3*z^6 - 9429056*t^3*z^5 + 11102400*t^3*z^4 - 7558352*t^3*z^3 + 2913248*t^3*z^2 - 588608*t^3*z + 48496*t^3 + 448*t^2*z^12 - 13440*t^2*z^11 + 176688*t^2*z^10 - 1329280*t^2*z^9 + 6275472*t^2*z^8 - 19215264*t^2*z^7 + 38300768*t^2*z^6 - 49174944*t^2*z^5 + 40241472*t^2*z^4 - 20649008*t^2*z^3 + 6399360*t^2*z^2 - 1092768*t^2*z + 78928*t^2 + 128*t*z^14 - 4480*t*z^13 + 70384*t*z^12 - 652352*t*z^11 + 3945424*t*z^10 - 16279456*t*z^9 + 46633600*t*z^8 - 92922320*t*z^7 + 127963904*t*z^6 - 120625120*t*z^5 + 76765424*t*z^4 - 32189024*t*z^3 + 8482976*t*z^2 - 1270528*t*z + 82432*t + 16*z^16 - 640*z^15 + 11696*z^14 - 128832*z^13 + 950768*z^12 - 4946000*z^11 + 18598768*z^10 - 51090816*z^9 + 102669424*z^8 - 150297648*z^7 + 159070336*z^6 - 120353728*z^5 + 63927728*z^4 - 23102112*z^3 + 5364032*z^2 - 713888*z + 40768:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6*z + 1792*t^6 - 896*t^5*z^3 + 8064*t^5*z^2 - 16848*t^5*z - 6560*t^5 - 1120*t^4*z^5 + 15680*t^4*z^4 - 75440*t^4*z^3 + 128960*t^4*z^2 - 29152*t^4*z + 38272*t^4 - 896*t^3*z^7 + 17024*t^3*z^6 - 126832*t^3*z^5 + 453344*t^3*z^4 - 750384*t^3*z^3 + 466160*t^3*z^2 - 191952*t^3*z - 39952*t^3 - 448*t^2*z^9 + 10752*t^2*z^8 - 108144*t^2*z^7 + 582304*t^2*z^6 - 1776096*t^2*z^5 + 2993520*t^2*z^4 - 2607872*t^2*z^3 + 1257744*t^2*z^2 - 243600*t^2*z + 44096*t^2 - 128*t*z^11 + 3712*t*z^10 - 46960*t*z^9 + 336800*t*z^8 - 1490848*t*z^7 + 4162288*t*z^6 - 7231840*t*z^5 + 7598144*t*z^4 - 4801616*t*z^3 + 1736608*t*z^2 - 336800*t*z + 133904*t - 16*z^13 + 544*z^12 - 8288*z^11 + 74160*z^10 - 429584*z^9 + 1676192*z^8 - 4452880*z^7 + 7999056*z^6 - 9570592*z^5 + 7523952*z^4 - 3794128*z^3 + 1161616*z^2 - 239024*z - 168960)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_45 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 45) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_45 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 12*t*z + 2*t + 2*z^4 - 18*z^3 + 52*z^2 - 48*z + 14:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(6 - 2*z)*hf
  · have hr : (16*t^8 + 192*t^7*z^2 - 960*t^7*z + 400*t^7 + 1056*t^6*z^4 - 10368*t^6*z^3 + 30048*t^6*z^2 - 21936*t^6*z + 4576*t^6 + 3456*t^5*z^6 - 50112*t^5*z^5 + 265392*t^5*z^4 - 609984*t^5*z^3 + 568080*t^5*z^2 - 224064*t^5*z + 31360*t^5 + 7344*t^4*z^8 - 139968*t^4*z^7 + 1067472*t^4*z^6 - 4122144*t^4*z^5 + 8429040*t^4*z^4 - 8909280*t^4*z^3 + 4897632*t^4*z^2 - 1330080*t^4*z + 140896*t^4 + 10368*t^3*z^10 - 243648*t^3*z^9 + 2410992*t^3*z^8 - 13004064*t^3*z^7 + 41405904*t^3*z^6 - 79215840*t^3*z^5 + 90276384*t^3*z^4 - 60998256*t^3*z^3 + 23837280*t^3*z^2 - 4962144*t^3*z + 425152*t^3 + 9504*t^2*z^12 - 264384*t^2*z^11 + 3199824*t^2*z^10 - 22044960*t^2*z^9 + 95044752*t^2*z^8 - 266076144*t^2*z^7 + 488199312*t^2*z^6 - 584956080*t^2*z^5 + 454734720*t^2*z^4 - 225661680*t^2*z^3 + 68652576*t^2*z^2 - 11633472*t^2*z + 839536*t^2 + 5184*t*z^14 - 165888*t*z^13 + 2363040*t*z^12 - 19719936*t*z^11 + 106805952*t*z^10 - 393343776*t*z^9 + 1005219504*t*z^8 - 1793033712*t*z^7 + 2227831776*t*z^6 - 1916571456*t*z^5 + 1127821248*t*z^4 - 442966176*t*z^3 + 110566704*t*z^2 - 15811584*t*z + 983632*t + 1296*z^16 - 46656*z^15 + 760752*z^14 - 7419600*z^13 + 48161088*z^12 - 219163968*z^11 + 718083792*z^10 - 1715329872*z^9 + 2998959120*z^8 - 3831775200*z^7 + 3559335264*z^6 - 2380381776*z^5 + 1126541280*z^4 - 366000480*z^3 + 77262144*z^2 - 9499152*z + 513760:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6*z + 4032*t^6 - 3456*t^5*z^3 + 29376*t^5*z^2 - 58032*t^5*z - 12960*t^5 - 7344*t^4*z^5 + 95904*t^4*z^4 - 425952*t^4*z^3 + 681264*t^4*z^2 - 220176*t^4*z + 178992*t^4 - 10368*t^3*z^7 + 181440*t^3*z^6 - 1229040*t^3*z^5 + 3965760*t^3*z^4 - 6005664*t^3*z^3 + 3802896*t^3*z^2 - 1510752*t^3*z - 309312*t^3 - 9504*t^2*z^9 + 207360*t^2*z^8 - 1870128*t^2*z^7 + 8929440*t^2*z^6 - 24014880*t^2*z^5 + 36011520*t^2*z^4 - 29207952*t^2*z^3 + 13560048*t^2*z^2 - 2468304*t^2*z + 1187568*t^2 - 5184*t*z^11 + 134784*t*z^10 - 1507680*t*z^9 + 9445248*t*z^8 - 36160992*t*z^7 + 86847552*t*z^6 - 130349520*t*z^5 + 120825648*t*z^4 - 69189552*t*z^3 + 22954752*t*z^2 - 4909824*t*z - 654192*t - 1296*z^13 + 38880*z^12 - 515808*z^11 + 3970944*z^10 - 19576512*z^9 + 64418976*z^8 - 143468496*z^7 + 216018576*z^6 - 218374272*z^5 + 146956896*z^4 - 64169712*z^3 + 17628624*z^2 - 2371440*z + 605088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_46 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 46) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_46 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z^2 - 704*t^7*z + 272*t^7 + 448*t^6*z^4 - 4928*t^6*z^3 + 15600*t^6*z^2 - 11120*t^6*z + 2176*t^6 + 896*t^5*z^6 - 14784*t^5*z^5 + 87888*t^5*z^4 - 220544*t^5*z^3 + 209136*t^5*z^2 - 80448*t^5*z + 10688*t^5 + 1120*t^4*z^8 - 24640*t^4*z^7 + 214960*t^4*z^6 - 935920*t^4*z^5 + 2103664*t^4*z^4 - 2336320*t^4*z^3 + 1297984*t^4*z^2 - 345760*t^4*z + 35104*t^4 + 896*t^3*z^10 - 24640*t^3*z^9 + 283440*t^3*z^8 - 1760640*t^3*z^7 + 6366816*t^3*z^6 - 13538496*t^3*z^5 + 16614864*t^3*z^4 - 11702544*t^3*z^3 + 4630368*t^3*z^2 - 952864*t^3*z + 79232*t^3 + 448*t^2*z^12 - 14784*t^2*z^11 + 211152*t^2*z^10 - 1705040*t^2*z^9 + 8537184*t^2*z^8 - 27402048*t^2*z^7 + 56616576*t^2*z^6 - 74587968*t^2*z^5 + 62082432*t^2*z^4 - 32129360*t^2*z^3 + 9954336*t^2*z^2 - 1684032*t^2*z + 119536*t^2 + 128*t*z^14 - 4928*t*z^13 + 84080*t*z^12 - 835840*t*z^11 + 5355952*t*z^10 - 23131648*t*z^9 + 68527056*t*z^8 - 139566864*t*z^7 + 194280240*t*z^6 - 183229984*t*z^5 + 115523440*t*z^4 - 47520640*t*z^3 + 12161648*t*z^2 - 1749056*t*z + 107408*t + 16*z^16 - 704*z^15 + 13968*z^14 - 164944*z^13 + 1288880*z^12 - 7012224*z^11 + 27238048*z^10 - 76335680*z^9 + 154567728*z^8 - 225192656*z^7 + 234290608*z^6 - 172066608*z^5 + 87543872*z^4 - 29881504*z^3 + 6459120*z^2 - 788816*z + 40768:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6*z + 2240*t^6 - 896*t^5*z^3 + 9408*t^5*z^2 - 23376*t^5*z - 7072*t^5 - 1120*t^4*z^5 + 17920*t^4*z^4 - 97360*t^4*z^3 + 187120*t^4*z^2 - 50944*t^4*z + 54496*t^4 - 896*t^3*z^7 + 19264*t^3*z^6 - 159792*t^3*z^5 + 625824*t^3*z^4 - 1115952*t^3*z^3 + 730992*t^3*z^2 - 307872*t^3*z - 71472*t^3 - 448*t^2*z^9 + 12096*t^2*z^8 - 134544*t^2*z^7 + 787568*t^2*z^6 - 2564592*t^2*z^5 + 4522752*t^2*z^4 - 4036032*t^2*z^3 + 1973232*t^2*z^2 - 350496*t^2*z + 159200*t^2 - 128*t*z^11 + 4160*t*z^10 - 57968*t*z^9 + 450208*t*z^8 - 2120512*t*z^7 + 6182800*t*z^6 - 10995024*t*z^5 + 11589984*t*z^4 - 7236720*t*z^3 + 2514736*t*z^2 - 534592*t*z - 29696*t - 16*z^13 + 608*z^12 - 10176*z^11 + 98368*z^10 - 605264*z^9 + 2464800*z^8 - 6706768*z^7 + 12096080*z^6 - 14235936*z^5 + 10792016*z^4 - 5126848*z^3 + 1469568*z^2 - 208784*z + 22144)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_47 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 47) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : (t - z^2 + 2*z - 1:ℝ)=0 := by
  apply cell_1_47 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z^2 - 512*t^7*z + 208*t^7 + 160*t^6*z^4 - 2176*t^6*z^3 + 8928*t^6*z^2 - 7072*t^6*z + 1456*t^6 + 256*t^5*z^6 - 4992*t^5*z^5 + 35376*t^5*z^4 - 107072*t^5*z^3 + 114288*t^5*z^2 - 47328*t^5*z + 6592*t^5 + 304*t^4*z^8 - 7424*t^4*z^7 + 73168*t^4*z^6 - 364064*t^4*z^5 + 939472*t^4*z^4 - 1165712*t^4*z^3 + 703744*t^4*z^2 - 198944*t^4*z + 21040*t^4 + 256*t^3*z^10 - 7552*t^3*z^9 + 93936*t^3*z^8 - 637632*t^3*z^7 + 2542992*t^3*z^6 - 5989056*t^3*z^5 + 8070288*t^3*z^4 - 6151248*t^3*z^3 + 2592192*t^3*z^2 - 560512*t^3*z + 48496*t^3 + 160*t^2*z^12 - 5376*t^2*z^11 + 79248*t^2*z^10 - 668512*t^2*z^9 + 3537072*t^2*z^8 - 12117744*t^2*z^7 + 26905632*t^2*z^6 - 38118384*t^2*z^5 + 33958368*t^2*z^4 - 18659440*t^2*z^3 + 6082032*t^2*z^2 - 1073280*t^2*z + 78928*t^2 + 64*t*z^14 - 2432*t*z^13 + 41248*t*z^12 - 411520*t*z^11 + 2675024*t*z^10 - 11851456*t*z^9 + 36403296*t*z^8 - 77562480*t*z^7 + 113585424*t*z^6 - 112875808*t*z^5 + 74852432*t*z^4 - 32266336*t*z^3 + 8621056*t*z^2 - 1290944*t*z + 82432*t + 16*z^16 - 640*z^15 + 11760*z^14 - 130880*z^13 + 980192*z^12 - 5194896*z^11 + 19967248*z^10 - 56194432*z^9 + 115782048*z^8 - 173502592*z^7 + 187071040*z^6 - 142970064*z^5 + 75783584*z^4 - 26920928*z^3 + 6041616*z^2 - 763840*z + 40768:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z + 1216*t^6 - 256*t^5*z^3 + 3456*t^5*z^2 - 12336*t^5*z + 1184*t^5 - 304*t^4*z^5 + 5600*t^4*z^4 - 36832*t^4*z^3 + 91760*t^4*z^2 - 40624*t^4*z - 14368*t^4 - 256*t^3*z^7 + 6016*t^3*z^6 - 55536*t^3*z^5 + 249504*t^3*z^4 - 528096*t^3*z^3 + 408336*t^3*z^2 - 118896*t^3*z + 178560*t^3 - 160*t^2*z^9 + 4416*t^2*z^8 - 51312*t^2*z^7 + 320416*t^2*z^6 - 1139520*t^2*z^5 + 2242944*t^2*z^4 - 2231040*t^2*z^3 + 1127088*t^2*z^2 - 387648*t^2*z - 503360*t^2 - 64*t*z^11 + 2048*t*z^10 - 28384*t*z^9 + 222592*t*z^8 - 1077872*t*z^7 + 3295744*t*z^6 - 6260208*t*z^5 + 7105920*t*z^4 - 4720800*t*z^3 + 1817104*t*z^2 - 144848*t*z + 880912*t - 16*z^13 + 544*z^12 - 8352*z^11 + 75824*z^10 - 448448*z^9 + 1796736*z^8 - 4923328*z^7 + 9138496*z^6 - 11250912*z^5 + 8980672*z^4 - 4513312*z^3 + 1311408*z^2 - 353312*z - 541552)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_48 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 48) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_48 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z^2 + 384*t^7*z - 432*t^7 + 160*t^6*z^4 - 1728*t^6*z^3 + 6528*t^6*z^2 - 9984*t^6*z + 5136*t^6 - 256*t^5*z^6 + 4032*t^5*z^5 - 25200*t^5*z^4 + 79632*t^5*z^3 - 133488*t^5*z^2 + 111456*t^5*z - 35568*t^5 + 304*t^4*z^8 - 6144*t^4*z^7 + 52560*t^4*z^6 - 247824*t^4*z^5 + 702000*t^4*z^4 - 1217952*t^4*z^3 + 1255824*t^4*z^2 - 696672*t^4*z + 156960*t^4 - 256*t^3*z^10 + 6336*t^3*z^9 - 68592*t^3*z^8 + 427152*t^3*z^7 - 1691808*t^3*z^6 + 4442976*t^3*z^5 - 7809120*t^3*z^4 + 9027216*t^3*z^3 - 6525216*t^3*z^2 + 2640384*t^3*z - 450144*t^3 + 160*t^2*z^12 - 4608*t^2*z^11 + 59472*t^2*z^10 - 454320*t^2*z^9 + 2284848*t^2*z^8 - 7955712*t^2*z^7 + 19620864*t^2*z^6 - 34429104*t^2*z^5 + 42491088*t^2*z^4 - 35792496*t^2*z^3 + 19416240*t^2*z^2 - 6048864*t^2*z + 813888*t^2 - 64*t*z^14 + 2112*t*z^13 - 31680*t*z^12 + 286128*t*z^11 - 1737072*t*z^10 + 7490736*t*z^9 - 23626080*t*z^8 + 55252512*t*z^7 - 96011856*t*z^6 + 122944608*t*z^5 - 113743008*t*z^4 + 73395504*t*z^3 - 31081968*t*z^2 + 7700832*t*z - 839808*t + 16*z^16 - 576*z^15 + 9552*z^14 - 96816*z^13 + 670848*z^12 - 3366288*z^11 + 12636576*z^10 - 36131472*z^9 + 79341696*z^8 - 133885008*z^7 + 172510992*z^6 - 167419008*z^5 + 119606544*z^4 - 60642432*z^3 + 20528640*z^2 - 4136832*z + 373248:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z + 768*t^6 + 256*t^5*z^3 - 2496*t^5*z^2 + 7920*t^5*z - 8880*t^5 - 304*t^4*z^5 + 4320*t^4*z^4 - 23904*t^4*z^3 + 64608*t^4*z^2 - 86256*t^4*z + 47232*t^4 + 256*t^3*z^7 - 4800*t^3*z^6 + 37488*t^3*z^5 - 158256*t^3*z^4 + 390480*t^3*z^3 - 563328*t^3*z^2 + 440064*t^3*z - 145440*t^3 - 160*t^2*z^9 + 3648*t^2*z^8 - 36144*t^2*z^7 + 204144*t^2*z^6 - 723744*t^2*z^5 + 1667520*t^2*z^4 - 2489616*t^2*z^3 + 2312496*t^2*z^2 - 1207008*t^2*z + 269136*t^2 + 64*t*z^11 - 1728*t*z^10 + 20736*t*z^9 - 145968*t*z^8 + 669456*t*z^7 - 2098080*t*z^6 + 4574592*t*z^5 - 6913872*t*z^4 + 7063056*t*z^3 - 4617648*t*z^2 + 1728000*t*z - 279504*t - 16*z^13 + 480*z^12 - 6528*z^11 + 53280*z^10 - 290976*z^9 + 1121328*z^8 - 3129984*z^7 + 6386688*z^6 - 9487728*z^5 + 10088496*z^4 - 7430400*z^3 + 3576960*z^2 - 1005696*z + 124416)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_49 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 49) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_49 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z + 2*z^4 - 20*z^3 + 62*z^2 - 60*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8 + 64*t^7*z - 240*t^7 + 192*t^6*z^4 - 1728*t^6*z^3 + 5008*t^6*z^2 - 5424*t^6*z + 2688*t^6 + 576*t^5*z^5 - 7344*t^5*z^4 + 34240*t^5*z^3 - 70128*t^5*z^2 + 59904*t^5*z - 18720*t^5 + 864*t^4*z^8 - 15552*t^4*z^7 + 114768*t^4*z^6 - 449712*t^4*z^5 + 1020400*t^4*z^4 - 1390272*t^4*z^3 + 1148544*t^4*z^2 - 531936*t^4*z + 104256*t^4 + 1728*t^3*z^9 - 37584*t^3*z^8 + 345216*t^3*z^7 - 1740960*t^3*z^6 + 5254912*t^3*z^5 - 9739536*t^3*z^4 + 11015664*t^3*z^3 - 7371360*t^3*z^2 + 2676960*t^3*z - 405216*t^3 + 1728*t^2*z^12 - 46656*t^2*z^11 + 553392*t^2*z^10 - 3795984*t^2*z^9 + 16701408*t^2*z^8 - 49500288*t^2*z^7 + 101262400*t^2*z^6 - 144468000*t^2*z^5 + 143527392*t^2*z^4 - 97425360*t^2*z^3 + 43015104*t^2*z^2 - 11081664*t^2*z + 1255824*t^2 + 1728*t*z^13 - 53136*t*z^12 + 727488*t*z^11 - 5846256*t*z^10 + 30619008*t*z^9 - 109792368*t*z^8 + 275856976*t*z^7 - 489445296*t*z^6 + 611297856*t*z^5 - 530315280*t*z^4 + 311004000*t*z^3 - 117085392*t*z^2 + 25453440*t*z - 2422224*t + 1296*z^16 - 46656*z^15 + 762480*z^14 - 7486992*z^13 + 49286448*z^12 - 229905216*z^11 + 783624864*z^10 - 1985195520*z^9 + 3769327120*z^8 - 5375156208*z^7 + 5737281648*z^6 - 4540207536*z^5 + 2616410304*z^4 - 1064041920*z^3 + 288755280*z^2 - 46838736*z + 3429216:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6*z + 576*t^6 - 576*t^5*z^2 + 3888*t^5*z - 5728*t^5 - 864*t^4*z^5 + 10368*t^4*z^4 - 44784*t^4*z^3 + 85104*t^4*z^2 - 75616*t^4*z + 36288*t^4 - 1728*t^3*z^6 + 27216*t^3*z^5 - 166368*t^3*z^4 + 492624*t^3*z^3 - 720208*t^3*z^2 + 485568*t^3*z - 142512*t^3 - 1728*t^2*z^9 + 36288*t^2*z^8 - 320112*t^2*z^7 + 1543536*t^2*z^6 - 4450320*t^2*z^5 + 7946208*t^2*z^4 - 8901664*t^2*z^3 + 6191184*t^2*z^2 - 2426688*t^2*z + 439584*t^2 - 1728*t*z^10 + 42768*t*z^9 - 455328*t*z^8 + 2724192*t*z^7 - 10047600*t*z^6 + 23623056*t*z^5 - 35517664*t*z^4 + 33589008*t*z^3 - 19235664*t*z^2 + 6047232*t*z - 832608*t - 1296*z^13 + 38880*z^12 - 517536*z^11 + 4027968*z^10 - 20344176*z^9 + 70035840*z^8 - 168228336*z^7 + 284470416*z^6 - 338342080*z^5 + 280184976*z^4 - 157681824*z^3 + 57425568*z^2 - 12165552*z + 1173024)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_50 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 50) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_50 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z^2 + 320*t^7*z - 368*t^7 + 160*t^6*z^4 - 1600*t^6*z^3 + 5600*t^6*z^2 - 8048*t^6*z + 4000*t^6 - 256*t^5*z^6 + 3840*t^5*z^5 - 22896*t^5*z^4 + 69104*t^5*z^3 - 110592*t^5*z^2 + 88224*t^5*z - 26816*t^5 + 304*t^4*z^8 - 6080*t^4*z^7 + 51152*t^4*z^6 - 235568*t^4*z^5 + 646816*t^4*z^4 - 1079440*t^4*z^3 + 1063760*t^4*z^2 - 561856*t^4*z + 119968*t^4 - 256*t^3*z^10 + 6400*t^3*z^9 - 69680*t^3*z^8 + 433936*t^3*z^7 - 1706640*t^3*z^6 + 4414096*t^3*z^5 - 7573536*t^3*z^4 + 8471200*t^3*z^3 - 5875792*t^3*z^2 + 2264896*t^3*z - 365696*t^3 + 160*t^2*z^12 - 4800*t^2*z^11 + 64080*t^2*z^10 - 502288*t^2*z^9 + 2568480*t^2*z^8 - 9002784*t^2*z^7 + 22114736*t^2*z^6 - 38237568*t^2*z^5 + 46027392*t^2*z^4 - 37471232*t^2*z^3 + 19495440*t^2*z^2 - 5788896*t^2*z + 738736*t^2 - 64*t*z^14 + 2240*t*z^13 - 35456*t*z^12 + 335824*t*z^11 - 2122256*t*z^10 + 9445568*t*z^9 - 30458192*t*z^8 + 72088912*t*z^7 - 125456224*t*z^6 + 159207872*t*z^5 - 144482848*t*z^4 + 90568528*t*z^3 - 36931648*t*z^2 + 8744480*t*z - 905840*t + 16*z^16 - 640*z^15 + 11696*z^14 - 129408*z^13 + 968432*z^12 - 5186912*z^11 + 20520016*z^10 - 61009488*z^9 + 137392000*z^8 - 234463056*z^7 + 301362256*z^6 - 287974624*z^5 + 200179232*z^4 - 97732752*z^3 + 31584272*z^2 - 6035120*z + 513760:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z + 640*t^6 + 256*t^5*z^3 - 2304*t^5*z^2 + 6768*t^5*z - 6992*t^5 - 304*t^4*z^5 + 4256*t^4*z^4 - 22880*t^4*z^3 + 59072*t^4*z^2 - 73696*t^4*z + 36976*t^4 + 256*t^3*z^7 - 4864*t^3*z^6 + 38192*t^3*z^5 - 160240*t^3*z^4 + 386880*t^3*z^3 - 536080*t^3*z^2 + 394416*t^3*z - 119344*t^3 - 160*t^2*z^9 + 3840*t^2*z^8 - 39600*t^2*z^7 + 229648*t^2*z^6 - 822672*t^2*z^5 + 1881120*t^2*z^4 - 2735024*t^2*z^3 + 2429328*t^2*z^2 - 1192848*t^2*z + 245120*t^2 + 64*t*z^11 - 1856*t*z^10 + 23744*t*z^9 - 176464*t*z^8 + 844208*t*z^7 - 2720912*t*z^6 + 6005456*t*z^5 - 9035344*t*z^4 + 9032320*t*z^3 - 5679488*t*z^2 + 2009008*t*z - 302128*t - 16*z^13 + 544*z^12 - 8288*z^11 + 74736*z^10 - 443792*z^9 + 1826672*z^8 - 5341648*z^7 + 11188176*z^6 - 16708096*z^5 + 17495952*z^4 - 12449152*z^3 + 5691856*z^2 - 1497872*z + 171360)*hf
  · have hr : (16*t^8 - 64*t^7*z^2 + 320*t^7*z - 368*t^7 + 160*t^6*z^4 - 1408*t^6*z^3 + 4640*t^6*z^2 - 6896*t^6*z + 3616*t^6 - 256*t^5*z^6 + 3264*t^5*z^5 - 17136*t^5*z^4 + 47936*t^5*z^3 - 75600*t^5*z^2 + 62592*t^5*z - 20192*t^5 + 304*t^4*z^8 - 4928*t^4*z^7 + 34736*t^4*z^6 - 139808*t^4*z^5 + 352048*t^4*z^4 - 566368*t^4*z^3 + 563936*t^4*z^2 - 311008*t^4*z + 70144*t^4 - 256*t^3*z^10 + 5056*t^3*z^9 - 44528*t^3*z^8 + 231328*t^3*z^7 - 787440*t^3*z^6 + 1835872*t^3*z^5 - 2960640*t^3*z^4 + 3240400*t^3*z^3 - 2277472*t^3*z^2 + 909856*t^3*z - 153248*t^3 + 160*t^2*z^12 - 3648*t^2*z^11 + 37872*t^2*z^10 - 237472*t^2*z^9 + 1003632*t^2*z^8 - 3013104*t^2*z^7 + 6580592*t^2*z^6 - 10501296*t^2*z^5 + 12087456*t^2*z^4 - 9707312*t^2*z^3 + 5099904*t^2*z^2 - 1546944*t^2*z + 201616*t^2 - 64*t*z^14 + 1664*t*z^13 - 19904*t*z^12 + 145600*t*z^11 - 729344*t*z^10 + 2649632*t*z^9 - 7197296*t*z^8 + 14823280*t*z^7 - 23184832*t*z^6 + 27274784*t*z^5 - 23602336*t*z^4 + 14443648*t*z^3 - 5842768*t*z^2 + 1381184*t*z - 142352*t + 16*z^16 - 448*z^15 + 5840*z^14 - 47184*z^13 + 264992*z^12 - 1097792*z^11 + 3468400*z^10 - 8510352*z^9 + 16345552*z^8 - 24570240*z^7 + 28687168*z^6 - 25614064*z^5 + 17046944*z^4 - 8120448*z^3 + 2589632*z^2 - 489104*z + 40768:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z + 448*t^6 + 256*t^5*z^3 - 1728*t^5*z^2 + 4464*t^5*z - 4832*t^5 - 304*t^4*z^5 + 3104*t^4*z^4 - 13376*t^4*z^3 + 30704*t^4*z^2 - 38128*t^4*z + 21136*t^4 + 256*t^3*z^7 - 3520*t^3*z^6 + 21104*t^3*z^5 - 72256*t^3*z^4 + 153408*t^3*z^3 - 201808*t^3*z^2 + 152352*t^3*z - 49792*t^3 - 160*t^2*z^9 + 2688*t^2*z^8 - 20304*t^2*z^7 + 90976*t^2*z^6 - 266976*t^2*z^5 + 531552*t^2*z^4 - 715568*t^2*z^3 + 622992*t^2*z^2 - 314736*t^2*z + 65264*t^2 + 64*t*z^11 - 1280*t*z^10 + 11648*t*z^9 - 64000*t*z^8 + 236672*t*z^7 - 618656*t*z^6 + 1163312*t*z^5 - 1565488*t*z^4 + 1466128*t*z^3 - 898688*t*z^2 + 318592*t*z - 45520*t - 16*z^13 + 352*z^12 - 3584*z^11 + 22464*z^10 - 96896*z^9 + 303488*z^8 - 708016*z^7 + 1240176*z^6 - 1621888*z^5 + 1553280*z^4 - 1049968*z^3 + 469072*z^2 - 122960*z + 11136)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_51 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 51) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_51 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z^2 + 576*t^7*z - 496*t^7 + 448*t^6*z^4 - 4032*t^6*z^3 + 12592*t^6*z^2 - 15792*t^6*z + 6592*t^6 - 896*t^5*z^6 + 12096*t^5*z^5 - 65136*t^5*z^4 + 177696*t^5*z^3 - 256272*t^5*z^2 + 182592*t^5*z - 49504*t^5 + 1120*t^4*z^8 - 20160*t^4*z^7 + 154160*t^4*z^6 - 651600*t^4*z^5 + 1656240*t^4*z^4 - 2573280*t^4*z^3 + 2363168*t^4*z^2 - 1159200*t^4*z + 230272*t^4 - 896*t^3*z^10 + 20160*t^3*z^9 - 199760*t^3*z^8 + 1145280*t^3*z^7 - 4194080*t^3*z^6 + 10206432*t^3*z^5 - 16618864*t^3*z^4 + 17746128*t^3*z^3 - 11789248*t^3*z^2 + 4359840*t^3*z - 677152*t^3 + 448*t^2*z^12 - 12096*t^2*z^11 + 147216*t^2*z^10 - 1066320*t^2*z^9 + 5108640*t^2*z^8 - 17005536*t^2*z^7 + 40176832*t^2*z^6 - 67549248*t^2*z^5 + 79734048*t^2*z^4 - 63992880*t^2*z^3 + 32899296*t^2*z^2 - 9661824*t^2*z + 1220560*t^2 - 128*t*z^14 + 4032*t*z^13 - 58192*t*z^12 + 509472*t*z^11 - 3018192*t*z^10 + 12771936*t*z^9 - 39702224*t*z^8 + 91776816*t*z^7 - 157851280*t*z^6 + 199996416*t*z^5 - 182683920*t*z^4 + 115939008*t*z^3 - 48035120*t*z^2 + 11574720*t*z - 1220752*t + 16*z^16 - 576*z^15 + 9616*z^14 - 98736*z^13 + 697072*z^12 - 3582144*z^11 + 13830592*z^10 - 40814496*z^9 + 92724400*z^8 - 162063600*z^7 + 216195760*z^6 - 216718416*z^5 + 159199648*z^4 - 82444896*z^3 + 28272208*z^2 - 5720208*z + 513760:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6*z + 1344*t^6 + 896*t^5*z^3 - 6720*t^5*z^2 + 16752*t^5*z - 14016*t^5 - 1120*t^4*z^5 + 13440*t^4*z^4 - 63440*t^4*z^3 + 146640*t^4*z^2 - 165120*t^4*z + 72480*t^4 + 896*t^3*z^7 - 14784*t^3*z^6 + 102992*t^3*z^5 - 391584*t^3*z^4 + 873296*t^3*z^3 - 1133424*t^3*z^2 + 783904*t^3*z - 222000*t^3 - 448*t^2*z^9 + 9408*t^2*z^8 - 86736*t^2*z^7 + 459888*t^2*z^6 - 1540464*t^2*z^5 + 3363552*t^2*z^4 - 4751680*t^2*z^3 + 4145808*t^2*z^2 - 2003424*t^2*z + 405024*t^2 + 128*t*z^11 - 3264*t*z^10 + 37456*t*z^9 - 254976*t*z^8 + 1141440*t*z^7 - 3516144*t*z^6 + 7567472*t*z^5 - 11302368*t*z^4 + 11381392*t*z^3 - 7284336*t*z^2 + 2638272*t*z - 406176*t - 16*z^13 + 480*z^12 - 6592*z^11 + 54816*z^10 - 307408*z^9 + 1224576*z^8 - 3552016*z^7 + 7558992*z^6 - 11728576*z^5 + 13005168*z^4 - 9930592*z^3 + 4902624*z^2 - 1393072*z + 171072)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_52 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 52) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_52 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z + 2*z^4 - 20*z^3 + 62*z^2 - 60*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8 + 64*t^7*z - 240*t^7 + 208*t^6*z^2 - 1200*t^6*z + 1536*t^6 + 400*t^5*z^3 - 3456*t^5*z^2 + 8928*t^5*z - 5760*t^5 + 592*t^4*z^4 - 6288*t^4*z^3 + 23184*t^4*z^2 - 33408*t^4*z + 13536*t^4 + 592*t^3*z^5 - 7680*t^3*z^4 + 36960*t^3*z^3 - 78768*t^3*z^2 + 68544*t^3*z - 19008*t^3 + 448*t^2*z^6 - 6480*t^2*z^5 + 36432*t^2*z^4 - 99648*t^2*z^3 + 133488*t^2*z^2 - 75168*t^2*z + 14256*t^2 + 208*t*z^7 - 3408*t*z^6 + 22176*t*z^5 - 72000*t*z^4 + 119952*t*z^3 - 95904*t*z^2 + 33696*t*z - 3888*t + 64*z^8 - 1056*z^7 + 6864*z^6 - 22752*z^5 + 41616*z^4 - 41904*z^3 + 20736*z^2 - 3888*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-400*t^5 - 592*t^4*z + 2736*t^4 - 592*t^3*z^2 + 4128*t^3*z - 6864*t^3 - 448*t^2*z^3 + 3792*t^2*z^2 - 9648*t^2*z + 6288*t^2 - 208*t*z^4 + 2160*t*z^3 - 7344*t*z^2 + 7872*t*z - 144*t - 64*z^5 + 672*z^4 - 2256*z^3 + 2976*z^2 - 1440*z - 288)*hf
  · have hr : (16*t^8 + 64*t^7*z - 240*t^7 + 192*t^6*z^4 - 1728*t^6*z^3 + 5008*t^6*z^2 - 5424*t^6*z + 2688*t^6 + 576*t^5*z^5 - 7344*t^5*z^4 + 34240*t^5*z^3 - 70128*t^5*z^2 + 59904*t^5*z - 18720*t^5 + 864*t^4*z^8 - 15552*t^4*z^7 + 114768*t^4*z^6 - 449712*t^4*z^5 + 1020400*t^4*z^4 - 1390272*t^4*z^3 + 1148544*t^4*z^2 - 531936*t^4*z + 104256*t^4 + 1728*t^3*z^9 - 37584*t^3*z^8 + 345216*t^3*z^7 - 1740960*t^3*z^6 + 5254912*t^3*z^5 - 9739536*t^3*z^4 + 11015664*t^3*z^3 - 7371360*t^3*z^2 + 2676960*t^3*z - 405216*t^3 + 1728*t^2*z^12 - 46656*t^2*z^11 + 553392*t^2*z^10 - 3795984*t^2*z^9 + 16701408*t^2*z^8 - 49500288*t^2*z^7 + 101262400*t^2*z^6 - 144468000*t^2*z^5 + 143527392*t^2*z^4 - 97425360*t^2*z^3 + 43015104*t^2*z^2 - 11081664*t^2*z + 1255824*t^2 + 1728*t*z^13 - 53136*t*z^12 + 727488*t*z^11 - 5846256*t*z^10 + 30619008*t*z^9 - 109792368*t*z^8 + 275856976*t*z^7 - 489445296*t*z^6 + 611297856*t*z^5 - 530315280*t*z^4 + 311004000*t*z^3 - 117085392*t*z^2 + 25453440*t*z - 2422224*t + 1296*z^16 - 46656*z^15 + 762480*z^14 - 7486992*z^13 + 49286448*z^12 - 229905216*z^11 + 783624864*z^10 - 1985195520*z^9 + 3769327120*z^8 - 5375156208*z^7 + 5737281648*z^6 - 4540207536*z^5 + 2616410304*z^4 - 1064041920*z^3 + 288755280*z^2 - 46838736*z + 3429216:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6*z + 576*t^6 - 576*t^5*z^2 + 3888*t^5*z - 5728*t^5 - 864*t^4*z^5 + 10368*t^4*z^4 - 44784*t^4*z^3 + 85104*t^4*z^2 - 75616*t^4*z + 36288*t^4 - 1728*t^3*z^6 + 27216*t^3*z^5 - 166368*t^3*z^4 + 492624*t^3*z^3 - 720208*t^3*z^2 + 485568*t^3*z - 142512*t^3 - 1728*t^2*z^9 + 36288*t^2*z^8 - 320112*t^2*z^7 + 1543536*t^2*z^6 - 4450320*t^2*z^5 + 7946208*t^2*z^4 - 8901664*t^2*z^3 + 6191184*t^2*z^2 - 2426688*t^2*z + 439584*t^2 - 1728*t*z^10 + 42768*t*z^9 - 455328*t*z^8 + 2724192*t*z^7 - 10047600*t*z^6 + 23623056*t*z^5 - 35517664*t*z^4 + 33589008*t*z^3 - 19235664*t*z^2 + 6047232*t*z - 832608*t - 1296*z^13 + 38880*z^12 - 517536*z^11 + 4027968*z^10 - 20344176*z^9 + 70035840*z^8 - 168228336*z^7 + 284470416*z^6 - 338342080*z^5 + 280184976*z^4 - 157681824*z^3 + 57425568*z^2 - 12165552*z + 1173024)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_53 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 53) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_53 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 4*t*z^2 - 20*t*z + 6*t + 2*z^4 - 20*z^3 + 62*z^2 - 60*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8 + 64*t^7*z^2 - 256*t^7*z - 48*t^7 + 160*t^6*z^4 - 1280*t^6*z^3 + 2656*t^6*z^2 - 480*t^6*z + 240*t^6 + 256*t^5*z^6 - 3072*t^5*z^5 + 12720*t^5*z^4 - 20128*t^5*z^3 + 8208*t^5*z^2 - 288*t^5*z - 576*t^5 + 304*t^4*z^8 - 4864*t^4*z^7 + 30288*t^4*z^6 - 91648*t^4*z^5 + 137008*t^4*z^4 - 92976*t^4*z^3 + 28512*t^4*z^2 - 6048*t^4*z + 1008*t^4 + 256*t^3*z^10 - 5120*t^3*z^9 + 42352*t^3*z^8 - 186784*t^3*z^7 + 471920*t^3*z^6 - 682432*t^3*z^5 + 531984*t^3*z^4 - 190032*t^3*z^3 + 12096*t^3*z^2 + 9216*t^3*z - 1296*t^3 + 160*t^2*z^12 - 3840*t^2*z^11 + 39696*t^2*z^10 - 231296*t^2*z^9 + 835152*t^2*z^8 - 1937040*t^2*z^7 + 2899456*t^2*z^6 - 2753136*t^2*z^5 + 1610208*t^2*z^4 - 578160*t^2*z^3 + 138672*t^2*z^2 - 22464*t^2*z + 1296*t^2 + 64*t*z^14 - 1792*t*z^13 + 22176*t*z^12 - 159776*t*z^11 + 743216*t*z^10 - 2338944*t*z^9 + 5070688*t*z^8 - 7552336*t*z^7 + 7543824*t*z^6 - 4783104*t*z^5 + 1705104*t*z^4 - 222336*t*z^3 - 37152*t*z^2 + 10368*t*z + 16*z^16 - 512*z^15 + 7408*z^14 - 64160*z^13 + 371200*z^12 - 1516016*z^11 + 4502704*z^10 - 9870176*z^9 + 16034176*z^8 - 19215264*z^7 + 16776960*z^6 - 10454832*z^5 + 4504608*z^4 - 1271808*z^3 + 211248*z^2 - 15552*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z + 320*t^6 - 256*t^5*z^3 + 1536*t^5*z^2 - 1200*t^5*z - 1664*t^5 - 304*t^4*z^5 + 3040*t^4*z^4 - 9312*t^4*z^3 + 7504*t^4*z^2 + 944*t^4*z + 3168*t^4 - 256*t^3*z^7 + 3584*t^3*z^6 - 18544*t^3*z^5 + 42496*t^3*z^4 - 39296*t^3*z^3 + 8560*t^3*z^2 + 528*t^3*z - 1728*t^3 - 160*t^2*z^9 + 2880*t^2*z^8 - 20976*t^2*z^7 + 79040*t^2*z^6 - 163488*t^2*z^5 + 181824*t^2*z^4 - 100000*t^2*z^3 + 26256*t^2*z^2 - 7200*t^2*z - 1344*t^2 - 64*t*z^11 + 1408*t*z^10 - 13152*t*z^9 + 68000*t*z^8 - 212624*t*z^7 + 411744*t*z^6 - 482608*t*z^5 + 313120*t*z^4 - 86400*t*z^3 - 1200*t*z^2 + 4656*t*z + 1872*t - 16*z^13 + 416*z^12 - 4768*z^11 + 31760*z^10 - 136480*z^9 + 396992*z^8 - 797152*z^7 + 1104896*z^6 - 1039456*z^5 + 643008*z^4 - 249120*z^3 + 54672*z^2 - 5472*z - 432)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_54 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 54) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_54 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 12*t*z + 2*t + 2*z^4 - 18*z^3 + 52*z^2 - 48*z + 14:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(6 - 2*z)*hf
  · have hr : (16*t^8 - 176*t^7 + 48*t^6*z^2 - 288*t^6*z + 784*t^6 - 432*t^5*z^2 + 2592*t^5*z - 2048*t^5 - 144*t^4*z^3 + 1872*t^4*z^2 - 7200*t^4*z + 3088*t^4 + 1008*t^3*z^3 - 5856*t^3*z^2 + 6912*t^3*z - 1424*t^3 - 1296*t^2*z^3 + 6048*t^2*z^2 - 1424*t^2 - 1152*t*z^3 + 6336*t*z^2 - 5760*t*z + 1408*t + 288*z^3 - 1536*z^2 + 1152*z - 224:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(144*t^4 - 1008*t^3 + 1296*t^2 + 1152*t - 288)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_55 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 55) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_55 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 4*t*z^2 - 20*t*z + 4*t + 2*z^4 - 20*z^3 + 60*z^2 - 50*z + 14:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8 - 64*t^7*z - 112*t^7 + 208*t^6*z^2 - 16*t^6*z + 352*t^6 - 400*t^5*z^3 + 96*t^5*z^2 + 1248*t^5*z - 832*t^5 + 592*t^4*z^4 - 1040*t^4*z^3 - 624*t^4*z^2 - 2240*t^4*z + 928*t^4 - 592*t^3*z^5 + 1504*t^3*z^4 + 2432*t^3*z^3 - 5200*t^3*z^2 + 2368*t^3*z + 128*t^3 + 448*t^2*z^6 - 2064*t^2*z^5 + 1392*t^2*z^4 + 320*t^2*z^3 + 4560*t^2*z^2 - 480*t^2*z - 848*t^2 - 208*t*z^7 + 1232*t*z^6 - 768*t*z^5 - 5408*t*z^4 + 6160*t*z^3 + 3552*t*z^2 - 4768*t*z + 1040*t + 64*z^8 - 640*z^7 + 2224*z^6 - 3040*z^5 + 880*z^4 + 2000*z^3 - 3104*z^2 + 1520*z - 224:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(400*t^5 - 592*t^4*z - 2512*t^4 + 592*t^3*z^2 + 2048*t^3*z + 4528*t^3 - 448*t^2*z^3 - 624*t^2*z^2 - 1104*t^2*z - 2672*t^2 + 208*t*z^4 + 16*t*z^3 - 1008*t*z^2 - 160*t*z + 2000*t - 64*z^5 + 256*z^4 - 112*z^3 - 128*z^2 + 128*z - 416)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_56 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 56) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_56 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z^2 + 320*t^7*z - 368*t^7 + 160*t^6*z^4 - 1408*t^6*z^3 + 4640*t^6*z^2 - 6896*t^6*z + 3616*t^6 - 256*t^5*z^6 + 3264*t^5*z^5 - 17136*t^5*z^4 + 47936*t^5*z^3 - 75600*t^5*z^2 + 62592*t^5*z - 20192*t^5 + 304*t^4*z^8 - 4928*t^4*z^7 + 34736*t^4*z^6 - 139808*t^4*z^5 + 352048*t^4*z^4 - 566368*t^4*z^3 + 563936*t^4*z^2 - 311008*t^4*z + 70144*t^4 - 256*t^3*z^10 + 5056*t^3*z^9 - 44528*t^3*z^8 + 231328*t^3*z^7 - 787440*t^3*z^6 + 1835872*t^3*z^5 - 2960640*t^3*z^4 + 3240400*t^3*z^3 - 2277472*t^3*z^2 + 909856*t^3*z - 153248*t^3 + 160*t^2*z^12 - 3648*t^2*z^11 + 37872*t^2*z^10 - 237472*t^2*z^9 + 1003632*t^2*z^8 - 3013104*t^2*z^7 + 6580592*t^2*z^6 - 10501296*t^2*z^5 + 12087456*t^2*z^4 - 9707312*t^2*z^3 + 5099904*t^2*z^2 - 1546944*t^2*z + 201616*t^2 - 64*t*z^14 + 1664*t*z^13 - 19904*t*z^12 + 145600*t*z^11 - 729344*t*z^10 + 2649632*t*z^9 - 7197296*t*z^8 + 14823280*t*z^7 - 23184832*t*z^6 + 27274784*t*z^5 - 23602336*t*z^4 + 14443648*t*z^3 - 5842768*t*z^2 + 1381184*t*z - 142352*t + 16*z^16 - 448*z^15 + 5840*z^14 - 47184*z^13 + 264992*z^12 - 1097792*z^11 + 3468400*z^10 - 8510352*z^9 + 16345552*z^8 - 24570240*z^7 + 28687168*z^6 - 25614064*z^5 + 17046944*z^4 - 8120448*z^3 + 2589632*z^2 - 489104*z + 40768:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z + 448*t^6 + 256*t^5*z^3 - 1728*t^5*z^2 + 4464*t^5*z - 4832*t^5 - 304*t^4*z^5 + 3104*t^4*z^4 - 13376*t^4*z^3 + 30704*t^4*z^2 - 38128*t^4*z + 21136*t^4 + 256*t^3*z^7 - 3520*t^3*z^6 + 21104*t^3*z^5 - 72256*t^3*z^4 + 153408*t^3*z^3 - 201808*t^3*z^2 + 152352*t^3*z - 49792*t^3 - 160*t^2*z^9 + 2688*t^2*z^8 - 20304*t^2*z^7 + 90976*t^2*z^6 - 266976*t^2*z^5 + 531552*t^2*z^4 - 715568*t^2*z^3 + 622992*t^2*z^2 - 314736*t^2*z + 65264*t^2 + 64*t*z^11 - 1280*t*z^10 + 11648*t*z^9 - 64000*t*z^8 + 236672*t*z^7 - 618656*t*z^6 + 1163312*t*z^5 - 1565488*t*z^4 + 1466128*t*z^3 - 898688*t*z^2 + 318592*t*z - 45520*t - 16*z^13 + 352*z^12 - 3584*z^11 + 22464*z^10 - 96896*z^9 + 303488*z^8 - 708016*z^7 + 1240176*z^6 - 1621888*z^5 + 1553280*z^4 - 1049968*z^3 + 469072*z^2 - 122960*z + 11136)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_57 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 57) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_57 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 12*t*z + 2*t + 2*z^4 - 18*z^3 + 52*z^2 - 48*z + 14:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(6 - 2*z)*hf
  · have hr : (16*t^8 - 176*t^7 + 192*t^6*z^4 - 1536*t^6*z^3 + 3888*t^6*z^2 - 3360*t^6*z + 1552*t^6 - 1584*t^5*z^4 + 12672*t^5*z^3 - 32112*t^5*z^2 + 27936*t^5*z - 8384*t^5 + 864*t^4*z^8 - 13824*t^4*z^7 + 90288*t^4*z^6 - 310176*t^4*z^5 + 608112*t^4*z^4 - 707472*t^4*z^3 + 505296*t^4*z^2 - 208800*t^4*z + 37072*t^4 - 4752*t^3*z^8 + 76032*t^3*z^7 - 496800*t^3*z^6 + 1708992*t^3*z^5 - 3340608*t^3*z^4 + 3771120*t^3*z^3 - 2422368*t^3*z^2 + 821760*t^3*z - 113552*t^3 + 1728*t^2*z^12 - 41472*t^2*z^11 + 436752*t^2*z^10 - 2655072*t^2*z^9 + 10325232*t^2*z^8 - 26957664*t^2*z^7 + 48405600*t^2*z^6 - 60464448*t^2*z^5 + 52621344*t^2*z^4 - 31435920*t^2*z^3 + 12297888*t^2*z^2 - 2817792*t^2*z + 283120*t^2 - 4752*t*z^12 + 114048*t*z^11 - 1201392*t*z^10 + 7308576*t*z^9 - 28442880*t*z^8 + 74189520*t*z^7 - 132317280*t*z^6 + 161956800*t*z^5 - 134771760*t*z^4 + 74369088*t*z^3 - 25872768*t*z^2 + 5106816*t*z - 433472*t + 1296*z^16 - 41472*z^15 + 602640*z^14 - 5264352*z^13 + 30853008*z^12 - 128253456*z^11 + 389998800*z^10 - 882436896*z^9 + 1497828240*z^8 - 1910120400*z^7 + 1822294368*z^6 - 1286836416*z^5 + 659880624*z^4 - 237837984*z^3 + 56900160*z^2 - 8082048*z + 513760:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6*z + 384*t^6 + 1584*t^5*z - 3168*t^5 - 864*t^4*z^5 + 8640*t^4*z^4 - 30672*t^4*z^3 + 45792*t^4*z^2 - 31392*t^4*z + 14976*t^4 + 4752*t^3*z^5 - 47520*t^3*z^4 + 168912*t^3*z^3 - 253584*t^3*z^2 + 156336*t^3*z - 44112*t^3 - 1728*t^2*z^9 + 31104*t^2*z^8 - 234576*t^2*z^7 + 962496*t^2*z^6 - 2345760*t^2*z^5 + 3516912*t^2*z^4 - 3304800*t^2*z^3 + 1946160*t^2*z^2 - 650448*t^2*z + 103392*t^2 + 4752*t*z^9 - 85536*t*z^8 + 645408*t*z^7 - 2652048*t*z^6 + 6465312*t*z^5 - 9592992*t*z^4 + 8615376*t*z^3 - 4531680*t*z^2 + 1264320*t*z - 151920*t - 1296*z^13 + 33696*z^12 - 388800*z^11 + 2624400*z^10 - 11506320*z^9 + 34429536*z^8 - 71991504*z^7 + 106103088*z^6 - 109997568*z^5 + 79232688*z^4 - 38610864*z^3 + 12084336*z^2 - 2178768*z + 173760)*hf
  · have hr : (16*t^8 - 176*t^7 + 48*t^6*z^2 - 288*t^6*z + 784*t^6 - 432*t^5*z^2 + 2592*t^5*z - 2048*t^5 - 144*t^4*z^3 + 1872*t^4*z^2 - 7200*t^4*z + 3088*t^4 + 1008*t^3*z^3 - 5856*t^3*z^2 + 6912*t^3*z - 1424*t^3 - 1296*t^2*z^3 + 6048*t^2*z^2 - 1424*t^2 - 1152*t*z^3 + 6336*t*z^2 - 5760*t*z + 1408*t + 288*z^3 - 1536*z^2 + 1152*z - 224:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(144*t^4 - 1008*t^3 + 1296*t^2 + 1152*t - 288)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_58 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 58) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_58 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z^2 + 256*t^7*z - 304*t^7 + 160*t^6*z^4 - 1280*t^6*z^3 + 3840*t^6*z^2 - 5216*t^6*z + 2608*t^6 - 256*t^5*z^6 + 3072*t^5*z^5 - 15216*t^5*z^4 + 40096*t^5*z^3 - 58992*t^5*z^2 + 45408*t^5*z - 13504*t^5 + 304*t^4*z^8 - 4864*t^4*z^7 + 33520*t^4*z^6 - 130432*t^4*z^5 + 313552*t^4*z^4 - 475120*t^4*z^3 + 439360*t^4*z^2 - 222880*t^4*z + 45616*t^4 - 256*t^3*z^10 + 5120*t^3*z^9 - 45360*t^3*z^8 + 234912*t^3*z^7 - 787920*t^3*z^6 + 1785600*t^3*z^5 - 2757744*t^3*z^4 + 2844720*t^3*z^3 - 1852416*t^3*z^2 + 674048*t^3*z - 101776*t^3 + 160*t^2*z^12 - 3840*t^2*z^11 + 41520*t^2*z^10 - 267776*t^2*z^9 + 1147824*t^2*z^8 - 3442896*t^2*z^7 + 7394496*t^2*z^6 - 11415312*t^2*z^5 + 12500064*t^2*z^4 - 9390896*t^2*z^3 + 4539792*t^2*z^2 - 1246272*t^2*z + 144592*t^2 - 64*t*z^14 + 1792*t*z^13 - 22912*t*z^12 + 177440*t*z^11 - 930128*t*z^10 + 3489344*t*z^9 - 9646656*t*z^8 + 19912560*t*z^7 - 30714864*t*z^6 + 35030336*t*z^5 - 28856048*t*z^4 + 16483328*t*z^3 - 6099040*t*z^2 + 1293184*t*z - 117376*t + 16*z^16 - 512*z^15 + 7536*z^14 - 67744*z^13 + 416288*z^12 - 1853232*z^11 + 6174736*z^10 - 15672224*z^9 + 30526560*z^8 - 45596000*z^7 + 51797728*z^6 - 44041488*z^5 + 27317024*z^4 - 11877568*z^3 + 3391824*z^2 - 564032*z + 40768:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z + 320*t^6 + 256*t^5*z^3 - 1536*t^5*z^2 + 3696*t^5*z - 3328*t^5 - 304*t^4*z^5 + 3040*t^4*z^4 - 12544*t^4*z^3 + 26896*t^4*z^2 - 30160*t^4*z + 14464*t^4 + 256*t^3*z^7 - 3584*t^3*z^6 + 21552*t^3*z^5 - 72576*t^3*z^4 + 147744*t^3*z^3 - 181296*t^3*z^2 + 122544*t^3*z - 34560*t^3 - 160*t^2*z^9 + 2880*t^2*z^8 - 22800*t^2*z^7 + 104576*t^2*z^6 - 306528*t^2*z^5 + 594144*t^2*z^4 - 757152*t^2*z^3 + 605520*t^2*z^2 - 270144*t^2*z + 48896*t^2 + 64*t*z^11 - 1408*t*z^10 + 13888*t*z^9 - 81248*t*z^8 + 313424*t*z^7 - 835904*t*z^6 + 1566672*t*z^5 - 2049120*t*z^4 + 1812384*t*z^3 - 1013936*t*z^2 + 313616*t*z - 39056*t - 16*z^13 + 416*z^12 - 4896*z^11 + 34576*z^10 - 163520*z^9 + 546240*z^8 - 1321888*z^7 + 2334176*z^6 - 2985792*z^5 + 2708000*z^4 - 1675072*z^3 + 661680*z^2 - 147296*z + 13456)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_59 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 59) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_59 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z^2 + 448*t^7*z - 368*t^7 + 448*t^6*z^4 - 3136*t^6*z^3 + 8112*t^6*z^2 - 9232*t^6*z + 3616*t^6 - 896*t^5*z^6 + 9408*t^5*z^5 - 40944*t^5*z^4 + 94816*t^5*z^3 - 121872*t^5*z^2 + 80256*t^5*z - 20192*t^5 + 1120*t^4*z^8 - 15680*t^4*z^7 + 95920*t^4*z^6 - 335600*t^4*z^5 + 731920*t^4*z^4 - 1009472*t^4*z^3 + 846400*t^4*z^2 - 384032*t^4*z + 70144*t^4 - 896*t^3*z^10 + 15680*t^3*z^9 - 123600*t^3*z^8 + 578880*t^3*z^7 - 1781280*t^3*z^6 + 3745824*t^3*z^5 - 5409840*t^3*z^4 + 5236752*t^3*z^3 - 3196992*t^3*z^2 + 1086560*t^3*z - 153248*t^3 + 448*t^2*z^12 - 9408*t^2*z^11 + 90768*t^2*z^10 - 532720*t^2*z^9 + 2116800*t^2*z^8 - 5983200*t^2*z^7 + 12277824*t^2*z^6 - 18304992*t^2*z^5 + 19495584*t^2*z^4 - 14283856*t^2*z^3 + 6721248*t^2*z^2 - 1790976*t^2*z + 201616*t^2 - 128*t*z^14 + 3136*t*z^13 - 35792*t*z^12 + 252512*t*z^11 - 1229776*t*z^10 + 4365536*t*z^9 - 11610768*t*z^8 + 23393904*t*z^7 - 35660208*t*z^6 + 40599008*t*z^5 - 33637264*t*z^4 + 19415264*t*z^3 - 7266512*t*z^2 + 1556032*t*z - 142352*t + 16*z^16 - 448*z^15 + 5904*z^14 - 48656*z^13 + 280592*z^12 - 1198944*z^11 + 3916576*z^10 - 9941632*z^9 + 19724112*z^8 - 30507568*z^7 + 36398608*z^6 - 32854896*z^5 + 21766592*z^4 - 10113920*z^3 + 3071952*z^2 - 539056*z + 40768:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6*z + 448*t^6 + 896*t^5*z^3 - 4032*t^5*z^2 + 8688*t^5*z - 3712*t^5 - 1120*t^4*z^5 + 8960*t^4*z^4 - 32080*t^4*z^3 + 59120*t^4*z^2 - 61600*t^4*z + 11552*t^4 + 896*t^3*z^7 - 10304*t^3*z^6 + 53712*t^3*z^5 - 161184*t^3*z^4 + 299856*t^3*z^3 - 334896*t^3*z^2 + 218208*t^3*z - 13872*t^3 - 448*t^2*z^9 + 6720*t^2*z^8 - 46416*t^2*z^7 + 192400*t^2*z^6 - 524496*t^2*z^5 + 965376*t^2*z^4 - 1187904*t^2*z^3 + 915696*t^2*z^2 - 414144*t^2*z - 5984*t^2 + 128*t*z^11 - 2368*t*z^10 + 20432*t*z^9 - 108224*t*z^8 + 389440*t*z^7 - 993584*t*z^6 + 1819632*t*z^5 - 2365536*t*z^4 + 2109552*t*z^3 - 1192976*t*z^2 + 396832*t*z + 31168*t - 16*z^13 + 352*z^12 - 3648*z^11 + 23552*z^10 - 105392*z^9 + 343680*z^8 - 835312*z^7 + 1520464*z^6 - 2052480*z^5 + 2002576*z^4 - 1349440*z^3 + 577632*z^2 - 148112*z - 21760)*hf
  · have hr : (16*t^8 + 64*t^7*z^2 - 320*t^7*z + 16*t^7 + 160*t^6*z^4 - 1600*t^6*z^3 + 4416*t^6*z^2 - 2128*t^6*z + 448*t^6 + 256*t^5*z^6 - 3840*t^5*z^5 + 20400*t^5*z^4 - 44144*t^5*z^3 + 32352*t^5*z^2 - 8160*t^5*z + 256*t^5 + 304*t^4*z^8 - 6080*t^4*z^7 + 47920*t^4*z^6 - 187088*t^4*z^5 + 373312*t^4*z^4 - 362384*t^4*z^3 + 173392*t^4*z^2 - 42368*t^4*z + 4576*t^4 + 256*t^3*z^10 - 6400*t^3*z^9 + 66672*t^3*z^8 - 373776*t^3*z^7 + 1216176*t^3*z^6 - 2317968*t^3*z^5 + 2522592*t^3*z^4 - 1518336*t^3*z^3 + 475920*t^3*z^2 - 64960*t^3*z + 1984*t^3 + 160*t^2*z^12 - 4800*t^2*z^11 + 62256*t^2*z^10 - 456688*t^2*z^9 + 2082528*t^2*z^8 - 6121152*t^2*z^7 + 11685840*t^2*z^6 - 14383008*t^2*z^5 + 11280960*t^2*z^4 - 5565952*t^2*z^3 + 1688880*t^2*z^2 - 292512*t^2*z + 22192*t^2 + 64*t*z^14 - 2240*t*z^13 + 34720*t*z^12 - 313744*t*z^11 + 1831568*t*z^10 - 7236928*t*z^9 + 19736304*t*z^8 - 37271280*t*z^7 + 48345792*t*z^6 - 42337120*t*z^5 + 24347840*t*z^4 - 8797744*t*z^3 + 1851904*t*z^2 - 196640*t*z + 7504*t + 16*z^16 - 640*z^15 + 11568*z^14 - 124928*z^13 + 898256*z^12 - 4537344*z^11 + 16567504*z^10 - 44359792*z^9 + 87547104*z^8 - 127176784*z^7 + 135069040*z^6 - 103592928*z^5 + 56229056*z^4 - 20886032*z^3 + 5004048*z^2 - 688912*z + 40768:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z + 640*t^6 - 256*t^5*z^3 + 2304*t^5*z^2 - 4272*t^5*z - 2992*t^5 - 304*t^4*z^5 + 4256*t^4*z^4 - 19648*t^4*z^3 + 29984*t^4*z^2 - 3808*t^4*z + 10736*t^4 - 256*t^3*z^7 + 4864*t^3*z^6 - 35184*t^3*z^5 + 118128*t^3*z^4 - 176160*t^3*z^3 + 92304*t^3*z^2 - 28944*t^3*z - 14544*t^3 - 160*t^2*z^9 + 3840*t^2*z^8 - 37776*t^2*z^7 + 194992*t^2*z^6 - 561072*t^2*z^5 + 886464*t^2*z^4 - 732432*t^2*z^3 + 327024*t^2*z^2 - 67536*t^2*z + 20224*t^2 - 64*t*z^11 + 1856*t*z^10 - 23008*t*z^9 + 158800*t*z^8 - 666128*t*z^7 + 1741936*t*z^6 - 2813136*t*z^5 + 2716656*t*z^4 - 1501824*t*z^3 + 436864*t*z^2 - 60272*t*z - 1136*t - 16*z^13 + 544*z^12 - 8160*z^11 + 71024*z^10 - 397040*z^9 + 1491408*z^8 - 3832624*z^7 + 6750256*z^6 - 8077728*z^5 + 6460240*z^4 - 3357280*z^3 + 1073904*z^2 - 189392*z + 12704)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_60 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 60) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_60 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z^2 - 192*t^7*z - 112*t^7 + 160*t^6*z^4 - 1152*t^6*z^3 + 2176*t^6*z^2 - 624*t^6*z + 736*t^6 + 256*t^5*z^6 - 2880*t^5*z^5 + 11184*t^5*z^4 - 16416*t^5*z^3 + 4944*t^5*z^2 + 2880*t^5*z - 2848*t^5 + 304*t^4*z^8 - 4800*t^4*z^7 + 29840*t^4*z^6 - 92160*t^4*z^5 + 147984*t^4*z^4 - 124992*t^4*z^3 + 69056*t^4*z^2 - 32928*t^4*z + 9280*t^4 + 256*t^3*z^10 - 5184*t^3*z^9 + 43696*t^3*z^8 - 197760*t^3*z^7 + 515920*t^3*z^6 - 769536*t^3*z^5 + 593600*t^3*z^4 - 136080*t^3*z^3 - 115840*t^3*z^2 + 93792*t^3*z - 20704*t^3 + 160*t^2*z^12 - 4032*t^2*z^11 + 44112*t^2*z^10 - 274752*t^2*z^9 + 1074768*t^2*z^8 - 2754288*t^2*z^7 + 4706896*t^2*z^6 - 5423184*t^2*z^5 + 4314048*t^2*z^4 - 2487888*t^2*z^3 + 1063776*t^2*z^2 - 299520*t^2*z + 38608*t^2 + 64*t*z^14 - 1920*t*z^13 + 25568*t*z^12 - 199008*t*z^11 + 1003008*t*z^10 - 3424320*t*z^9 + 8038288*t*z^8 - 12855792*t*z^7 + 13438688*t*z^6 - 8119584*t*z^5 + 1404096*t*z^4 + 1652256*t*z^3 - 1305200*t*z^2 + 386304*t*z - 42448*t + 16*z^16 - 576*z^15 + 9424*z^14 - 92784*z^13 + 613600*z^12 - 2881728*z^11 + 9911344*z^10 - 25384464*z^9 + 48775120*z^8 - 70354560*z^7 + 75788896*z^6 - 60296976*z^5 + 34751392*z^4 - 14037984*z^3 + 3747520*z^2 - 589008*z + 40768:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z + 192*t^6 - 256*t^5*z^3 + 1344*t^5*z^2 - 816*t^5*z - 1344*t^5 - 304*t^4*z^5 + 2976*t^4*z^4 - 9248*t^4*z^3 + 8976*t^4*z^2 - 1968*t^4*z + 4656*t^4 - 256*t^3*z^7 + 3648*t^3*z^6 - 19504*t^3*z^5 + 47136*t^3*z^4 - 46624*t^3*z^3 + 7056*t^3*z^2 + 9760*t^3*z - 8736*t^3 - 160*t^2*z^9 + 3072*t^2*z^8 - 24240*t^2*z^7 + 101184*t^2*z^6 - 240288*t^2*z^5 + 329184*t^2*z^4 - 265648*t^2*z^3 + 145776*t^2*z^2 - 61008*t^2*z + 12912*t^2 - 64*t*z^11 + 1536*t*z^10 - 15776*t*z^9 + 90336*t*z^8 - 314400*t*z^7 + 677568*t*z^6 - 872272*t*z^5 + 580848*t*z^4 - 70448*t*z^3 - 147552*t*z^2 + 87168*t*z - 12624*t - 16*z^13 + 480*z^12 - 6400*z^11 + 50016*z^10 - 254464*z^9 + 885600*z^8 - 2157520*z^7 + 3705552*z^6 - 4467328*z^5 + 3728064*z^4 - 2097904*z^3 + 754992*z^2 - 156112*z + 12672)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_61 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 61) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_61 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 4*t*z^2 - 20*t*z + 4*t + 2*z^4 - 20*z^3 + 60*z^2 - 50*z + 14:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8 + 192*t^7*z^2 - 832*t^7*z + 272*t^7 + 1056*t^6*z^4 - 9216*t^6*z^3 + 23392*t^6*z^2 - 14416*t^6*z + 2560*t^6 + 3456*t^5*z^6 - 45504*t^5*z^5 + 217008*t^5*z^4 - 444640*t^5*z^3 + 364560*t^5*z^2 - 126336*t^5*z + 15584*t^5 + 7344*t^4*z^8 - 129600*t^4*z^7 + 909648*t^4*z^6 - 3213120*t^4*z^5 + 5975920*t^4*z^4 - 5722976*t^4*z^3 + 2847648*t^4*z^2 - 701600*t^4*z + 67648*t^4 + 10368*t^3*z^10 - 229824*t^3*z^9 + 2134512*t^3*z^8 - 10754688*t^3*z^7 + 31857552*t^3*z^6 - 56541184*t^3*z^5 + 59728768*t^3*z^4 - 37424080*t^3*z^3 + 13581632*t^3*z^2 - 2631392*t^3*z + 210464*t^3 + 9504*t^2*z^12 - 254016*t^2*z^11 + 2940624*t^2*z^10 - 19298304*t^2*z^9 + 78977232*t^2*z^8 - 209334960*t^2*z^7 + 363279472*t^2*z^6 - 411986064*t^2*z^5 + 303664128*t^2*z^4 - 143227696*t^2*z^3 + 41541216*t^2*z^2 - 6734208*t^2*z + 466576*t^2 + 5184*t*z^14 - 162432*t*z^13 + 2255904*t*z^12 - 18283104*t*z^11 + 95848704*t*z^10 - 340820928*t*z^9 + 839856720*t*z^8 - 1444758736*t*z^7 + 1734135872*t*z^6 - 1445072064*t*z^5 + 826362400*t*z^4 - 316517888*t*z^3 + 77340528*t*z^2 - 10874368*t*z + 668720*t + 1296*z^16 - 46656*z^15 + 757296*z^14 - 7322832*z^13 + 46969632*z^12 - 210687264*z^11 + 679532304*z^10 - 1598021712*z^9 + 2755223632*z^8 - 3483491872*z^7 + 3217286560*z^6 - 2151713968*z^5 + 1024946848*z^4 - 337458880*z^3 + 72697888*z^2 - 9184240*z + 513760:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6*z + 2880*t^6 - 3456*t^5*z^3 + 24768*t^5*z^2 - 37296*t^5*z - 12416*t^5 - 7344*t^4*z^5 + 85536*t^4*z^4 - 330336*t^4*z^3 + 439248*t^4*z^2 - 110800*t^4*z + 113936*t^4 - 10368*t^3*z^7 + 167616*t^3*z^6 - 1035504*t^3*z^5 + 3002016*t^3*z^4 - 4023072*t^3*z^3 + 2278096*t^3*z^2 - 846496*t^3*z - 226976*t^3 - 9504*t^2*z^9 + 196992*t^2*z^8 - 1673136*t^2*z^7 + 7458048*t^2*z^6 - 18579744*t^2*z^5 + 25714656*t^2*z^4 - 19399696*t^2*z^3 + 8416752*t^2*z^2 - 1422384*t^2*z + 743536*t^2 - 5184*t*z^11 + 131328*t*z^10 - 1421280*t*z^9 + 8557920*t*z^8 - 31315680*t*z^7 + 71641728*t*z^6 - 102491472*t*z^5 + 91087312*t*z^4 - 50263568*t*z^3 + 16230432*t*z^2 - 3345760*t*z - 421264*t - 1296*z^13 + 38880*z^12 - 512352*z^11 + 3894912*z^10 - 18872352*z^9 + 60861888*z^8 - 132825072*z^7 + 196697232*z^6 - 197028928*z^5 + 132568000*z^4 - 58526512*z^3 + 16356112*z^2 - 2367568*z + 468928)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_62 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 62) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_62 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z^2 - 320*t^7*z + 16*t^7 + 160*t^6*z^4 - 1600*t^6*z^3 + 4416*t^6*z^2 - 2128*t^6*z + 448*t^6 + 256*t^5*z^6 - 3840*t^5*z^5 + 20400*t^5*z^4 - 44144*t^5*z^3 + 32352*t^5*z^2 - 8160*t^5*z + 256*t^5 + 304*t^4*z^8 - 6080*t^4*z^7 + 47920*t^4*z^6 - 187088*t^4*z^5 + 373312*t^4*z^4 - 362384*t^4*z^3 + 173392*t^4*z^2 - 42368*t^4*z + 4576*t^4 + 256*t^3*z^10 - 6400*t^3*z^9 + 66672*t^3*z^8 - 373776*t^3*z^7 + 1216176*t^3*z^6 - 2317968*t^3*z^5 + 2522592*t^3*z^4 - 1518336*t^3*z^3 + 475920*t^3*z^2 - 64960*t^3*z + 1984*t^3 + 160*t^2*z^12 - 4800*t^2*z^11 + 62256*t^2*z^10 - 456688*t^2*z^9 + 2082528*t^2*z^8 - 6121152*t^2*z^7 + 11685840*t^2*z^6 - 14383008*t^2*z^5 + 11280960*t^2*z^4 - 5565952*t^2*z^3 + 1688880*t^2*z^2 - 292512*t^2*z + 22192*t^2 + 64*t*z^14 - 2240*t*z^13 + 34720*t*z^12 - 313744*t*z^11 + 1831568*t*z^10 - 7236928*t*z^9 + 19736304*t*z^8 - 37271280*t*z^7 + 48345792*t*z^6 - 42337120*t*z^5 + 24347840*t*z^4 - 8797744*t*z^3 + 1851904*t*z^2 - 196640*t*z + 7504*t + 16*z^16 - 640*z^15 + 11568*z^14 - 124928*z^13 + 898256*z^12 - 4537344*z^11 + 16567504*z^10 - 44359792*z^9 + 87547104*z^8 - 127176784*z^7 + 135069040*z^6 - 103592928*z^5 + 56229056*z^4 - 20886032*z^3 + 5004048*z^2 - 688912*z + 40768:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6*z + 640*t^6 - 256*t^5*z^3 + 2304*t^5*z^2 - 4272*t^5*z - 2992*t^5 - 304*t^4*z^5 + 4256*t^4*z^4 - 19648*t^4*z^3 + 29984*t^4*z^2 - 3808*t^4*z + 10736*t^4 - 256*t^3*z^7 + 4864*t^3*z^6 - 35184*t^3*z^5 + 118128*t^3*z^4 - 176160*t^3*z^3 + 92304*t^3*z^2 - 28944*t^3*z - 14544*t^3 - 160*t^2*z^9 + 3840*t^2*z^8 - 37776*t^2*z^7 + 194992*t^2*z^6 - 561072*t^2*z^5 + 886464*t^2*z^4 - 732432*t^2*z^3 + 327024*t^2*z^2 - 67536*t^2*z + 20224*t^2 - 64*t*z^11 + 1856*t*z^10 - 23008*t*z^9 + 158800*t*z^8 - 666128*t*z^7 + 1741936*t*z^6 - 2813136*t*z^5 + 2716656*t*z^4 - 1501824*t*z^3 + 436864*t*z^2 - 60272*t*z - 1136*t - 16*z^13 + 544*z^12 - 8160*z^11 + 71024*z^10 - 397040*z^9 + 1491408*z^8 - 3832624*z^7 + 6750256*z^6 - 8077728*z^5 + 6460240*z^4 - 3357280*z^3 + 1073904*z^2 - 189392*z + 12704)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_1_63 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 63) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : False := by
  apply cell_1_63 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (-48*t*z^12 + 1296*t*z^11 - 15552*t*z^10 + 109296*t*z^9 - 498672*t*z^8 + 1546128*t*z^7 - 3310224*t*z^6 + 4869504*t*z^5 - 4803408*t*z^4 + 3033936*t*z^3 - 1138464*t*z^2 + 224640*t*z - 17472*t + 16*z^16 - 576*z^15 + 9488*z^14 - 94704*z^13 + 639376*z^12 - 3086064*z^11 + 10974272*z^10 - 29198016*z^9 + 58430848*z^8 - 87713328*z^7 + 97790720*z^6 - 79573824*z^5 + 46025872*z^4 - 18186192*z^3 + 4604960*z^2 - 663936*z + 40768:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t*z^9 - 1008*t*z^8 + 9072*t*z^7 - 45648*t*z^6 + 140112*t*z^5 - 267408*t*z^4 + 307824*t*z^3 - 195552*t*z^2 + 57456*t*z - 5760*t - 16*z^13 + 480*z^12 - 6464*z^11 + 51552*z^10 - 270448*z^9 + 980016*z^8 - 2505488*z^7 + 4533600*z^6 - 5739808*z^5 + 4955616*z^4 - 2797952*z^3 + 966144*z^2 - 180592*z + 13488)*hf


private def limit1 (z t : ℝ) : Fin 64→Prop := ![False,False,False,False,False,False,False,((t + z^2 - 4*z:ℝ)=0),False,False,False,False,False,((t + z^2 - 4*z:ℝ)=0),False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,((t - z^2 + 2*z - 1:ℝ)=0),False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False]

private def hue1 : Fin 64→Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_1_7_13 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit1 z t 7) (_hj : limit1 z t 13) (he : edge4 (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 7) (profile4 (-z^2 + 5*z - 2) (z) t 13) (-z^2 + 5*z - 2) (z) t=0) : False := by
  apply pair_1_7_13 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (1296*t^8 + 10368*t^7*z^2 - 51840*t^7*z + 19440*t^7 + 36288*t^6*z^4 - 362880*t^6*z^3 + 1045872*t^6*z^2 - 694656*t^6*z + 130896*t^6 + 72576*t^5*z^6 - 1088640*t^5*z^5 + 5866992*t^5*z^4 - 13317696*t^5*z^3 + 11448864*t^5*z^2 - 4090176*t^5*z + 517104*t^5 + 90720*t^4*z^8 - 1814400*t^4*z^7 + 14327280*t^4*z^6 - 56168640*t^4*z^5 + 112954176*t^4*z^4 - 111607632*t^4*z^3 + 55944432*t^4*z^2 - 13722048*t^4*z + 1308960*t^4 + 72576*t^3*z^10 - 1814400*t^3*z^9 + 18876240*t^3*z^8 - 105390720*t^3*z^7 + 339945984*t^3*z^6 - 638834688*t^3*z^5 + 687270096*t^3*z^4 - 426885552*t^3*z^3 + 151142112*t^3*z^2 - 28289088*t^3*z + 2169504*t^3 + 36288*t^2*z^12 - 1088640*t^2*z^11 + 14055120*t^2*z^10 - 101917440*t^2*z^9 + 454638096*t^2*z^8 - 1287760032*t^2*z^7 + 2322809136*t^2*z^6 - 2647473984*t^2*z^5 + 1907308944*t^2*z^4 - 861921648*t^2*z^3 + 236114352*t^2*z^2 - 35751456*t^2*z + 2291328*t^2 + 10368*t*z^14 - 362880*t*z^13 + 5594832*t*z^12 - 49916736*t*z^11 + 284796000*t*z^10 - 1084995648*t*z^9 + 2805000192*t*z^8 - 4928427504*t*z^7 + 5861693952*t*z^6 - 4708498896*t*z^5 + 2538455760*t*z^4 - 900931248*t*z^3 + 201158640*t*z^2 - 25528608*t*z + 1399680*t + 1296*z^16 - 51840*z^15 + 929232*z^14 - 9844416*z^13 + 68467680*z^12 - 328552848*z^11 + 1114033824*z^10 - 2694117024*z^9 + 4651778160*z^8 - 5720564736*z^7 + 4995616032*z^6 - 3080455920*z^5 + 1323953424*z^4 - 386101728*z^3 + 72498240*z^2 - 7869312*z + 373248:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-36288*t^6*z + 145152*t^6 - 72576*t^5*z^3 + 653184*t^5*z^2 - 1294704*t^5*z - 546912*t^5 - 90720*t^4*z^5 + 1270080*t^4*z^4 - 5890320*t^4*z^3 + 9123840*t^4*z^2 - 1388016*t^4*z + 3494016*t^4 - 72576*t^3*z^7 + 1378944*t^3*z^6 - 9949392*t^3*z^5 + 33066144*t^3*z^4 - 47867760*t^3*z^3 + 24184656*t^3*z^2 - 12153888*t^3*z - 7302960*t^3 - 36288*t^2*z^9 + 870912*t^2*z^8 - 8503056*t^2*z^7 + 42952032*t^2*z^6 - 117785664*t^2*z^5 + 168968592*t^2*z^4 - 120070512*t^2*z^3 + 52976592*t^2*z^2 - 1909008*t^2*z + 13466736*t^2 - 10368*t*z^11 + 300672*t*z^10 - 3697488*t*z^9 + 24994656*t*z^8 - 100648656*t*z^7 + 245059344*t*z^6 - 353822256*t*z^5 + 298013904*t*z^4 - 154032192*t*z^3 + 40713840*t*z^2 - 13841280*t*z - 10637568*t - 1296*z^13 + 44064*z^12 - 653184*z^11 + 5524848*z^10 - 29307744*z^9 + 101023200*z^8 - 227550384*z^7 + 331682688*z^6 - 310658976*z^5 + 188815536*z^4 - 71743968*z^3 + 18675360*z^2 + 241056*z + 4237920)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_1_7_47 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit1 z t 7) (hj : limit1 z t 47) (_he : edge4 (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 7) (profile4 (-z^2 + 5*z - 2) (z) t 47) (-z^2 + 5*z - 2) (z) t=0) : False := by
  apply pair_1_7_47 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_1_13_47 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit1 z t 13) (hj : limit1 z t 47) (_he : edge4 (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t 13) (profile4 (-z^2 + 5*z - 2) (z) t 47) (-z^2 + 5*z - 2) (z) t=0) : False := by
  apply pair_1_13_47 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma exclude_field_1 (z t : ℝ) (hf : z^3 - 6*z^2 + 9*z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(-z^2 + 5*z - 2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (g : Fin 5→Fin 64) (hinj : Function.Injective g)
    (hc : ∀ i, cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t (g i)) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t)
    (he : ∀ i j : Fin 5, i≠j → edge4 (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t (g i)) (profile4 (-z^2 + 5*z - 2) (z) t (g j)) (-z^2 + 5*z - 2) (z) t=0) : False := by
  have row (k : Fin 64) (hh : cell (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t k) ((1),(-z^2 + 5*z - 2),(z)) ((1),(z),(-z^2 + 5*z - 2)) (-z^2 + 5*z - 2) (z) t) : limit1 z t k := by
    fin_cases k
    · exact row_1_0 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_1 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_2 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_3 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_4 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_5 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_6 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_7 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_8 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_9 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_10 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_11 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_12 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_13 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_14 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_15 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_16 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_17 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_18 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_19 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_20 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_21 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_22 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_23 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_24 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_25 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_26 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_27 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_28 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_29 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_30 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_31 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_32 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_33 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_34 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_35 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_36 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_37 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_38 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_39 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_40 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_41 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_42 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_43 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_44 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_45 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_46 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_47 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_48 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_49 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_50 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_51 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_52 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_53 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_54 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_55 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_56 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_57 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_58 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_59 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_60 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_61 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_62 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_1_63 z t hf hn0 hn1 hn2 hn3 hh
  have allowed (k : Fin 64) (hh : limit1 z t k) : k∈([7,13,47]:List (Fin 64)) := by
    fin_cases k <;> first | decide | exact False.elim hh
  have cert : ∀ i j : Fin 64, i∈([7,13,47]:List (Fin 64)) → j∈([7,13,47]:List (Fin 64)) → i<j → hue1 i=hue1 j → (i,j)∈([(7,13),(7,47),(13,47)]:List (Fin 64×Fin 64)) := by decide
  have bad (i j : Fin 64) (hi : limit1 z t i) (hj : limit1 z t j) (hlt : i<j) (hc : hue1 i=hue1 j) (hb : edge4 (1) (1) (1) (profile4 (-z^2 + 5*z - 2) (z) t i) (profile4 (-z^2 + 5*z - 2) (z) t j) (-z^2 + 5*z - 2) (z) t=0) : False := by
    have h := cert i j (allowed i hi) (allowed j hj) hlt hc
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact rowpair_1_7_13 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_1_7_47 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_1_13_47 z t hf hn0 hn1 hn2 hn3 hi hj hb
  have hi : Function.Injective (fun i : Fin 5 => hue1 (g i)) := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne (show g i≠g j from fun e => hne (hinj e)) with hl|hl
    · exact bad _ _ (row _ (hc i)) (row _ (hc j)) hl h (he i j hne)
    · exact bad _ _ (row _ (hc j)) (row _ (hc i)) hl h.symm (he j i (Ne.symm hne))
  have hh := Fintype.card_le_of_injective _ hi
  norm_num at hh

private lemma no_0000012211 (x y t : ℝ) (H : admissible ![0,0,0,0,0,1,2,2,1,1] x y) (E : hasExtension ![0,0,0,0,0,1,2,2,1,1] x y t)
    (t1 : t-1≠0) (tx : t-x≠0) (ty : t-y≠0) (t0 : t≠0) : False := by
  obtain ⟨h0,h1⟩ := shape_0000012211 x y H
  by_cases G0 : y^3 - 6*y^2 + 9*y - 3=0
  · have ex : x=-y^2 + 5*y - 2 := by linear_combination (1)*h0
    obtain ⟨u,hu,hc,he⟩ := E
    change ∀ i, cell (1) (1) (1) (profile4 x y t (u i)) ((1),(x),(y)) ((1),(y),(x)) x y t at hc
    change ∀ i j, i≠j → edge4 (1) (1) (1) (profile4 x y t (u i)) (profile4 x y t (u j)) x y t=0 at he
    simp only [ex] at hc he tx ty
    apply exclude_field_1 y t (by linear_combination (1)*G0) t1 tx ty (by simpa using t0) u hu hc he
  apply G0
  linear_combination (1)*h1

private lemma no_0000011120 (x y t : ℝ) (H : admissible ![0,0,0,0,0,1,1,1,2,0] x y) (E : hasExtension ![0,0,0,0,0,1,1,1,2,0] x y t)
    (t1 : t-1≠0) (tx : t-x≠0) (ty : t-y≠0) (t0 : t≠0) : False := by
  obtain ⟨h0,h1⟩ := shape_0000011120 x y H
  by_cases G0 : x^2 - 4*x + 1=0
  · have ey : y=2 := by linear_combination (1)*h1
    obtain ⟨u,hu,hc,he⟩ := E
    change ∀ i, cell (1) (1) (1) (profile4 x y t (u i)) ((1),(x),(x)) ((1),(x),(y)) x y t at hc
    change ∀ i j, i≠j → edge4 (1) (1) (1) (profile4 x y t (u i)) (profile4 x y t (u j)) x y t=0 at he
    simp only [ey] at hc he tx ty
    apply exclude_field_0 x t (by linear_combination (1)*G0) t1 tx ty (by simpa using t0) u hu hc he
  apply G0
  linear_combination (1)*h0

end Erdos1082Ten

open Erdos1082Ten EuclideanGeometry

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H3_R1.H2 := by
  intro A hn hA hd M hm B hBA hB hf hthree p r c hc hh
  obtain ⟨x,y,t,H,E,t1,tx,ty,t0⟩ := given_extension A B M hm hBA hA hB hd hthree hn hf p r c hc
  change colorCode c∈([157,123]:List ℕ) at hh
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with eq|eq
  · have cc : c=![0,0,0,0,0,1,2,2,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact no_0000012211 x y t H E t1 tx ty t0
  · have cc : c=![0,0,0,0,0,1,1,1,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact no_0000011120 x y t H E t1 tx ty t0
