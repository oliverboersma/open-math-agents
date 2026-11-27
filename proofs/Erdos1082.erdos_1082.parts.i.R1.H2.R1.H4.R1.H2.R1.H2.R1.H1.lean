import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H2_R1

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
private lemma base_0011101102 (x y : ℝ) (g0 : 2*x^3 - 4*x^2 - 4*x + (2:ℝ)=0) (g1 : 3*x^3 - x^2*y - 10*x^2 + 4*x*y + 5*x - (2:ℝ)=0) (g2 : 2*x^3 - 4*x^2 - 4*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : 4*x - (1:ℝ)≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : 4*x*y - y^2≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : (x + (1:ℝ)=0) ∧ (y + (4:ℝ)=0) := by
  have h1 : x^3 - 2*x^2 - 2*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^3 - x^2*y/3 - 10*x^2/3 + 4*x*y/3 + 5*x/3 - 2/(3:ℝ)=0 := by linear_combination (1/3)*g1
  have h3 : x^3 - 2*x^2 - 2*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x^2 - 3*x + y=0 := by linear_combination (-18*x^2/25 + 39*x/25 + 42/25)*h2 + (18*x^2/25 - 6*x*y/25 - 63*x/25 + y + 28/25)*h3
  have h5 : x*y - x + y - (1:ℝ)=0 := by linear_combination (-3*x^2/5 + 9*x/5 + 12/5)*h2 + (3*x^2/5 - x*y/5 - 13*x/5 + y + 3/5)*h3
  have h6 : y^2 + 3*y - (4:ℝ)=0 := by linear_combination (-18*x^2*y/25 - 57*x^2/25 + 39*x*y/25 + 111*x/25 + 42*y/25 + 183/25)*h2 + (18*x^2*y/25 + 57*x^2/25 - 6*x*y^2/25 - 82*x*y/25 - 187*x/25 + y^2 + 103*y/25 + 22/25)*h3
  have h8 : y - (1:ℝ)≠0 := by
    intro he
    apply n3
    linear_combination (1)*he
  have h9 : ((y - 1))*(x + 1)=0 := by linear_combination (1)*h5
  have h7 := (mul_eq_zero.mp h9).resolve_left h8
  have h11 : ((y - 1))*(y + 4)=0 := by linear_combination (1)*h6
  have h10 := (mul_eq_zero.mp h11).resolve_left h8
  have h12 : x + (1:ℝ)=0 := by linear_combination (1)*h7
  have h13 : y + (4:ℝ)=0 := by linear_combination (1)*h10
  have h14 : x + (1:ℝ)=0 := by linear_combination (1)*h12
  have h15 : y + (4:ℝ)=0 := by linear_combination (1)*h13
  exact ⟨h14, h15⟩



private lemma base_0011201102 (x y : ℝ) (g0 : 2*x^2 + 2*x*y^2 - 6*x*y - 4*x + (2:ℝ)=0) (g1 : x^2*y - 2*x^2 + 2*x*y^2 - 8*x*y + 4*x - y^3 + 4*y^2 + y - (2:ℝ)=0) (g2 : 2*x^2 + 2*x*y^2 - 6*x*y - 4*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (n5 : -y^2 + 4*y≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : 4*x - (1:ℝ)≠0) (_n9 : -x^2 + 4*x≠0) (n10 : 4*x*y - y^2≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : (x + y^3/3 - y^2 - 4*y/3 + (1:ℝ)=0) ∧ (y^4 - 6*y^3 + 5*y^2 + 12*y - (9:ℝ)=0) := by
  have h1 : x^2 + x*y^2 - 3*x*y - 2*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 + x*y^2 - 3*x*y - 2*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h3 : 3*x^2 + 3*x*y - 6*x - y^5 + 7*y^4 - 8*y^3 - 19*y^2 + 12*y + (3:ℝ)=0 := by linear_combination (x + y^2 - 3*y - 3)*g1 + (-x*y + 2*x - 2*y^2 + 9*y - 3)*h2
  have h4 : 3*x*y^2 - 12*x*y + y^5 - 7*y^4 + 8*y^3 + 19*y^2 - 12*y=0 := by linear_combination (-x - y^2 + 3*y + 3)*g1 + (x*y - 2*x + 2*y^2 - 9*y + 6)*h2
  have h5 : y^6 - 10*y^5 + 29*y^4 - 8*y^3 - 57*y^2 + 36*y=0 := by linear_combination (-x*y + 3*x - y^3 + 6*y^2 - 6*y - 6)*g1 + (x*y^2 - 5*x*y + 6*x + 2*y^3 - 15*y^2 + 30*y - 12)*h2
  have h6 : x^2 + x*y - 2*x - y^5/3 + 7*y^4/3 - 8*y^3/3 - 19*y^2/3 + 4*y + (1:ℝ)=0 := by linear_combination (1/3)*h3
  have h8 : y - (4:ℝ)≠0 := by
    intro he
    apply n5
    linear_combination (-y)*he
  have h9 : y≠0 := by
    intro he
    apply n10
    linear_combination (4*x - y)*he
  have h10 : ((y - 4) * (y))*(x + y^3/3 - y^2 - 4*y/3 + 1)=0 := by linear_combination (1/3)*h4
  have h7 := (mul_eq_zero.mp h10).resolve_left (mul_ne_zero h8 h9)
  have h12 : ((y - 4) * (y))*(y^4 - 6*y^3 + 5*y^2 + 12*y - 9)=0 := by linear_combination (1)*h5
  have h11 := (mul_eq_zero.mp h12).resolve_left (mul_ne_zero h8 h9)
  exact ⟨h7, h11⟩



private lemma shape_0011101102 (x y : ℝ) (ha : admissible ![0,0,1,1,1,0,1,1,0,2] x y) : (x + 1=0) ∧ (y + 4=0) := by
  apply base_0011101102 x y
  · have hg : gram 1 1 x x 1 x x 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 x x x 1 y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x x 1 x x 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
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
  · have hn : area x x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0011201102 (x y : ℝ) (ha : admissible ![0,0,1,1,2,0,1,1,0,2] x y) : (x + y^3/3 - y^2 - 4*y/3 + 1=0) ∧ (y^4 - 6*y^3 + 5*y^2 + 12*y - 9=0) := by
  apply base_0011201102 x y
  · have hg : gram 1 1 y x 1 x x 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 y x 1 x x x 1 y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 y x x 1 x x 1 0=0 := ha.2.2.2.2
    convert hg using 1 ; unfold gram area ; ring
  · exact ha.1.1
  · exact ha.1.2.1
  · exact ha.1.2.2.1
  · exact ha.1.2.2.2.1
  · exact ha.1.2.2.2.2
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 2 (by decide) (by decide)
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring

private lemma cell_11_0 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/9 - 7/18)*h0 + (-4/9)*hf
  norm_num at hh

private lemma cell_11_1 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (24*z - 18:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z/9 - 17/18)*h0 + (-16/3)*hf
  norm_num at hh

private lemma cell_11_2 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/6 - 1/2)*h0 + (-1/3)*hf
  norm_num at hh

private lemma cell_11_3 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 6*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 176*z) + t^6*(4048*z - 2624) + t^5*(32128 - 46064*z) + t^4*(318112*z - 222080) + t^3*(963712 - 1382096*z) + t^2*(3687440*z - 2570864) + t*(3844240 - 5513648*z) + 3529696*z - 2460992:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(1610*z/4131 - 13853/8262) + t^6*(3409/306 - 793*z/306) + t^5*(2206*z/459 - 9407/459) + t^4*(-352*z/4131 - 6121/4131) + t^3*(76349/2754 - 10771*z/2754) + t^2*(-8011*z/918 - 193/918) + t*(92342*z/4131 - 105046/4131) - 41921*z/2754 + 30457/2754)*h0 + (t*(13853/66096 - 805*z/16524) + 2867*z/22032 - 6167/11016)*h1 + (-32200*t^8/4131 + 878200*t^7/4131 - 11342492*t^6/4131 + 88662491*t^5/4131 - 449182103*t^4/4131 + 1485085121*t^3/4131 - 3091450144*t^2/4131 + 3673601908*t/4131 - 632351639/1377)*hf
  norm_num at hh

private lemma cell_11_4 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (24*z - 18:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z/9 - 17/18)*h0 + (-16/3)*hf
  norm_num at hh

private lemma cell_11_5 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (68*z - 48:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (17*z/36 - 73/36)*h0 + (-289/9)*hf
  norm_num at hh

private lemma cell_11_6 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 1)*h0 + (-1)*hf
  norm_num at hh

private lemma cell_11_7 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2 - 8*z) + 32*z - 22:ℝ)=0) (h1 : (16*t^8 + t^7*(208 - 368*z) + t^6*(13984*z - 9728) + t^5*(199024 - 285392*z) + t^4*(3536800*z - 2465984) + t^3*(19001968 - 27253712*z) + t^2*(127569632*z - 88944656) + t*(231492736 - 332020448*z) + 368468416*z - 256905152:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(611/324 - 71*z/162) + t^6*(1181*z/972 - 5083/972) + t^5*(541/324 - 61*z/162) + t^4*(1607/324 - 221*z/162) + t^3*(3539*z/972 - 5749/972) + t^2*(4235/324 - 1393*z/81) + t*(9235*z/162 - 6443/162) - 19423*z/243 + 26593/486)*h0 + (t*(71*z/1296 - 611/2592) - 325*z/3888 + 2797/7776)*h1 + (1349*t^8/81 - 187867*t^7/243 + 1357717*t^6/81 - 52880399*t^5/243 + 434673977*t^4/243 - 750641165*t^3/81 + 7011524912*t^2/243 - 11649999802*t/243 + 277227268/9)*hf
  norm_num at hh

private lemma cell_11_8 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/6 - 1/2)*h0 + (-1/3)*hf
  norm_num at hh

private lemma cell_11_9 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 1)*h0 + (-1)*hf
  norm_num at hh

private lemma cell_11_10 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (14*z - 12:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7*z/54 - 29/54)*h0 + (-49/27)*hf
  norm_num at hh

private lemma cell_11_11 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z - 6):ℝ)=0) (h1 : (16*t^8 + t^7*(-48*z - 48) + t^6*(480*z - 240) + t^5*(1584 - 2160*z) + t^4*(5760*z - 4176) + t^3*(6768 - 9696*z) + t^2*(9712*z - 6720) + t*(3168 - 4560*z):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(409/5832 - 95*z/5832) + t^5*(11*z/243 - 95/486) + t^4*(19*z/1944 - 71/1944) + t^3*(43/162 - 11*z/162) + t^2*(31*z/648 - 77/648) + t*(-z/108 - 35/216) + 11*z/72 - 11/36)*h0 + (95*z/46656 - 409/46656)*h1 + (95*t^7/729 - 173*t^6/162 + 1064*t^5/243 - 313*t^4/27 + 19097*t^3/972 - 57611*t^2/2916 + 2182*t/243)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_11_12 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 6*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-112*z - 176) + t^6*(2880*z - 416) + t^5*(18352 - 33568*z) + t^4*(230432*z - 152000) + t^3*(690016 - 1001136*z) + t^2*(2728736*z - 1898672) + t*(2982400 - 4278816*z) + 2948896*z - 2055968:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(21653/78003 - 5032*z/78003) + t^6*(140285*z/156006 - 603691/156006) + t^5*(1065721/52002 - 247631*z/52002) + t^4*(959597*z/78003 - 4128868/78003) + t^3*(5620387/78003 - 2622331*z/156006) + t^2*(676751*z/52002 - 2803837/52002) + t*(3524233/156006 - 1070105*z/156006) + 550871*z/156006 - 921511/156006)*h0 + (t*(629*z/78003 - 21653/624024) - 7625*z/1248048 + 32785/1248048)*h1 + (20128*t^8/26001 - 564806*t^7/26001 + 21323024*t^6/78003 - 156791105*t^5/78003 + 243716627*t^4/26001 - 2183581573*t^3/78003 + 3984627650*t^2/78003 - 1296739216*t/26001 + 1403680637/78003)*hf
  norm_num at hh

private lemma cell_11_13 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2 - 8*z) + 32*z - 22:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 304*z) + t^6*(12368*z - 7712) + t^5*(174160 - 252688*z) + t^4*(3166400*z - 2205536) + t^3*(17620864 - 25274224*z) + t^2*(125688144*z - 87632768) + t*(248217232 - 356007632*z) + 439581376*z - 306486848:ℝ)=0) (h2 : (16*t^8 + t^7*(208 - 368*z) + t^6*(13984*z - 9728) + t^5*(199024 - 285392*z) + t^4*(3536800*z - 2465984) + t^3*(19001968 - 27253712*z) + t^2*(127569632*z - 88944656) + t*(231492736 - 332020448*z) + 368468416*z - 256905152:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(13497691/4566456 - 3136973*z/4566456) + t^12*(42044387*z/4566456 - 45226891/1141614) + t^11*(314894765/1522152 - 73184101*z/1522152) + t^10*(69598027*z/570807 - 2395717345/4566456) + t^9*(693342271/1141614 - 644554805*z/4566456) + t^8*(5670301*z/507384 - 24386351/507384) + t^7*(113996251*z/761076 - 490740713/761076) + t^6*(1063712821/1522152 - 61518815*z/380538) + t^5*(4084885*z/63423 - 38255047/126846) + t^4*(180976691*z/4566456 - 39056737/1141614) + t^3*(944207125/4566456 - 397539649*z/2283228) + t^2*(316520135*z/761076 - 251590663/761076) + t*(525434827/1141614 - 1505391319*z/2283228) + 280022392*z/570807 - 389116933/1141614)*h0 + (t^7*(3136973*z/36531648 - 13497691/36531648) + t^6*(39743779/36531648 - 9236777*z/36531648) + t^5*(72161*z/761076 - 4967881/12177216) + t^4*(2125511*z/9132912 - 9145603/9132912) + t^3*(15564581/18265824 - 904327*z/4566456) + t^2*(826513*z/12177216 - 1778365/6088608) + t*(23573*z/9132912 - 200939/18265824) - 890101*z/18265824 + 3827537/18265824)*h1 + (2629/7776 - 611*z/7776)*h2 + (15684865*t^14/761076 - 595502444*t^13/570807 + 27598567319*t^12/1141614 - 763459325057*t^11/2283228 + 6819749412959*t^10/2283228 - 13256111776981*t^9/761076 + 48677787990433*t^8/761076 - 50671623589405*t^7/380538 + 14008388514419*t^6/126846 + 51553016448839*t^5/761076 - 412905767848927*t^4/2283228 + 245511659792735*t^3/2283228 - 14597914106129*t^2/1141614 - 50854930166299*t/1141614 + 9581513753552/190269)*hf
  norm_num at hh

private lemma cell_11_14 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z - 6):ℝ)=0) (h2 : (16*t^8 + t^7*(-48*z - 48) + t^6*(480*z - 240) + t^5*(1584 - 2160*z) + t^4*(5760*z - 4176) + t^3*(6768 - 9696*z) + t^2*(9712*z - 6720) + t*(3168 - 4560*z):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(409/5832 - 95*z/5832) + t^5*(11*z/243 - 95/486) + t^4*(19*z/1944 - 71/1944) + t^3*(43/162 - 11*z/162) + t^2*(31*z/648 - 77/648) + t*(-z/108 - 35/216) + 11*z/72 - 11/36)*h0 + (95*z/46656 - 409/46656)*h2 + (95*t^7/729 - 173*t^6/162 + 1064*t^5/243 - 313*t^4/27 + 19097*t^3/972 - 57611*t^2/2916 + 2182*t/243)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_11_15 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z - 8*t*z + 10*z - 6:ℝ)=0) (h1 : (t^8*(1520*z - 1056) + t^7*(26352 - 37872*z) + t^6*(413120*z - 287760) + t^5*(1796208 - 2577184*z) + t^4*(10055360*z - 7010112) + t^3*(17512944 - 25118464*z) + t^2*(39209232*z - 27337680) + t*(24359568 - 34937872*z) + 13589472*z - 9474912:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(2779/7452 - 307*z/3726) + t^6*(1369*z/1242 - 12805/2484) + t^5*(96409/3726 - 9490*z/1863) + t^4*(21011*z/2484 - 142735/2484) + t^3*(32351*z/7452 + 180313/3726) + t^2*(453/46 - 2931*z/92) + t*(286303*z/7452 - 246497/7452) - 440*z/27 + 695/54)*h0 + (t*(6491*z/201204 - 223481/1609632) - 198019*z/1609632 + 852101/1609632)*h1 + (-2458291*t^9/50301 + 141437291*t^8/100602 - 1807497011*t^7/100602 + 4490063597*t^6/33534 - 21506441533*t^5/33534 + 34328398367*t^4/16767 - 9525263491*t^3/2187 + 299358960314*t^2/50301 - 238277026262*t/50301 + 28033707983/16767)*hf
  norm_num at hh

private lemma cell_11_16 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (24*z - 18:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z/9 - 17/18)*h0 + (-16/3)*hf
  norm_num at hh

private lemma cell_11_17 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h1 : (t*(240 - 208*z):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (25/1944 - 13*z/3888)*h1 + (-169*t/243)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_11_18 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (56*z - 40:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7*z/24 - 5/4)*h0 + (-49/3)*hf
  norm_num at hh

private lemma cell_11_19 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(8*z - 10) + 16*z - 10:ℝ)=0) (h1 : (16*t^8 + t^7*(144*z - 176) + t^6*(1472*z - 992) + t^5*(10080*z - 6800) + t^4*(43168*z - 30272) + t^3*(115920*z - 81056) + t^2*(190176*z - 132464) + t*(171872*z - 119744) + 64480*z - 44960:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(6761/11016 - 1573*z/11016) + t^6*(15677*z/33048 - 67987/33048) + t^5*(607*z/2754 - 12287/11016) + t^4*(71297/11016 - 9509*z/5508) + t^3*(4681/4131 - 33679*z/33048) + t^2*(-4843*z/11016 - 12643/2754) + t*(985/1377 - 2426*z/1377) - 4457*z/4131 + 29035/16524)*h0 + (t*(1573*z/88128 - 6761/88128) - 3923*z/264384 + 8537/132192)*h1 + (-7865*t^8/5508 - 423797*t^7/16524 - 461101*t^6/2754 - 840869*t^5/1377 - 7671251*t^4/5508 - 27340351*t^3/16524 - 309466*t^2/1377 + 5932928*t/4131 + 8047469/8262)*hf
  norm_num at hh

private lemma cell_11_20 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h2 : (t*(240 - 208*z):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (25/1944 - 13*z/3888)*h2 + (-169*t/243)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_11_21 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(39264*z - 27360) + 558048*z - 389088:ℝ)=0) : (t + 4*z - 3:ℝ)=0 := by
  have hh : (t + 4*z - 3:ℝ)=0 := by linear_combination (55/729 - 409*z/23328)*h1 + (167281*t/243 + 2377517/243)*hf
  exact hh

private lemma cell_11_22 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (14*z - 10:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7*z/6 - 5)*h0 + (-49/3)*hf
  norm_num at hh

private lemma cell_11_23 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z - 4) - 2*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 48*z) + t^6*(208*z - 224) + t^5*(112 - 48*z) + t^4*(736 - 896*z) + t^3*(720*z - 608) + t^2*(1232*z - 896) + t*(496 - 656*z) - 512*z + 352:ℝ)=0) (h2 : (16*t^8 + t^7*(16*z - 176) + t^6*(640 - 64*z) + t^5*(16*z - 848) + t^4*(160*z + 64) + t^3*(496 - 144*z) + t^2*(112 - 256*z) + t*(288*z - 224) - 224*z + 160:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(42451*z/236196 - 182657/236196) + t^12*(830329/118098 - 385951*z/236196) + t^11*(296885*z/78732 - 638711/39366) + t^10*(1105907*z/236196 - 1189648/59049) + t^9*(6195115/59049 - 5759069*z/236196) + t^8*(129145*z/26244 - 277927/13122) + t^7*(3842477*z/78732 - 16531741/78732) + t^6*(6627685/78732 - 385316*z/19683) + t^5*(4676525/26244 - 271564*z/6561) + t^4*(409358*z/59049 - 1768723/59049) + t^3*(3387895*z/236196 - 14570219/236196) + t^2*(496069*z/78732 - 531842/19683) + t*(59743*z/236196 - 76745/59049) - 87532*z/59049 + 757345/118098)*h0 + (t^7*(182657/1889568 - 42451*z/1889568) + t^6*(12341*z/59049 - 1699217/1889568) + t^5*(1699217/629856 - 12341*z/19683) + t^4*(1035569*z/1889568 - 4455817/1889568) + t^3*(569785*z/1889568 - 2451659/1889568) + t^2*(688177/629856 - 79969*z/314928) + t*(652741/944784 - 303403*z/1889568) - 241853*z/1889568 + 520319/944784)*h1 + (25/1944 - 13*z/3888)*h2 + (-84902*t^14/59049 + 721667*t^13/39366 - 10092023*t^12/118098 + 17100503*t^11/118098 + 15583093*t^10/118098 - 93508843*t^9/118098 + 8425319*t^8/13122 + 18216961*t^7/19683 - 26804099*t^6/19683 - 46858583*t^5/118098 + 30622385*t^4/39366 + 17324494*t^3/59049 - 3921757*t^2/59049 - 9550637*t/59049 - 4088938/59049)*hf
  norm_num at hh

private lemma cell_11_24 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (56*z - 40:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7*z/24 - 5/4)*h0 + (-49/3)*hf
  norm_num at hh

private lemma cell_11_25 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (14*z - 10:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7*z/6 - 5)*h0 + (-49/3)*hf
  norm_num at hh

private lemma cell_11_26 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (102*z - 72:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (17*z/54 - 73/54)*h0 + (-289/9)*hf
  norm_num at hh

private lemma cell_11_27 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(12*z - 12) + 44*z - 30:ℝ)=0) (h1 : (16*t^8 + t^7*(272*z - 240) + t^6*(6480*z - 4560) + t^5*(91232*z - 63408) + t^4*(793104*z - 552960) + t^3*(4341872*z - 3027504) + t^2*(14618176*z - 10192128) + t*(27658848*z - 19284336) + 22506336*z - 15691968:ℝ)=0) (h2 : (16*t^8 + t^7*(336*z - 432) + t^6*(7168*z - 4080) + t^5*(106416*z - 76176) + t^4*(885696*z - 615600) + t^3*(4442144*z - 3097776) + t^2*(13048816*z - 9098016) + t*(20659856*z - 14404512) + 13589472*z - 9474912:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(450563*z/10628820 - 3877343/21257640) + t^12*(15616993/7085880 - 907379*z/1771470) + t^11*(7362067*z/3542940 - 31677323/3542940) + t^10*(22244107/2361960 - 5169713*z/2361960) + t^9*(19816657/787320 - 4605563*z/787320) + t^8*(727789*z/52488 - 15657757/262440) + t^7*(489449*z/787320 - 263891/98415) + t^6*(1044043/13122 - 1213867*z/65610) + t^5*(1516981*z/262440 - 6580247/262440) + t^4*(137425*z/17496 - 1508903/43740) + t^3*(36187/2430 - 313*z/81) + t^2*(-215*z/1944 - 6001/2430) + t*(563/405 - 169*z/162) - 8*z/9 + 104/45)*h0 + (t^7*(3877343/170061120 - 450563*z/85030560) + t^6*(358873*z/6298560 - 154415/629856) + t^5*(10363477/11337408 - 12042781*z/56687040) + t^4*(297323*z/944784 - 12793141/9447840) + t^3*(10855541/18895680 - 1261457*z/9447840) + t^2*(37979/629856 - 11033*z/787320) + t*(6511/1049760 - 605*z/419904) - 241*z/14580 + 1037/14580)*h1 + (11/729 - 409*z/116640)*h2 + (4956193*t^14/5314410 + 245739839*t^13/10628820 + 450659918*t^12/2657205 + 54389401*t^11/236196 - 49281810349*t^10/10628820 - 77559886919*t^9/2657205 - 368675617*t^8/196830 + 1381285612171*t^7/3542940 + 345496873231*t^6/590490 - 2252831011703*t^5/1180980 - 1245050067973*t^4/393660 + 229712013973*t^3/65610 + 14054640539*t^2/21870 + 2048907904*t/3645 + 509946581/1215)*hf
  norm_num at hh

private lemma cell_11_28 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(8*z - 10) + 16*z - 10:ℝ)=0) (h1 : (16*t^8 + t^7*(208*z - 368) + t^6*(1648*z + 64) + t^5*(15280*z - 13952) + t^4*(58624*z - 36128) + t^3*(146704*z - 105824) + t^2*(198704*z - 137264) + t*(138640*z - 96848) + 37504*z - 26144:ℝ)=0) (h2 : (16*t^8 + t^7*(144*z - 176) + t^6*(1472*z - 992) + t^5*(10080*z - 6800) + t^4*(43168*z - 30272) + t^3*(115920*z - 81056) + t^2*(190176*z - 132464) + t*(171872*z - 119744) + 64480*z - 44960:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(6253/19683 - 5813*z/78732) + t^12*(93863*z/78732 - 403873/78732) + t^11*(212534/6561 - 197581*z/26244) + t^10*(881659*z/39366 - 1896889/19683) + t^9*(4141943/39366 - 1925993*z/78732) + t^8*(1060579/8748 - 61742*z/2187) + t^7*(626903*z/6561 - 10815529/26244) + t^6*(5943895/26244 - 1399637*z/26244) + t^5*(2448911/8748 - 145651*z/2187) + t^4*(2696731*z/39366 - 6012109/19683) + t^3*(55762*z/19683 - 1960667/78732) + t^2*(3173449/26244 - 201707*z/6561) + t*(498145*z/78732 - 2714459/78732) - 22951*z/19683 + 52253/19683)*h0 + (t^7*(5813*z/629856 - 6253/157464) + t^6*(6913/39366 - 12853*z/314928) + t^5*(781*z/104976 - 3359/104976) + t^4*(84275*z/629856 - 181283/314928) + t^3*(162541/629856 - 4717*z/78732) + t^2*(69095/104976 - 16045*z/104976) + t*(18641*z/629856 - 39923/314928) + 9529*z/157464 - 163853/629856)*h1 + (161/3888 - 37*z/3888)*h2 + (-5813*t^14/4374 - 593509*t^13/39366 - 1344547*t^12/39366 - 639163*t^11/39366 + 10909964*t^10/19683 + 47645824*t^9/19683 - 2748592*t^8/2187 - 899881*t^7/81 - 49139585*t^6/6561 + 176521537*t^5/13122 + 986574541*t^4/39366 + 392968633*t^3/39366 - 320614013*t^2/39366 - 156600020*t/19683 - 32226826/19683)*hf
  norm_num at hh

private lemma cell_11_29 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z - 4) - 2*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(16*z - 176) + t^6*(640 - 64*z) + t^5*(16*z - 848) + t^4*(160*z + 64) + t^3*(496 - 144*z) + t^2*(112 - 256*z) + t*(288*z - 224) - 224*z + 160:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(81343/8748 - 18899*z/8748) + t^6*(47306*z/2187 - 407165/4374) + t^5*(232381/729 - 53999*z/729) + t^4*(798085*z/8748 - 858692/2187) + t^3*(14695*z/4374 - 126067/8748) + t^2*(661649/2916 - 38440*z/729) + t*(126629/4374 - 29575*z/4374) + 2762*z/2187 - 23807/4374)*h0 + (t*(18899*z/69984 - 81343/69984) - 19133*z/69984 + 82243/69984)*h1 + (-18899*t^7/729 + 741781*t^6/4374 - 807965*t^5/2187 + 565058*t^4/2187 + 620857*t^3/4374 - 174740*t^2/729 + 89797*t/729 - 128407/2187)*hf
  norm_num at hh

private lemma cell_11_30 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(12*z - 12) + 44*z - 30:ℝ)=0) (h1 : (16*t^8 + t^7*(336*z - 432) + t^6*(7168*z - 4080) + t^5*(106416*z - 76176) + t^4*(885696*z - 615600) + t^3*(4442144*z - 3097776) + t^2*(13048816*z - 9098016) + t*(20659856*z - 14404512) + 13589472*z - 9474912:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(678311/262440 - 31529*z/52488) + t^6*(80096*z/10935 - 2757083/87480) + t^5*(6250027/43740 - 2905129*z/87480) + t^4*(998047*z/14580 - 4294529/14580) + t^3*(1496413/5832 - 1739443*z/29160) + t^2*(4351*z/405 - 18851/405) + t*(1852*z/405 - 65797/3240) - 397*z/540 + 362/135)*h0 + (t*(31529*z/419904 - 678311/2099520) - 9647*z/77760 + 41509/77760)*h1 + (-157645*t^8/8748 - 4881383*t^7/8748 - 307268383*t^6/43740 - 2303422621*t^5/43740 - 7412596664*t^4/32805 - 55924994023*t^3/131220 + 4399418771*t^2/65610 + 67469495993*t/43740 + 1365626581/810)*hf
  norm_num at hh

private lemma cell_11_31 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(12*z - 12) + 10*z - 6:ℝ)=0) (h1 : (t^8*(1520*z - 1056) + t^7*(14480*z - 10128) + t^6*(58560*z - 40752) + t^5*(131680*z - 91824) + t^4*(177568*z - 123936) + t^3*(141984*z - 98928) + t^2*(61008*z - 42480) + t*(10512*z - 7344):ℝ)=0) : (t + z - 3:ℝ)=0 := by
  have hh : (t + z - 3:ℝ)=0 := by linear_combination (t^6*(241/54 - 28*z/27) + t^5*(331*z/54 - 712/27) + t^4*(353/18 - 41*z/9) + t^3*(482/9 - 112*z/9) + t^2*(365*z/54 - 785/27) + t*(431*z/54 - 1855/54) + 2*z/3 - 17/6)*h0 + (2231*z/5832 - 19199/11664)*h1 + (-422378*t^8/729 - 4037975*t^7/729 - 5456780*t^6/243 - 36708949*t^5/729 - 49387057*t^4/729 - 4397315*t^3/81 - 5711225*t^2/243 - 332839*t/81 - 20/3)*hf
  exact hh

private lemma cell_11_32 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (48*z - 36:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/9 - 17/36)*h0 + (-16/3)*hf
  norm_num at hh

private lemma cell_11_33 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (102*z - 72:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (17*z/54 - 73/54)*h0 + (-289/9)*hf
  norm_num at hh

private lemma cell_11_34 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (20*z - 16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (5*z/36 - 7/12)*h0 + (-25/9)*hf
  norm_num at hh

private lemma cell_11_35 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2 - 10*z) + 58*z - 40:ℝ)=0) (h1 : (16*t^8 + t^7*(208 - 432*z) + t^6*(20384*z - 14096) + t^5*(358384 - 513792*z) + t^4*(7977664*z - 5562512) + t^3*(54571696 - 78270048*z) + t^2*(473847552*z - 330377888) + t*(1128552928 - 1618636624*z) + 2389217344*z - 1665820544:ℝ)=0) : (t - 3*z + 2:ℝ)=0 := by
  have hh : (t - 3*z + 2:ℝ)=0 := by linear_combination (t^6*(211/2916 - 25*z/1458) + t^5*(43*z/486 - 64/243) + t^4*(659/972 - 1051*z/972) + t^3*(56653*z/2916 - 38207/2916) + t^2*(64769/486 - 185759*z/972) + t*(236791*z/243 - 660749/972) - 1474529*z/729 + 2055725/1458)*h0 + (25*z/11664 - 211/23328)*h1 + (550*t^7/729 - 10160*t^6/243 + 175817*t^5/162 - 4092583*t^4/243 + 120082289*t^3/729 - 161156123*t^2/162 + 2473172801*t/729 - 3647629418/729)*hf
  exact hh

private lemma cell_11_36 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (102*z - 72:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (17*z/54 - 73/54)*h0 + (-289/9)*hf
  norm_num at hh

private lemma cell_11_37 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (180*z - 126:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (5*z/9 - 43/18)*h0 + (-100)*hf
  norm_num at hh

private lemma cell_11_38 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (56*z - 40:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7*z/24 - 5/4)*h0 + (-49/3)*hf
  norm_num at hh

private lemma cell_11_39 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(8 - 16*z) + 118*z - 82:ℝ)=0) (h1 : (16*t^8 + t^7*(400 - 624*z) + t^6*(38896*z - 27152) + t^5*(932944 - 1337952*z) + t^4*(28211248*z - 19669568) + t^3*(260218768 - 373221072*z) + t^2*(3025963040*z - 2109775136) + t*(9590594416 - 13755392000*z) + 26866340704*z - 18731867264:ℝ)=0) (h2 : (16*t^8 + t^7*(208 - 560*z) + t^6*(36320*z - 24560) + t^5*(863728 - 1240832*z) + t^4*(26193952*z - 18262064) + t^3*(245134000 - 351585504*z) + t^2*(2931061184*z - 2043607424) + t*(9674887264 - 13876289712*z) + 28562914816*z - 19914760064:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(921035327*z/975725676 - 7926016733/1951451352) + t^12*(47259409075/975725676 - 21966940903*z/1951451352) + t^11*(191235821*z/4015332 - 822844831/4015332) + t^10*(35453571781/114791256 - 2059924571*z/28697814) + t^9*(95836835731/487862838 - 22273202831*z/487862838) + t^8*(80230931*z/334611 - 2761768295/2676888) + t^7*(53385993286/81310473 - 99201359599*z/650483784) + t^6*(49693209866/81310473 - 93408300071*z/650483784) + t^5*(4515086089*z/24091992 - 17292234527/24091992) + t^4*(284964153305/1951451352 - 456524082751*z/1951451352) + t^3*(392866875362*z/243931419 - 929234625319/975725676) + t^2*(16325701456/3011499 - 187841250031*z/24091992) + t*(21752200542533*z/975725676 - 30363334578197/1951451352) - 14249340377659*z/487862838 + 4967634075151/243931419)*h0 + (t^7*(7926016733/15611610816 - 921035327*z/7805805408) + t^6*(10417995995*z/7805805408 - 89652598721/15611610816) + t^5*(41094082013/1734623424 - 9550598377*z/1734623424) + t^4*(141991918*z/14348907 - 19550699623/459165024) + t^3*(433189671865/15611610816 - 50338404001*z/7805805408) + t^2*(5578801915/1734623424 - 1296546467*z/1734623424) + t*(8630021767*z/7805805408 - 74268942067/15611610816) - 148032929*z/3902902704 + 319379147/1951451352)*h1 + (70103/209952 - 32585*z/419904)*h2 + (-28552095137*t^14/487862838 + 834376625279*t^13/162620946 - 51500653600370*t^12/243931419 + 5198670273589523*t^11/975725676 - 21816625488498614*t^10/243931419 + 499566461991076657*t^9/487862838 - 1301673952857744677*t^8/162620946 + 6840383480809746055*t^7/162620946 - 1300249709582165939*t^6/9034497 + 8702460192867615847*t^5/28697814 - 4238853466571515853*t^4/12045996 + 77857086823953222997*t^3/487862838 + 34767650780372957059*t^2/975725676 - 30544899599337394483*t/975725676 + 790086761062398967/243931419)*hf
  norm_num at hh

private lemma cell_11_40 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (20*z - 16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (5*z/36 - 7/12)*h0 + (-25/9)*hf
  norm_num at hh

private lemma cell_11_41 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (56*z - 40:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7*z/24 - 5/4)*h0 + (-49/3)*hf
  norm_num at hh

private lemma cell_11_42 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/6 - 2/3)*h0 + (-1)*hf
  norm_num at hh

private lemma cell_11_43 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t*z + 26*z - 18:ℝ)=0) (h1 : (16*t^8 + t^7*(144 - 304*z) + t^6*(10224*z - 7104) + t^5*(128832 - 184528*z) + t^4*(2070528*z - 1443744) + t^3*(10326048 - 14810416*z) + t^2*(65925040*z - 45964464) + t*(116366832 - 166900080*z) + 183905856*z - 128223648:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(5*z/18 - 1549/1296) + t^6*(3311/648 - 19*z/16) + t^5*(137*z/324 - 131/72) + t^4*(445*z/144 - 479/36) + t^3*(215/24 - 881*z/432) + t^2*(2339/216 - 1879*z/648) + t*(1451*z/432 - 1051/144) - 11*z/4 - 7/24)*h0 + (t*(1549/10368 - 5*z/144) + 763*z/10368 - 3283/10368)*h1 + (-80*t^8/9 + 29405*t^7/81 - 769631*t^6/108 + 27695725*t^5/324 - 72005443*t^4/108 + 1094804099*t^3/324 - 862373779*t^2/81 + 1008071837*t/54 - 40601686/3)*hf
  norm_num at hh

private lemma cell_11_44 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2 - 10*z) + 58*z - 40:ℝ)=0) (h2 : (16*t^8 + t^7*(208 - 432*z) + t^6*(20384*z - 14096) + t^5*(358384 - 513792*z) + t^4*(7977664*z - 5562512) + t^3*(54571696 - 78270048*z) + t^2*(473847552*z - 330377888) + t*(1128552928 - 1618636624*z) + 2389217344*z - 1665820544:ℝ)=0) : (t - 3*z + 2:ℝ)=0 := by
  have hh : (t - 3*z + 2:ℝ)=0 := by linear_combination (t^6*(211/2916 - 25*z/1458) + t^5*(43*z/486 - 64/243) + t^4*(659/972 - 1051*z/972) + t^3*(56653*z/2916 - 38207/2916) + t^2*(64769/486 - 185759*z/972) + t*(236791*z/243 - 660749/972) - 1474529*z/729 + 2055725/1458)*h0 + (25*z/11664 - 211/23328)*h2 + (550*t^7/729 - 10160*t^6/243 + 175817*t^5/162 - 4092583*t^4/243 + 120082289*t^3/729 - 161156123*t^2/162 + 2473172801*t/729 - 3647629418/729)*hf
  exact hh

private lemma cell_11_45 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(8 - 16*z) + 118*z - 82:ℝ)=0) (h1 : (16*t^8 + t^7*(208 - 560*z) + t^6*(36320*z - 24560) + t^5*(863728 - 1240832*z) + t^4*(26193952*z - 18262064) + t^3*(245134000 - 351585504*z) + t^2*(2931061184*z - 2043607424) + t*(9674887264 - 13876289712*z) + 28562914816*z - 19914760064:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(573677/314928 - 133327*z/314928) + t^6*(1517653*z/314928 - 6530219/314928) + t^5*(1509649/17496 - 701581*z/34992) + t^4*(5725423*z/157464 - 3088036/19683) + t^3*(32406433/314928 - 6999977*z/314928) + t^2*(442361/17496 - 788189*z/34992) + t*(35383895*z/314928 - 29436643/314928) - 4937414*z/19683 + 3448129/19683)*h0 + (t*(133327*z/2519424 - 573677/2519424) - 103865*z/1259712 + 893825/2519424)*h1 + (133327*t^8/5832 - 96638441*t^7/52488 + 10671267245*t^6/157464 - 233918295575*t^5/157464 + 817271946017*t^4/39366 - 28988671952533*t^3/157464 + 12807107519669*t^2/13122 - 139391102495153*t/52488 + 46355069292412/19683)*hf
  norm_num at hh

private lemma cell_11_46 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t*z + 26*z - 18:ℝ)=0) (h1 : (16*t^8 + t^7*(-240*z - 48) + t^6*(8608*z - 4896) + t^5*(103104 - 151776*z) + t^4*(1641216*z - 1141056) + t^3*(7939392 - 11389504*z) + t^2*(49697152*z - 34649808) + t*(86925552 - 124673680*z) + 137608128*z - 95943744:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(4793*z/14904 - 20623/14904) + t^6*(34142/1863 - 31741*z/7452) + t^5*(13306*z/621 - 228953/2484) + t^4*(91369/414 - 21269*z/414) + t^3*(16549*z/276 - 5859/23) + t^2*(104663/828 - 3089*z/92) + t*(32027*z/1656 - 15043/552) - 1381*z/69 + 1621/138)*h0 + (t*(20623/119232 - 4793*z/119232) + 8999*z/119232 - 38719/119232)*h1 + (-4793*t^8/621 + 205072*t^7/621 - 898603*t^6/138 + 10565977*t^5/138 - 2161157443*t^4/3726 + 5320042150*t^3/1863 - 32645865515*t^2/3726 + 27834686423*t/1863 - 2149780379/207)*hf
  norm_num at hh

private lemma cell_11_47 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(12 - 24*z) + 70*z - 48:ℝ)=0) (h1 : (t^8*(1520*z - 1056) + t^7*(54384 - 78064*z) + t^6*(1755168*z - 1223568) + t^5*(15737520 - 22572080*z) + t^4*(181620640*z - 126630240) + t^3*(652790160 - 936269664*z) + t^2*(3019710912*z - 2105416080) + t*(3884090832 - 5570790480*z) + 4500264096*z - 3137693760:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(1525/2484 - 59*z/414) + t^6*(4045*z/2484 - 5831/828) + t^5*(17032/621 - 7703*z/1242) + t^4*(17789*z/2484 - 8155/207) + t^3*(36559*z/2484 - 4459/1242) + t^2*(60013/828 - 15499*z/207) + t*(14933*z/92 - 16337/138) - 22013*z/138 + 7532/69)*h0 + (t*(1765*z/33534 - 121511/536544) - 45245*z/268272 + 389363/536544)*h1 + (-1336621*t^9/16767 + 16239511*t^8/3726 - 1768655579*t^7/16767 + 1081673888*t^6/729 - 149400104779*t^5/11178 + 2679694245247*t^4/33534 - 1770847595444*t^3/5589 + 4485185802457*t^2/5589 - 190578634943*t/162 + 157112225735/207)*hf
  norm_num at hh

private lemma cell_11_48 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(2*z - 6):ℝ)=0) (h1 : (t^8*(1520*z - 1056) + t^7*(14480*z - 10128) + t^6*(58560*z - 40752) + t^5*(131680*z - 91824) + t^4*(177568*z - 123936) + t^3*(141984*z - 98928) + t^2*(61008*z - 42480) + t*(10512*z - 7344):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(1/27 - 5*z/108) + t^5*(7/27 - 11*z/27) + t^4*(41/36 - 29*z/18) + t^3*(29/12 - 41*z/12) + t^2*(311/108 - 227*z/54) + t*(209/108 - 313*z/108) - 31*z/36 + 7/18)*h0 + (13*z/23328 - 25/11664)*h1 + (-550*t^8/729 - 5221*t^7/729 - 6949*t^6/243 - 92329*t^5/1458 - 122053*t^4/1458 - 10517*t^3/162 - 12869*t^2/486 - 335*t/81)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_11_49 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(12*z - 12) + 10*z - 6:ℝ)=0) (h1 : (t^8*(1520*z - 1056) + t^7*(40656*z - 28368) + t^6*(474624*z - 330912) + t^5*(3162656*z - 2204976) + t^4*(13153856*z - 9171264) + t^3*(34954544*z - 24371328) + t^2*(57926224*z - 40387488) + t*(54693024*z - 38133216) + 22506336*z - 15691968:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(7*z/351 + 43/702) + t^6*(739*z/702 - 127/117) + t^5*(173*z/18 - 185/27) + t^4*(18496*z/351 - 4099/117) + t^3*(124223*z/702 - 86743/702) + t^2*(123893*z/351 - 58219/234) + t*(136226*z/351 - 94969/351) + 42583*z/234 - 14713/117)*h0 + (t*(289*z/37908 - 5009/151632) - 457*z/37908 + 1955/37908)*h1 + (-110198*t^9/9477 - 2785957*t^8/9477 - 9983471*t^7/3159 - 176467667*t^6/9477 - 22195934*t^5/351 - 351482008*t^4/3159 - 255880673*t^3/9477 + 2585462551*t^2/9477 + 1521706286*t/3159 + 10510711/39)*hf
  norm_num at hh

private lemma cell_11_50 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z - 6*t*z + 6*z - 4:ℝ)=0) (h1 : (t^8*(1520*z - 1056) + t^7*(3888 - 5616*z) + t^6*(3984*z - 2736) + t^5*(5744*z - 3936) + t^4*(4848 - 7168*z) + t^3*(-16*z - 48) + t^2*(2656*z - 1728) + t*(672 - 912*z) - 512*z + 352:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(1547*z/18792 - 2215/6264) + t^6*(8071/3132 - 1427*z/2349) + t^5*(4187*z/4698 - 23869/6264) + t^4*(14633*z/9396 - 41519/6264) + t^3*(3589/261 - 4999*z/1566) + t^2*(38393/6264 - 13307*z/9396) + t*(1855*z/696 - 3967/348) + 82*z/87 - 4181/1044)*h0 + (t*(6533/50112 - 4555*z/150336) + 13517*z/150336 - 2423/6264)*h1 + (71863*t^9/1566 - 955621*t^8/3132 + 5823025*t^7/9396 - 837631*t^6/4698 - 6795701*t^5/9396 + 5809913*t^4/9396 + 22769*t^3/261 - 572768*t^2/2349 + 263795*t/4698 + 94852/2349)*hf
  norm_num at hh

private lemma cell_11_51 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(4*z - 10) + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(144*z - 176) + t^6*(1472*z - 992) + t^5*(10080*z - 6800) + t^4*(43168*z - 30272) + t^3*(115920*z - 81056) + t^2*(190176*z - 132464) + t*(171872*z - 119744) + 64480*z - 44960:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(575881/5231304 - 66187*z/2615652) + t^6*(24499*z/201204 - 199015/402408) + t^5*(110143*z/1743768 + 6848/217971) + t^4*(557755*z/5231304 + 3317021/2615652) + t^3*(9334733*z/5231304 - 9674203/5231304) + t^2*(6294095*z/1743768 - 7075567/1743768) + t*(182459*z/56862 - 55619/28431) + 2939065*z/2615652 - 148136/653913)*h0 + (t*(66187*z/20925216 - 575881/41850432) - 444653*z/41850432 + 1911763/41850432)*h1 + (-463309*t^8/1307826 - 9450479*t^7/2615652 - 21574201*t^6/1307826 - 19532293*t^5/653913 + 110977349*t^4/1307826 + 536783017*t^3/871884 + 638268599*t^2/435942 + 2115619523*t/1307826 + 68921215/100602)*hf
  norm_num at hh

private lemma cell_11_52 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(12*z - 12) + 10*z - 6:ℝ)=0) (h1 : (t^8*(1520*z - 1056) + t^7*(40656*z - 28368) + t^6*(466688*z - 325344) + t^5*(3003824*z - 2094384) + t^4*(11844992*z - 8258592) + t^3*(29284016*z - 20417520) + t^2*(44304240*z - 30890016) + t*(37493504*z - 26141376) + 13589472*z - 9474912:ℝ)=0) (h2 : (t^8*(1520*z - 1056) + t^7*(40656*z - 28368) + t^6*(474624*z - 330912) + t^5*(3162656*z - 2204976) + t^4*(13153856*z - 9171264) + t^3*(34954544*z - 24371328) + t^2*(57926224*z - 40387488) + t*(54693024*z - 38133216) + 22506336*z - 15691968:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(z/243 - 5/972) + t^12*(149*z/972 - 85/972) + t^11*(3241*z/972 - 2303/972) + t^10*(4573*z/108 - 3191/108) + t^9*(356173*z/972 - 124075/486) + t^8*(553073*z/243 - 385654/243) + t^7*(5070887*z/486 - 3535597/486) + t^6*(1287275*z/36 - 224378/9) + t^5*(89064823*z/972 - 62098115/972) + t^4*(168601259*z/972 - 58776227/486) + t^3*(114632483*z/486 - 39962486/243) + t^2*(11787367*z/54 - 16437055/108) + t*(19974851*z/162 - 13926835/162) + 867515*z/27 - 604822/27)*h0 + (t^7*(211/209952 - 25*z/104976) + t^6*(119*z/104976 - 1121/209952) + t^5*(85/69984 - 95*z/69984) + t^4*(2297/69984 - 119*z/8748) + t^3*(1067/209952 - 4423*z/209952) + t^2*(-7579*z/209952 - 3169/209952) + t*(1043/23328 - 1261*z/23328) - 2155*z/69984 + 773/17496)*h1 + (161/3888 - 37*z/3888)*h2 + (2321*t^15/6561 + 99769*t^14/13122 + 384266*t^13/6561 + 1784075*t^12/13122 - 8397761*t^11/13122 - 29450770*t^10/6561 - 26977861*t^9/4374 + 295119617*t^8/13122 + 573246385*t^7/6561 + 392839157*t^6/6561 - 1231680173*t^5/6561 - 4653835423*t^4/13122 + 290629015*t^3/6561 + 3088303903*t^2/4374 + 1729952650*t/2187 + 226963991/729)*hf
  norm_num at hh

private lemma cell_11_53 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(22*z - 18) + 44*z - 30:ℝ)=0) (h1 : (t^8*(1520*z - 1056) + t^7*(66832*z - 46608) + t^6*(1280960*z - 893136) + t^5*(13990848*z - 9754704) + t^4*(95238016*z - 66402240) + t^3*(413725120*z - 288459312) + t^2*(1119992464*z - 780886032) + t*(1727248528*z - 1204279728) + 1161687456*z - 809956800:ℝ)=0) : (t + 2*z - 3:ℝ)=0 := by
  have hh : (t + 2*z - 3:ℝ)=0 := by linear_combination (t^6*(157/54 - 73*z/108) + t^5*(37*z/54 - 161/54) + t^4*(5*z - 22) + t^3*(113/36 - 29*z/18) + t^2*(2039/54 - 1367*z/108) + t*(1249/108 - 320*z/27) - 155*z/18 - 19/9)*h0 + (5813*z/23328 - 6253/5832)*h1 + (-275132*t^8/729 - 12130609*t^7/729 - 232690988*t^6/729 - 847208267*t^5/243 - 34601393861*t^4/1458 - 150310963745*t^3/1458 - 406906044809*t^2/1458 - 627529944299*t/1458 - 23447501191/81)*hf
  exact hh

private lemma cell_11_54 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(4*z - 6) - 2*z + 2:ℝ)=0) (h1 : (t^8*(1520*z - 1056) + t^7*(20560*z - 14352) + t^6*(106448*z - 74208) + t^5*(258000*z - 179856) + t^4*(277264*z - 193344) + t^3*(85648*z - 59712) + t^2*(7056 - 10112*z) + t*(3024 - 4352*z) - 224*z + 160:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(20521/22678 - 14345*z/68034) + t^6*(30272*z/34017 - 175357/45356) + t^5*(73251/45356 - 9733*z/22678) + t^4*(160605/22678 - 20543*z/11339) + t^3*(64535*z/68034 - 117519/22678) + t^2*(-155*z/986 - 195/1972) + t*(2963/2346 - 565*z/1564) + 104723*z/204102 - 481825/204102)*h0 + (t*(42193*z/544272 - 60515/181424) - 131107*z/816408 + 2256539/3265632)*h1 + (-1331330*t^9/11339 - 8108191*t^8/6003 - 505503799*t^7/102051 - 295850033*t^6/102051 + 678390535*t^5/34017 + 3865604120*t^4/102051 + 129040085*t^3/8874 - 14586567*t^2/11339 - 139666561*t/204102 - 3566273/102051)*hf
  norm_num at hh

private lemma cell_11_55 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(8*z - 10) + 16*z - 10:ℝ)=0) (h1 : (16*t^8 + t^7*(272*z - 176) + t^6*(7488*z - 5312) + t^5*(114896*z - 80144) + t^4*(1100576*z - 767168) + t^3*(6717936*z - 4683920) + t^2*(25501568*z - 17780432) + t*(55007904*z - 38352800) + 51578272*z - 35961632:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(53705/13122 - 12481*z/13122) + t^6*(123743/26244 - 7177*z/6561) + t^5*(45049*z/8748 - 96091/4374) + t^4*(113413*z/26244 - 425867/26244) + t^3*(498505/13122 - 123823*z/26244) + t^2*(85921*z/4374 - 49711/8748) + t*(394369*z/6561 - 849991/13122) + 723091*z/13122 - 226870/6561)*h0 + (t*(12481*z/104976 - 53705/104976) - 5965*z/26244 + 205315/209952)*h1 + (-162253*t^8/6561 - 1759408*t^7/2187 - 78615043*t^6/6561 - 687946820*t^5/6561 - 399931333*t^4/729 - 9875230588*t^3/6561 - 542845210*t^2/729 + 4643006530*t/729 + 76910313392/6561)*hf
  norm_num at hh

private lemma cell_11_56 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z - 6*t*z + 6*z - 4:ℝ)=0) (h1 : (t^8*(1520*z - 1056) + t^7*(3888 - 5616*z) + t^6*(10064*z - 6960) + t^5*(7728 - 11104*z) + t^4*(6176*z - 4368) + t^3*(528 - 688*z) + t^2*(1104 - 1584*z) + t*(944*z - 672) - 224*z + 160:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(875/2484 - 655*z/7452) + t^6*(1126*z/1863 - 6287/2484) + t^5*(6353/1242 - 9011*z/7452) + t^4*(502*z/1863 - 1327/1242) + t^3*(9949*z/7452 - 7117/1242) + t^2*(10315/2484 - 1784*z/1863) + t*(257/2484 - 67*z/7452) + 407*z/1242 - 283/207)*h0 + (t*(1775*z/59616 - 2545/19872) - 5231*z/59616 + 7501/19872)*h1 + (-27995*t^9/621 + 371167*t^8/1242 - 1464034*t^7/1863 + 2239798*t^6/1863 - 2146178*t^5/1863 + 1063225*t^4/1863 - 50198*t^3/1863 - 603829*t^2/3726 + 170503*t/1863 - 40280/1863)*hf
  norm_num at hh

private lemma cell_11_57 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(4*z - 6) - 2*z + 2:ℝ)=0) (h1 : (t^8*(1520*z - 1056) + t^7*(20560*z - 14352) + t^6*(120464*z - 84000) + t^5*(399984*z - 278784) + t^4*(821296*z - 572640) + t^3*(1061488*z - 740256) + t^2*(835264*z - 582336) + t*(360928*z - 251568) + 64480*z - 44960:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(247*z/2784 + 85/928) + t^6*(593*z/348 - 817/464) + t^5*(7333*z/928 - 5781/928) + t^4*(18795*z/928 - 5151/464) + t^3*(47101*z/1392 - 5259/232) + t^2*(31079*z/928 - 26253/928) + t*(22523*z/1392 - 33139/2784) + 10777*z/4176 + 1147/4176)*h0 + (t*(115*z/7424 - 1501/22272) - 1589*z/66816 + 6859/66816)*h1 + (-16511*t^9/696 - 597367*t^8/2088 - 100765*t^7/72 - 14197301*t^6/4176 - 4653031*t^5/1392 + 6112093*t^4/2088 + 50975933*t^3/4176 + 19864169*t^2/1392 + 15882821*t/2088 + 803153/522)*hf
  norm_num at hh

private lemma cell_11_58 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(6 - 14*z) + 26*z - 18:ℝ)=0) (h1 : (t^8*(1520*z - 1056) + t^7*(17904 - 25712*z) + t^6*(190112*z - 132528) + t^5*(559728 - 802704*z) + t^4*(2115328*z - 1474944) + t^3*(2479728 - 3556640*z) + t^2*(3715552*z - 2590512) + t*(1530768 - 2195504*z) + 558048*z - 389088:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(677*z/7047 - 5837/14094) + t^6*(1969/783 - 913*z/1566) + t^5*(136*z/243 - 1177/486) + t^4*(7657*z/4698 - 16507/2349) + t^3*(64733/7047 - 29663*z/14094) + t^2*(26447/4698 - 6421*z/4698) + t*(418*z/261 - 1739/261) + 155*z/522 - 350/261)*h0 + (t*(465151/3044304 - 13513*z/380538) + 289523*z/3044304 - 622871/1522152)*h1 + (10233322*t^9/190269 - 200750048*t^8/190269 + 1747513946*t^7/190269 - 8859827080*t^6/190269 + 28819666751*t^5/190269 - 6924538219*t^4/21141 + 9940928480*t^3/21141 - 27352206152*t^2/63423 + 43491376042*t/190269 - 3366484043/63423)*hf
  norm_num at hh

private lemma cell_11_59 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t + 2*z:ℝ)=0) (h1 : (16*t^8 + t^7*(16*z - 48) + t^6*(32*z - 96) + t^5*(192 - 32*z) + t^4*(192 - 128*z) + t^3*(-64*z - 192) + t^2*(48 - 128*z) + t*(240 - 208*z):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(30649/145962 - 3565*z/72981) + t^6*(7318*z/72981 - 63097/145962) + t^5*(6079*z/24327 - 52415/48654) + t^4*(10603/5406 - 7405*z/16218) + t^3*(29879/16218 - 10394*z/24327) + t^2*(1694*z/2703 - 21617/8109) + t*(15173*z/48654 - 20455/16218) - z/6 + 5/6)*h0 + (t*(3565*z/583848 - 30649/1167696) - 19637*z/1167696 + 84487/1167696)*h1 + (-7130*t^8/72981 + 4169*t^7/24327 + 4322*t^6/8109 - 6236*t^5/24327 - 3643*t^4/4293 + 40856*t^3/72981 - 155882*t^2/72981 - 300800*t/72981 + 1/3)*hf
  norm_num at hh

private lemma cell_11_60 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(4*z - 10) + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(208*z - 368) + t^6*(1648*z + 64) + t^5*(15280*z - 13952) + t^4*(58624*z - 36128) + t^3*(146704*z - 105824) + t^2*(198704*z - 137264) + t*(138640*z - 96848) + 37504*z - 26144:ℝ)=0) (h2 : (16*t^8 + t^7*(144*z - 176) + t^6*(1472*z - 992) + t^5*(10080*z - 6800) + t^4*(43168*z - 30272) + t^3*(115920*z - 81056) + t^2*(190176*z - 132464) + t*(171872*z - 119744) + 64480*z - 44960:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(533*z/78732 - 2293/78732) + t^12*(33823/78732 - 1964*z/19683) + t^11*(14977*z/26244 - 64277/26244) + t^10*(125947/19683 - 57697*z/39366) + t^9*(116981*z/78732 - 432001/78732) + t^8*(36101*z/8748 - 50147/4374) + t^7*(78175*z/26244 + 249305/13122) + t^6*(231248*z/6561 - 867745/26244) + t^5*(826411*z/8748 - 353653/4374) + t^4*(3468355*z/19683 - 2128349/19683) + t^3*(19990751*z/78732 - 3459709/19683) + t^2*(6344747*z/26244 - 1151827/6561) + t*(5311165*z/39366 - 7241617/78732) + 1351421*z/39366 - 922375/39366)*h0 + (t^7*(2293/629856 - 533*z/629856) + t^6*(1177*z/314928 - 5069/314928) + t^5*(311/104976 - 19*z/26244) + t^4*(33343/629856 - 7877*z/629856) + t^3*(2945*z/629856 - 7271/314928) + t^2*(325*z/26244 - 6215/104976) + t*(8077/629856 - 2795*z/629856) - 3949*z/629856 + 7669/314928)*h1 + (161/3888 - 37*z/3888)*h2 + (5863*t^14/39366 + 40009*t^13/39366 + 20291*t^12/4374 + 28333*t^11/13122 - 2763415*t^10/39366 - 6825733*t^9/39366 + 1459307*t^8/13122 + 3926995*t^7/4374 + 4904674*t^6/6561 - 48727531*t^5/39366 - 43818068*t^4/19683 + 33101*t^3/729 + 17496355*t^2/6561 + 99751429*t/39366 + 16706138/19683)*hf
  norm_num at hh

private lemma cell_11_61 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(8*z - 10) + 16*z - 10:ℝ)=0) (h1 : (16*t^8 + t^7*(336*z - 368) + t^6*(8560*z - 5600) + t^5*(141072*z - 98672) + t^4*(1409056*z - 982592) + t^3*(8851056*z - 6170912) + t^2*(34121840*z - 23790560) + t*(73802800*z - 51457136) + 68578720*z - 47814752:ℝ)=0) (h2 : (16*t^8 + t^7*(272*z - 176) + t^6*(7488*z - 5312) + t^5*(114896*z - 80144) + t^4*(1100576*z - 767168) + t^3*(6717936*z - 4683920) + t^2*(25501568*z - 17780432) + t*(55007904*z - 38352800) + 51578272*z - 35961632:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(6253*z/118098 - 107621/472392) + t^12*(364409/472392 - 84691*z/472392) + t^11*(306995/157464 - 35669*z/78732) + t^10*(690167*z/472392 - 1482839/236196) + t^9*(588925*z/472392 - 2452823/472392) + t^8*(878041/52488 - 86611*z/26244) + t^7*(269369*z/39366 - 158033/78732) + t^6*(10423801*z/157464 - 1228330/19683) + t^5*(4870049*z/13122 - 6535511/26244) + t^4*(794585867*z/472392 - 569261695/472392) + t^3*(2539927111*z/472392 - 221126881/59049) + t^2*(462606139*z/39366 - 641911561/78732) + t*(3707280659*z/236196 - 2582135971/236196) + 570434029*z/59049 - 795476407/118098)*h0 + (t^7*(107621/3779136 - 6253*z/944784) + t^6*(297157/3779136 - 34531*z/1889568) + t^5*(3581*z/1259712 - 7709/629856) + t^4*(38119*z/1889568 - 164201/1889568) + t^3*(293561/1889568 - 68545*z/1889568) + t^2*(348463/1259712 - 81935*z/1259712) + t*(602911/1889568 - 71815*z/944784) - 155093*z/944784 + 1318841/1889568)*h1 + (37/23328 - z/2916)*h2 + (106301*t^14/59049 + 2495065*t^13/39366 + 258786955*t^12/236196 + 2803229387*t^11/236196 + 19777920877*t^10/236196 + 90007189385*t^9/236196 + 41890630091*t^8/39366 + 10414927945*t^7/6561 + 20363226517*t^6/26244 + 56825911225*t^5/236196 + 114100677317*t^4/26244 + 2635228456883*t^3/236196 + 1814805431261*t^2/118098 + 1004926217513*t/59049 + 656672479354/59049)*hf
  norm_num at hh

private lemma cell_11_62 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t + 2*z:ℝ)=0) (h1 : (16*t^8 + t^7*(80*z - 240) + t^6*(960 - 240*z) + t^5*(80*z - 1632) + t^4*(1728 - 480*z) + t^3*(1424*z - 1344) + t^2*(208*z - 240) + t*(1008 - 1392*z):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(2102/1053 - 977*z/2106) + t^6*(5470*z/1053 - 47071/2106) + t^5*(829/9 - 578*z/27) + t^4*(9247*z/234 - 19895/117) + t^3*(29729/234 - 3455*z/117) + t^2*(857*z/351 - 817/78) + t*(392*z/117 - 1117/78) - z/6 + 5/6)*h0 + (t*(977*z/16848 - 1051/4212) - 2621*z/16848 + 5639/8424)*h1 + (-4885*t^8/1053 + 3193*t^7/117 - 18380*t^6/351 + 87499*t^5/1053 - 248806*t^4/1053 + 282758*t^3/1053 + 113930*t^2/1053 - 78361*t/351 + 1/3)*hf
  norm_num at hh

private lemma cell_11_63 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t*(2*z - 6) + 2*z:ℝ)=0) (h1 : (t*(39264*z - 27360) + 558048*z - 389088:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (17/6 - 2*z/3)*h0 + (19199/23328 - 2231*z/11664)*h1 + (1825282*t/243 + 25937930/243)*hf
  norm_num at hh

private lemma pair_11_21_31 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + 4*z - 3:ℝ)=0) (h1 : (t + z - 3:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (5/9 - z/9)*h0 + (z/9 - 5/9)*h1 + (1/3)*hf
  norm_num at hh

private lemma pair_11_21_35 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + 4*z - 3:ℝ)=0) (h1 : (t - 3*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7*z/3 - 10)*h0 + (10 - 7*z/3)*h1 + (-49/3)*hf
  norm_num at hh

private lemma pair_11_21_44 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + 4*z - 3:ℝ)=0) (h1 : (t - 3*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7*z/3 - 10)*h0 + (10 - 7*z/3)*h1 + (-49/3)*hf
  norm_num at hh

private lemma pair_11_21_53 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + 4*z - 3:ℝ)=0) (h1 : (t + 2*z - 3:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (5/6 - z/6)*h0 + (z/6 - 5/6)*h1 + (1/3)*hf
  norm_num at hh

private lemma pair_11_31_35 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + z - 3:ℝ)=0) (h1 : (t - 3*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (4*z/27 - 5/9)*h0 + (5/9 - 4*z/27)*h1 + (-16/27)*hf
  norm_num at hh

private lemma pair_11_31_44 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + z - 3:ℝ)=0) (h1 : (t - 3*z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (4*z/27 - 5/9)*h0 + (5/9 - 4*z/27)*h1 + (-16/27)*hf
  norm_num at hh

private lemma pair_11_31_53 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + z - 3:ℝ)=0) (h1 : (t + 2*z - 3:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/3 - 5/3)*h0 + (5/3 - z/3)*h1 + (1/3)*hf
  norm_num at hh

private lemma pair_11_35_44 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 3*z + 2:ℝ)=0) (h2 : (t^8*(2272 - 528*z) + t^7*(4592*z - 19760) + t^6*(69952 - 16256*z) + t^5*(30160*z - 129776) + t^4*(135712 - 31552*z) + t^3*(18832*z - 80720) + t^2*(26560 - 6256*z) + t*(832*z - 4256) - 32*z + 256:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(5971633*z/435942 - 25694597/435942) + t^6*(110558086/217971 - 25694597*z/217971) + t^5*(29858165*z/72657 - 128472985/72657) + t^4*(1396995631/435942 - 162336565*z/217971) + t^3*(326907065*z/435942 - 703303892/217971) + t^2*(130540978/72657 - 60677593*z/145314) + t*(26468939*z/217971 - 113891740/217971) - 3343904*z/217971 + 14368087/217971)*h0 + (6748/217971 - 50185*z/6975072)*h2 + (-552035*t^8/145314 + 16158997*t^7/217971 - 102577771*t^6/217971 + 632045695*t^5/435942 - 536492105*t^4/217971 + 519894470*t^3/217971 - 282860336*t^2/217971 + 80711627*t/217971 - 10081897/217971)*hf
  norm_num at hh

private lemma pair_11_35_53 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 3*z + 2:ℝ)=0) (h1 : (t + 2*z - 3:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (4/5 - z/5)*h0 + (z/5 - 4/5)*h1 + (-1)*hf
  norm_num at hh

private lemma pair_11_44_53 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 3*z + 2:ℝ)=0) (h1 : (t + 2*z - 3:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (4/5 - z/5)*h0 + (z/5 - 4/5)*h1 + (-1)*hf
  norm_num at hh

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_0 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 0) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_0 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_1 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 1) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_1 z t hf hn0 hn1 hn2 hn3
  · have hr : (6*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-6)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_2 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 2) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_2 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_3 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 3) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_3 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 + 64*t^7*z - 128*t^7 + 48*t^6*z^4 - 96*t^6*z^3 + 448*t^6*z^2 - 640*t^6*z + 448*t^6 - 16*t^5*z^6 - 352*t^5*z^4 + 1120*t^5*z^3 - 2320*t^5*z^2 + 2496*t^5*z - 896*t^5 + 32*t^4*z^7 + 48*t^4*z^6 - 176*t^4*z^5 + 1520*t^4*z^4 - 5120*t^4*z^3 + 7328*t^4*z^2 - 5120*t^4*z + 1120*t^4 - 16*t^3*z^8 - 176*t^3*z^7 + 32*t^3*z^6 + 1984*t^3*z^5 - 6592*t^3*z^4 + 13248*t^3*z^3 - 13392*t^3*z^2 + 6080*t^3*z - 896*t^3 - 32*t^2*z^9 + 496*t^2*z^8 - 1264*t^2*z^7 + 1632*t^2*z^6 - 5664*t^2*z^5 + 14736*t^2*z^4 - 19808*t^2*z^3 + 13696*t^2*z^2 - 4224*t^2*z + 448*t^2 + 32*t*z^10 - 288*t*z^9 + 144*t*z^8 + 2544*t*z^7 - 6544*t*z^6 + 10688*t*z^5 - 16352*t*z^4 + 15328*t*z^3 - 7280*t*z^2 + 1600*t*z - 128*t - 96*z^10 + 1152*z^9 - 4592*z^8 + 7568*z^7 - 3856*z^6 - 3760*z^5 + 6992*z^4 - 4672*z^3 + 1568*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 - 144*t^6*z - 1024*t^6 + 16*t^5*z^4 + 80*t^5*z^3 + 704*t^5*z^2 + 2160*t^5*z + 11008*t^5 - 32*t^4*z^5 - 208*t^4*z^4 - 768*t^4*z^3 - 4736*t^4*z^2 - 16256*t^4*z - 74400*t^4 + 16*t^3*z^6 + 256*t^3*z^5 + 1200*t^3*z^4 + 3248*t^3*z^3 + 19232*t^3*z^2 + 73168*t^3*z + 321536*t^3 + 32*t^2*z^7 - 336*t^2*z^6 - 512*t^2*z^5 - 3184*t^2*z^4 - 8720*t^2*z^3 - 48784*t^2*z^2 - 197952*t^2*z - 857104*t^2 - 32*t*z^8 + 128*t*z^7 + 592*t*z^6 + 32*t*z^5 + 4928*t*z^4 + 13856*t*z^3 + 70848*t*z^2 + 297344*t*z + 1281456*t + 96*z^8 - 672*z^7 + 944*z^6 - 832*z^5 - 3136*z^4 - 9424*z^3 - 44704*z^2 - 190576*z - 820336)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_4 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 4) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_4 z t hf hn0 hn1 hn2 hn3
  · have hr : (6*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-6)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_5 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 5) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_5 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 + 6*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_6 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 6) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_6 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*z^3 + 12*z^2 - 12*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z - 2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_7 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 7) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_7 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 + 2*t*z - 4*t + 8*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 8)*hf
  · have hr : (16*t^8 - 112*t^7*z^2 + 192*t^7*z - 128*t^7 + 288*t^6*z^4 - 960*t^6*z^3 + 1856*t^6*z^2 - 1536*t^6*z + 448*t^6 - 320*t^5*z^6 + 1536*t^5*z^5 - 5632*t^5*z^4 + 10560*t^5*z^3 - 10576*t^5*z^2 + 5184*t^5*z - 896*t^5 + 128*t^4*z^8 - 768*t^4*z^7 + 5872*t^4*z^6 - 19568*t^4*z^5 + 39184*t^4*z^4 - 45952*t^4*z^3 + 29728*t^4*z^2 - 9600*t^4*z + 1120*t^4 - 2000*t^3*z^8 + 11024*t^3*z^7 - 42544*t^3*z^6 + 96640*t^3*z^5 - 128960*t^3*z^4 + 102528*t^3*z^3 - 46352*t^3*z^2 + 10560*t^3*z - 896*t^3 - 32*t^2*z^10 + 352*t^2*z^9 + 10288*t^2*z^8 - 55376*t^2*z^7 + 146048*t^2*z^6 - 228512*t^2*z^5 + 216832*t^2*z^4 - 124096*t^2*z^3 + 40960*t^2*z^2 - 6912*t^2*z + 448*t^2 + 304*t*z^10 - 3376*t*z^9 - 16464*t*z^8 + 105520*t*z^7 - 224496*t*z^6 + 259200*t*z^5 - 181184*t*z^4 + 77376*t*z^3 - 19248*t*z^2 + 2496*t*z - 128*t - 672*z^10 + 7264*z^9 + 432*z^8 - 55536*z^7 + 114416*z^6 - 109296*z^5 + 59472*z^4 - 19456*z^3 + 3744*z^2 - 384*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(112*t^7 - 288*t^6*z^2 - 480*t^6*z - 3392*t^6 + 320*t^5*z^4 + 64*t^5*z^3 + 4992*t^5*z^2 + 14208*t^5*z + 66640*t^5 - 128*t^4*z^6 + 128*t^4*z^5 - 4848*t^4*z^4 - 5056*t^4*z^3 - 49920*t^4*z^2 - 188480*t^4*z - 822368*t^4 + 2000*t^3*z^6 - 1024*t^3*z^5 + 31424*t^3*z^4 + 63552*t^3*z^3 + 352448*t^3*z^2 + 1469056*t^3*z + 6334288*t^3 + 32*t^2*z^8 - 192*t^2*z^7 - 11344*t^2*z^6 - 768*t^2*z^5 - 115856*t^2*z^4 - 348464*t^2*z^3 - 1611584*t^2*z^2 - 6888432*t^2*z - 29648368*t^2 - 304*t*z^8 + 1856*t*z^7 + 26656*t*z^6 + 22192*t*z^5 + 255488*t*z^4 + 951664*t*z^3 + 4173040*t*z^2 + 17932832*t*z + 77164288*t + 672*z^8 - 3904*z^7 - 21968*z^6 - 42592*z^5 - 261472*z^4 - 1070288*z^3 - 4626496*z^2 - 19902160*z - 85635056)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_8 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 8) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_8 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_9 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 9) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_9 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*z^3 + 12*z^2 - 12*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z - 2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_10 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 10) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_10 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 6*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_11 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 11) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_11 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 8*t*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 128*t^7*z - 48*t^6*z^3 + 320*t^6*z^2 - 64*t^6*z + 80*t^5*z^4 - 560*t^5*z^3 + 512*t^5*z^2 - 16*t^4*z^6 + 64*t^4*z^5 + 224*t^4*z^4 - 608*t^4*z^3 - 32*t^4*z^2 - 16*t^3*z^8 + 240*t^3*z^7 - 1200*t^3*z^6 + 2160*t^3*z^5 - 784*t^3*z^4 - 128*t^3*z^3 + 16*t^2*z^9 - 240*t^2*z^8 + 1264*t^2*z^7 - 2704*t^2*z^6 + 2000*t^2*z^5 - 512*t^2*z^4 + 192*t^2*z^3 - 16*t*z^10 + 272*t*z^9 - 1760*t*z^8 + 5360*t*z^7 - 7616*t*z^6 + 4272*t*z^5 - 768*t*z^4 - 16*z^9 + 192*z^8 - 816*z^7 + 1424*z^6 - 864*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 48*t^6*z - 80*t^6 - 80*t^5*z^2 + 160*t^5*z + 528*t^5 + 16*t^4*z^4 + 16*t^4*z^3 - 192*t^4*z^2 - 400*t^4*z - 1392*t^4 + 16*t^3*z^6 - 160*t^3*z^5 + 352*t^3*z^4 + 80*t^3*z^3 + 128*t^3*z^2 + 528*t^3*z + 2256*t^3 - 16*t^2*z^7 + 160*t^2*z^6 - 416*t^2*z^5 + 144*t^2*z^4 - 32*t^2*z^3 - 80*t^2*z^2 - 496*t^2*z - 2240*t^2 + 16*t*z^8 - 192*t*z^7 + 752*t*z^6 - 1024*t*z^5 + 240*t*z^4 + 48*t*z^2 + 240*t*z + 1056*t + 16*z^7 - 112*z^6 + 208*z^5 - 48*z^4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_12 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 12) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_12 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 192*t^7*z - 128*t^7 - 96*t^6*z^3 + 768*t^6*z^2 + 1152*t^6*z + 448*t^6 + 272*t^5*z^4 - 1824*t^5*z^3 - 3280*t^5*z^2 - 2880*t^5*z - 896*t^5 - 16*t^4*z^6 - 304*t^4*z^5 + 2448*t^4*z^4 + 5504*t^4*z^3 + 5088*t^4*z^2 + 3840*t^4*z + 1120*t^4 - 16*t^3*z^8 + 272*t^3*z^7 - 1024*t^3*z^6 - 192*t^3*z^5 - 5344*t^3*z^4 - 5952*t^3*z^3 - 3472*t^3*z^2 - 2880*t^3*z - 896*t^3 + 32*t^2*z^9 - 496*t^2*z^8 + 2128*t^2*z^7 - 1376*t^2*z^6 + 608*t^2*z^5 + 4000*t^2*z^4 + 3488*t^2*z^3 + 832*t^2*z^2 + 1152*t^2*z + 448*t^2 - 32*t*z^10 + 544*t*z^9 - 3056*t*z^8 + 6576*t*z^7 - 7168*t*z^6 + 3136*t*z^5 - 1072*t*z^4 - 1440*t*z^3 + 80*t*z^2 - 192*t*z - 128*t - 32*z^10 + 256*z^9 - 400*z^8 - 272*z^7 + 880*z^6 - 176*z^5 - 304*z^4 + 320*z^3 - 32*z^2 + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 96*t^6*z - 288*t^6 - 272*t^5*z^2 + 464*t^5*z + 6416*t^5 + 16*t^4*z^4 + 384*t^4*z^3 - 576*t^4*z^2 - 9536*t^4*z - 51040*t^4 + 16*t^3*z^6 - 192*t^3*z^5 + 16*t^3*z^4 + 848*t^3*z^3 + 9536*t^3*z^2 + 51088*t^3*z + 230304*t^3 - 32*t^2*z^7 + 336*t^2*z^6 - 352*t^2*z^5 - 1392*t^2*z^4 - 6512*t^2*z^3 - 32384*t^2*z^2 - 145872*t^2*z - 633040*t^2 + 32*t*z^8 - 384*t*z^7 + 1040*t*z^6 - 224*t*z^5 + 2928*t*z^4 + 12176*t*z^3 + 53168*t*z^2 + 230752*t*z + 994176*t + 32*z^8 - 96*z^7 - 176*z^6 - 320*z^5 - 1952*z^4 - 8624*z^3 - 36960*z^2 - 159248*z - 685328)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_13 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 13) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_13 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 + 2*t*z - 4*t + 8*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 8)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 - 64*t^7*z - 128*t^7 + 48*t^6*z^4 + 256*t^6*z^3 + 384*t^6*z^2 + 256*t^6*z + 448*t^6 - 16*t^5*z^6 - 336*t^5*z^5 - 592*t^5*z^4 - 1216*t^5*z^3 - 784*t^5*z^2 - 192*t^5*z - 896*t^5 + 160*t^4*z^7 + 624*t^4*z^6 + 1904*t^4*z^5 + 304*t^4*z^4 + 2112*t^4*z^3 + 608*t^4*z^2 - 640*t^4*z + 1120*t^4 - 16*t^3*z^9 - 336*t^3*z^8 - 1200*t^3*z^7 - 1456*t^3*z^6 - 1376*t^3*z^5 + 1952*t^3*z^4 - 2432*t^3*z^3 - 592*t^3*z^2 + 1600*t^3*z - 896*t^3 + 48*t^2*z^10 + 288*t^2*z^9 + 1952*t^2*z^8 - 944*t^2*z^7 - 352*t^2*z^6 + 2016*t^2*z^5 - 3760*t^2*z^4 + 1920*t^2*z^3 + 1216*t^2*z^2 - 1536*t^2*z + 448*t^2 - 32*t*z^11 - 336*t*z^10 - 624*t*z^9 - 416*t*z^8 + 5296*t*z^7 - 5280*t*z^6 - 720*t*z^5 + 3120*t*z^4 - 448*t*z^3 - 1136*t*z^2 + 704*t*z - 128*t + 192*z^11 + 160*z^10 - 1408*z^9 + 1168*z^8 + 1040*z^7 - 2736*z^6 + 2608*z^5 - 1072*z^4 - 192*z^3 + 352*z^2 - 128*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 - 496*t^6*z - 2720*t^6 + 16*t^5*z^4 + 416*t^5*z^3 + 2624*t^5*z^2 + 13088*t^5*z + 58352*t^5 - 160*t^4*z^5 - 1424*t^4*z^4 - 8544*t^4*z^3 - 38752*t^4*z^2 - 170240*t^4*z - 735552*t^4 + 16*t^3*z^7 + 416*t^3*z^6 + 3232*t^3*z^5 + 16368*t^3*z^4 + 73520*t^3*z^3 + 316544*t^3*z^2 + 1364592*t^3*z + 5873920*t^3 - 48*t^2*z^8 - 528*t^2*z^7 - 4448*t^2*z^6 - 19712*t^2*z^5 - 84864*t^2*z^4 - 367200*t^2*z^3 - 1577648*t^2*z^2 - 6788560*t^2*z - 29211072*t^2 + 32*t*z^9 + 496*t*z^8 + 3008*t*z^7 + 13968*t*z^6 + 55520*t*z^5 + 240976*t*z^4 + 1039040*t*z^3 + 4469152*t*z^2 + 19229088*t*z + 82739120*t - 192*z^9 - 1120*z^8 - 3616*z^7 - 15888*z^6 - 69632*z^5 - 297760*z^4 - 1282512*z^3 - 5518208*z^2 - 23743312*z - 102162288)*hf
  · have hr : (16*t^8 - 112*t^7*z^2 + 192*t^7*z - 128*t^7 + 288*t^6*z^4 - 960*t^6*z^3 + 1856*t^6*z^2 - 1536*t^6*z + 448*t^6 - 320*t^5*z^6 + 1536*t^5*z^5 - 5632*t^5*z^4 + 10560*t^5*z^3 - 10576*t^5*z^2 + 5184*t^5*z - 896*t^5 + 128*t^4*z^8 - 768*t^4*z^7 + 5872*t^4*z^6 - 19568*t^4*z^5 + 39184*t^4*z^4 - 45952*t^4*z^3 + 29728*t^4*z^2 - 9600*t^4*z + 1120*t^4 - 2000*t^3*z^8 + 11024*t^3*z^7 - 42544*t^3*z^6 + 96640*t^3*z^5 - 128960*t^3*z^4 + 102528*t^3*z^3 - 46352*t^3*z^2 + 10560*t^3*z - 896*t^3 - 32*t^2*z^10 + 352*t^2*z^9 + 10288*t^2*z^8 - 55376*t^2*z^7 + 146048*t^2*z^6 - 228512*t^2*z^5 + 216832*t^2*z^4 - 124096*t^2*z^3 + 40960*t^2*z^2 - 6912*t^2*z + 448*t^2 + 304*t*z^10 - 3376*t*z^9 - 16464*t*z^8 + 105520*t*z^7 - 224496*t*z^6 + 259200*t*z^5 - 181184*t*z^4 + 77376*t*z^3 - 19248*t*z^2 + 2496*t*z - 128*t - 672*z^10 + 7264*z^9 + 432*z^8 - 55536*z^7 + 114416*z^6 - 109296*z^5 + 59472*z^4 - 19456*z^3 + 3744*z^2 - 384*z + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(112*t^7 - 288*t^6*z^2 - 480*t^6*z - 3392*t^6 + 320*t^5*z^4 + 64*t^5*z^3 + 4992*t^5*z^2 + 14208*t^5*z + 66640*t^5 - 128*t^4*z^6 + 128*t^4*z^5 - 4848*t^4*z^4 - 5056*t^4*z^3 - 49920*t^4*z^2 - 188480*t^4*z - 822368*t^4 + 2000*t^3*z^6 - 1024*t^3*z^5 + 31424*t^3*z^4 + 63552*t^3*z^3 + 352448*t^3*z^2 + 1469056*t^3*z + 6334288*t^3 + 32*t^2*z^8 - 192*t^2*z^7 - 11344*t^2*z^6 - 768*t^2*z^5 - 115856*t^2*z^4 - 348464*t^2*z^3 - 1611584*t^2*z^2 - 6888432*t^2*z - 29648368*t^2 - 304*t*z^8 + 1856*t*z^7 + 26656*t*z^6 + 22192*t*z^5 + 255488*t*z^4 + 951664*t*z^3 + 4173040*t*z^2 + 17932832*t*z + 77164288*t + 672*z^8 - 3904*z^7 - 21968*z^6 - 42592*z^5 - 261472*z^4 - 1070288*z^3 - 4626496*z^2 - 19902160*z - 85635056)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_14 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 14) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_14 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 8*t*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 128*t^7*z - 48*t^6*z^3 + 320*t^6*z^2 - 64*t^6*z + 80*t^5*z^4 - 560*t^5*z^3 + 512*t^5*z^2 - 16*t^4*z^6 + 64*t^4*z^5 + 224*t^4*z^4 - 608*t^4*z^3 - 32*t^4*z^2 - 16*t^3*z^8 + 240*t^3*z^7 - 1200*t^3*z^6 + 2160*t^3*z^5 - 784*t^3*z^4 - 128*t^3*z^3 + 16*t^2*z^9 - 240*t^2*z^8 + 1264*t^2*z^7 - 2704*t^2*z^6 + 2000*t^2*z^5 - 512*t^2*z^4 + 192*t^2*z^3 - 16*t*z^10 + 272*t*z^9 - 1760*t*z^8 + 5360*t*z^7 - 7616*t*z^6 + 4272*t*z^5 - 768*t*z^4 - 16*z^9 + 192*z^8 - 816*z^7 + 1424*z^6 - 864*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 48*t^6*z - 80*t^6 - 80*t^5*z^2 + 160*t^5*z + 528*t^5 + 16*t^4*z^4 + 16*t^4*z^3 - 192*t^4*z^2 - 400*t^4*z - 1392*t^4 + 16*t^3*z^6 - 160*t^3*z^5 + 352*t^3*z^4 + 80*t^3*z^3 + 128*t^3*z^2 + 528*t^3*z + 2256*t^3 - 16*t^2*z^7 + 160*t^2*z^6 - 416*t^2*z^5 + 144*t^2*z^4 - 32*t^2*z^3 - 80*t^2*z^2 - 496*t^2*z - 2240*t^2 + 16*t*z^8 - 192*t*z^7 + 752*t*z^6 - 1024*t*z^5 + 240*t*z^4 + 48*t*z^2 + 240*t*z + 1056*t + 16*z^7 - 112*z^6 + 208*z^5 - 48*z^4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_15 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 15) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_15 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 8*t*z + 2*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8*z^4 - 48*t^7*z^5 - 192*t^7*z^4 + 48*t^6*z^6 + 640*t^6*z^5 + 704*t^6*z^4 - 16*t^5*z^7 - 736*t^5*z^6 - 2704*t^5*z^5 - 576*t^5*z^4 - 16*t^4*z^8 + 464*t^4*z^7 + 3184*t^4*z^6 + 3872*t^4*z^5 - 1312*t^4*z^4 + 16*t^3*z^9 - 48*t^3*z^8 - 2592*t^3*z^7 - 3520*t^3*z^6 - 336*t^3*z^5 + 1728*t^3*z^4 - 176*t^2*z^9 + 1680*t^2*z^8 + 1184*t^2*z^7 + 656*t^2*z^6 - 2496*t^2*z^5 + 448*t^2*z^4 + 32*t*z^10 + 80*t*z^9 - 3472*t*z^8 + 7984*t*z^7 - 8288*t*z^6 + 4624*t*z^5 - 960*t*z^4 - 96*z^10 + 912*z^9 - 2112*z^8 + 1680*z^7 - 48*z^6 - 480*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 80*t^8*z - 352*t^8 + 48*t^7*z^3 + 432*t^7*z^2 + 2016*t^7*z + 8784*t^7 - 48*t^6*z^4 - 880*t^6*z^3 - 4960*t^6*z^2 - 22160*t^6*z - 95920*t^6 + 16*t^5*z^5 + 816*t^5*z^4 + 6736*t^5*z^3 + 31808*t^5*z^2 + 138832*t^5*z + 598736*t^5 + 16*t^4*z^6 - 384*t^4*z^5 - 5152*t^4*z^4 - 28480*t^4*z^3 - 125632*t^4*z^2 - 542720*t^4*z - 2336704*t^4 - 16*t^3*z^7 - 32*t^3*z^6 + 2480*t^3*z^5 + 16016*t^3*z^4 + 72976*t^3*z^3 + 315104*t^3*z^2 + 1356592*t^3*z + 5837648*t^3 + 176*t^2*z^7 - 800*t^2*z^6 - 5712*t^2*z^5 - 26816*t^2*z^4 - 114448*t^2*z^3 - 492240*t^2*z^2 - 2117856*t^2*z - 9112560*t^2 - 32*t*z^8 - 240*t*z^7 + 2368*t*z^6 + 4576*t*z^5 + 24064*t*z^4 + 101968*t*z^3 + 438608*t*z^2 + 1887136*t*z + 8119856*t + 96*z^8 - 432*z^7 - 336*z^6 - 2064*z^5 - 9264*z^4 - 39648*z^3 - 170592*z^2 - 734016*z - 3158304)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_16 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 16) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_16 z t hf hn0 hn1 hn2 hn3
  · have hr : (6*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-6)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_17 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 17) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_17 z t hf hn0 hn1 hn2 hn3
  · have hr : (-16*t*z^10 + 272*t*z^9 - 1792*t*z^8 + 5632*t*z^7 - 8192*t*z^6 + 4096*t*z^5:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(16*t*z^8 - 192*t*z^7 + 784*t*z^6 - 1136*t*z^5 + 160*t*z^4 + 112*t*z^3 + 80*t*z^2 + 64*t*z + 80*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_18 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 18) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_18 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 + 4*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 14)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_19 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 19) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_19 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 2*t*z - 4*t + 4*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t - 4)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 + 64*t^7*z - 128*t^7 + 96*t^6*z^3 - 640*t^6*z + 448*t^6 + 272*t^5*z^4 - 608*t^5*z^3 - 976*t^5*z^2 + 2496*t^5*z - 896*t^5 - 16*t^4*z^6 + 592*t^4*z^5 - 2160*t^4*z^4 + 640*t^4*z^3 + 5088*t^4*z^2 - 5120*t^4*z + 1120*t^4 - 16*t^3*z^8 + 144*t^3*z^7 + 128*t^3*z^6 - 2752*t^3*z^5 + 4384*t^3*z^4 + 3648*t^3*z^3 - 11152*t^3*z^2 + 6080*t^3*z - 896*t^3 - 32*t^2*z^9 + 336*t^2*z^8 - 816*t^2*z^7 - 1248*t^2*z^6 + 5984*t^2*z^5 - 1632*t^2*z^4 - 11168*t^2*z^3 + 12352*t^2*z^2 - 4224*t^2*z + 448*t^2 - 32*t*z^10 + 416*t*z^9 - 1904*t*z^8 + 3376*t*z^7 - 640*t*z^6 - 2496*t*z^5 - 4656*t*z^4 + 11296*t*z^3 - 6832*t*z^2 + 1600*t*z - 128*t - 32*z^10 + 448*z^9 - 2384*z^8 + 6000*z^7 - 6928*z^6 + 1744*z^5 + 3792*z^4 - 3904*z^3 + 1504*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 - 96*t^6*z - 480*t^6 - 272*t^5*z^2 - 752*t^5*z - 1968*t^5 + 16*t^4*z^4 - 512*t^4*z^3 - 448*t^4*z^2 - 1344*t^4*z - 10464*t^4 + 16*t^3*z^6 - 64*t^3*z^5 - 496*t^3*z^4 + 464*t^3*z^3 - 576*t^3*z^2 - 7920*t^3*z - 26720*t^3 + 32*t^2*z^7 - 176*t^2*z^6 - 160*t^2*z^5 + 976*t^2*z^4 - 624*t^2*z^3 - 4416*t^2*z^2 - 9040*t^2*z - 44304*t^2 + 32*t*z^8 - 256*t*z^7 + 528*t*z^6 + 32*t*z^5 - 784*t*z^4 - 1520*t*z^3 - 592*t*z^2 - 9696*t*z - 39872*t + 32*z^8 - 288*z^7 + 848*z^6 - 896*z^5 - 96*z^4 + 464*z^3 - 1184*z^2 - 3408*z - 14992)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_20 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 20) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_20 z t hf hn0 hn1 hn2 hn3
  · have hr : (-16*t*z^10 + 272*t*z^9 - 1792*t*z^8 + 5632*t*z^7 - 8192*t*z^6 + 4096*t*z^5:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(16*t*z^8 - 192*t*z^7 + 784*t*z^6 - 1136*t*z^5 + 160*t*z^4 + 112*t*z^3 + 80*t*z^2 + 64*t*z + 80*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_21 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 21) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : (t + 4*z - 3:ℝ)=0 := by
  apply cell_11_21 z t hf hn0 hn1 hn2 hn3
  · have hr : (-32*t*z^10 + 480*t*z^9 - 2688*t*z^8 + 6912*t*z^7 - 7936*t*z^6 + 3072*t*z^5 - 32*z^10 + 352*z^9 - 1280*z^8 + 1792*z^7 - 768*z^6:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(32*t*z^8 - 320*t*z^7 + 992*t*z^6 - 992*t*z^5 - 96*t*z^3 - 480*t*z^2 - 2112*t*z - 9120*t + 32*z^8 - 192*z^7 + 224*z^6 - 96*z^5 - 384*z^4 - 1632*z^3 - 7008*z^2 - 30144*z - 129696)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_22 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 22) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_22 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*z^3 + 14*z^2 - 12*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z - 4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_23 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 23) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_23 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z - 4*t - 2*z^3 + 10*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 + 192*t^7*z - 128*t^7 + 48*t^6*z^4 - 448*t^6*z^3 + 1408*t^6*z^2 - 1536*t^6*z + 448*t^6 - 16*t^5*z^6 + 336*t^5*z^5 - 2320*t^5*z^4 + 6912*t^5*z^3 - 9232*t^5*z^2 + 5184*t^5*z - 896*t^5 - 96*t^4*z^7 + 1392*t^4*z^6 - 8016*t^4*z^5 + 23216*t^4*z^4 - 35392*t^4*z^3 + 27488*t^4*z^2 - 9600*t^4*z + 1120*t^4 + 16*t^3*z^9 - 400*t^3*z^8 + 3920*t^3*z^7 - 19760*t^3*z^6 + 56032*t^3*z^5 - 91872*t^3*z^4 + 86528*t^3*z^3 - 44112*t^3*z^2 + 10560*t^3*z - 896*t^3 + 48*t^2*z^10 - 928*t^2*z^9 + 7584*t^2*z^8 - 34224*t^2*z^7 + 93600*t^2*z^6 - 160416*t^2*z^5 + 171856*t^2*z^4 - 110656*t^2*z^3 + 39616*t^2*z^2 - 6912*t^2*z + 448*t^2 + 32*t*z^11 - 688*t*z^10 + 6224*t*z^9 - 30880*t*z^8 + 92144*t*z^7 - 171808*t*z^6 + 203600*t*z^5 - 153744*t*z^4 + 71424*t*z^3 - 18800*t*z^2 + 2496*t*z - 128*t - 32*z^11 + 640*z^10 - 5312*z^9 + 23696*z^8 - 61744*z^7 + 96592*z^6 - 91536*z^5 + 52816*z^4 - 18368*z^3 + 3680*z^2 - 384*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 + 208*t^6*z - 224*t^6 + 16*t^5*z^4 - 256*t^5*z^3 + 992*t^5*z^2 - 1184*t^5*z + 336*t^5 + 96*t^4*z^5 - 912*t^4*z^4 + 3168*t^4*z^3 - 4640*t^4*z^2 + 2688*t^4*z - 128*t^4 - 16*t^3*z^7 + 320*t^3*z^6 - 2272*t^3*z^5 + 7440*t^3*z^4 - 12016*t^3*z^3 + 9472*t^3*z^2 - 3120*t^3*z + 96*t^3 - 48*t^2*z^8 + 688*t^2*z^7 - 4000*t^2*z^6 + 12160*t^2*z^5 - 20800*t^2*z^4 + 19936*t^2*z^3 - 9776*t^2*z^2 + 1968*t^2*z - 448*t^2 - 32*t*z^9 + 528*t*z^8 - 3488*t*z^7 + 11856*t*z^6 - 22400*t*z^5 + 24240*t*z^4 - 15200*t*z^3 + 5024*t*z^2 - 704*t*z + 208*t + 32*z^9 - 480*z^8 + 2816*z^7 - 8176*z^6 + 12416*z^5 - 9984*z^4 + 4368*z^3 - 1024*z^2 + 144*z + 112)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 64*t^7*z - 128*t^7 - 64*t^6*z^2 + 256*t^6*z + 448*t^6 + 32*t^5*z^4 - 256*t^5*z^3 + 560*t^5*z^2 - 192*t^5*z - 896*t^5 - 16*t^4*z^6 + 144*t^4*z^5 - 496*t^4*z^4 + 1152*t^4*z^3 - 1632*t^4*z^2 - 640*t^4*z + 1120*t^4 - 16*t^3*z^8 + 208*t^3*z^7 - 880*t^3*z^6 + 1024*t^3*z^5 + 1408*t^3*z^4 - 3072*t^3*z^3 + 1648*t^3*z^2 + 1600*t^3*z - 896*t^3 + 16*t^2*z^8 - 208*t^2*z^7 + 832*t^2*z^6 - 544*t^2*z^5 - 2848*t^2*z^4 + 3840*t^2*z^3 - 128*t^2*z^2 - 1536*t^2*z + 448*t^2 - 16*t*z^10 + 272*t*z^9 - 1776*t*z^8 + 5424*t*z^7 - 7152*t*z^6 + 1536*t*z^5 + 3296*t*z^4 - 1792*t*z^3 - 688*t*z^2 + 704*t*z - 128*t - 16*z^8 + 208*z^7 - 976*z^6 + 1936*z^5 - 1392*z^4 + 128*z^3 + 288*z^2 - 128*z + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 64*t^6 - 32*t^5*z^2 + 96*t^5*z + 16*t^5 + 16*t^4*z^4 - 64*t^4*z^3 + 128*t^4*z^2 - 320*t^4*z - 352*t^4 + 16*t^3*z^6 - 128*t^3*z^5 + 192*t^3*z^4 + 320*t^3*z^3 - 384*t^3*z^2 + 192*t^3*z + 464*t^3 - 16*t^2*z^6 + 128*t^2*z^5 - 144*t^2*z^4 - 560*t^2*z^3 + 480*t^2*z^2 + 240*t^2*z - 112*t^2 + 16*t*z^8 - 192*t*z^7 + 768*t*z^6 - 1008*t*z^5 - 192*t*z^4 + 528*t*z^3 - 80*t*z^2 - 192*t*z - 32*t + 16*z^6 - 128*z^5 + 288*z^4 - 112*z^3 - 32*z^2 + 48*z + 48)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_24 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 24) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_24 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 + 4*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 14)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_25 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 25) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_25 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*z^3 + 14*z^2 - 12*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z - 4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_26 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 26) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_26 z t hf hn0 hn1 hn2 hn3
  · have hr : (6*z^3 - 6*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-6*z - 24)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_27 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 27) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_27 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 4*t*z^2 - 8*t*z + 2*z^3:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4*t - 2*z - 10)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 128*t^7*z + 144*t^6*z^4 - 368*t^6*z^3 + 192*t^6*z^2 - 64*t^6*z + 112*t^5*z^6 - 240*t^5*z^5 - 112*t^5*z^4 + 16*t^5*z^3 + 512*t^5*z^2 + 32*t^4*z^8 + 112*t^4*z^7 - 864*t^4*z^6 + 1024*t^4*z^5 + 96*t^4*z^4 - 224*t^4*z^3 - 32*t^4*z^2 + 112*t^3*z^9 - 448*t^3*z^8 + 592*t^3*z^7 - 1424*t^3*z^6 + 3760*t^3*z^5 - 2896*t^3*z^4 - 128*t^3*z^3 + 112*t^2*z^10 - 416*t^2*z^9 - 368*t^2*z^8 + 3152*t^2*z^7 - 4096*t^2*z^6 + 1808*t^2*z^5 - 384*t^2*z^4 + 192*t^2*z^3 + 32*t*z^11 + 112*t*z^10 - 1856*t*z^9 + 5184*t*z^8 - 3520*t*z^7 - 3904*t*z^6 + 4720*t*z^5 - 768*t*z^4 + 96*z^11 - 672*z^10 + 1488*z^9 - 576*z^8 - 2064*z^7 + 2832*z^6 - 1248*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 - 352*t^6*z - 1520*t^6 - 112*t^5*z^4 - 320*t^5*z^3 - 1152*t^5*z^2 - 4816*t^5*z - 21136*t^5 - 32*t^4*z^6 - 272*t^4*z^5 - 400*t^4*z^4 - 2208*t^4*z^3 - 9936*t^4*z^2 - 42832*t^4*z - 184320*t^4 - 112*t^3*z^7 - 112*t^3*z^6 - 816*t^3*z^5 - 2320*t^3*z^4 - 12912*t^3*z^3 - 54704*t^3*z^2 - 234656*t^3*z - 1009168*t^3 - 112*t^2*z^8 - 144*t^2*z^7 - 16*t^2*z^6 - 2800*t^2*z^5 - 9856*t^2*z^4 - 42688*t^2*z^3 - 183488*t^2*z^2 - 789568*t^2*z - 3397376*t^2 - 32*t*z^9 - 272*t*z^8 + 592*t*z^7 - 1408*t*z^6 - 5296*t*z^5 - 18352*t*z^4 - 80592*t*z^3 - 347136*t*z^2 - 1493904*t*z - 6428112*t - 96*z^9 + 192*z^8 - 240*z^7 - 1200*z^6 - 3216*z^5 - 15312*z^4 - 65664*z^3 - 282528*z^2 - 1215648*z - 5230656)*hf
  · have hr : (16*t^8 + 144*t^7*z^2 - 384*t^7*z + 480*t^6*z^4 - 2544*t^6*z^3 + 3520*t^6*z^2 - 64*t^6*z + 704*t^5*z^6 - 5568*t^5*z^5 + 15728*t^5*z^4 - 16176*t^5*z^3 + 1280*t^5*z^2 + 384*t^4*z^8 - 4032*t^4*z^7 + 18256*t^4*z^6 - 41472*t^4*z^5 + 41248*t^4*z^4 - 8160*t^4*z^3 - 32*t^4*z^2 + 1712*t^3*z^8 - 14096*t^3*z^7 + 42928*t^3*z^6 - 53456*t^3*z^5 + 18032*t^3*z^4 + 128*t^3*z^3 - 96*t^2*z^10 + 1392*t^2*z^9 - 4816*t^2*z^8 + 2800*t^2*z^7 + 7824*t^2*z^6 - 5360*t^2*z^5 - 640*t^2*z^4 + 192*t^2*z^3 - 208*t*z^10 + 2576*t*z^9 - 9472*t*z^8 + 15280*t*z^7 - 14240*t*z^6 + 7600*t*z^5 - 1536*t*z^4 - 96*z^10 + 912*z^9 - 2112*z^8 + 1680*z^7 - 48*z^6 - 480*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-144*t^7 - 480*t^6*z^2 + 144*t^6*z - 1360*t^6 - 704*t^5*z^4 + 2048*t^5*z^3 - 3376*t^5*z^2 - 6848*t^5*z - 25392*t^5 - 384*t^4*z^6 + 2112*t^4*z^5 - 6544*t^4*z^4 + 2416*t^4*z^3 - 9536*t^4*z^2 - 46768*t^4*z - 205200*t^4 - 1712*t^3*z^6 + 5536*t^3*z^5 - 10112*t^3*z^4 - 13712*t^3*z^3 - 56256*t^3*z^2 - 240272*t^3*z - 1032592*t^3 + 96*t^2*z^8 - 912*t^2*z^7 - 32*t^2*z^6 - 224*t^2*z^5 - 8848*t^2*z^4 - 38208*t^2*z^3 - 163856*t^2*z^2 - 704848*t^2*z - 3032672*t^2 + 208*t*z^8 - 1536*t*z^7 + 1168*t*z^6 - 4832*t*z^5 - 13424*t*z^4 - 60224*t*z^3 - 259312*t*z^2 - 1115888*t*z - 4801504*t + 96*z^8 - 432*z^7 - 336*z^6 - 2064*z^5 - 9264*z^4 - 39648*z^3 - 170592*z^2 - 734016*z - 3158304)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_28 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 28) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_28 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 2*t*z - 4*t + 4*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t - 4)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 192*t^7*z - 128*t^7 + 144*t^6*z^4 - 672*t^6*z^3 + 320*t^6*z^2 + 1152*t^6*z + 448*t^6 + 112*t^5*z^6 - 768*t^5*z^5 + 1280*t^5*z^4 + 1056*t^5*z^3 - 1936*t^5*z^2 - 2880*t^5*z - 896*t^5 + 32*t^4*z^8 - 288*t^4*z^7 + 880*t^4*z^6 - 560*t^4*z^5 - 1424*t^4*z^4 - 256*t^4*z^3 + 2848*t^4*z^2 + 3840*t^4*z + 1120*t^4 + 16*t^3*z^8 + 80*t^3*z^7 - 1120*t^3*z^6 + 2752*t^3*z^5 - 1280*t^3*z^4 - 192*t^3*z^3 - 1232*t^3*z^2 - 2880*t^3*z - 896*t^3 - 32*t^2*z^10 + 448*t^2*z^9 - 2288*t^2*z^8 + 5008*t^2*z^7 - 3232*t^2*z^6 - 3104*t^2*z^5 + 2800*t^2*z^4 + 608*t^2*z^3 - 512*t^2*z^2 + 1152*t^2*z + 448*t^2 - 32*t*z^10 + 416*t*z^9 - 2064*t*z^8 + 5104*t*z^7 - 7056*t*z^6 + 5568*t*z^5 - 1280*t*z^4 - 864*t*z^3 + 528*t*z^2 - 192*t*z - 128*t - 32*z^9 + 336*z^8 - 1200*z^7 + 1712*z^6 - 816*z^5 - 240*z^4 + 320*z^3 - 96*z^2 + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 - 48*t^6*z - 128*t^6 - 112*t^5*z^4 + 208*t^5*z^3 + 96*t^5*z^2 - 1200*t^5*z - 4352*t^5 - 32*t^4*z^6 + 128*t^4*z^5 - 144*t^4*z^4 - 544*t^4*z^3 - 864*t^4*z^2 - 2432*t^4*z - 12416*t^4 - 16*t^3*z^6 - 160*t^3*z^5 + 368*t^3*z^4 - 432*t^3*z^3 - 1984*t^3*z^2 - 8432*t^3*z - 34976*t^3 + 32*t^2*z^8 - 288*t^2*z^7 + 752*t^2*z^6 - 384*t^2*z^5 - 944*t^2*z^4 - 464*t^2*z^3 - 2288*t^2*z^2 - 10656*t^2*z - 45904*t^2 + 32*t*z^8 - 256*t*z^7 + 688*t*z^6 - 896*t*z^5 + 512*t*z^4 - 320*t*z^3 - 1856*t*z^2 - 7456*t*z - 32240*t + 32*z^7 - 176*z^6 + 224*z^5 - 64*z^4 - 176*z^3 - 448*z^2 - 2032*z - 8720)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 + 64*t^7*z - 128*t^7 + 96*t^6*z^3 - 640*t^6*z + 448*t^6 + 272*t^5*z^4 - 608*t^5*z^3 - 976*t^5*z^2 + 2496*t^5*z - 896*t^5 - 16*t^4*z^6 + 592*t^4*z^5 - 2160*t^4*z^4 + 640*t^4*z^3 + 5088*t^4*z^2 - 5120*t^4*z + 1120*t^4 - 16*t^3*z^8 + 144*t^3*z^7 + 128*t^3*z^6 - 2752*t^3*z^5 + 4384*t^3*z^4 + 3648*t^3*z^3 - 11152*t^3*z^2 + 6080*t^3*z - 896*t^3 - 32*t^2*z^9 + 336*t^2*z^8 - 816*t^2*z^7 - 1248*t^2*z^6 + 5984*t^2*z^5 - 1632*t^2*z^4 - 11168*t^2*z^3 + 12352*t^2*z^2 - 4224*t^2*z + 448*t^2 - 32*t*z^10 + 416*t*z^9 - 1904*t*z^8 + 3376*t*z^7 - 640*t*z^6 - 2496*t*z^5 - 4656*t*z^4 + 11296*t*z^3 - 6832*t*z^2 + 1600*t*z - 128*t - 32*z^10 + 448*z^9 - 2384*z^8 + 6000*z^7 - 6928*z^6 + 1744*z^5 + 3792*z^4 - 3904*z^3 + 1504*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 - 96*t^6*z - 480*t^6 - 272*t^5*z^2 - 752*t^5*z - 1968*t^5 + 16*t^4*z^4 - 512*t^4*z^3 - 448*t^4*z^2 - 1344*t^4*z - 10464*t^4 + 16*t^3*z^6 - 64*t^3*z^5 - 496*t^3*z^4 + 464*t^3*z^3 - 576*t^3*z^2 - 7920*t^3*z - 26720*t^3 + 32*t^2*z^7 - 176*t^2*z^6 - 160*t^2*z^5 + 976*t^2*z^4 - 624*t^2*z^3 - 4416*t^2*z^2 - 9040*t^2*z - 44304*t^2 + 32*t*z^8 - 256*t*z^7 + 528*t*z^6 + 32*t*z^5 - 784*t*z^4 - 1520*t*z^3 - 592*t*z^2 - 9696*t*z - 39872*t + 32*z^8 - 288*z^7 + 848*z^6 - 896*z^5 - 96*z^4 + 464*z^3 - 1184*z^2 - 3408*z - 14992)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_29 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 29) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_29 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z - 4*t - 2*z^3 + 10*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 64*t^7*z - 128*t^7 - 64*t^6*z^2 + 256*t^6*z + 448*t^6 + 32*t^5*z^4 - 256*t^5*z^3 + 560*t^5*z^2 - 192*t^5*z - 896*t^5 - 16*t^4*z^6 + 144*t^4*z^5 - 496*t^4*z^4 + 1152*t^4*z^3 - 1632*t^4*z^2 - 640*t^4*z + 1120*t^4 - 16*t^3*z^8 + 208*t^3*z^7 - 880*t^3*z^6 + 1024*t^3*z^5 + 1408*t^3*z^4 - 3072*t^3*z^3 + 1648*t^3*z^2 + 1600*t^3*z - 896*t^3 + 16*t^2*z^8 - 208*t^2*z^7 + 832*t^2*z^6 - 544*t^2*z^5 - 2848*t^2*z^4 + 3840*t^2*z^3 - 128*t^2*z^2 - 1536*t^2*z + 448*t^2 - 16*t*z^10 + 272*t*z^9 - 1776*t*z^8 + 5424*t*z^7 - 7152*t*z^6 + 1536*t*z^5 + 3296*t*z^4 - 1792*t*z^3 - 688*t*z^2 + 704*t*z - 128*t - 16*z^8 + 208*z^7 - 976*z^6 + 1936*z^5 - 1392*z^4 + 128*z^3 + 288*z^2 - 128*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 64*t^6 - 32*t^5*z^2 + 96*t^5*z + 16*t^5 + 16*t^4*z^4 - 64*t^4*z^3 + 128*t^4*z^2 - 320*t^4*z - 352*t^4 + 16*t^3*z^6 - 128*t^3*z^5 + 192*t^3*z^4 + 320*t^3*z^3 - 384*t^3*z^2 + 192*t^3*z + 464*t^3 - 16*t^2*z^6 + 128*t^2*z^5 - 144*t^2*z^4 - 560*t^2*z^3 + 480*t^2*z^2 + 240*t^2*z - 112*t^2 + 16*t*z^8 - 192*t*z^7 + 768*t*z^6 - 1008*t*z^5 - 192*t*z^4 + 528*t*z^3 - 80*t*z^2 - 192*t*z - 32*t + 16*z^6 - 128*z^5 + 288*z^4 - 112*z^3 - 32*z^2 + 48*z + 48)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_30 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 30) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_30 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 4*t*z^2 - 8*t*z + 2*z^3:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4*t - 2*z - 10)*hf
  · have hr : (16*t^8 + 144*t^7*z^2 - 384*t^7*z + 480*t^6*z^4 - 2544*t^6*z^3 + 3520*t^6*z^2 - 64*t^6*z + 704*t^5*z^6 - 5568*t^5*z^5 + 15728*t^5*z^4 - 16176*t^5*z^3 + 1280*t^5*z^2 + 384*t^4*z^8 - 4032*t^4*z^7 + 18256*t^4*z^6 - 41472*t^4*z^5 + 41248*t^4*z^4 - 8160*t^4*z^3 - 32*t^4*z^2 + 1712*t^3*z^8 - 14096*t^3*z^7 + 42928*t^3*z^6 - 53456*t^3*z^5 + 18032*t^3*z^4 + 128*t^3*z^3 - 96*t^2*z^10 + 1392*t^2*z^9 - 4816*t^2*z^8 + 2800*t^2*z^7 + 7824*t^2*z^6 - 5360*t^2*z^5 - 640*t^2*z^4 + 192*t^2*z^3 - 208*t*z^10 + 2576*t*z^9 - 9472*t*z^8 + 15280*t*z^7 - 14240*t*z^6 + 7600*t*z^5 - 1536*t*z^4 - 96*z^10 + 912*z^9 - 2112*z^8 + 1680*z^7 - 48*z^6 - 480*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-144*t^7 - 480*t^6*z^2 + 144*t^6*z - 1360*t^6 - 704*t^5*z^4 + 2048*t^5*z^3 - 3376*t^5*z^2 - 6848*t^5*z - 25392*t^5 - 384*t^4*z^6 + 2112*t^4*z^5 - 6544*t^4*z^4 + 2416*t^4*z^3 - 9536*t^4*z^2 - 46768*t^4*z - 205200*t^4 - 1712*t^3*z^6 + 5536*t^3*z^5 - 10112*t^3*z^4 - 13712*t^3*z^3 - 56256*t^3*z^2 - 240272*t^3*z - 1032592*t^3 + 96*t^2*z^8 - 912*t^2*z^7 - 32*t^2*z^6 - 224*t^2*z^5 - 8848*t^2*z^4 - 38208*t^2*z^3 - 163856*t^2*z^2 - 704848*t^2*z - 3032672*t^2 + 208*t*z^8 - 1536*t*z^7 + 1168*t*z^6 - 4832*t*z^5 - 13424*t*z^4 - 60224*t*z^3 - 259312*t*z^2 - 1115888*t*z - 4801504*t + 96*z^8 - 432*z^7 - 336*z^6 - 2064*z^5 - 9264*z^4 - 39648*z^3 - 170592*z^2 - 734016*z - 3158304)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_31 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 31) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : (t + z - 3:ℝ)=0 := by
  apply cell_11_31 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z + 4*t*z^2 - 8*t*z + 2*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4*t - 2)*hf
  · have hr : (16*t^8*z^4 + 80*t^7*z^5 - 192*t^7*z^4 + 144*t^6*z^6 - 640*t^6*z^5 + 704*t^6*z^4 + 112*t^5*z^7 - 640*t^5*z^6 + 1136*t^5*z^5 - 576*t^5*z^4 + 16*t^4*z^8 + 16*t^4*z^7 - 528*t^4*z^6 + 1440*t^4*z^5 - 1312*t^4*z^4 - 48*t^3*z^9 + 624*t^3*z^8 - 2848*t^3*z^7 + 5632*t^3*z^6 - 4816*t^3*z^5 + 1728*t^3*z^4 - 32*t^2*z^10 + 432*t^2*z^9 - 2192*t^2*z^8 + 5152*t^2*z^7 - 5392*t^2*z^6 + 1600*t^2*z^5 + 448*t^2*z^4 - 32*t*z^10 + 464*t*z^9 - 2608*t*z^8 + 7088*t*z^7 - 9344*t*z^6 + 5136*t*z^5 - 960*t*z^4 - 16*z^9 + 192*z^8 - 816*z^7 + 1424*z^6 - 864*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 80*t^8*z - 352*t^8 - 80*t^7*z^3 - 208*t^7*z^2 - 800*t^7*z - 3376*t^7 - 144*t^6*z^4 - 80*t^6*z^3 - 672*t^6*z^2 - 3120*t^6*z - 13584*t^6 - 112*t^5*z^5 + 80*t^5*z^4 - 400*t^5*z^3 - 1664*t^5*z^2 - 7120*t^5*z - 30608*t^5 - 16*t^4*z^6 - 96*t^4*z^5 + 96*t^4*z^4 - 672*t^4*z^3 - 2336*t^4*z^2 - 9664*t^4*z - 41312*t^4 + 48*t^3*z^7 - 384*t^3*z^6 + 784*t^3*z^5 - 560*t^3*z^4 - 336*t^3*z^3 - 1728*t^3*z^2 - 7632*t^3*z - 32976*t^3 + 32*t^2*z^8 - 272*t^2*z^7 + 736*t^2*z^6 - 656*t^2*z^5 - 96*t^2*z^4 - 112*t^2*z^3 - 720*t^2*z^2 - 3264*t^2*z - 14160*t^2 + 32*t*z^8 - 304*t*z^7 + 992*t*z^6 - 1216*t*z^5 + 288*t*z^4 - 48*t*z^3 - 144*t*z^2 - 576*t*z - 2448*t + 16*z^7 - 112*z^6 + 208*z^5 - 48*z^4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_32 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 32) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_32 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*z^3 - 8*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4*z - 12)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_33 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 33) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_33 z t hf hn0 hn1 hn2 hn3
  · have hr : (6*z^3 - 6*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-6*z - 24)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_34 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 34) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_34 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 4*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 6)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_35 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 35) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : (t - 3*z + 2:ℝ)=0 := by
  apply cell_11_35 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 - 4*t + 4*z^3 - 6*z^2 + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 4*z - 14)*hf
  · have hr : (16*t^8 - 112*t^7*z^2 + 128*t^7*z - 128*t^7 + 288*t^6*z^4 - 496*t^6*z^3 + 992*t^6*z^2 - 1024*t^6*z + 448*t^6 - 320*t^5*z^6 + 288*t^5*z^5 - 1264*t^5*z^4 + 3200*t^5*z^3 - 4432*t^5*z^2 + 3456*t^5*z - 896*t^5 + 128*t^4*z^8 + 704*t^4*z^7 - 944*t^4*z^6 + 64*t^4*z^5 + 2784*t^4*z^4 - 9312*t^4*z^3 + 11488*t^4*z^2 - 6400*t^4*z + 1120*t^4 - 640*t^3*z^9 + 496*t^3*z^8 - 1904*t^3*z^7 + 7120*t^3*z^6 - 6816*t^3*z^5 - 3280*t^3*z^4 + 16704*t^3*z^3 - 17552*t^3*z^2 + 7040*t^3*z - 896*t^3 + 1120*t^2*z^10 - 1232*t^2*z^9 - 1392*t^2*z^8 + 4464*t^2*z^7 - 13872*t^2*z^6 + 17440*t^2*z^5 + 928*t^2*z^4 - 18800*t^2*z^3 + 15520*t^2*z^2 - 4608*t^2*z + 448*t^2 - 800*t*z^11 - 528*t*z^10 + 7488*t*z^9 - 8096*t*z^8 - 4752*t*z^7 + 19440*t*z^6 - 19776*t*z^5 + 864*t*z^4 + 11712*t*z^3 - 7344*t*z^2 + 1664*t*z - 128*t + 192*z^12 + 800*z^11 - 2976*z^10 - 2848*z^9 + 12624*z^8 - 4080*z^7 - 12624*z^6 + 11536*z^5 - 752*z^4 - 3008*z^3 + 1440*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(112*t^7 - 288*t^6*z^2 - 944*t^6*z - 4848*t^6 + 320*t^5*z^4 + 1312*t^5*z^3 + 6864*t^5*z^2 + 27184*t^5*z + 119760*t^5 - 128*t^4*z^6 - 1344*t^4*z^5 - 5392*t^4*z^4 - 22992*t^4*z^3 - 101568*t^4*z^2 - 429552*t^4*z - 1854544*t^4 + 640*t^3*z^7 + 2704*t^3*z^6 + 13504*t^3*z^5 + 52288*t^3*z^4 + 227744*t^3*z^3 + 985136*t^3*z^2 + 4225744*t^3*z + 18190864*t^3 - 1120*t^2*z^8 - 4368*t^2*z^7 - 17088*t^2*z^6 - 76800*t^2*z^5 - 318864*t^2*z^4 - 1381360*t^2*z^3 - 5951136*t^2*z^2 - 25592800*t^2*z - 110126112*t^2 + 800*t*z^9 + 4528*t*z^8 + 12752*t*z^7 + 58272*t*z^6 + 257856*t*z^5 + 1095024*t*z^4 + 4721328*t*z^3 + 20320704*t*z^2 + 87427824*t*z + 376184352*t - 192*z^10 - 1760*z^9 - 5248*z^8 - 18112*z^7 - 87440*z^6 - 378784*z^5 - 1618976*z^4 - 6970064*z^3 - 29992640*z^2 - 129050000*z - 555273520)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_36 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 36) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_36 z t hf hn0 hn1 hn2 hn3
  · have hr : (6*z^3 - 6*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-6*z - 24)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_37 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 37) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_37 z t hf hn0 hn1 hn2 hn3
  · have hr : (10*z^3 - 8*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-10*z - 42)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_38 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 38) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_38 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 + 4*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 14)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_39 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 39) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_39 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z^2 + 4*t*z - 4*t + 6*z^3 - 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4*t - 6*z - 28)*hf
  · have hr : (16*t^8 - 176*t^7*z^2 + 256*t^7*z - 128*t^7 + 720*t^6*z^4 - 1872*t^6*z^3 + 2720*t^6*z^2 - 1920*t^6*z + 448*t^6 - 1296*t^5*z^6 + 3888*t^5*z^5 - 9856*t^5*z^4 + 16096*t^5*z^3 - 14224*t^5*z^2 + 6144*t^5*z - 896*t^5 + 864*t^4*z^8 - 432*t^4*z^7 + 5408*t^4*z^6 - 24032*t^4*z^5 + 50112*t^4*z^4 - 58784*t^4*z^3 + 36768*t^4*z^2 - 10880*t^4*z + 1120*t^4 - 3888*t^3*z^9 + 7280*t^3*z^8 - 9792*t^3*z^7 - 4736*t^3*z^6 + 65856*t^3*z^5 - 126576*t^3*z^4 + 114304*t^3*z^3 - 53072*t^3*z^2 + 11520*t^3*z - 896*t^3 + 6384*t^2*z^10 - 896*t^2*z^9 - 34432*t^2*z^8 + 64352*t^2*z^7 - 21808*t^2*z^6 - 99072*t^2*z^5 + 171664*t^2*z^4 - 123088*t^2*z^3 + 43744*t^2*z^2 - 7296*t^2*z + 448*t^2 - 4512*t*z^11 - 11824*t*z^10 + 34912*t*z^9 + 28976*t*z^8 - 116016*t*z^7 + 61952*t*z^6 + 73904*t*z^5 - 119664*t*z^4 + 69152*t*z^3 - 19312*t*z^2 + 2560*t*z - 128*t + 1152*z^12 + 7008*z^11 + 96*z^10 - 34592*z^9 + 6672*z^8 + 61584*z^7 - 44656*z^6 - 17808*z^5 + 33168*z^4 - 15808*z^3 + 3552*z^2 - 384*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(176*t^7 - 720*t^6*z^2 - 1728*t^6*z - 9200*t^6 + 1296*t^5*z^4 + 2592*t^5*z^3 + 18928*t^5*z^2 + 70768*t^5*z + 311280*t^5 - 864*t^4*z^6 - 3888*t^4*z^5 - 22256*t^4*z^4 - 75584*t^4*z^3 - 361264*t^4*z^2 - 1520784*t^4*z - 6556896*t^4 + 3888*t^3*z^7 + 12160*t^3*z^6 + 58928*t^3*z^5 + 262896*t^3*z^4 + 1071840*t^3*z^3 + 4697088*t^3*z^2 + 20155616*t^3*z + 86739888*t^3 - 6384*t^2*z^8 - 31024*t^2*z^7 - 101536*t^2*z^6 - 478960*t^2*z^5 - 2068384*t^2*z^4 - 8805968*t^2*z^3 - 37996352*t^2*z^2 - 163440768*t^2*z - 703258528*t^2 + 4512*t*z^9 + 34384*t*z^8 + 123472*t*z^7 + 485232*t*z^6 + 2171760*t*z^5 + 9341152*t*z^4 + 40116576*t*z^3 + 172679088*t*z^2 + 742976560*t*z + 3196864848*t - 1152*z^10 - 12768*z^9 - 60480*z^8 - 229504*z^7 - 972752*z^6 - 4236832*z^5 - 18221248*z^4 - 78377936*z^3 - 337259104*z^2 - 1451145904*z - 6243955760)*hf
  · have hr : (16*t^8 - 112*t^7*z^2 - 128*t^7 + 288*t^6*z^4 + 304*t^6*z^3 + 480*t^6*z^2 - 128*t^6*z + 448*t^6 - 320*t^5*z^6 - 1536*t^5*z^5 - 208*t^5*z^4 - 1248*t^5*z^3 - 592*t^5*z^2 + 768*t^5*z - 896*t^5 + 128*t^4*z^8 + 2496*t^4*z^7 + 1168*t^4*z^6 + 3232*t^4*z^5 - 3488*t^4*z^4 + 3488*t^4*z^3 - 32*t^4*z^2 - 1920*t^4*z + 1120*t^4 - 1280*t^3*z^9 - 5584*t^3*z^8 + 1456*t^3*z^7 - 400*t^3*z^6 - 2944*t^3*z^5 + 9136*t^3*z^4 - 7168*t^3*z^3 + 368*t^3*z^2 + 2560*t^3*z - 896*t^3 + 4576*t^2*z^10 + 1360*t^2*z^9 + 2288*t^2*z^8 - 15344*t^2*z^7 + 12496*t^2*z^6 + 1056*t^2*z^5 - 12320*t^2*z^4 + 8496*t^2*z^3 + 160*t^2*z^2 - 1920*t^2*z + 448*t^2 - 6976*t*z^11 + 6512*t*z^10 + 2880*t*z^9 - 5824*t*z^8 + 16208*t*z^7 - 20048*t*z^6 + 2144*t*z^5 + 9920*t*z^4 - 5024*t*z^3 - 432*t*z^2 + 768*t*z - 128*t + 3840*z^12 - 3648*z^11 - 12512*z^10 + 20000*z^9 + 112*z^8 - 18160*z^7 + 12144*z^6 + 784*z^5 - 3760*z^4 + 1152*z^3 + 160*z^2 - 128*z + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(112*t^7 - 288*t^6*z^2 - 1744*t^6*z - 8336*t^6 + 320*t^5*z^4 + 3136*t^5*z^3 + 14928*t^5*z^2 + 66480*t^5*z + 288208*t^5 - 128*t^4*z^6 - 3136*t^4*z^5 - 16464*t^4*z^4 - 76144*t^4*z^3 - 327840*t^4*z^2 - 1414256*t^4*z - 6087728*t^4 + 1280*t^3*z^7 + 11984*t^3*z^6 + 54624*t^3*z^5 + 237568*t^3*z^4 + 1026912*t^3*z^3 + 4412720*t^3*z^2 + 18990032*t^3*z + 81711632*t^3 - 4576*t^2*z^8 - 24240*t^2*z^7 - 109760*t^2*z^6 - 460736*t^2*z^5 - 1986896*t^2*z^4 - 8553328*t^2*z^3 - 36793632*t^2*z^2 - 158316672*t^2*z - 681202624*t^2 + 6976*t*z^9 + 28368*t*z^8 + 118032*t*z^7 + 510880*t*z^6 + 2184096*t*z^5 + 9407888*t*z^4 + 40485008*t*z^3 + 174191456*t*z^2 + 749507280*t*z + 3224962464*t - 3840*z^10 - 15552*z^9 - 53728*z^8 - 241984*z^7 - 1048848*z^6 - 4500128*z^5 - 19366240*z^4 - 83331600*z^3 - 358555520*z^2 - 1542783952*z - 6638253360)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_40 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 40) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_40 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 4*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 6)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_41 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 41) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_41 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 + 4*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 14)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_42 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 42) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_42 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 8*z^2 + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_43 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 43) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_43 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t*z + 2*z^3 - 4*z^2 + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 6)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 - 64*t^7*z + 48*t^6*z^4 + 256*t^6*z^3 + 32*t^6*z^2 - 128*t^6*z - 16*t^5*z^6 - 336*t^5*z^5 - 256*t^5*z^4 + 128*t^5*z^3 + 512*t^5*z^2 + 160*t^4*z^7 + 496*t^4*z^6 + 368*t^4*z^5 - 1776*t^4*z^4 + 128*t^4*z^3 + 256*t^4*z^2 - 16*t^3*z^9 - 320*t^3*z^8 - 528*t^3*z^7 + 560*t^3*z^6 + 2368*t^3*z^5 - 768*t^3*z^4 - 1024*t^3*z^3 + 48*t^2*z^10 + 192*t^2*z^9 + 1072*t^2*z^8 - 3408*t^2*z^7 - 192*t^2*z^6 + 3328*t^2*z^5 - 1024*t^2*z^4 - 32*t*z^11 - 208*t*z^10 - 16*t*z^9 + 1024*t*z^8 + 3072*t*z^7 - 8192*t*z^6 + 4096*t*z^5 + 160*z^11 - 288*z^10 - 832*z^9 + 2048*z^8 - 1024*z^7:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 - 496*t^6*z - 2368*t^6 + 16*t^5*z^4 + 416*t^5*z^3 + 2288*t^5*z^2 + 10064*t^5*z + 42944*t^5 - 160*t^4*z^5 - 1296*t^4*z^4 - 6368*t^4*z^3 - 26176*t^4*z^2 - 111904*t^4*z - 481248*t^4 + 16*t^3*z^7 + 400*t^3*z^6 + 2480*t^3*z^5 + 10640*t^3*z^4 + 43392*t^3*z^3 + 185808*t^3*z^2 + 799888*t^3*z + 3442016*t^3 - 48*t^2*z^8 - 432*t^2*z^7 - 3088*t^2*z^6 - 10736*t^2*z^5 - 44224*t^2*z^4 - 192240*t^2*z^3 - 827504*t^2*z^2 - 3560800*t^2*z - 15321488*t^2 + 32*t*z^9 + 368*t*z^8 + 1760*t*z^7 + 6672*t*z^6 + 25008*t*z^5 + 113216*t*z^4 + 486960*t*z^3 + 2095152*t*z^2 + 9014880*t*z + 38788944*t - 160*z^9 - 512*z^8 - 1248*z^7 - 6752*z^6 - 28992*z^5 - 124704*z^4 - 536544*z^3 - 2308608*z^2 - 9933408*z - 42741216)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_44 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 44) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : (t - 3*z + 2:ℝ)=0 := by
  apply cell_11_44 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 - 4*t + 4*z^3 - 6*z^2 + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 4*z - 14)*hf
  · have hr : (16*t^8 - 112*t^7*z^2 + 128*t^7*z - 128*t^7 + 288*t^6*z^4 - 496*t^6*z^3 + 992*t^6*z^2 - 1024*t^6*z + 448*t^6 - 320*t^5*z^6 + 288*t^5*z^5 - 1264*t^5*z^4 + 3200*t^5*z^3 - 4432*t^5*z^2 + 3456*t^5*z - 896*t^5 + 128*t^4*z^8 + 704*t^4*z^7 - 944*t^4*z^6 + 64*t^4*z^5 + 2784*t^4*z^4 - 9312*t^4*z^3 + 11488*t^4*z^2 - 6400*t^4*z + 1120*t^4 - 640*t^3*z^9 + 496*t^3*z^8 - 1904*t^3*z^7 + 7120*t^3*z^6 - 6816*t^3*z^5 - 3280*t^3*z^4 + 16704*t^3*z^3 - 17552*t^3*z^2 + 7040*t^3*z - 896*t^3 + 1120*t^2*z^10 - 1232*t^2*z^9 - 1392*t^2*z^8 + 4464*t^2*z^7 - 13872*t^2*z^6 + 17440*t^2*z^5 + 928*t^2*z^4 - 18800*t^2*z^3 + 15520*t^2*z^2 - 4608*t^2*z + 448*t^2 - 800*t*z^11 - 528*t*z^10 + 7488*t*z^9 - 8096*t*z^8 - 4752*t*z^7 + 19440*t*z^6 - 19776*t*z^5 + 864*t*z^4 + 11712*t*z^3 - 7344*t*z^2 + 1664*t*z - 128*t + 192*z^12 + 800*z^11 - 2976*z^10 - 2848*z^9 + 12624*z^8 - 4080*z^7 - 12624*z^6 + 11536*z^5 - 752*z^4 - 3008*z^3 + 1440*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(112*t^7 - 288*t^6*z^2 - 944*t^6*z - 4848*t^6 + 320*t^5*z^4 + 1312*t^5*z^3 + 6864*t^5*z^2 + 27184*t^5*z + 119760*t^5 - 128*t^4*z^6 - 1344*t^4*z^5 - 5392*t^4*z^4 - 22992*t^4*z^3 - 101568*t^4*z^2 - 429552*t^4*z - 1854544*t^4 + 640*t^3*z^7 + 2704*t^3*z^6 + 13504*t^3*z^5 + 52288*t^3*z^4 + 227744*t^3*z^3 + 985136*t^3*z^2 + 4225744*t^3*z + 18190864*t^3 - 1120*t^2*z^8 - 4368*t^2*z^7 - 17088*t^2*z^6 - 76800*t^2*z^5 - 318864*t^2*z^4 - 1381360*t^2*z^3 - 5951136*t^2*z^2 - 25592800*t^2*z - 110126112*t^2 + 800*t*z^9 + 4528*t*z^8 + 12752*t*z^7 + 58272*t*z^6 + 257856*t*z^5 + 1095024*t*z^4 + 4721328*t*z^3 + 20320704*t*z^2 + 87427824*t*z + 376184352*t - 192*z^10 - 1760*z^9 - 5248*z^8 - 18112*z^7 - 87440*z^6 - 378784*z^5 - 1618976*z^4 - 6970064*z^3 - 29992640*z^2 - 129050000*z - 555273520)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_45 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 45) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_45 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z^2 + 4*t*z - 4*t + 6*z^3 - 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4*t - 6*z - 28)*hf
  · have hr : (16*t^8 - 112*t^7*z^2 - 128*t^7 + 288*t^6*z^4 + 304*t^6*z^3 + 480*t^6*z^2 - 128*t^6*z + 448*t^6 - 320*t^5*z^6 - 1536*t^5*z^5 - 208*t^5*z^4 - 1248*t^5*z^3 - 592*t^5*z^2 + 768*t^5*z - 896*t^5 + 128*t^4*z^8 + 2496*t^4*z^7 + 1168*t^4*z^6 + 3232*t^4*z^5 - 3488*t^4*z^4 + 3488*t^4*z^3 - 32*t^4*z^2 - 1920*t^4*z + 1120*t^4 - 1280*t^3*z^9 - 5584*t^3*z^8 + 1456*t^3*z^7 - 400*t^3*z^6 - 2944*t^3*z^5 + 9136*t^3*z^4 - 7168*t^3*z^3 + 368*t^3*z^2 + 2560*t^3*z - 896*t^3 + 4576*t^2*z^10 + 1360*t^2*z^9 + 2288*t^2*z^8 - 15344*t^2*z^7 + 12496*t^2*z^6 + 1056*t^2*z^5 - 12320*t^2*z^4 + 8496*t^2*z^3 + 160*t^2*z^2 - 1920*t^2*z + 448*t^2 - 6976*t*z^11 + 6512*t*z^10 + 2880*t*z^9 - 5824*t*z^8 + 16208*t*z^7 - 20048*t*z^6 + 2144*t*z^5 + 9920*t*z^4 - 5024*t*z^3 - 432*t*z^2 + 768*t*z - 128*t + 3840*z^12 - 3648*z^11 - 12512*z^10 + 20000*z^9 + 112*z^8 - 18160*z^7 + 12144*z^6 + 784*z^5 - 3760*z^4 + 1152*z^3 + 160*z^2 - 128*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(112*t^7 - 288*t^6*z^2 - 1744*t^6*z - 8336*t^6 + 320*t^5*z^4 + 3136*t^5*z^3 + 14928*t^5*z^2 + 66480*t^5*z + 288208*t^5 - 128*t^4*z^6 - 3136*t^4*z^5 - 16464*t^4*z^4 - 76144*t^4*z^3 - 327840*t^4*z^2 - 1414256*t^4*z - 6087728*t^4 + 1280*t^3*z^7 + 11984*t^3*z^6 + 54624*t^3*z^5 + 237568*t^3*z^4 + 1026912*t^3*z^3 + 4412720*t^3*z^2 + 18990032*t^3*z + 81711632*t^3 - 4576*t^2*z^8 - 24240*t^2*z^7 - 109760*t^2*z^6 - 460736*t^2*z^5 - 1986896*t^2*z^4 - 8553328*t^2*z^3 - 36793632*t^2*z^2 - 158316672*t^2*z - 681202624*t^2 + 6976*t*z^9 + 28368*t*z^8 + 118032*t*z^7 + 510880*t*z^6 + 2184096*t*z^5 + 9407888*t*z^4 + 40485008*t*z^3 + 174191456*t*z^2 + 749507280*t*z + 3224962464*t - 3840*z^10 - 15552*z^9 - 53728*z^8 - 241984*z^7 - 1048848*z^6 - 4500128*z^5 - 19366240*z^4 - 83331600*z^3 - 358555520*z^2 - 1542783952*z - 6638253360)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_46 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 46) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_46 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t*z + 2*z^3 - 4*z^2 + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 6)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 320*t^7*z - 192*t^6*z^3 + 2592*t^6*z^2 - 128*t^6*z + 992*t^5*z^4 - 11648*t^5*z^3 + 2048*t^5*z^2 - 16*t^4*z^6 - 2672*t^4*z^5 + 31760*t^4*z^4 - 11648*t^4*z^3 + 256*t^4*z^2 - 16*t^3*z^8 + 336*t^3*z^7 + 2512*t^3*z^6 - 50752*t^3*z^5 + 31488*t^3*z^4 - 3072*t^3*z^3 + 64*t^2*z^9 - 1232*t^2*z^8 + 3344*t^2*z^7 + 40640*t^2*z^6 - 41216*t^2*z^5 + 9216*t^2*z^4 - 80*t*z^10 + 1680*t*z^9 - 9472*t*z^8 - 3072*t*z^7 + 12288*t*z^6 - 4096*t*z^5 - 320*z^10 + 3136*z^9 - 3584*z^8 + 1024*z^7:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 192*t^6*z - 1632*t^6 - 992*t^5*z^2 + 6688*t^5*z + 34368*t^5 + 16*t^4*z^4 + 2752*t^4*z^3 - 18048*t^4*z^2 - 86848*t^4*z - 380352*t^4 + 16*t^3*z^6 - 256*t^3*z^5 - 3840*t^3*z^4 + 32320*t^3*z^3 + 141632*t^3*z^2 + 614272*t^3*z + 2646464*t^3 - 64*t^2*z^7 + 912*t^2*z^6 + 1408*t^2*z^5 - 36336*t^2*z^4 - 144688*t^2*z^3 - 623648*t^2*z^2 - 2684176*t^2*z - 11549936*t^2 + 80*t*z^8 - 1280*t*z^7 + 2832*t*z^6 + 21072*t*z^5 + 84576*t*z^4 + 363760*t*z^3 + 1565072*t*z^2 + 6734080*t*z + 28975184*t + 320*z^8 - 1536*z^7 - 5056*z^6 - 21696*z^5 - 93312*z^4 - 401472*z^3 - 1727424*z^2 - 7432704*z - 31981248)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_47 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 47) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_47 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 4*t*z^2 - 4*t*z + 4*z^3 - 4*z^2 + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4*t - 4*z - 16)*hf
  · have hr : (16*t^8*z^4 - 176*t^7*z^5 - 64*t^7*z^4 + 848*t^6*z^6 + 672*t^6*z^5 - 128*t^6*z^4 - 2352*t^5*z^7 - 2896*t^5*z^6 + 704*t^5*z^5 + 512*t^5*z^4 + 4112*t^4*z^8 + 6864*t^4*z^7 - 1712*t^4*z^6 - 3328*t^4*z^5 + 256*t^4*z^4 - 4624*t^3*z^9 - 9888*t^3*z^8 + 2464*t^3*z^7 + 9088*t^3*z^6 - 768*t^3*z^5 - 1024*t^3*z^4 + 3232*t^2*z^10 + 8880*t^2*z^9 - 2368*t^2*z^8 - 13696*t^2*z^7 + 2688*t^2*z^6 + 2560*t^2*z^5 - 1248*t*z^11 - 4848*t*z^10 + 2256*t*z^9 + 8832*t*z^8 + 384*t*z^7 - 8448*t*z^6 + 3072*t*z^5 + 192*z^12 + 1248*z^11 - 768*z^10 - 3744*z^9 + 3072*z^8 + 768*z^7 - 768*z^6:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 80*t^8*z - 352*t^8 + 176*t^7*z^3 + 944*t^7*z^2 + 4192*t^7*z + 18128*t^7 - 848*t^6*z^4 - 4912*t^6*z^3 - 21888*t^6*z^2 - 94704*t^6*z - 407856*t^6 + 2352*t^5*z^5 + 14656*t^5*z^4 + 65520*t^5*z^3 + 283120*t^5*z^2 + 1219040*t^5*z + 5245840*t^5 - 4112*t^4*z^6 - 27424*t^4*z^5 - 123072*t^4*z^4 - 529760*t^4*z^3 - 2279840*t^4*z^2 - 9809920*t^4*z - 42210080*t^4 + 4624*t^3*z^7 + 33008*t^3*z^6 + 148704*t^3*z^5 + 635408*t^3*z^4 + 2731696*t^3*z^3 + 11753280*t^3*z^2 + 50571312*t^3*z + 217596720*t^3 - 3232*t^2*z^8 - 25040*t^2*z^7 - 113136*t^2*z^6 - 476864*t^2*z^5 - 2047600*t^2*z^4 - 8809968*t^2*z^3 - 37907040*t^2*z^2 - 163105296*t^2*z - 701805360*t^2 + 1248*t*z^9 + 11088*t*z^8 + 49440*t*z^7 + 205104*t*z^6 + 876816*t*z^5 + 3777216*t*z^4 + 16252560*t*z^3 + 69931152*t*z^2 + 300898080*t*z + 1294696944*t - 192*z^10 - 2208*z^9 - 9696*z^8 - 38112*z^7 - 164544*z^6 - 709152*z^5 - 3051360*z^4 - 13129344*z^3 - 56492640*z^2 - 243075168*z - 1045897920)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_48 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 48) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_48 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z + 2*t*z^2 - 8*t*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8*z^4 + 80*t^7*z^5 - 192*t^7*z^4 + 144*t^6*z^6 - 640*t^6*z^5 + 704*t^6*z^4 + 112*t^5*z^7 - 640*t^5*z^6 + 1136*t^5*z^5 - 576*t^5*z^4 + 16*t^4*z^8 + 16*t^4*z^7 - 528*t^4*z^6 + 1440*t^4*z^5 - 1312*t^4*z^4 - 48*t^3*z^9 + 624*t^3*z^8 - 2848*t^3*z^7 + 5632*t^3*z^6 - 4816*t^3*z^5 + 1728*t^3*z^4 - 32*t^2*z^10 + 432*t^2*z^9 - 2192*t^2*z^8 + 5152*t^2*z^7 - 5392*t^2*z^6 + 1600*t^2*z^5 + 448*t^2*z^4 - 32*t*z^10 + 464*t*z^9 - 2608*t*z^8 + 7088*t*z^7 - 9344*t*z^6 + 5136*t*z^5 - 960*t*z^4 - 16*z^9 + 192*z^8 - 816*z^7 + 1424*z^6 - 864*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 80*t^8*z - 352*t^8 - 80*t^7*z^3 - 208*t^7*z^2 - 800*t^7*z - 3376*t^7 - 144*t^6*z^4 - 80*t^6*z^3 - 672*t^6*z^2 - 3120*t^6*z - 13584*t^6 - 112*t^5*z^5 + 80*t^5*z^4 - 400*t^5*z^3 - 1664*t^5*z^2 - 7120*t^5*z - 30608*t^5 - 16*t^4*z^6 - 96*t^4*z^5 + 96*t^4*z^4 - 672*t^4*z^3 - 2336*t^4*z^2 - 9664*t^4*z - 41312*t^4 + 48*t^3*z^7 - 384*t^3*z^6 + 784*t^3*z^5 - 560*t^3*z^4 - 336*t^3*z^3 - 1728*t^3*z^2 - 7632*t^3*z - 32976*t^3 + 32*t^2*z^8 - 272*t^2*z^7 + 736*t^2*z^6 - 656*t^2*z^5 - 96*t^2*z^4 - 112*t^2*z^3 - 720*t^2*z^2 - 3264*t^2*z - 14160*t^2 + 32*t*z^8 - 304*t*z^7 + 992*t*z^6 - 1216*t*z^5 + 288*t*z^4 - 48*t*z^3 - 144*t*z^2 - 576*t*z - 2448*t + 16*z^7 - 112*z^6 + 208*z^5 - 48*z^4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_49 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 49) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_49 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z + 4*t*z^2 - 8*t*z + 2*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4*t - 2)*hf
  · have hr : (16*t^8*z^4 + 144*t^7*z^5 - 192*t^7*z^4 + 544*t^6*z^6 - 1344*t^6*z^5 + 704*t^6*z^4 + 1136*t^5*z^7 - 3904*t^5*z^6 + 3632*t^5*z^5 - 576*t^5*z^4 + 1424*t^4*z^8 - 5968*t^4*z^7 + 7120*t^4*z^6 - 1120*t^4*z^5 - 1312*t^4*z^4 + 1056*t^3*z^9 - 4720*t^3*z^8 + 4848*t^3*z^7 + 3840*t^3*z^6 - 7184*t^3*z^5 + 1728*t^3*z^4 + 416*t^2*z^10 - 1456*t^2*z^9 - 1776*t^2*z^8 + 12480*t^2*z^7 - 15872*t^2*z^6 + 5760*t^2*z^5 + 448*t^2*z^4 + 64*t*z^11 + 128*t*z^10 - 2848*t*z^9 + 8016*t*z^8 - 6080*t*z^7 - 3776*t*z^6 + 5456*t*z^5 - 960*t*z^4 + 96*z^11 - 672*z^10 + 1488*z^9 - 576*z^8 - 2064*z^7 + 2832*z^6 - 1248*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 80*t^8*z - 352*t^8 - 144*t^7*z^3 - 528*t^7*z^2 - 2208*t^7*z - 9456*t^7 - 544*t^6*z^4 - 1376*t^6*z^3 - 5952*t^6*z^2 - 25632*t^6*z - 110304*t^6 - 1136*t^5*z^5 - 1776*t^5*z^4 - 9104*t^5*z^3 - 39616*t^5*z^2 - 170768*t^5*z - 734992*t^5 - 1424*t^4*z^6 - 1152*t^4*z^5 - 8608*t^4*z^4 - 38464*t^4*z^3 - 165184*t^4*z^2 - 710528*t^4*z - 3057088*t^4 - 1056*t^3*z^7 - 560*t^3*z^6 - 4480*t^3*z^5 - 24560*t^3*z^4 - 102176*t^3*z^3 - 438928*t^3*z^2 - 1888112*t^3*z - 8123776*t^3 - 416*t^2*z^8 - 624*t^2*z^7 - 96*t^2*z^6 - 11088*t^2*z^5 - 39280*t^2*z^4 - 168896*t^2*z^3 - 727088*t^2*z^2 - 3128752*t^2*z - 13462496*t^2 - 64*t*z^9 - 448*t*z^8 + 800*t*z^7 - 2672*t*z^6 - 9680*t*z^5 - 36608*t*z^4 - 159456*t*z^3 - 686496*t*z^2 - 2954112*t*z - 12711072*t - 96*z^9 + 192*z^8 - 240*z^7 - 1200*z^6 - 3216*z^5 - 15312*z^4 - 65664*z^3 - 282528*z^2 - 1215648*z - 5230656)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_50 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 50) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_50 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 6*t*z + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8*z^4 + 16*t^7*z^5 - 128*t^7*z^4 - 64*t^6*z^6 + 304*t^6*z^5 - 96*t^6*z^4 + 64*t^6*z^3 - 48*t^5*z^7 + 656*t^5*z^6 - 2416*t^5*z^5 + 2224*t^5*z^4 - 384*t^5*z^3 + 80*t^4*z^8 - 816*t^4*z^7 + 2544*t^4*z^6 - 2352*t^4*z^5 + 656*t^4*z^4 - 576*t^4*z^3 + 96*t^4*z^2 + 32*t^3*z^9 - 688*t^3*z^8 + 5168*t^3*z^7 - 17392*t^3*z^6 + 26944*t^3*z^5 - 18064*t^3*z^4 + 4656*t^3*z^3 - 384*t^3*z^2 - 32*t^2*z^10 + 560*t^2*z^9 - 3792*t^2*z^8 + 12496*t^2*z^7 - 20848*t^2*z^6 + 17600*t^2*z^5 - 9120*t^2*z^4 + 3952*t^2*z^3 - 864*t^2*z^2 + 64*t^2*z + 64*t*z^10 - 1200*t*z^9 + 9104*t*z^8 - 35760*t*z^7 + 77408*t*z^6 - 91600*t*z^5 + 56720*t*z^4 - 17312*t*z^3 + 2448*t*z^2 - 128*t*z - 32*z^11 + 640*z^10 - 5312*z^9 + 23696*z^8 - 61744*z^7 + 96592*z^6 - 91536*z^5 + 52816*z^4 - 18368*z^3 + 3680*z^2 - 384*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 80*t^8*z - 352*t^8 - 16*t^7*z^3 + 48*t^7*z^2 + 288*t^7*z + 1296*t^7 + 64*t^6*z^4 + 16*t^6*z^3 - 16*t^6*z^2 - 192*t^6*z - 912*t^6 + 48*t^5*z^5 - 416*t^5*z^4 + 192*t^5*z^3 - 16*t^5*z^2 - 272*t^5*z - 1312*t^5 - 80*t^4*z^6 + 416*t^4*z^5 - 224*t^4*z^4 - 16*t^4*z^3 - 64*t^4*z^2 + 304*t^4*z + 1616*t^4 - 32*t^3*z^7 + 528*t^3*z^6 - 2432*t^3*z^5 + 3648*t^3*z^4 - 1408*t^3*z^3 + 80*t^3*z^2 - 32*t^3*z - 16*t^3 + 32*t^2*z^8 - 400*t^2*z^7 + 1696*t^2*z^6 - 2816*t^2*z^5 + 1680*t^2*z^4 - 752*t^2*z^3 + 320*t^2*z^2 - 96*t^2*z - 576*t^2 - 64*t*z^8 + 880*t*z^7 - 4512*t*z^6 + 10560*t*z^5 - 11072*t*z^4 + 4560*t*z^3 - 704*t*z^2 + 112*t*z + 224*t + 32*z^9 - 480*z^8 + 2816*z^7 - 8176*z^6 + 12416*z^5 - 9984*z^4 + 4368*z^3 - 1024*z^2 + 144*z + 112)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_51 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 51) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_51 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 6*t*z - 4*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 + 64*t^7*z - 128*t^7 + 96*t^6*z^3 - 640*t^6*z + 448*t^6 + 272*t^5*z^4 - 608*t^5*z^3 - 976*t^5*z^2 + 2496*t^5*z - 896*t^5 - 16*t^4*z^6 + 592*t^4*z^5 - 2160*t^4*z^4 + 640*t^4*z^3 + 5088*t^4*z^2 - 5120*t^4*z + 1120*t^4 - 16*t^3*z^8 + 144*t^3*z^7 + 128*t^3*z^6 - 2752*t^3*z^5 + 4384*t^3*z^4 + 3648*t^3*z^3 - 11152*t^3*z^2 + 6080*t^3*z - 896*t^3 - 32*t^2*z^9 + 336*t^2*z^8 - 816*t^2*z^7 - 1248*t^2*z^6 + 5984*t^2*z^5 - 1632*t^2*z^4 - 11168*t^2*z^3 + 12352*t^2*z^2 - 4224*t^2*z + 448*t^2 - 32*t*z^10 + 416*t*z^9 - 1904*t*z^8 + 3376*t*z^7 - 640*t*z^6 - 2496*t*z^5 - 4656*t*z^4 + 11296*t*z^3 - 6832*t*z^2 + 1600*t*z - 128*t - 32*z^10 + 448*z^9 - 2384*z^8 + 6000*z^7 - 6928*z^6 + 1744*z^5 + 3792*z^4 - 3904*z^3 + 1504*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 - 96*t^6*z - 480*t^6 - 272*t^5*z^2 - 752*t^5*z - 1968*t^5 + 16*t^4*z^4 - 512*t^4*z^3 - 448*t^4*z^2 - 1344*t^4*z - 10464*t^4 + 16*t^3*z^6 - 64*t^3*z^5 - 496*t^3*z^4 + 464*t^3*z^3 - 576*t^3*z^2 - 7920*t^3*z - 26720*t^3 + 32*t^2*z^7 - 176*t^2*z^6 - 160*t^2*z^5 + 976*t^2*z^4 - 624*t^2*z^3 - 4416*t^2*z^2 - 9040*t^2*z - 44304*t^2 + 32*t*z^8 - 256*t*z^7 + 528*t*z^6 + 32*t*z^5 - 784*t*z^4 - 1520*t*z^3 - 592*t*z^2 - 9696*t*z - 39872*t + 32*z^8 - 288*z^7 + 848*z^6 - 896*z^5 - 96*z^4 + 464*z^3 - 1184*z^2 - 3408*z - 14992)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_52 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 52) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_52 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z + 4*t*z^2 - 8*t*z + 2*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4*t - 2)*hf
  · have hr : (16*t^8*z^4 + 144*t^7*z^5 - 192*t^7*z^4 + 480*t^6*z^6 - 1088*t^6*z^5 + 704*t^6*z^4 + 704*t^5*z^7 - 1600*t^5*z^6 + 1328*t^5*z^5 - 576*t^5*z^4 + 368*t^4*z^8 + 656*t^4*z^7 - 3824*t^4*z^6 + 4256*t^4*z^5 - 1312*t^4*z^4 - 80*t^3*z^9 + 2640*t^3*z^8 - 8112*t^3*z^7 + 10496*t^3*z^6 - 6672*t^3*z^5 + 1728*t^3*z^4 - 96*t^2*z^10 + 1072*t^2*z^9 - 1296*t^2*z^8 - 1600*t^2*z^7 + 4160*t^2*z^6 - 2688*t^2*z^5 + 448*t^2*z^4 - 208*t*z^10 + 2336*t*z^9 - 7216*t*z^8 + 11536*t*z^7 - 10688*t*z^6 + 5200*t*z^5 - 960*t*z^4 - 96*z^10 + 912*z^9 - 2112*z^8 + 1680*z^7 - 48*z^6 - 480*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 80*t^8*z - 352*t^8 - 144*t^7*z^3 - 528*t^7*z^2 - 2208*t^7*z - 9456*t^7 - 480*t^6*z^4 - 1312*t^6*z^3 - 5824*t^6*z^2 - 25184*t^6*z - 108448*t^6 - 704*t^5*z^5 - 1920*t^5*z^4 - 8816*t^5*z^3 - 37744*t^5*z^2 - 162272*t^5*z - 698128*t^5 - 368*t^4*z^6 - 2496*t^4*z^5 - 7552*t^4*z^4 - 34528*t^4*z^3 - 148672*t^4*z^2 - 639776*t^4*z - 2752864*t^4 + 80*t^3*z^7 - 2240*t^3*z^6 - 3328*t^3*z^5 - 20416*t^3*z^4 - 85424*t^3*z^3 - 367600*t^3*z^2 - 1581728*t^3*z - 6805840*t^3 + 96*t^2*z^8 - 592*t^2*z^7 - 1952*t^2*z^6 - 6384*t^2*z^5 - 30224*t^2*z^4 - 129280*t^2*z^3 - 556176*t^2*z^2 - 2393040*t^2*z - 10296672*t^2 + 208*t*z^8 - 1296*t*z^7 + 112*t*z^6 - 7088*t*z^5 - 25088*t*z^4 - 109376*t*z^3 - 470656*t*z^2 - 2025152*t*z - 8713792*t + 96*z^8 - 432*z^7 - 336*z^6 - 2064*z^5 - 9264*z^4 - 39648*z^3 - 170592*z^2 - 734016*z - 3158304)*hf
  · have hr : (16*t^8*z^4 + 144*t^7*z^5 - 192*t^7*z^4 + 544*t^6*z^6 - 1344*t^6*z^5 + 704*t^6*z^4 + 1136*t^5*z^7 - 3904*t^5*z^6 + 3632*t^5*z^5 - 576*t^5*z^4 + 1424*t^4*z^8 - 5968*t^4*z^7 + 7120*t^4*z^6 - 1120*t^4*z^5 - 1312*t^4*z^4 + 1056*t^3*z^9 - 4720*t^3*z^8 + 4848*t^3*z^7 + 3840*t^3*z^6 - 7184*t^3*z^5 + 1728*t^3*z^4 + 416*t^2*z^10 - 1456*t^2*z^9 - 1776*t^2*z^8 + 12480*t^2*z^7 - 15872*t^2*z^6 + 5760*t^2*z^5 + 448*t^2*z^4 + 64*t*z^11 + 128*t*z^10 - 2848*t*z^9 + 8016*t*z^8 - 6080*t*z^7 - 3776*t*z^6 + 5456*t*z^5 - 960*t*z^4 + 96*z^11 - 672*z^10 + 1488*z^9 - 576*z^8 - 2064*z^7 + 2832*z^6 - 1248*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 80*t^8*z - 352*t^8 - 144*t^7*z^3 - 528*t^7*z^2 - 2208*t^7*z - 9456*t^7 - 544*t^6*z^4 - 1376*t^6*z^3 - 5952*t^6*z^2 - 25632*t^6*z - 110304*t^6 - 1136*t^5*z^5 - 1776*t^5*z^4 - 9104*t^5*z^3 - 39616*t^5*z^2 - 170768*t^5*z - 734992*t^5 - 1424*t^4*z^6 - 1152*t^4*z^5 - 8608*t^4*z^4 - 38464*t^4*z^3 - 165184*t^4*z^2 - 710528*t^4*z - 3057088*t^4 - 1056*t^3*z^7 - 560*t^3*z^6 - 4480*t^3*z^5 - 24560*t^3*z^4 - 102176*t^3*z^3 - 438928*t^3*z^2 - 1888112*t^3*z - 8123776*t^3 - 416*t^2*z^8 - 624*t^2*z^7 - 96*t^2*z^6 - 11088*t^2*z^5 - 39280*t^2*z^4 - 168896*t^2*z^3 - 727088*t^2*z^2 - 3128752*t^2*z - 13462496*t^2 - 64*t*z^9 - 448*t*z^8 + 800*t*z^7 - 2672*t*z^6 - 9680*t*z^5 - 36608*t*z^4 - 159456*t*z^3 - 686496*t*z^2 - 2954112*t*z - 12711072*t - 96*z^9 + 192*z^8 - 240*z^7 - 1200*z^6 - 3216*z^5 - 15312*z^4 - 65664*z^3 - 282528*z^2 - 1215648*z - 5230656)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_53 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 53) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : (t + 2*z - 3:ℝ)=0 := by
  apply cell_11_53 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z + 6*t*z^2 - 8*t*z + 2*z^3:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-6*t - 2*z - 10)*hf
  · have hr : (16*t^8*z^4 + 208*t^7*z^5 - 192*t^7*z^4 + 1136*t^6*z^6 - 1920*t^6*z^5 + 704*t^6*z^4 + 3408*t^5*z^7 - 7840*t^5*z^6 + 4976*t^5*z^5 - 576*t^5*z^4 + 6128*t^4*z^8 - 16752*t^4*z^7 + 13040*t^4*z^6 - 992*t^4*z^5 - 1312*t^4*z^4 + 6704*t^3*z^9 - 19568*t^3*z^8 + 13600*t^3*z^7 + 6848*t^3*z^6 - 9296*t^3*z^5 + 1728*t^3*z^4 + 4288*t^2*z^10 - 11632*t^2*z^9 + 848*t^2*z^8 + 22944*t^2*z^7 - 22576*t^2*z^6 + 5696*t^2*z^5 + 448*t^2*z^4 + 1440*t*z^11 - 2816*t*z^10 - 5776*t*z^9 + 18096*t*z^8 - 11376*t*z^7 - 4384*t*z^6 + 5648*t*z^5 - 960*t*z^4 + 192*z^12 - 96*z^11 - 2048*z^10 + 3984*z^9 - 1280*z^8 - 2608*z^7 + 3024*z^6 - 1248*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 80*t^8*z - 352*t^8 - 208*t^7*z^3 - 848*t^7*z^2 - 3616*t^7*z - 15536*t^7 - 1136*t^6*z^4 - 3760*t^6*z^3 - 16096*t^6*z^2 - 69200*t^6*z - 297712*t^6 - 3408*t^5*z^5 - 9200*t^5*z^4 - 40752*t^5*z^3 - 175584*t^5*z^2 - 755664*t^5*z - 3251568*t^5 - 6128*t^4*z^6 - 13888*t^4*z^5 - 64096*t^4*z^4 - 277824*t^4*z^3 - 1195520*t^4*z^2 - 5144128*t^4*z - 22134080*t^4 - 6704*t^3*z^7 - 13952*t^3*z^6 - 63248*t^3*z^5 - 281232*t^3*z^4 - 1207120*t^3*z^3 - 5193632*t^3*z^2 - 22346800*t^3*z - 96153104*t^3 - 4288*t^2*z^8 - 9808*t^2*z^7 - 37024*t^2*z^6 - 178640*t^2*z^5 - 759552*t^2*z^4 - 3267536*t^2*z^3 - 14059472*t^2*z^2 - 60494752*t^2*z - 260295344*t^2 - 1440*t*z^9 - 4384*t*z^8 - 11824*t*z^7 - 64064*t*z^6 - 273472*t*z^5 - 1170784*t*z^4 - 5039152*t*z^3 - 21682448*t*z^2 - 93294784*t*z - 401426576*t - 192*z^10 - 864*z^9 - 1696*z^8 - 9872*z^7 - 42992*z^6 - 182736*z^5 - 787728*z^4 - 3389184*z^3 - 14582880*z^2 - 62746848*z - 269985600)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_54 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 54) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_54 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z + 2*t*z^2 - 6*t*z - 2*z^3 + 10*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t + 2*z)*hf
  · have hr : (16*t^8*z^4 + 80*t^7*z^5 - 128*t^7*z^4 + 16*t^6*z^6 + 240*t^6*z^5 - 224*t^6*z^4 + 64*t^6*z^3 - 368*t^5*z^7 + 2816*t^5*z^6 - 5392*t^5*z^5 + 3184*t^5*z^4 - 384*t^5*z^3 - 176*t^4*z^8 + 704*t^4*z^7 + 928*t^4*z^6 - 2832*t^4*z^5 + 2384*t^4*z^4 - 960*t^4*z^3 + 96*t^4*z^2 + 688*t^3*z^9 - 8976*t^3*z^8 + 41392*t^3*z^7 - 83344*t^3*z^6 + 79584*t^3*z^5 - 35344*t^3*z^4 + 6384*t^3*z^3 - 384*t^3*z^2 + 96*t^2*z^10 - 256*t^2*z^9 - 5264*t^2*z^8 + 30848*t^2*z^7 - 59184*t^2*z^6 + 55328*t^2*z^5 - 29136*t^2*z^4 + 8752*t^2*z^3 - 1248*t^2*z^2 + 64*t^2*z - 544*t*z^11 + 9568*t*z^10 - 67184*t*z^9 + 242432*t*z^8 - 488912*t*z^7 + 573648*t*z^6 - 393920*t*z^5 + 153888*t*z^4 - 32128*t*z^3 + 3280*t*z^2 - 128*t*z + 192*z^12 - 4128*z^11 + 36544*z^10 - 172288*z^9 + 470416*z^8 - 769840*z^7 + 775152*z^6 - 487664*z^5 + 192080*z^4 - 46656*z^3 + 6688*z^2 - 512*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 80*t^8*z - 352*t^8 - 80*t^7*z^3 - 272*t^7*z^2 - 1120*t^7*z - 4784*t^7 - 16*t^6*z^4 - 320*t^6*z^3 - 1328*t^6*z^2 - 5744*t^6*z - 24736*t^6 + 368*t^5*z^5 - 976*t^5*z^4 - 592*t^5*z^3 - 3216*t^5*z^2 - 13920*t^5*z - 59952*t^5 + 176*t^4*z^6 + 176*t^4*z^5 - 576*t^4*z^4 - 576*t^4*z^3 - 3536*t^4*z^2 - 14992*t^4*z - 64448*t^4 - 688*t^3*z^7 + 5536*t^3*z^6 - 11648*t^3*z^5 + 8496*t^3*z^4 - 2160*t^3*z^3 - 944*t^3*z^2 - 4624*t^3*z - 19904*t^3 - 96*t^2*z^8 - 224*t^2*z^7 + 4432*t^2*z^6 - 8016*t^2*z^5 + 5808*t^2*z^4 - 2240*t^2*z^3 + 512*t^2*z^2 + 528*t^2*z + 2352*t^2 + 544*t*z^9 - 6848*t*z^8 + 31312*t*z^7 - 65328*t*z^6 + 68336*t*z^5 - 35984*t*z^4 + 8992*t*z^3 - 976*t*z^2 + 272*t*z + 1008*t - 192*z^10 + 3168*z^9 - 20128*z^8 + 62144*z^7 - 99312*z^6 + 86848*z^5 - 42976*z^4 + 12240*z^3 - 1952*z^2 + 176*z + 48)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_55 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 55) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_55 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 2*t*z - 4*t + 4*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t - 4)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 + 192*t^7*z - 128*t^7 + 192*t^6*z^3 + 960*t^6*z^2 - 1536*t^6*z + 448*t^6 + 992*t^5*z^4 + 2496*t^5*z^3 - 7888*t^5*z^2 + 5184*t^5*z - 896*t^5 - 16*t^4*z^6 + 2960*t^4*z^5 + 3216*t^4*z^4 - 22912*t^4*z^3 + 25248*t^4*z^2 - 9600*t^4*z + 1120*t^4 - 16*t^3*z^8 + 80*t^3*z^7 + 4880*t^3*z^6 + 1920*t^3*z^5 - 42496*t^3*z^4 + 67968*t^3*z^3 - 41872*t^3*z^2 + 10560*t^3*z - 896*t^3 - 64*t^2*z^9 + 464*t^2*z^8 + 3952*t^2*z^7 + 1600*t^2*z^6 - 53920*t^2*z^5 + 111328*t^2*z^4 - 95296*t^2*z^3 + 38272*t^2*z^2 - 6912*t^2*z + 448*t^2 - 80*t*z^10 + 592*t*z^9 + 1360*t*z^8 + 2928*t*z^7 - 46192*t*z^6 + 109696*t*z^5 - 117088*t*z^4 + 64704*t*z^3 - 18352*t*z^2 + 2496*t*z - 128*t - 320*z^10 + 3712*z^9 - 9424*z^8 - 2096*z^7 + 38704*z^6 - 60656*z^5 + 44048*z^4 - 17152*z^3 + 3616*z^2 - 384*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 - 192*t^6*z - 1920*t^6 - 992*t^5*z^2 - 7456*t^5*z - 26416*t^5 + 16*t^4*z^4 - 2880*t^4*z^3 - 17664*t^4*z^2 - 56768*t^4*z - 256096*t^4 + 16*t^3*z^6 - 4928*t^3*z^4 - 26560*t^3*z^3 - 75520*t^3*z^2 - 365888*t^3*z - 1561008*t^3 + 64*t^2*z^7 - 144*t^2*z^6 - 4864*t^2*z^5 - 25488*t^2*z^4 - 58928*t^2*z^3 - 329504*t^2*z^2 - 1375440*t^2*z - 5926960*t^2 + 80*t*z^8 - 192*t*z^7 - 2560*t*z^6 - 15152*t*z^5 - 21888*t*z^4 - 173680*t*z^3 - 685648*t*z^2 - 2971904*t*z - 12784224*t + 320*z^8 - 2112*z^7 - 2096*z^6 - 2048*z^5 - 42656*z^4 - 146480*z^3 - 648480*z^2 - 2785808*z - 11987216)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_56 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 56) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_56 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 6*t*z + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8*z^4 + 16*t^7*z^5 - 128*t^7*z^4 - 16*t^6*z^5 + 160*t^6*z^4 + 64*t^6*z^3 + 32*t^5*z^6 - 304*t^5*z^5 + 688*t^5*z^4 - 384*t^5*z^3 - 16*t^4*z^8 + 144*t^4*z^7 - 432*t^4*z^6 + 720*t^4*z^5 - 1072*t^4*z^4 + 192*t^4*z^3 + 96*t^4*z^2 - 16*t^3*z^9 + 240*t^3*z^8 - 1232*t^3*z^7 + 2368*t^3*z^6 - 736*t^3*z^5 - 1552*t^3*z^4 + 1584*t^3*z^3 - 384*t^3*z^2 - 16*t^2*z^8 + 96*t^2*z^7 + 112*t^2*z^6 - 1440*t^2*z^5 + 2144*t^2*z^4 - 848*t^2*z^3 - 96*t^2*z^2 + 64*t^2*z - 16*t*z^10 + 288*t*z^9 - 2016*t*z^8 + 6832*t*z^7 - 11216*t*z^6 + 7456*t*z^5 - 480*t*z^4 - 1888*t*z^3 + 912*t*z^2 - 128*t*z - 16*z^8 + 208*z^7 - 976*z^6 + 1936*z^5 - 1392*z^4 + 128*z^3 + 288*z^2 - 128*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 80*t^8*z - 352*t^8 - 16*t^7*z^3 + 48*t^7*z^2 + 288*t^7*z + 1296*t^7 + 16*t^6*z^3 - 80*t^6*z^2 - 512*t^6*z - 2320*t^6 - 32*t^5*z^4 + 144*t^5*z^3 + 128*t^5*z^2 + 592*t^5*z + 2576*t^5 + 16*t^4*z^6 - 64*t^4*z^5 + 64*t^4*z^4 - 208*t^4*z^3 - 160*t^4*z^2 - 368*t^4*z - 1456*t^4 + 16*t^3*z^7 - 160*t^3*z^6 + 384*t^3*z^5 + 32*t^3*z^4 - 256*t^3*z^3 + 176*t^3*z^2 + 64*t^3*z + 176*t^3 + 16*t^2*z^6 - 16*t^2*z^5 - 240*t^2*z^4 + 288*t^2*z^3 + 16*t^2*z^2 + 64*t^2*z + 368*t^2 + 16*t*z^8 - 208*t*z^7 + 928*t*z^6 - 1568*t*z^5 + 592*t*z^4 + 208*t*z^3 - 256*t*z^2 - 16*t*z - 224*t + 16*z^6 - 128*z^5 + 288*z^4 - 112*z^3 - 32*z^2 + 48*z + 48)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_57 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 57) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_57 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z + 2*t*z^2 - 6*t*z - 2*z^3 + 10*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t + 2*z)*hf
  · have hr : (16*t^8*z^4 + 80*t^7*z^5 - 128*t^7*z^4 + 144*t^6*z^6 - 336*t^6*z^5 + 32*t^6*z^4 + 64*t^6*z^3 + 112*t^5*z^7 - 112*t^5*z^6 - 976*t^5*z^5 + 1648*t^5*z^4 - 384*t^5*z^3 + 16*t^4*z^8 + 416*t^4*z^7 - 2432*t^4*z^6 + 3888*t^4*z^5 - 1648*t^4*z^4 - 192*t^4*z^3 + 96*t^4*z^2 - 48*t^3*z^9 + 704*t^3*z^8 - 2720*t^3*z^7 + 2496*t^3*z^6 + 4288*t^3*z^5 - 8080*t^3*z^4 + 3312*t^3*z^3 - 384*t^3*z^2 - 32*t^2*z^10 + 352*t^2*z^9 - 960*t^2*z^8 - 1072*t^2*z^7 + 8176*t^2*z^6 - 11520*t^2*z^5 + 5360*t^2*z^4 + 112*t^2*z^3 - 480*t^2*z^2 + 64*t^2*z - 80*t*z^10 + 1120*t*z^9 - 5824*t*z^8 + 13584*t*z^7 - 11584*t*z^6 - 5856*t*z^5 + 15280*t*z^4 - 8256*t*z^3 + 1744*t*z^2 - 128*t*z - 32*z^10 + 448*z^9 - 2384*z^8 + 6000*z^7 - 6928*z^6 + 1744*z^5 + 3792*z^4 - 3904*z^3 + 1504*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 80*t^8*z - 352*t^8 - 80*t^7*z^3 - 272*t^7*z^2 - 1120*t^7*z - 4784*t^7 - 144*t^6*z^4 - 384*t^6*z^3 - 1520*t^6*z^2 - 6512*t^6*z - 28000*t^6 - 112*t^5*z^5 - 448*t^5*z^4 - 928*t^5*z^3 - 4944*t^5*z^2 - 21552*t^5*z - 92928*t^5 - 16*t^4*z^6 - 496*t^4*z^5 - 2400*t^4*z^3 - 10352*t^4*z^2 - 44368*t^4*z - 190880*t^4 + 48*t^3*z^7 - 464*t^3*z^6 + 256*t^3*z^5 + 176*t^3*z^4 - 4176*t^3*z^3 - 13328*t^3*z^2 - 57424*t^3*z - 246752*t^3 + 32*t^2*z^8 - 192*t^2*z^7 - 96*t^2*z^6 + 1168*t^2*z^5 - 2048*t^2*z^4 - 2224*t^2*z^3 - 10336*t^2*z^2 - 45120*t^2*z - 194112*t^2 + 80*t*z^8 - 720*t*z^7 + 1984*t*z^6 - 1504*t*z^5 - 1888*t*z^4 + 928*t*z^3 - 4976*t*z^2 - 19408*t*z - 83856*t + 32*z^8 - 288*z^7 + 848*z^6 - 896*z^5 - 96*z^4 + 464*z^3 - 1184*z^2 - 3408*z - 14992)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_58 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 58) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_58 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 2*t*z^2 - 4*t*z + 2*z^3 - 4*z^2 + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 2*z - 6)*hf
  · have hr : (16*t^8*z^4 - 48*t^7*z^5 - 64*t^7*z^4 + 48*t^6*z^6 + 288*t^6*z^5 - 128*t^6*z^4 - 16*t^5*z^7 - 400*t^5*z^6 - 64*t^5*z^5 + 512*t^5*z^4 - 16*t^4*z^8 + 336*t^4*z^7 + 336*t^4*z^6 - 1280*t^4*z^5 + 256*t^4*z^4 + 16*t^3*z^9 - 96*t^3*z^8 - 800*t^3*z^7 + 1920*t^3*z^6 + 256*t^3*z^5 - 1024*t^3*z^4 - 112*t^2*z^9 + 1152*t^2*z^8 - 2688*t^2*z^7 + 1152*t^2*z^6 + 512*t^2*z^5 + 16*t*z^10 - 16*t*z^9 - 1152*t*z^8 + 5248*t*z^7 - 7424*t*z^6 + 3072*t*z^5 - 32*z^10 + 352*z^9 - 1280*z^8 + 1792*z^7 - 768*z^6:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 80*t^8*z - 352*t^8 + 48*t^7*z^3 + 304*t^7*z^2 + 1376*t^7*z + 5968*t^7 - 48*t^6*z^4 - 528*t^6*z^3 - 2368*t^6*z^2 - 10256*t^6*z - 44176*t^6 + 16*t^5*z^5 + 480*t^5*z^4 + 2416*t^5*z^3 + 10128*t^5*z^2 + 43392*t^5*z + 186576*t^5 + 16*t^4*z^6 - 256*t^4*z^5 - 1664*t^4*z^4 - 6272*t^4*z^3 - 26624*t^4*z^2 - 114304*t^4*z - 491648*t^4 - 16*t^3*z^7 + 16*t^3*z^6 + 928*t^3*z^5 + 2672*t^3*z^4 + 10320*t^3*z^3 + 44608*t^3*z^2 + 192080*t^3*z + 826576*t^3 + 112*t^2*z^7 - 592*t^2*z^6 - 608*t^2*z^5 - 2416*t^2*z^4 - 10768*t^2*z^3 - 46592*t^2*z^2 - 200656*t^2*z - 863504*t^2 - 16*t*z^8 - 64*t*z^7 + 880*t*z^6 - 656*t*z^5 + 1504*t*z^4 + 6416*t*z^3 + 27568*t*z^2 + 118592*t*z + 510256*t + 32*z^8 - 192*z^7 + 224*z^6 - 96*z^5 - 384*z^4 - 1632*z^3 - 7008*z^2 - 30144*z - 129696)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_59 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 59) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_59 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 64*t^7*z + 32*t^6*z^2 - 128*t^6*z + 32*t^5*z^4 - 256*t^5*z^3 + 512*t^5*z^2 - 16*t^4*z^6 + 144*t^4*z^5 - 368*t^4*z^4 + 128*t^4*z^3 + 256*t^4*z^2 - 16*t^3*z^8 + 208*t^3*z^7 - 944*t^3*z^6 + 1600*t^3*z^5 - 256*t^3*z^4 - 1024*t^3*z^3 - 16*t^2*z^8 + 208*t^2*z^7 - 960*t^2*z^6 + 1792*t^2*z^5 - 1024*t^2*z^4 - 16*t*z^10 + 272*t*z^9 - 1792*t*z^8 + 5632*t*z^7 - 8192*t*z^6 + 4096*t*z^5:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 - 32*t^6 - 32*t^5*z^2 + 96*t^5*z + 64*t^5 + 16*t^4*z^4 - 64*t^4*z^3 + 64*t^4*z + 64*t^4 + 16*t^3*z^6 - 128*t^3*z^5 + 256*t^3*z^4 + 64*t^3*z^3 - 192*t^3*z^2 - 128*t^3*z - 64*t^3 + 16*t^2*z^6 - 128*t^2*z^5 + 272*t^2*z^4 - 48*t^2*z^3 - 32*t^2*z^2 - 16*t^2*z + 16*t^2 + 16*t*z^8 - 192*t*z^7 + 784*t*z^6 - 1136*t*z^5 + 160*t*z^4 + 112*t*z^3 + 80*t*z^2 + 64*t*z + 80*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_60 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 60) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_60 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 6*t*z - 4*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 192*t^7*z - 128*t^7 + 144*t^6*z^4 - 672*t^6*z^3 + 320*t^6*z^2 + 1152*t^6*z + 448*t^6 + 112*t^5*z^6 - 768*t^5*z^5 + 1280*t^5*z^4 + 1056*t^5*z^3 - 1936*t^5*z^2 - 2880*t^5*z - 896*t^5 + 32*t^4*z^8 - 288*t^4*z^7 + 880*t^4*z^6 - 560*t^4*z^5 - 1424*t^4*z^4 - 256*t^4*z^3 + 2848*t^4*z^2 + 3840*t^4*z + 1120*t^4 + 16*t^3*z^8 + 80*t^3*z^7 - 1120*t^3*z^6 + 2752*t^3*z^5 - 1280*t^3*z^4 - 192*t^3*z^3 - 1232*t^3*z^2 - 2880*t^3*z - 896*t^3 - 32*t^2*z^10 + 448*t^2*z^9 - 2288*t^2*z^8 + 5008*t^2*z^7 - 3232*t^2*z^6 - 3104*t^2*z^5 + 2800*t^2*z^4 + 608*t^2*z^3 - 512*t^2*z^2 + 1152*t^2*z + 448*t^2 - 32*t*z^10 + 416*t*z^9 - 2064*t*z^8 + 5104*t*z^7 - 7056*t*z^6 + 5568*t*z^5 - 1280*t*z^4 - 864*t*z^3 + 528*t*z^2 - 192*t*z - 128*t - 32*z^9 + 336*z^8 - 1200*z^7 + 1712*z^6 - 816*z^5 - 240*z^4 + 320*z^3 - 96*z^2 + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 - 48*t^6*z - 128*t^6 - 112*t^5*z^4 + 208*t^5*z^3 + 96*t^5*z^2 - 1200*t^5*z - 4352*t^5 - 32*t^4*z^6 + 128*t^4*z^5 - 144*t^4*z^4 - 544*t^4*z^3 - 864*t^4*z^2 - 2432*t^4*z - 12416*t^4 - 16*t^3*z^6 - 160*t^3*z^5 + 368*t^3*z^4 - 432*t^3*z^3 - 1984*t^3*z^2 - 8432*t^3*z - 34976*t^3 + 32*t^2*z^8 - 288*t^2*z^7 + 752*t^2*z^6 - 384*t^2*z^5 - 944*t^2*z^4 - 464*t^2*z^3 - 2288*t^2*z^2 - 10656*t^2*z - 45904*t^2 + 32*t*z^8 - 256*t*z^7 + 688*t*z^6 - 896*t*z^5 + 512*t*z^4 - 320*t*z^3 - 1856*t*z^2 - 7456*t*z - 32240*t + 32*z^7 - 176*z^6 + 224*z^5 - 64*z^4 - 176*z^3 - 448*z^2 - 2032*z - 8720)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 + 64*t^7*z - 128*t^7 + 96*t^6*z^3 - 640*t^6*z + 448*t^6 + 272*t^5*z^4 - 608*t^5*z^3 - 976*t^5*z^2 + 2496*t^5*z - 896*t^5 - 16*t^4*z^6 + 592*t^4*z^5 - 2160*t^4*z^4 + 640*t^4*z^3 + 5088*t^4*z^2 - 5120*t^4*z + 1120*t^4 - 16*t^3*z^8 + 144*t^3*z^7 + 128*t^3*z^6 - 2752*t^3*z^5 + 4384*t^3*z^4 + 3648*t^3*z^3 - 11152*t^3*z^2 + 6080*t^3*z - 896*t^3 - 32*t^2*z^9 + 336*t^2*z^8 - 816*t^2*z^7 - 1248*t^2*z^6 + 5984*t^2*z^5 - 1632*t^2*z^4 - 11168*t^2*z^3 + 12352*t^2*z^2 - 4224*t^2*z + 448*t^2 - 32*t*z^10 + 416*t*z^9 - 1904*t*z^8 + 3376*t*z^7 - 640*t*z^6 - 2496*t*z^5 - 4656*t*z^4 + 11296*t*z^3 - 6832*t*z^2 + 1600*t*z - 128*t - 32*z^10 + 448*z^9 - 2384*z^8 + 6000*z^7 - 6928*z^6 + 1744*z^5 + 3792*z^4 - 3904*z^3 + 1504*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 - 96*t^6*z - 480*t^6 - 272*t^5*z^2 - 752*t^5*z - 1968*t^5 + 16*t^4*z^4 - 512*t^4*z^3 - 448*t^4*z^2 - 1344*t^4*z - 10464*t^4 + 16*t^3*z^6 - 64*t^3*z^5 - 496*t^3*z^4 + 464*t^3*z^3 - 576*t^3*z^2 - 7920*t^3*z - 26720*t^3 + 32*t^2*z^7 - 176*t^2*z^6 - 160*t^2*z^5 + 976*t^2*z^4 - 624*t^2*z^3 - 4416*t^2*z^2 - 9040*t^2*z - 44304*t^2 + 32*t*z^8 - 256*t*z^7 + 528*t*z^6 + 32*t*z^5 - 784*t*z^4 - 1520*t*z^3 - 592*t*z^2 - 9696*t*z - 39872*t + 32*z^8 - 288*z^7 + 848*z^6 - 896*z^5 - 96*z^4 + 464*z^3 - 1184*z^2 - 3408*z - 14992)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_61 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 61) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_61 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 2*t*z - 4*t + 4*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t - 4)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 64*t^7*z - 128*t^7 + 144*t^6*z^4 - 128*t^6*z^3 - 512*t^6*z^2 + 256*t^6*z + 448*t^6 + 112*t^5*z^6 + 48*t^5*z^5 - 880*t^5*z^4 - 64*t^5*z^3 + 1904*t^5*z^2 - 192*t^5*z - 896*t^5 + 32*t^4*z^8 + 224*t^4*z^7 - 656*t^4*z^6 - 1040*t^4*z^5 + 2352*t^4*z^4 + 2112*t^4*z^3 - 3872*t^4*z^2 - 640*t^4*z + 1120*t^4 + 112*t^3*z^9 - 48*t^3*z^8 - 688*t^3*z^7 - 1264*t^3*z^6 + 6048*t^3*z^5 - 2208*t^3*z^4 - 6272*t^3*z^3 + 3888*t^3*z^2 + 1600*t^3*z - 896*t^3 + 112*t^2*z^10 + 64*t^2*z^9 - 2016*t^2*z^8 + 2384*t^2*z^7 + 4960*t^2*z^6 - 8480*t^2*z^5 - 2128*t^2*z^4 + 7680*t^2*z^3 - 1472*t^2*z^2 - 1536*t^2*z + 448*t^2 + 32*t*z^11 + 336*t*z^10 - 2224*t*z^9 + 2208*t*z^8 + 6704*t*z^7 - 14560*t*z^6 + 5808*t*z^5 + 5008*t*z^4 - 3904*t*z^3 - 240*t*z^2 + 704*t*z - 128*t + 128*z^11 - 576*z^10 + 288*z^9 + 2192*z^8 - 4272*z^7 + 2192*z^6 + 1712*z^5 - 2288*z^4 + 576*z^3 + 224*z^2 - 128*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 - 592*t^6*z - 2016*t^6 - 112*t^5*z^4 - 608*t^5*z^3 - 1824*t^5*z^2 - 7232*t^5*z - 32592*t^5 - 32*t^4*z^6 - 384*t^4*z^5 - 1168*t^4*z^4 - 3648*t^4*z^3 - 17088*t^4*z^2 - 76608*t^4*z - 327904*t^4 - 112*t^3*z^7 - 512*t^3*z^6 - 1536*t^3*z^5 - 4880*t^3*z^4 - 25840*t^3*z^3 - 112352*t^3*z^2 - 477968*t^3*z - 2056672*t^3 - 112*t^2*z^8 - 624*t^2*z^7 - 768*t^2*z^6 - 4352*t^2*z^5 - 24416*t^2*z^4 - 100544*t^2*z^3 - 427344*t^2*z^2 - 1842768*t^2*z - 7930336*t^2 - 32*t*z^9 - 496*t*z^8 - 160*t*z^7 - 1520*t*z^6 - 13824*t*z^5 - 50000*t*z^4 - 214336*t*z^3 - 926688*t*z^2 - 3986528*t*z - 17152336*t - 128*z^9 - 64*z^8 - 224*z^7 - 3120*z^6 - 10656*z^5 - 46112*z^4 - 200304*z^3 - 860896*z^2 - 3704144*z - 15938256)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 + 192*t^7*z - 128*t^7 + 192*t^6*z^3 + 960*t^6*z^2 - 1536*t^6*z + 448*t^6 + 992*t^5*z^4 + 2496*t^5*z^3 - 7888*t^5*z^2 + 5184*t^5*z - 896*t^5 - 16*t^4*z^6 + 2960*t^4*z^5 + 3216*t^4*z^4 - 22912*t^4*z^3 + 25248*t^4*z^2 - 9600*t^4*z + 1120*t^4 - 16*t^3*z^8 + 80*t^3*z^7 + 4880*t^3*z^6 + 1920*t^3*z^5 - 42496*t^3*z^4 + 67968*t^3*z^3 - 41872*t^3*z^2 + 10560*t^3*z - 896*t^3 - 64*t^2*z^9 + 464*t^2*z^8 + 3952*t^2*z^7 + 1600*t^2*z^6 - 53920*t^2*z^5 + 111328*t^2*z^4 - 95296*t^2*z^3 + 38272*t^2*z^2 - 6912*t^2*z + 448*t^2 - 80*t*z^10 + 592*t*z^9 + 1360*t*z^8 + 2928*t*z^7 - 46192*t*z^6 + 109696*t*z^5 - 117088*t*z^4 + 64704*t*z^3 - 18352*t*z^2 + 2496*t*z - 128*t - 320*z^10 + 3712*z^9 - 9424*z^8 - 2096*z^7 + 38704*z^6 - 60656*z^5 + 44048*z^4 - 17152*z^3 + 3616*z^2 - 384*z + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 - 192*t^6*z - 1920*t^6 - 992*t^5*z^2 - 7456*t^5*z - 26416*t^5 + 16*t^4*z^4 - 2880*t^4*z^3 - 17664*t^4*z^2 - 56768*t^4*z - 256096*t^4 + 16*t^3*z^6 - 4928*t^3*z^4 - 26560*t^3*z^3 - 75520*t^3*z^2 - 365888*t^3*z - 1561008*t^3 + 64*t^2*z^7 - 144*t^2*z^6 - 4864*t^2*z^5 - 25488*t^2*z^4 - 58928*t^2*z^3 - 329504*t^2*z^2 - 1375440*t^2*z - 5926960*t^2 + 80*t*z^8 - 192*t*z^7 - 2560*t*z^6 - 15152*t*z^5 - 21888*t*z^4 - 173680*t*z^3 - 685648*t*z^2 - 2971904*t*z - 12784224*t + 320*z^8 - 2112*z^7 - 2096*z^6 - 2048*z^5 - 42656*z^4 - 146480*z^3 - 648480*z^2 - 2785808*z - 11987216)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_62 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 62) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_62 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 320*t^7*z + 144*t^6*z^4 - 1216*t^6*z^3 + 2592*t^6*z^2 - 128*t^6*z + 112*t^5*z^6 - 1584*t^5*z^5 + 7424*t^5*z^4 - 12032*t^5*z^3 + 2048*t^5*z^2 + 32*t^4*z^8 - 800*t^4*z^7 + 6768*t^4*z^6 - 24656*t^4*z^5 + 36240*t^4*z^4 - 11648*t^4*z^3 + 256*t^4*z^2 - 112*t^3*z^9 + 2048*t^3*z^8 - 14288*t^3*z^7 + 46576*t^3*z^6 - 67904*t^3*z^5 + 32000*t^3*z^4 - 3072*t^3*z^3 + 112*t^2*z^10 - 1952*t^2*z^9 + 13264*t^2*z^8 - 43600*t^2*z^7 + 69056*t^2*z^6 - 44800*t^2*z^5 + 9216*t^2*z^4 - 32*t*z^11 + 560*t*z^10 - 3856*t*z^9 + 13056*t*z^8 - 22016*t*z^7 + 16384*t*z^6 - 4096*t*z^5:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 + 496*t^6*z + 320*t^6 - 112*t^5*z^4 + 1024*t^5*z^3 - 1968*t^5*z^2 - 880*t^5*z - 544*t^5 - 32*t^4*z^6 + 640*t^4*z^5 - 3472*t^4*z^4 + 5376*t^4*z^3 + 1056*t^4*z^2 + 800*t^4*z + 576*t^4 + 112*t^3*z^7 - 1488*t^3*z^6 + 6512*t^3*z^5 - 9552*t^3*z^4 + 608*t^3*z^3 - 304*t^3*z^2 - 272*t^3*z - 448*t^3 - 112*t^2*z^8 + 1392*t^2*z^7 - 5968*t^2*z^6 + 9584*t^2*z^5 - 3232*t^2*z^4 - 112*t^2*z^3 - 80*t^2*z^2 - 64*t^2*z - 80*t^2 + 32*t*z^9 - 400*t*z^8 + 1760*t*z^7 - 3056*t*z^6 + 1456*t*z^5 + 64*t*z^4 + 48*t*z^3 + 48*t*z^2 + 96*t*z + 336*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_11_63 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (1 - z) (z) t 63) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : False := by
  apply cell_11_63 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t*z^2 - 8*t*z + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (-32*t*z^10 + 480*t*z^9 - 2688*t*z^8 + 6912*t*z^7 - 7936*t*z^6 + 3072*t*z^5 - 32*z^10 + 352*z^9 - 1280*z^8 + 1792*z^7 - 768*z^6:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(32*t*z^8 - 320*t*z^7 + 992*t*z^6 - 992*t*z^5 - 96*t*z^3 - 480*t*z^2 - 2112*t*z - 9120*t + 32*z^8 - 192*z^7 + 224*z^6 - 96*z^5 - 384*z^4 - 1632*z^3 - 7008*z^2 - 30144*z - 129696)*hf


private def limit11 (z t : ℝ) : Fin 64→Prop := ![False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,((t + 4*z - 3:ℝ)=0),False,False,False,False,False,False,False,False,False,((t + z - 3:ℝ)=0),False,False,False,((t - 3*z + 2:ℝ)=0),False,False,False,False,False,False,False,False,((t - 3*z + 2:ℝ)=0),False,False,False,False,False,False,False,False,((t + 2*z - 3:ℝ)=0),False,False,False,False,False,False,False,False,False,False]

private def hue11 : Fin 64→Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_11_21_31 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit11 z t 21) (hj : limit11 z t 31) (_he : edge4 (1) (1) (z) (profile4 (1 - z) (z) t 21) (profile4 (1 - z) (z) t 31) (1 - z) (z) t=0) : False := by
  apply pair_11_21_31 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_11_21_35 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit11 z t 21) (hj : limit11 z t 35) (_he : edge4 (1) (1) (z) (profile4 (1 - z) (z) t 21) (profile4 (1 - z) (z) t 35) (1 - z) (z) t=0) : False := by
  apply pair_11_21_35 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_11_21_44 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit11 z t 21) (hj : limit11 z t 44) (_he : edge4 (1) (1) (z) (profile4 (1 - z) (z) t 21) (profile4 (1 - z) (z) t 44) (1 - z) (z) t=0) : False := by
  apply pair_11_21_44 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_11_21_53 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit11 z t 21) (hj : limit11 z t 53) (_he : edge4 (1) (1) (z) (profile4 (1 - z) (z) t 21) (profile4 (1 - z) (z) t 53) (1 - z) (z) t=0) : False := by
  apply pair_11_21_53 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_11_31_35 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit11 z t 31) (hj : limit11 z t 35) (_he : edge4 (1) (1) (z) (profile4 (1 - z) (z) t 31) (profile4 (1 - z) (z) t 35) (1 - z) (z) t=0) : False := by
  apply pair_11_31_35 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_11_31_44 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit11 z t 31) (hj : limit11 z t 44) (_he : edge4 (1) (1) (z) (profile4 (1 - z) (z) t 31) (profile4 (1 - z) (z) t 44) (1 - z) (z) t=0) : False := by
  apply pair_11_31_44 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_11_31_53 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit11 z t 31) (hj : limit11 z t 53) (_he : edge4 (1) (1) (z) (profile4 (1 - z) (z) t 31) (profile4 (1 - z) (z) t 53) (1 - z) (z) t=0) : False := by
  apply pair_11_31_53 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_11_35_44 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit11 z t 35) (_hj : limit11 z t 44) (he : edge4 (1) (1) (z) (profile4 (1 - z) (z) t 35) (profile4 (1 - z) (z) t 44) (1 - z) (z) t=0) : False := by
  apply pair_11_35_44 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (16*t^8*z^4 - 256*t^8*z^3 + 1536*t^8*z^2 - 4096*t^8*z + 4096*t^8 - 16*t^7*z^5 + 128*t^7*z^4 + 512*t^7*z^3 - 8192*t^7*z^2 + 28672*t^7*z - 32768*t^7 + 64*t^6*z^5 - 576*t^6*z^4 - 1024*t^6*z^3 + 26624*t^6*z^2 - 98304*t^6*z + 114688*t^6 + 32*t^5*z^6 - 560*t^5*z^5 + 2944*t^5*z^4 + 1536*t^5*z^3 - 65536*t^5*z^2 + 217088*t^5*z - 229376*t^5 - 16*t^4*z^8 + 272*t^4*z^7 - 1904*t^4*z^6 + 7264*t^4*z^5 - 15264*t^4*z^4 - 512*t^4*z^3 + 119808*t^4*z^2 - 327680*t^4*z + 286720*t^4 + 16*t^3*z^9 - 208*t^3*z^8 + 688*t^3*z^7 + 1920*t^3*z^6 - 17520*t^3*z^5 + 37760*t^3*z^4 - 512*t^3*z^3 - 155648*t^3*z^2 + 331776*t^3*z - 229376*t^3 - 16*t^2*z^9 + 176*t^2*z^8 - 128*t^2*z^7 - 5664*t^2*z^6 + 28800*t^2*z^5 - 49728*t^2*z^4 - 3072*t^2*z^3 + 133120*t^2*z^2 - 212992*t^2*z + 114688*t^2 - 16*t*z^10 + 256*t*z^9 - 1456*t*z^8 + 2736*t*z^7 + 4832*t*z^6 - 27472*t*z^5 + 34944*t*z^4 + 6656*t*z^3 - 65536*t*z^2 + 77824*t*z - 32768*t + 16*z^9 - 288*z^8 + 2064*z^7 - 7408*z^6 + 13536*z^5 - 10224*z^4 - 3328*z^3 + 13824*z^2 - 12288*z + 4096:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-16*t^8*z^2 + 176*t^8*z - 608*t^8 + 16*t^7*z^3 - 48*t^7*z^2 - 800*t^7*z + 4336*t^7 - 64*t^6*z^3 + 256*t^6*z^2 + 2496*t^6*z - 14912*t^6 - 32*t^5*z^4 + 400*t^5*z^3 - 848*t^5*z^2 - 6976*t^5*z + 33200*t^5 + 16*t^4*z^6 - 192*t^4*z^5 + 896*t^4*z^4 - 2208*t^4*z^3 + 1536*t^4*z^2 + 14816*t^4*z - 50336*t^4 - 16*t^3*z^7 + 128*t^3*z^6 - 2304*t^3*z^4 + 6000*t^3*z^3 - 848*t^3*z^2 - 21728*t^3*z + 49552*t^3 + 16*t^2*z^7 - 96*t^2*z^6 - 400*t^2*z^5 + 3952*t^2*z^4 - 7840*t^2*z^3 - 1328*t^2*z^2 + 19952*t^2*z - 29376*t^2 + 16*t*z^8 - 176*t*z^7 + 528*t*z^6 + 432*t*z^5 - 4256*t*z^4 + 4896*t*z^3 + 2304*t*z^2 - 9824*t*z + 9504*t - 16*z^7 + 208*z^6 - 976*z^5 + 1904*z^4 - 1088*z^3 - 928*z^2 + 1952*z - 1280)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_11_35_53 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit11 z t 35) (hj : limit11 z t 53) (_he : edge4 (1) (1) (z) (profile4 (1 - z) (z) t 35) (profile4 (1 - z) (z) t 53) (1 - z) (z) t=0) : False := by
  apply pair_11_35_53 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_11_44_53 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit11 z t 44) (hj : limit11 z t 53) (_he : edge4 (1) (1) (z) (profile4 (1 - z) (z) t 44) (profile4 (1 - z) (z) t 53) (1 - z) (z) t=0) : False := by
  apply pair_11_44_53 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma exclude_field_11 (z t : ℝ) (hf : z^2 - 5*z + 3=0) (hn0 : t-(1)≠0) (hn1 : t-(1 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (g : Fin 5→Fin 64) (hinj : Function.Injective g)
    (hc : ∀ i, cell (1) (1) (z) (profile4 (1 - z) (z) t (g i)) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t)
    (he : ∀ i j : Fin 5, i≠j → edge4 (1) (1) (z) (profile4 (1 - z) (z) t (g i)) (profile4 (1 - z) (z) t (g j)) (1 - z) (z) t=0) : False := by
  have row (k : Fin 64) (hh : cell (1) (1) (z) (profile4 (1 - z) (z) t k) ((1 - z),(1),(1 - z)) ((1 - z),(1 - z),(1)) (1 - z) (z) t) : limit11 z t k := by
    fin_cases k
    · exact row_11_0 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_1 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_2 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_3 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_4 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_5 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_6 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_7 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_8 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_9 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_10 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_11 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_12 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_13 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_14 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_15 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_16 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_17 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_18 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_19 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_20 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_21 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_22 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_23 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_24 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_25 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_26 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_27 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_28 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_29 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_30 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_31 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_32 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_33 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_34 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_35 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_36 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_37 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_38 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_39 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_40 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_41 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_42 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_43 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_44 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_45 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_46 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_47 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_48 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_49 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_50 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_51 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_52 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_53 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_54 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_55 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_56 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_57 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_58 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_59 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_60 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_61 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_62 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_11_63 z t hf hn0 hn1 hn2 hn3 hh
  have allowed (k : Fin 64) (hh : limit11 z t k) : k∈([21,31,35,44,53]:List (Fin 64)) := by
    fin_cases k <;> first | decide | exact False.elim hh
  have cert : ∀ i j : Fin 64, i∈([21,31,35,44,53]:List (Fin 64)) → j∈([21,31,35,44,53]:List (Fin 64)) → i<j → hue11 i=hue11 j → (i,j)∈([(21,31),(21,35),(21,44),(21,53),(31,35),(31,44),(31,53),(35,44),(35,53),(44,53)]:List (Fin 64×Fin 64)) := by decide
  have bad (i j : Fin 64) (hi : limit11 z t i) (hj : limit11 z t j) (hlt : i<j) (hc : hue11 i=hue11 j) (hb : edge4 (1) (1) (z) (profile4 (1 - z) (z) t i) (profile4 (1 - z) (z) t j) (1 - z) (z) t=0) : False := by
    have h := cert i j (allowed i hi) (allowed j hj) hlt hc
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact rowpair_11_21_31 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_11_21_35 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_11_21_44 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_11_21_53 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_11_31_35 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_11_31_44 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_11_31_53 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_11_35_44 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_11_35_53 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_11_44_53 z t hf hn0 hn1 hn2 hn3 hi hj hb
  have hi : Function.Injective (fun i : Fin 5 => hue11 (g i)) := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne (show g i≠g j from fun e => hne (hinj e)) with hl|hl
    · exact bad _ _ (row _ (hc i)) (row _ (hc j)) hl h (he i j hne)
    · exact bad _ _ (row _ (hc j)) (row _ (hc i)) hl h.symm (he j i (Ne.symm hne))
  have hh := Fintype.card_le_of_injective _ hi
  norm_num at hh

private lemma cell_12_0 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-z/9 - 1/18)*h0 + (-4/9)*hf
  norm_num at hh

private lemma cell_12_1 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-z/9 - 1/18)*h0 + (-4/9)*hf
  norm_num at hh

private lemma cell_12_2 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (8 - 6*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-3*z/46 - 1/46)*h0 + (-9/23)*hf
  norm_num at hh

private lemma cell_12_3 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) - 2*z + 8:ℝ)=0) (h1 : (16*t^8 + t^7*(112 - 112*z) + t^6*(832 - 208*z) + t^5*(352 - 16*z) + t^4*(992*z - 4544) + t^3*(4304*z - 7424) + t^2*(2096*z - 4208) + t*(19408 - 10288*z) + 2528*z - 2048:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-13*z/59049 - 11/39366) + t^6*(z/13122 + 1/4374) + t^5*(29*z/6561 + 14/2187) + t^4*(-4*z/729 - 5/729) + t^3*(-25*z/1458 - 41/1458) + t^2*(5*z/162 + 13/486) + t*(1/729 - 7*z/729) - 109*z/1458 - 5/1458)*h0 + (t*(13*z/472392 + 11/314928) + 37*z/314928 + 1/6561)*h1 + (52*t^8/19683 + 122*t^7/6561 + 2000*t^6/59049 - 1627*t^5/59049 - 16549*t^4/59049 - 31645*t^3/59049 + 4688*t^2/59049 + 57302*t/59049 - 8789/19683)*hf
  norm_num at hh

private lemma cell_12_4 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-z/9 - 1/18)*h0 + (-4/9)*hf
  norm_num at hh

private lemma cell_12_5 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(-163296*z - 186624) + 1189728*z + 1539648:ℝ)=0) : (t - 2*z - 3:ℝ)=0 := by
  have hh : (t - 2*z - 3:ℝ)=0 := by linear_combination (5/209952 - 7*z/629856)*h1 + (119/9 - 49*t/27)*hf
  exact hh

private lemma cell_12_6 (z t : ℝ) (_hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_12_7 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2 - 4*z) + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(304 - 176*z) + t^6*(4384 - 1440*z) + t^5*(17584 - 9392*z) + t^4*(31456 - 3744*z) + t^3*(8368*z - 70064) + t^2*(70272*z + 28816) + t*(-67136*z - 45632) + 146592*z + 188704:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(23/236196 - 143*z/3542940) + t^6*(743/236196 - 2443*z/1771470) + t^5*(7169/196830 - 18527*z/1180980) + t^4*(194987/1180980 - 127949*z/1771470) + t^3*(38635/236196 - 242167*z/3542940) + t^2*(13295*z/59049 - 105241/196830) + t*(173699*z/1771470 - 106657/590490) - 128069*z/885735 + 143357/590490)*h0 + (t*(143*z/28343520 - 23/1889568) + 247*z/14171760 - 179/4723920)*h1 + (143*t^8/196830 + 158*t^7/32805 + 17239*t^6/1771470 - 94178*t^5/885735 - 443527*t^4/1771470 + 354491*t^3/885735 - 145804*t^2/295245 - 43649*t/295245 - 251446/98415)*hf
  norm_num at hh

private lemma cell_12_8 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (8 - 6*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-3*z/46 - 1/46)*h0 + (-9/23)*hf
  norm_num at hh

private lemma cell_12_9 (z t : ℝ) (_hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_12_10 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z - 12:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-z/54 - 5/54)*h0 + (1/27)*hf
  norm_num at hh

private lemma cell_12_11 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(6 - 6*z):ℝ)=0) (h1 : (16*t^8 + t^7*(432 - 240*z) + t^6*(8400 - 3360*z) + t^5*(61200 - 27504*z) + t^4*(184176 - 77472*z) + t^3*(36720 - 19872*z) + t^2*(47952*z - 98496) + t*(3888*z - 15552):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(-7*z/402408 - 1/67068) + t^5*(1/3726 - z/33534) + t^4*(1/486 - z/648) + t^3*(47/3726 - z/207) + t^2*(-89*z/14904 - 1/3726) + t*(-z/1656 - 37/1656) - 47*z/828 - 5/1656)*h0 + (7*z/3219264 + 1/536544)*h1 + (7*t^7/16767 + 239*t^6/33534 + 565*t^5/11178 + 1559*t^4/11178 + 55*t^3/7452 - 67*t^2/621 - 289*t/828)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_12_12 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) - 2*z + 8:ℝ)=0) (h1 : (16*t^8 + t^7*(80*z - 80) + t^6*(448 - 256*z) + t^5*(128*z - 1520) + t^4*(2176 - 256*z) + t^3*(2960*z - 3776) + t^2*(9328 - 8416*z) + t*(3008*z + 5536) + 2048*z - 9632:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-605*z/1003833 - 257/334611) + t^6*(-2755*z/669222 - 1231/223074) + t^5*(749*z/223074 + 347/74358) + t^4*(583*z/12393 + 256/4131) + t^3*(-947*z/24786 - 212/4131) + t^2*(-355*z/2754 - 485/2754) + t*(287*z/918 + 383/918) - 2983*z/8262 - 3143/8262)*h0 + (t*(605*z/8030664 + 257/2676888) - 19*z/66096 - 25/66096)*h1 + (-2420*t^8/334611 + 10990*t^7/334611 - 85076*t^6/1003833 + 157483*t^5/1003833 - 279983*t^4/1003833 + 1155103*t^3/1003833 - 2287148*t^2/1003833 + 615916*t/1003833 - 551/4131)*hf
  norm_num at hh

private lemma cell_12_13 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2 - 4*z) + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(16*z + 112) + t^6*(240*z - 32) + t^5*(688*z - 272) + t^4*(480*z + 1888) + t^3*(976*z - 32) + t^2*(1312 - 2448*z) + t*(13072 - 9200*z) + 3840*z - 6080:ℝ)=0) (h2 : (16*t^8 + t^7*(304 - 176*z) + t^6*(4384 - 1440*z) + t^5*(17584 - 9392*z) + t^4*(31456 - 3744*z) + t^3*(8368*z - 70064) + t^2*(70272*z + 28816) + t*(-67136*z - 45632) + 146592*z + 188704:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(361*z/46490458680 - 34/1937102445) + t^12*(1436*z/5811307335 - 8783/15496819560) + t^11*(38717*z/15496819560 - 3701/645700815) + t^10*(230389*z/46490458680 - 174371/15496819560) + t^9*(1816201/15496819560 - 293539*z/5811307335) + t^8*(335269/860934420 - 861913*z/5165606520) + t^7*(2756509*z/7748409780 - 2051573/2582803260) + t^6*(1054027*z/3099363912 - 3555253/5165606520) + t^5*(2788381/860934420 - 766151*z/645700815) + t^4*(10884844*z/1162261467 - 322967087/15496819560) + t^3*(235908247/15496819560 - 35082247*z/9298091736) + t^2*(3980588/129140163 - 26694431*z/1937102445) + t*(48960190*z/1162261467 - 426018487/7748409780) - 872884883*z/11622614670 + 244810352/1937102445)*h0 + (t^7*(17/7748409780 - 361*z/371923669440) + t^6*(4117/61987278240 - 10687*z/371923669440) + t^5*(26621/41324852160 - 6965*z/24794911296) + t^4*(123317/61987278240 - 3997*z/4649045868) + t^3*(121733*z/185961834720 - 96901/61987278240) + t^2*(41413*z/15496819560 - 249607/41324852160) + t*(697957/61987278240 - 118261*z/23245229340) + 520031*z/37192366944 - 123281/3874204890)*h1 + (z/4723920 + 1/629856)*h2 + (361*t^14/7748409780 + 2171*t^13/1291401630 + 102521*t^12/4649045868 + 1409017*t^11/11622614670 + 2345683*t^10/11622614670 - 74437*t^9/645700815 + 4743131*t^8/4649045868 + 772324*t^7/5811307335 - 83660419*t^6/7748409780 + 28399441*t^5/1162261467 - 209093*t^4/1162261467 - 708081901*t^3/11622614670 + 506688601*t^2/3874204890 - 534736517*t/3874204890 - 164118082/1937102445)*hf
  norm_num at hh

private lemma cell_12_14 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(6 - 6*z):ℝ)=0) (h1 : (16*t^8 + t^7*(240 - 48*z) + t^6*(912 - 336*z) + t^5*(576*z - 1872) + t^4*(5904*z - 13248) + t^3*(4752 - 2160*z) + t^2*(46656 - 23328*z) + t*(15552*z - 27216):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(z/314928 - 1/52488) + t^5*(z/26244 - 1/4374) + t^4*(-z/5832 - 1/3888) + t^3*(7/3888 - 5*z/2916) + t^2*(-z/324 - 1/648) + t*(-z/648 - 13/432) - 25*z/432 + 1/144)*h0 + (1/419904 - z/2519424)*h1 + (5*t^6/52488 - 7*t^5/8748 - 139*t^4/17496 - 113*t^3/5832 - t^2/54 - 221*t/648)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_12_15 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z - 8*t*z + 2*z + 6:ℝ)=0) (h1 : (t^8*(112*z + 192) + t^7*(176*z - 624) + t^6*(2352 - 2624*z) + t^5*(6272*z - 11280) + t^4*(24672 - 7424*z) + t^3*(1664*z - 14736) + t^2*(9616*z - 21840) + t*(27888 - 8464*z) - 32*z - 4128:ℝ)=0) : (t + z - 3:ℝ)=0 := by
  have hh : (t + z - 3:ℝ)=0 := by linear_combination (t^6*(37/13122 - 25*z/19683) + t^5*(235*z/13122 - 91/2187) + t^4*(95/486 - 62*z/729) + t^3*(4075*z/19683 - 3137/6561) + t^2*(1031/2187 - 2723*z/13122) + t*(317/1458 - 451*z/4374) + 4901*z/19683 - 8381/13122)*h0 + (17/104976 - 11*z/157464)*h1 + (68*t^8/6561 - 221*t^7/6561 + 290*t^6/2187 - 4541*t^5/6561 + 11303*t^4/6561 - 1277*t^3/729 - 1549*t^2/6561 + 10543*t/6561 - 1094/2187)*hf
  exact hh

private lemma cell_12_16 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (8*z + 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z/27 - 7/54)*h0 + (-16/27)*hf
  norm_num at hh

private lemma cell_12_17 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h1 : (t*(3888*z + 19440):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (1/17496 - z/104976)*h1 + (t/27)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_12_18 (z t : ℝ) (_hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/8)*h0
  norm_num at hh

private lemma cell_12_19 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 10) + 12*z + 14:ℝ)=0) (h1 : (16*t^8 + t^7*(-176*z - 80) + t^6*(1536*z + 2176) + t^5*(-8960*z - 12080) + t^4*(26112*z + 32512) + t^3*(-29936*z - 46784) + t^2*(13536*z + 15280) + t*(13024 - 1472*z) - 1344*z - 1568:ℝ)=0) (h2 : (16*t^8 + t^7*(16*z - 272) + t^6*(1792 - 240*z) + t^5*(1552*z - 6176) + t^4*(14176 - 5952*z) + t^3*(15088*z - 28448) + t^2*(44368 - 22896*z) + t*(6352*z - 14672) + 5376*z - 8288:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(161/172186884 - 211*z/516560652) + t^12*(839*z/516560652 - 154/43046721) + t^11*(3673*z/172186884 - 2927/57395628) + t^10*(38711/172186884 - 47971*z/516560652) + t^9*(13763*z/516560652 - 4105/43046721) + t^8*(7621/19131876 - 8729*z/57395628) + t^7*(40852/14348907 - 212159*z/172186884) + t^6*(1730077*z/172186884 - 334106/14348907) + t^5*(910123/19131876 - 1173671*z/57395628) + t^4*(378665/43046721 - 1416455*z/258280326) + t^3*(19369747/86093442 - 11973571*z/129140163) + t^2*(13238999/28697814 - 17321755*z/86093442) + t*(120845999*z/516560652 - 91003153/172186884) + 29667104*z/129140163 - 21719716/43046721)*h0 + (t^7*(211*z/4132485216 - 161/1377495072) + t^6*(2515/1377495072 - 3287*z/4132485216) + t^5*(3137*z/688747536 - 601/57395628) + t^4*(43739/1377495072 - 1781*z/129140163) + t^3*(134387*z/4132485216 - 51587/688747536) + t^2*(34487/229582512 - 89747*z/1377495072) + t*(7778*z/129140163 - 189947/1377495072) + 23323*z/258280326 - 8734/43046721)*h1 + (7/629856 - z/236196)*h2 + (211*t^14/28697814 - 5941*t^13/28697814 + 328879*t^12/129140163 - 2390476*t^11/129140163 + 11782163*t^10/129140163 - 14177335*t^9/43046721 + 117033622*t^8/129140163 - 249253508*t^7/129140163 + 263845955*t^6/86093442 - 758918195*t^5/258280326 + 3364391*t^4/129140163 + 285076510*t^3/129140163 + 87470077*t^2/43046721 - 70925755*t/43046721 - 51424/19683)*hf
  norm_num at hh

private lemma cell_12_20 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h2 : (t*(3888*z + 19440):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (1/17496 - z/104976)*h2 + (t/27)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_12_21 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4*z - 12:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/36 - 1/9)*h0 + (1/9)*hf
  norm_num at hh

private lemma cell_12_22 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z - 10:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/54 - 1/9)*h0 + (1/27)*hf
  norm_num at hh

private lemma cell_12_23 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-6*z - 4) + 6*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(112 - 240*z) + t^6*(240*z + 4384) + t^5*(976 - 13104*z) + t^4*(17184*z + 59104) + t^3*(-57648*z - 58304) + t^2*(68400*z + 40480) + t*(-18672*z - 48848) + 3840*z + 2080:ℝ)=0) (h2 : (16*t^8 + t^7*(-48*z - 80) + t^6*(192*z - 32) + t^5*(432*z + 1264) + t^4*(-1632*z - 3296) + t^3*(-1680*z - 5552) + t^2*(4320*z + 15568) + t*(3840*z + 12448) - 1536*z - 896:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(11/57395628 - 7*z/43046721) + t^12*(475/57395628 - 215*z/172186884) + t^11*(493/19131876 - 2249*z/57395628) + t^10*(10933*z/172186884 + 13279/57395628) + t^9*(-7237*z/172186884 - 45349/57395628) + t^8*(11987*z/19131876 - 19159/6377292) + t^7*(87814*z/14348907 - 2087/19131876) + t^6*(-2035*z/57395628 - 226853/9565938) + t^5*(185563*z/19131876 - 148807/3188646) + t^4*(2156969*z/86093442 + 839185/14348907) + t^3*(13879187/57395628 - 10600211*z/86093442) + t^2*(5781881/19131876 - 13695391*z/57395628) + t*(3583715*z/172186884 + 12133313/57395628) + 4259951*z/86093442 - 2101345/28697814)*h0 + (t^7*(7*z/344373768 - 11/459165024) + t^6*(-97*z/1377495072 - 5/57395628) + t^5*(53/76527504 - 71*z/459165024) + t^4*(233*z/172186884 + 205/459165024) + t^3*(-1697*z/688747536 - 385/459165024) + t^2*(41/38263752 - 4195*z/459165024) + t*(13309*z/1377495072 - 2651/459165024) + 33893*z/1377495072 - 4489/459165024)*h1 + (1/17496 - z/104976)*h2 + (56*t^14/14348907 - 406*t^13/14348907 + 266*t^12/14348907 - 4220*t^11/14348907 - 34255*t^10/28697814 + 248947*t^9/14348907 - 208405*t^8/9565938 - 114752*t^7/4782969 + 963497*t^6/9565938 - 2285863*t^5/28697814 - 2822927*t^4/14348907 - 1614449*t^3/14348907 + 1868672*t^2/14348907 + 9052802*t/14348907 - 5825623/14348907)*hf
  norm_num at hh

private lemma cell_12_24 (z t : ℝ) (_hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/8)*h0
  norm_num at hh

private lemma cell_12_25 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z - 10:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/54 - 1/9)*h0 + (1/27)*hf
  norm_num at hh

private lemma cell_12_26 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z - 12:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-z/54 - 5/54)*h0 + (1/27)*hf
  norm_num at hh

private lemma cell_12_27 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t*z + 8*z + 6:ℝ)=0) (h1 : (16*t^8 + t^7*(240 - 304*z) + t^6*(8016 - 1232*z) + t^5*(34512 - 27520*z) + t^4*(194304 - 48560*z) + t^3*(237552 - 151984*z) + t^2*(194880 - 59552*z) + t*(20400 - 7648*z) + 2272*z - 10176:ℝ)=0) (h2 : (16*t^8 + t^7*(48 - 112*z) + t^6*(64*z + 528) + t^5*(560*z - 48) + t^4*(-1184*z - 4848) + t^3*(1952*z - 5232) + t^2*(6544*z + 5664) + t*(18240 - 6640*z) - 32*z - 4128:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(-5*z/129140163 - 19/344373768) + t^12*(335*z/258280326 + 515/344373768) + t^11*(-619*z/43046721 - 1249/57395628) + t^10*(98045*z/1033121304 + 34877/344373768) + t^9*(-182305*z/1033121304 - 105397/344373768) + t^8*(-37379*z/114791256 - 18563/38263752) + t^7*(810151*z/344373768 + 197201/57395628) + t^6*(-508531*z/172186884 - 66335/28697814) + t^5*(-644681*z/114791256 - 203477/38263752) + t^4*(14053493*z/1033121304 + 37853/86093442) + t^3*(6551050*z/129140163 - 9268603/86093442) + t^2*(42378487*z/344373768 - 4987489/14348907) + t*(80714647*z/516560652 - 56144963/172186884) + 11495905*z/129140163 - 13094641/86093442)*h0 + (t^7*(5*z/1033121304 + 19/2754990144) + t^6*(-485*z/8264970432 - 25/344373768) + t^5*(331*z/2754990144 + 139/918330048) + t^4*(299*z/516560652 + 1039/1377495072) + t^3*(-5807*z/4132485216 - 5383/2754990144) + t^2*(-3655*z/1377495072 - 701/229582512) + t*(25291*z/8264970432 + 2231/1377495072) + 3413*z/4132485216 + 2641/172186884)*h1 + (13*z/944784 + 11/629856)*h2 + (50*t^14/43046721 - 205*t^13/172186884 - 7231*t^12/258280326 - 93839*t^11/516560652 - 119251*t^10/172186884 + 1214182*t^9/129140163 + 3012298*t^8/129140163 - 14373275*t^7/172186884 - 62980955*t^6/258280326 - 85453579*t^5/516560652 + 37215227*t^4/57395628 + 108793460*t^3/129140163 + 65635873*t^2/258280326 - 38496875*t/86093442 - 3413063/4782969)*hf
  norm_num at hh

private lemma cell_12_28 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 10) + 12*z + 14:ℝ)=0) (h1 : (16*t^8 + t^7*(16*z - 272) + t^6*(1792 - 240*z) + t^5*(1552*z - 6176) + t^4*(14176 - 5952*z) + t^3*(15088*z - 28448) + t^2*(44368 - 22896*z) + t*(6352*z - 14672) + 5376*z - 8288:ℝ)=0) (h2 : (16*t^8 + t^7*(-176*z - 80) + t^6*(1536*z + 2176) + t^5*(-8960*z - 12080) + t^4*(26112*z + 32512) + t^3*(-29936*z - 46784) + t^2*(13536*z + 15280) + t*(13024 - 1472*z) - 1344*z - 1568:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(211*z/516560652 - 161/172186884) + t^12*(1099/172186884 - 368*z/129140163) + t^11*(2261/57395628 - 2773*z/172186884) + t^10*(40217*z/258280326 - 16088/43046721) + t^9*(139375/172186884 - 169673*z/516560652) + t^8*(19655*z/57395628 - 4189/4782969) + t^7*(116939*z/172186884 - 44723/28697814) + t^6*(1865897/57395628 - 1210565*z/86093442) + t^5*(2713481*z/57395628 - 1027853/9565938) + t^4*(12758789/86093442 - 17918191*z/258280326) + t^3*(59532127*z/516560652 - 20674609/86093442) + t^2*(1459711/28697814 - 4488283*z/172186884) + t*(229630315/172186884 - 148540843*z/258280326) + 162666689*z/258280326 - 122679901/86093442)*h0 + (t^7*(161/1377495072 - 211*z/4132485216) + t^6*(733/688747536 - 469*z/1033121304) + t^5*(205/229582512 - 323*z/688747536) + t^4*(6799*z/4132485216 - 4103/1377495072) + t^3*(16441*z/4132485216 - 1813/172186884) + t^2*(16237*z/688747536 - 12341/229582512) + t*(1313*z/4132485216 - 1375/1377495072) - 198277*z/4132485216 + 37601/344373768)*h1 + (7*z/104976 - 5/34992)*h2 + (211*t^14/86093442 - 611*t^13/28697814 - 13541*t^12/258280326 + 278393*t^11/258280326 - 1047319*t^10/258280326 + 535903*t^9/86093442 + 1261477*t^8/258280326 - 25085477*t^7/258280326 + 15788957*t^6/43046721 - 114554623*t^5/258280326 - 30016250*t^4/129140163 + 138053723*t^3/129140163 - 177248195*t^2/43046721 + 845594459*t/86093442 - 310371998/43046721)*hf
  norm_num at hh

private lemma cell_12_29 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-6*z - 4) + 6*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-48*z - 80) + t^6*(192*z - 32) + t^5*(432*z + 1264) + t^4*(-1632*z - 3296) + t^3*(-1680*z - 5552) + t^2*(4320*z + 15568) + t*(3840*z + 12448) - 1536*z - 896:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(5941*z/108413964 - 3089/36137988) + t^6*(-7751*z/54206982 - 1042/9034497) + t^5*(11351/6022998 - 5036*z/9034497) + t^4*(329401*z/108413964 - 5828/9034497) + t^3*(86423/36137988 - 165208*z/27103491) + t^2*(68135/12045996 - 162517*z/9034497) + t*(504913*z/27103491 - 132254/9034497) + 3562399*z/54206982 - 693964/9034497)*h0 + (t*(3089/289103904 - 5941*z/867311712) - 2321*z/867311712 + 13435/289103904)*h1 + (5941*t^6/6022998 + 11596*t^5/1003833 - 70949*t^4/1003833 - 278639*t^3/6022998 + 258557*t^2/1003833 + 16669*t/59049 - 1199845/3011499)*hf
  norm_num at hh

private lemma cell_12_30 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t*z + 8*z + 6:ℝ)=0) (h1 : (16*t^8 + t^7*(48 - 112*z) + t^6*(64*z + 528) + t^5*(560*z - 48) + t^4*(-1184*z - 4848) + t^3*(1952*z - 5232) + t^2*(6544*z + 5664) + t*(18240 - 6640*z) - 32*z - 4128:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(121*z/1417176 - 31/236196) + t^6*(895*z/1417176 - 1043/472392) + t^5*(155*z/59049 - 707/157464) + t^4*(487/59049 - 209*z/708588) + t^3*(1615/59049 - 28447*z/1417176) + t^2*(1499/19683 - 5621*z/118098) + t*(35413/472392 - 27647*z/1417176) + 21341*z/177147 - 53323/236196)*h0 + (t*(31/1889568 - 121*z/11337408) - 337*z/11337408 + 247/1889568)*h1 + (-121*t^8/236196 + 407*t^7/236196 + 16883*t^6/708588 - 13711*t^5/708588 - 3397*t^4/19683 - 65417*t^3/708588 + 123419*t^2/354294 + 217801*t/236196 - 12659/13122)*hf
  norm_num at hh

private lemma cell_12_31 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(-12*z - 12) + 18*z + 18:ℝ)=0) (h1 : (t^8*(112*z + 192) + t^7*(-2256*z - 3312) + t^6*(17856*z + 23760) + t^5*(-70848*z - 92016) + t^4*(152928*z + 196992) + t^3*(-178848*z - 221616) + t^2*(99792*z + 125712) + t*(-19440*z - 27216):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(13*z/22356 + 7/7452) + t^6*(-6137*z/603612 - 3071/201204) + t^5*(3467*z/50301 + 3187/33534) + t^4*(-14981*z/67068 - 1604/5589) + t^3*(3875*z/11178 + 3223/7452) + t^2*(-905*z/3726 - 665/2484) + t*(211*z/2484 + 5/1242) + z/18 - 1/9)*h0 + (t*(-5*z/536544 - 1/536544) + 269*z/4828896 + 11/402408)*h1 + (-2*t^9/16767 + 5*t^8/100602 + 1094*t^7/50301 - 41*t^6/207 + 1411*t^5/1863 - 629*t^4/414 + 974*t^3/621 - 857*t^2/1863 + 137*t/621 - 1)*hf
  norm_num at hh

private lemma cell_12_32 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (8*z - 12:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/18 + 1/36)*h0 + (-4/9)*hf
  norm_num at hh

private lemma cell_12_33 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z - 12:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-z/54 - 5/54)*h0 + (1/27)*hf
  norm_num at hh

private lemma cell_12_34 (z t : ℝ) (_hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_12_35 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 10) + 10*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-112*z - 80) + t^6*(800*z + 688) + t^5*(-1888*z - 2960) + t^4*(320*z + 1168) + t^3*(6752*z + 4816) + t^2*(832 - 4672*z) + t*(9856 - 7792*z) + 2528*z - 2048:ℝ)=0) (h2 : (16*t^8 + t^7*(80*z - 272) + t^6*(2032 - 976*z) + t^5*(4304*z - 8288) + t^4*(21280 - 9136*z) + t^3*(13616*z - 39920) + t^2*(34672 - 13456*z) + t*(12400 - 544*z) + 2048*z - 9632:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(-13*z/3099363912 - 11/2066242608) + t^12*(119*z/2066242608 + 25/344373768) + t^11*(-97*z/688747536 - 5/28697814) + t^10*(-19*z/19131876 - 95/76527504) + t^9*(55*z/12754584 + 389/76527504) + t^8*(25*z/6377292 + 61/8503056) + t^7*(-383*z/12754584 - 559/12754584) + t^6*(-41*z/25509168 - 125/12754584) + t^5*(5*z/11664 + 737/944784) + t^4*(-105917*z/38263752 - 399047/76527504) + t^3*(87623/19131876 - 13925*z/19131876) + t^2*(4319*z/236196 + 7999/944784) + t*(212723*z/38263752 + 1337611/38263752) + 563423*z/19131876 - 102650/4782969)*h0 + (t^7*(13*z/24794911296 + 11/16529940864) + t^6*(1/2754990144 - z/16529940864) + t^5*(-5*z/918330048 - 7/612220032) + t^4*(17*z/1836660096 + 7/204073344) + t^3*(35*z/306110016 + 47/612220032) + t^2*(41*z/204073344 + 5/11337408) + t*(31*z/19131876 + 1081/612220032) + 2681*z/306110016 + 1829/153055008)*h1 + (1/944784 - z/5668704)*h2 + (13*t^14/258280326 - 139*t^13/516560652 - 665*t^12/1549681956 + 1756*t^11/387420489 + 15739*t^10/1549681956 - 254689*t^9/3099363912 + 271141*t^8/1549681956 + 96406*t^7/387420489 - 527090*t^6/129140163 + 178417*t^5/28697814 + 727573*t^4/57395628 - 154495*t^3/38263752 - 1158197*t^2/9565938 + 71593*t/1062882 - 56027/177147)*hf
  norm_num at hh

private lemma cell_12_36 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z - 12:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-z/54 - 5/54)*h0 + (1/27)*hf
  norm_num at hh

private lemma cell_12_37 (z t : ℝ) (_hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-18:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/18)*h0
  norm_num at hh

private lemma cell_12_38 (z t : ℝ) (_hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/16)*h0
  norm_num at hh

private lemma cell_12_39 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 6*z - 10:ℝ)=0) (h1 : (16*t^8 + t^7*(112 - 176*z) + t^6*(2512 - 48*z) + t^5*(1744 - 5792*z) + t^4*(5424*z + 23488) + t^3*(-20816*z - 24272) + t^2*(33984*z + 10528) + t*(-10400*z - 33296) + 3840*z + 2080:ℝ)=0) : (t - z + 2:ℝ)=0 := by
  have hh : (t - z + 2:ℝ)=0 := by linear_combination (t^6*(-z/118098 - 1/39366) + t^5*z/4374 + t^4*(-5*z/19683 - 17/6561) + t^3*(661*z/118098 - 46/19683) + t^2*(7*z/6561 - 121/4374) + t*(947*z/39366 - 517/13122) + 2957*z/118098 - 6025/39366)*h0 + (z/944784 + 1/314928)*h1 + (t^7/6561 + 20*t^6/19683 + 221*t^5/59049 + 1073*t^4/59049 - 430*t^3/59049 + 1060*t^2/19683 - 653*t/19683 - 3037/19683)*hf
  exact hh

private lemma cell_12_40 (z t : ℝ) (_hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_12_41 (z t : ℝ) (_hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/16)*h0
  norm_num at hh

private lemma cell_12_42 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z - 18:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-z/138 - 4/69)*h0 + (1/69)*hf
  norm_num at hh

private lemma cell_12_43 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t*z + 6*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(240 - 240*z) + t^6*(5568 - 1392*z) + t^5*(28800 - 16272*z) + t^4*(124128 - 47232*z) + t^3*(233280 - 104976*z) + t^2*(213840 - 97200*z) + t*(73872 - 27216*z):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(77*z/472392 + 61/314928) + t^6*(-871*z/314928 - 109/26244) + t^5*(583*z/26244 + 101/4374) + t^4*(-2107*z/34992 - 629/5832) + t^3*(469*z/3888 + 53/648) + t^2*(7*z/648 - 17/216) + t*(-37*z/432 - 25/144) + z/18)*h0 + (t*(-77*z/3779136 - 61/2519424) + 293*z/2519424 + 125/839808)*h1 + (-77*t^8/19683 - 473*t^7/26244 - 173*t^6/8748 + 2857*t^5/6561 + 38833*t^4/8748 + 9301*t^3/972 + 4943*t^2/486 + 325*t/81 - 1/3)*hf
  norm_num at hh

private lemma cell_12_44 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 10) + 10*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(80*z - 272) + t^6*(2032 - 976*z) + t^5*(4304*z - 8288) + t^4*(21280 - 9136*z) + t^3*(13616*z - 39920) + t^2*(34672 - 13456*z) + t*(12400 - 544*z) + 2048*z - 9632:ℝ)=0) (h2 : (16*t^8 + t^7*(-112*z - 80) + t^6*(800*z + 688) + t^5*(-1888*z - 2960) + t^4*(320*z + 1168) + t^3*(6752*z + 4816) + t^2*(832 - 4672*z) + t*(9856 - 7792*z) + 2528*z - 2048:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(13*z/3099363912 + 11/2066242608) + t^12*(-19*z/258280326 - 65/688747536) + t^11*(229*z/688747536 + 25/57395628) + t^10*(5*z/6377292 + 37/38263752) + t^9*(-107*z/12754584 - 103/9565938) + t^8*(61*z/12754584 + 25/4251528) + t^7*(103*z/1594323 + 2135/25509168) + t^6*(-265*z/1594323 - 2743/12754584) + t^5*(277*z/236196 + 1489/944784) + t^4*(-42715*z/9565938 - 131635/19131876) + t^3*(6913/76527504 - 62347*z/19131876) + t^2*(175043*z/8503056 + 113383/8503056) + t*(68335*z/9565938 + 1399127/38263752) + 547111*z/19131876 - 217379/9565938)*h0 + (t^7*(-13*z/24794911296 - 11/16529940864) + t^6*(83*z/8264970432 + 73/5509980288) + t^5*(-359*z/5509980288 - 155/1836660096) + t^4*(29*z/229582512 + 17/102036672) + t^3*(23*z/153055008 + 127/612220032) + t^2*(-85*z/204073344 - 11/22674816) + t*(-17*z/38263752 - 163/612220032) - 31*z/38263752 + 191/306110016)*h1 + (z/78732 + 7/419904)*h2 + (13*t^14/258280326 - 259*t^13/172186884 + 14467*t^12/774840978 - 47833*t^11/387420489 + 1444165*t^10/3099363912 - 1564039*t^9/1549681956 + 1921055*t^8/1549681956 + 504223*t^7/774840978 - 9545657*t^6/1033121304 + 3665989*t^5/344373768 + 3092167*t^4/114791256 - 286247*t^3/38263752 - 5453407*t^2/38263752 + 90553*t/1062882 - 112105/354294)*hf
  norm_num at hh

private lemma cell_12_45 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 6*z - 10:ℝ)=0) (h1 : (16*t^8 + t^7*(16*z - 80) + t^6*(-96*z - 176) + t^5*(1168 - 32*z) + t^4*(1440*z - 464) + t^3*(-1856*z - 3920) + t^2*(5920 - 4608*z) + t*(2608*z + 10720) - 1536*z - 896:ℝ)=0) : (t - z + 2:ℝ)=0 := by
  have hh : (t - z + 2:ℝ)=0 := by linear_combination (t^6*(11*z/39366 - 17/26244) + t^5*(13/2916 - 17*z/8748) + t^4*(73*z/26244 - 14/2187) + t^3*(173*z/78732 - 139/26244) + t^2*(29/729 - 40*z/2187) + t*(25*z/26244 - 131/8748) + 1079*z/39366 - 1861/13122)*h0 + (17/209952 - 11*z/314928)*h1 + (11*t^7/6561 - 28*t^6/2187 + 853*t^5/39366 + 1669*t^4/39366 - 5951*t^3/39366 - 311*t^2/6561 + 853*t/4374 - 53/243)*hf
  exact hh

private lemma cell_12_46 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t*z + 6*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(48 - 48*z) + t^6*(-96*z - 192) + t^5*(576*z + 288) + t^4*(1152*z + 576) + t^3*(-1728*z - 8640) + t^2*(-2592*z - 1296) + t*(3888*z + 19440):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(973*z/8030664 - 443/2676888) + t^6*(565*z/892296 - 545/297432) + t^5*(-251*z/892296 - 749/297432) + t^4*(251*z/297432 + 749/99144) + t^3*(13*z/33048 + 307/11016) + t^2*(869/11016 - 2167*z/33048) + t*(4/51 - 47*z/612) + z/18)*h0 + (t*(443/21415104 - 973*z/64245312) - 361*z/10707552 + 149/892296)*h1 + (4865*t^5/111537 + 247*t^4/24786 - 12227*t^3/24786 - 44*t^2/459 + 1274*t/1377 - 1/3)*hf
  norm_num at hh

private lemma cell_12_47 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(-8*z - 12) + 14*z:ℝ)=0) (h1 : (t^8*(112*z + 192) + t^7*(-1360*z - 1776) + t^6*(5344*z + 6384) + t^5*(-6544*z - 9552) + t^4*(-2432*z - 5280) + t^3*(10400*z + 18384) + t^2*(3216 - 5792*z) + t*(-4528*z - 912) + 736*z + 1632:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(157*z/118098 + 137/78732) + t^6*(-9065*z/708588 - 3911/236196) + t^5*(2272*z/59049 + 982/19683) + t^4*(-5045*z/236196 - 1183/39366) + t^3*(-43495*z/708588 - 4717/59049) + t^2*(2410*z/59049 + 5065/78732) + t*(6149*z/236196 + 1591/39366) + 2890*z/177147 - 3937/118098)*h0 + (t*(-13*z/944784 - 11/629856) + 199*z/2834352 + 185/1889568)*h1 + (-22*t^9/19683 + 1139*t^8/118098 - 1706*t^7/59049 + 3802*t^6/59049 - 18989*t^5/118098 + 4747*t^4/118098 + 19127*t^3/59049 - 3035*t^2/59049 + 11111*t/118098 - 16538/59049)*hf
  norm_num at hh

private lemma cell_12_48 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(6 - 6*z):ℝ)=0) (h1 : (t^8*(112*z + 192) + t^7*(-2256*z - 3312) + t^6*(17856*z + 23760) + t^5*(-70848*z - 92016) + t^4*(152928*z + 196992) + t^3*(-178848*z - 221616) + t^2*(99792*z + 125712) + t*(-19440*z - 27216):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(-85*z/8748 - 37/2916) + t^5*(122*z/729 + 53/243) + t^4*(-1087*z/972 - 118/81) + t^3*(293*z/81 + 509/108) + t^2*(-619*z/108 - 403/54) + t*(107*z/27 + 559/108) - 35*z/36 - 43/36)*h0 + (7*z/69984 + 1/7776)*h1 + (2*t^8/243 - 122*t^7/729 + 707*t^6/486 - 1111*t^5/162 + 965*t^4/54 - 1319*t^3/54 + 425*t^2/27 - 35*t/9)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_12_49 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z - 8*t*z + 2*z + 6:ℝ)=0) (h1 : (t^8*(112*z + 192) + t^7*(-3472*z - 4656) + t^6*(40960*z + 53184) + t^5*(-256096*z - 334416) + t^4*(937120*z + 1218432) + t^3*(-2033296*z - 2642880) + t^2*(2554384*z + 3329184) + t*(-1710592*z - 2215200) + 465472*z + 606144:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(257/354294 - 62*z/531441) + t^6*(-3169*z/1062882 - 1187/177147) + t^5*(16577*z/354294 + 3448/59049) + t^4*(-156880*z/531441 - 70630/177147) + t^3*(1182451*z/1062882 + 498709/354294) + t^2*(-409910*z/177147 - 340693/118098) + t*(1309606*z/531441 + 567400/177147) - 1271785*z/1062882 - 226886/177147)*h0 + (t*(85/2834352 - 8*z/531441) + 71*z/1062882 - 181/1417176)*h1 + (340*t^9/177147 - 359*t^8/6561 + 129551*t^7/177147 - 995665*t^6/177147 + 1566794*t^5/59049 - 14010368*t^4/177147 + 26325859*t^3/177147 - 10017475*t^2/59049 + 18914480*t/177147 - 1694719/59049)*hf
  norm_num at hh

private lemma cell_12_50 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z - 6*t*z - 2*z + 8:ℝ)=0) (h1 : (t^8*(112*z + 192) + t^7*(-3024*z - 3888) + t^6*(29808*z + 38448) + t^5*(-154224*z - 202176) + t^4*(457920*z + 593136) + t^3*(-775440*z - 1007856) + t^2*(728544*z + 957408) + t*(-351312*z - 448896) + 63776*z + 83872:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(362/570807 - 571*z/6849684) + t^6*(-15541*z/4566456 - 3287/761076) + t^5*(15043*z/380538 + 23017/507384) + t^4*(-27667*z/126846 - 12589/42282) + t^3*(4601*z/6264 + 1913/2088) + t^2*(-24637*z/18792 - 5099/3132) + t*(7223*z/6264 + 1627/1044) - 57*z/116 - 557/1044)*h0 + (t*(115/4566456 - 707*z/54797472) + 1979*z/36531648 - 73/761076)*h1 + (920*t^9/570807 - 7378*t^8/190269 + 768454*t^7/1712421 - 1677010*t^6/570807 + 2200291*t^5/190269 - 1789694*t^4/63423 + 24375529*t^3/570807 - 762130*t^2/19683 + 32899214*t/1712421 - 2533039/570807)*hf
  norm_num at hh

private lemma cell_12_51 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2 - 4*z) + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-176*z - 80) + t^6*(1536*z + 2176) + t^5*(-8960*z - 12080) + t^4*(26112*z + 32512) + t^3*(-29936*z - 46784) + t^2*(13536*z + 15280) + t*(13024 - 1472*z) - 1344*z - 1568:ℝ)=0) (h2 : (16*t^8 + t^7*(16*z - 272) + t^6*(1792 - 240*z) + t^5*(1552*z - 6176) + t^4*(14176 - 5952*z) + t^3*(15088*z - 28448) + t^2*(44368 - 22896*z) + t*(6352*z - 14672) + 5376*z - 8288:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(127*z/387420489 + 217/516560652) + t^12*(-20813*z/1549681956 - 8981/516560652) + t^11*(30212*z/129140163 + 52397/172186884) + t^10*(-1745437*z/774840978 - 1516727/516560652) + t^9*(20150023*z/1549681956 + 8764507/516560652) + t^8*(-3882755*z/86093442 - 3382741/57395628) + t^7*(43826681*z/516560652 + 19188401/172186884) + t^6*(-20863453*z/516560652 - 9703171/172186884) + t^5*(-7022728*z/43046721 - 11117449/57395628) + t^4*(129802045*z/387420489 + 104666735/258280326) + t^3*(-169032457*z/774840978 - 62374507/258280326) + t^2*(8368729*z/258280326 - 2118814/43046721) + t*(23076265*z/387420489 - 124011599/516560652) - 121176517*z/774840978 + 81610541/258280326)*h0 + (t^7*(-127*z/3099363912 - 217/4132485216) + t^6*(3667*z/6198727824 + 3107/4132485216) + t^5*(-3127*z/1033121304 - 1297/344373768) + t^4*(74497*z/12397455648 + 14045/2066242608) + t^3*(15031/4132485216 - 9167*z/12397455648) + t^2*(-45151*z/4132485216 - 44149/1377495072) + t*(31831/516560652 - 12043*z/12397455648) + 195425*z/3099363912 - 262013/2066242608)*h1 + (451*z/5668704 + 49/472392)*h2 + (-254*t^14/43046721 + 14636*t^13/129140163 - 338110*t^12/387420489 + 2376119*t^11/774840978 - 885499*t^10/774840978 - 7759987*t^9/258280326 + 72659773*t^8/774840978 - 2772058*t^7/387420489 - 8047804*t^6/14348907 + 579086137*t^5/387420489 - 1487471695*t^4/774840978 + 629826331*t^3/774840978 + 307418053*t^2/258280326 - 89486341*t/86093442 - 44291072/129140163)*hf
  norm_num at hh

private lemma cell_12_52 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z - 8*t*z + 2*z + 6:ℝ)=0) (h1 : (t^8*(112*z + 192) + t^7*(-3472*z - 4656) + t^6*(43264*z + 54912) + t^5*(-298000*z - 386256) + t^4*(1280128*z + 1679808) + t^3*(-3524272*z - 4595088) + t^2*(6020752*z + 7818528) + t*(-5812864*z - 7585824) + 2437696*z + 3173952:ℝ)=0) (h2 : (t^8*(112*z + 192) + t^7*(-3472*z - 4656) + t^6*(40960*z + 53184) + t^5*(-256096*z - 334416) + t^4*(937120*z + 1218432) + t^3*(-2033296*z - 2642880) + t^2*(2554384*z + 3329184) + t*(-1710592*z - 2215200) + 465472*z + 606144:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(-83*z/1549681956 - 205/258280326) + t^12*(9323*z/774840978 + 8869/516560652) + t^11*(-73217*z/258280326 - 59581/172186884) + t^10*(2876915*z/774840978 + 2497177/516560652) + t^9*(-51709349*z/1549681956 - 22526105/516560652) + t^8*(18358801*z/86093442 + 7961827/28697814) + t^7*(-256043975*z/258280326 - 55645555/43046721) + t^6*(1759511657*z/516560652 + 763584395/172186884) + t^5*(-371269612*z/43046721 - 644866237/57395628) + t^4*(24613210261*z/1549681956 + 10680446311/516560652) + t^3*(-7963880924*z/387420489 - 6920037433/258280326) + t^2*(9062992355*z/516560652 + 989680493/43046721) + t*(-3405556352*z/387420489 - 2951201863/258280326) + 1381654181*z/774840978 + 334925323/129140163)*h0 + (t^7*(173*z/12397455648 - 47/2066242608) + t^6*(-1249*z/12397455648 - 1/1033121304) + t^5*(1255*z/2066242608 + 1253/1377495072) + t^4*(-42347*z/12397455648 - 7837/2066242608) + t^3*(51557*z/6198727824 + 52855/4132485216) + t^2*(-23711*z/2066242608 - 28807/1377495072) + t*(30329*z/3099363912 + 55025/4132485216) + 6839*z/12397455648 - 46609/4132485216)*h1 + (7*z/104976 - 5/34992)*h2 + (-188*t^15/129140163 + 1517*t^14/43046721 - 46261*t^13/129140163 + 166696*t^12/129140163 + 96145*t^11/9565938 - 42296441*t^10/258280326 + 48215539*t^9/43046721 - 142548761*t^8/28697814 + 684889429*t^7/43046721 - 10091272429*t^6/258280326 + 6739673743*t^5/86093442 - 17336787880*t^4/129140163 + 49249818881*t^3/258280326 - 2837863124*t^2/14348907 + 16176588008*t/129140163 - 1547512231/43046721)*hf
  norm_num at hh

private lemma cell_12_53 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(-10*z - 6) + 8*z + 6:ℝ)=0) (h1 : (t^8*(112*z + 192) + t^7*(-4688*z - 6000) + t^6*(74176*z + 96240) + t^5*(-653984*z - 853584) + t^4*(3512320*z + 4572192) + t^3*(-11710976*z - 15255024) + t^2*(23707984*z + 30897264) + t*(-26671472*z - 34739664) + 12772960*z + 16641408:ℝ)=0) : (t - z - 3:ℝ)=0 := by
  have hh : (t - z - 3:ℝ)=0 := by linear_combination (t^6*(13*z/52488 - 1/2187) + t^5*(z/8748 - 11/2916) + t^4*(19*z/1458 + 7/486) + t^3*(-1169*z/13122 - 1565/17496) + t^2*(4627*z/17496 + 1403/2916) + t*(-667*z/972 - 389/648) + 11597*z/26244 + 8297/8748)*h0 + (5*z/419904 - 1/34992)*h1 + (-4*t^8/2187 + 127*t^7/2187 - 1327*t^6/1458 + 35407*t^5/4374 - 379199*t^4/8748 + 140141*t^3/972 - 2555851*t^2/8748 + 2864959*t/8748 - 226907/1458)*hf
  exact hh

private lemma cell_12_54 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(-8*z - 6) + 6*z + 2:ℝ)=0) (h1 : (t^8*(112*z + 192) + t^7*(-4240*z - 5232) + t^6*(59056*z + 77664) + t^5*(-471376*z - 613488) + t^4*(2287024*z + 2977248) + t^3*(-6929392*z - 9028992) + t^2*(12807520*z + 16689744) + t*(-13202368*z - 17190384) + 5810496*z + 7559872:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(48445*z/48892572 + 15205/16297524) + t^6*(-612877*z/24446286 - 567641/16297524) + t^5*(5021155*z/16297524 + 539590/1358127) + t^4*(-48313475*z/24446286 - 10472698/4074381) + t^3*(360582305*z/48892572 + 157287419/16297524) + t^2*(-262081889*z/16297524 - 113586599/5432508) + t*(922897201*z/48892572 + 399409219/16297524) - 9745169*z/1062882 - 2158420/177147)*h0 + (t*(-1375*z/391140576 - 3235/130380192) - 1585*z/391140576 + 2251/65190096)*h1 + (-6470*t^9/4074381 + 177709*t^8/4074381 - 7728358*t^7/12223143 + 62949716*t^6/12223143 - 107072510*t^5/4074381 + 2149519427*t^4/24446286 - 4735423429*t^3/24446286 + 2210923343*t^2/8148762 - 596702531*t/2716254 + 320072597/4074381)*hf
  norm_num at hh

private lemma cell_12_55 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2 - 8*z) + 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-304*z - 80) + t^6*(3776*z + 7072) + t^5*(-49552*z - 57680) + t^4*(301856*z + 403360) + t^3*(-1166608*z - 1524272) + t^2*(2633696*z + 3398800) + t*(-3172480*z - 4145696) + 1592960*z + 2074048:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(40/518319 - 521*z/6219828) + t^6*(599*z/2073276 + 2837/691092) + t^5*(-4988*z/172773 - 2669/230364) + t^4*(36155*z/230364 + 67061/230364) + t^3*(-200413*z/230364 - 114475/115182) + t^2*(81211*z/38394 + 52567/19197) + t*(-152963*z/57591 - 442259/115182) + 86279*z/57591 + 195539/115182)*h0 + (t*(521*z/49758624 - 5/518319) + z/25596 - 23/230364)*h1 + (2605*t^8/1036638 - 12965*t^7/518319 + 432887*t^6/3109914 + 227629*t^5/1554957 - 22284805*t^4/3109914 + 59715088*t^3/1554957 - 154541282*t^2/1554957 + 201949048*t/1554957 - 3929276/57591)*hf
  norm_num at hh

private lemma cell_12_56 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z - 6*t*z - 2*z + 8:ℝ)=0) (h1 : (t^8*(112*z + 192) + t^7*(-3024*z - 3888) + t^6*(31536*z + 38448) + t^5*(-173664*z - 229392) + t^4*(584928*z + 808272) + t^3*(-1275696*z - 1619568) + t^2*(1690608*z + 1895280) + t*(-1074480*z - 1545312) + 143072*z + 832864:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(5781718*z/1775780577 + 10008307/2367707436) + t^6*(-164811271*z/2367707436 - 17900314/197308953) + t^5*(16711439*z/27215028 + 7263323/9071676) + t^4*(-189906820*z/65769651 - 164864339/43846434) + t^3*(227536769*z/29230956 + 98727845/9743652) + t^2*(-38898479*z/3247884 - 8451493/541314) + t*(15742519*z/1623942 + 13730105/1082628) - 17126*z/5307 - 133249/31842)*h0 + (t*(-469621*z/14206244616 - 831457/18941659488) + 88141*z/9470829744 + 84305/6313886496)*h1 + (-1662914*t^9/591926859 + 22786559*t^8/394617906 - 1009708144*t^7/1775780577 + 1944856447*t^6/591926859 - 2113658134*t^5/197308953 + 1135710773*t^4/65769651 - 4687931440*t^3/591926859 - 12534831743*t^2/1183853718 + 26201629666*t/1775780577 - 271089538/34819227)*hf
  norm_num at hh

private lemma cell_12_57 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(-8*z - 6) + 6*z + 2:ℝ)=0) (h1 : (t^8*(112*z + 192) + t^7*(-4240*z - 5232) + t^6*(58480*z + 75936) + t^5*(-448912*z - 588864) + t^4*(2076208*z + 2699904) + t^3*(-5854864*z - 7619808) + t^2*(9861280*z + 12868704) + t*(-9107872*z - 11861232) + 3533664*z + 4595680:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-814345*z/8507307528 - 176491/708942294) + t^6*(8472833*z/2126826882 + 6033883/1417884588) + t^5*(-122519509*z/2835769176 - 6678428/118157049) + t^4*(1103423147*z/4253653764 + 992981263/2835769176) + t^3*(-3846636523*z/4253653764 - 407316478/354471147) + t^2*(4862216333*z/2835769176 + 1053054547/472628196) + t*(-14114270821*z/8507307528 - 6475850785/2835769176) + 2944113247*z/4253653764 + 513947807/708942294)*h0 + (t*(223279*z/68058460224 - 3899/1417884588) - 5221*z/2959063488 + 311/246588624)*h1 + (-62384*t^9/354471147 + 82829*t^8/15411789 - 171169925*t^7/2126826882 + 1462343935*t^6/2126826882 - 4906395935*t^5/1417884588 + 45306311455*t^4/4253653764 - 43007356111*t^3/2126826882 + 31668427711*t^2/1417884588 - 17257542971*t/1417884588 + 246003650/118157049)*hf
  norm_num at hh

private lemma cell_12_58 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2*z + t*(-6*z - 6) + 6*z - 6:ℝ)=0) (h1 : (t^8*(112*z + 192) + t^7*(-3792*z - 4464) + t^6*(44640*z + 60048) + t^5*(-306288*z - 395280) + t^4*(1231200*z + 1607040) + t^3*(-3035232*z - 3951504) + t^2*(4447872*z + 5804784) + t*(-3557520*z - 4630608) + 1189728*z + 1539648:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-791*z/1712421 - 715/1141614) + t^6*(169*z/14094 + 4/261) + t^5*(-23300*z/190269 - 20407/126846) + t^4*(9343*z/14094 + 2023/2349) + t^3*(-28265*z/14094 - 6133/2349) + t^2*(47921*z/14094 + 20861/4698) + t*(-7033*z/2349 - 3061/783) + 61*z/58 + 113/87)*h0 + (t*(71*z/13699368 + 49/9132912) - 13*z/9132912 - 5/1522152)*h1 + (196*t^9/570807 - 3962*t^8/570807 + 47308*t^7/570807 - 30542*t^6/63423 + 120895*t^5/63423 - 112621*t^4/21141 + 25954*t^3/2349 - 36878*t^2/2349 + 10214*t/783 - 1205/261)*hf
  norm_num at hh

private lemma cell_12_59 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(6 - 8*z) + 2*z:ℝ)=0) (h1 : (16*t^8 + t^7*(48 - 304*z) + t^6*(1696*z + 6912) + t^5*(-33280*z - 17760) + t^4*(108160*z + 219072) + t^3*(-405952*z - 403392) + t^2*(577504*z + 824304) + t*(-493840*z - 657552) + 169408*z + 205248:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(48865/1395564066 - 41581*z/2093346099) + t^6*(1677373/1395564066 - 800437*z/2093346099) + t^5*(4856695/465188022 - 4142434*z/697782033) + t^4*(94110215/1395564066 - 105719677*z/4186692198) + t^3*(300001301/1395564066 - 158212541*z/2093346099) + t^2*(52499141/232594011 - 161269573*z/697782033) + t*(356515465*z/4186692198 + 653118571/1395564066) - 50964155*z/322053246 - 22733723/107351082)*h0 + (t*(41581*z/16746768792 - 48865/11164512528) + 649379*z/33493537584 - 429943/11164512528)*h1 + (415810*t^8/697782033 - 932435*t^7/697782033 + 6325244*t^6/2093346099 + 390509096*t^5/2093346099 - 382199603*t^4/232594011 + 9920350090*t^3/2093346099 - 18478211198*t^2/2093346099 + 5385304018*t/697782033 - 2071030279/697782033)*hf
  norm_num at hh

private lemma cell_12_60 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2 - 4*z) + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(16*z - 272) + t^6*(1792 - 240*z) + t^5*(1552*z - 6176) + t^4*(14176 - 5952*z) + t^3*(15088*z - 28448) + t^2*(44368 - 22896*z) + t*(6352*z - 14672) + 5376*z - 8288:ℝ)=0) (h2 : (16*t^8 + t^7*(-176*z - 80) + t^6*(1536*z + 2176) + t^5*(-8960*z - 12080) + t^4*(26112*z + 32512) + t^3*(-29936*z - 46784) + t^2*(13536*z + 15280) + t*(13024 - 1472*z) - 1344*z - 1568:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(-127*z/387420489 - 217/516560652) + t^12*(19289*z/1549681956 + 4165/258280326) + t^11*(-50851*z/258280326 - 44141/172186884) + t^10*(1296211*z/774840978 + 281840/129140163) + t^9*(-6321203*z/774840978 - 5502145/516560652) + t^8*(3804649*z/172186884 + 1657903/57395628) + t^7*(-13225799*z/516560652 - 5800829/172186884) + t^6*(-9856451*z/516560652 - 954908/43046721) + t^5*(15846595*z/172186884 + 7414897/57395628) + t^4*(-84741857*z/774840978 - 20834290/129140163) + t^3*(60772787*z/1549681956 + 34446773/516560652) + t^2*(49595929*z/516560652 - 15506717/172186884) + t*(-58798195*z/1549681956 - 51211019/258280326) - 118118945*z/774840978 + 40830887/129140163)*h0 + (t^7*(127*z/3099363912 + 217/4132485216) + t^6*(-6811*z/6198727824 - 1487/1033121304) + t^5*(1409*z/129140163 + 9785/688747536) + t^4*(-292961*z/6198727824 - 254341/4132485216) + t^3*(988877*z/12397455648 + 429737/4132485216) + t^2*(-32243*z/1033121304 - 27727/688747536) + t*(6023*z/387420489 + 83725/4132485216) + 943531*z/12397455648 + 406363/4132485216)*h1 + (7*z/104976 - 5/34992)*h2 + (-254*t^14/129140163 + 9970*t^13/129140163 - 499541*t^12/387420489 + 4655018*t^11/387420489 - 53729555*t^10/774840978 + 22714321*t^9/86093442 - 546484033*t^8/774840978 + 1108619921*t^7/774840978 - 293781089*t^6/129140163 + 1035629561*t^5/387420489 - 1807753667*t^4/774840978 + 1051703543*t^3/774840978 + 195569233*t^2/258280326 - 92862419*t/86093442 - 41264132/129140163)*hf
  norm_num at hh

private lemma cell_12_61 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2 - 8*z) + 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-112*z - 272) + t^6*(2000*z + 2656) + t^5*(-15280*z - 18512) + t^4*(65600*z + 82624) + t^3*(-168592*z - 221312) + t^2*(252368*z + 341248) + t*(-205168*z - 260336) + 63776*z + 83872:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(11*z/65610 - 13/87480) + t^6*(-19*z/6561 - 17/17496) + t^5*(1229*z/43740 + 527/14580) + t^4*(-365*z/1944 - 8069/29160) + t^3*(5689*z/7290 + 31313/29160) + t^2*(-9097*z/4860 - 11597/4860) + t*(69611*z/29160 + 4139/1458) - 16621*z/14580 - 6284/3645)*h0 + (t*(13/699840 - 11*z/524880) - 47*z/2099520 + 187/699840)*h1 + (-11*t^8/10935 + 227*t^7/14580 - 5129*t^6/131220 - 76333*t^5/131220 + 323419*t^4/65610 - 2175787*t^3/131220 + 3665591*t^2/131220 - 2877007*t/131220 + 392849/65610)*hf
  norm_num at hh

private lemma cell_12_62 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(6 - 8*z) + 2*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-112*z - 144) + t^6*(1264*z + 1152) + t^5*(-6064*z - 7392) + t^4*(16864*z + 23808) + t^3*(-26512*z - 39648) + t^2*(18928*z + 33744) + t*(5136 - 9424*z) + 1216*z - 6432:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-2315*z/13817466 - 79/2302911) + t^6*(20603*z/6908733 + 18127/4605822) + t^5*(-66907*z/2302911 - 33415/767637) + t^4*(2188343*z/13817466 + 486565/2302911) + t^3*(-3164156*z/6908733 - 2647183/4605822) + t^2*(1563002*z/2302911 + 1272397/1535274) + t*(-2903614*z/6908733 - 2076551/4605822) - 80429*z/1062882 + 38809/354294)*h0 + (t*(2315*z/110539728 + 79/18423288) - 5059*z/110539728 - 4643/18423288)*h1 + (2315*t^8/2302911 - 17053*t^7/2302911 - 28456*t^6/531441 + 4797443*t^5/6908733 - 2037050*t^4/767637 + 32718952*t^3/6908733 - 25258592*t^2/6908733 - 510257*t/2302911 + 476687/2302911)*hf
  norm_num at hh

private lemma cell_12_63 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t*(6 - 6*z) + 2*z:ℝ)=0) (h1 : (t*(864 - 1440*z) + 736*z + 1632:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/6)*h0 + (17/23328 - z/11664)*h1 + (46/729 - 10*t/81)*hf
  norm_num at hh

private lemma pair_12_5_15 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z - 3:ℝ)=0) (h1 : (t + z - 3:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/9 - z/9)*h0 + (z/9 - 1/9)*h1 + (-1/3)*hf
  norm_num at hh

private lemma pair_12_5_39 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z - 3:ℝ)=0) (h1 : (t - z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/27 - 2/9)*h0 + (2/9 - z/27)*h1 + (1/27)*hf
  norm_num at hh

private lemma pair_12_5_45 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z - 3:ℝ)=0) (h1 : (t - z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/27 - 2/9)*h0 + (2/9 - z/27)*h1 + (1/27)*hf
  norm_num at hh

private lemma pair_12_5_53 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z - 3:ℝ)=0) (h1 : (t - z - 3:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/3 - z/3)*h0 + (z/3 - 1/3)*h1 + (-1/3)*hf
  norm_num at hh

private lemma pair_12_15_39 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + z - 3:ℝ)=0) (h1 : (t - z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-2*z/3 - 1)*h0 + (2*z/3 + 1)*h1 + (4/3)*hf
  norm_num at hh

private lemma pair_12_15_45 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + z - 3:ℝ)=0) (h1 : (t - z + 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-2*z/3 - 1)*h0 + (2*z/3 + 1)*h1 + (4/3)*hf
  norm_num at hh

private lemma pair_12_15_53 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + z - 3:ℝ)=0) (h1 : (t - z - 3:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/6 - 1/6)*h0 + (1/6 - z/6)*h1 + (-1/3)*hf
  norm_num at hh

private lemma pair_12_39_45 (z t : ℝ) (hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z + 2:ℝ)=0) (h2 : (t^8*(8128 - 3472*z) + t^7*(28720 - 14128*z) + t^6*(49600 - 2176*z) + t^5*(-78880*z - 91568) + t^4*(272480*z + 316096) + t^3*(-493168*z - 716672) + t^2*(564464*z + 709408) + t*(-308896*z - 387584) + 63776*z + 83872:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-191*z/217971 - 641/435942) + t^6*(6002*z/217971 + 7789/217971) + t^5*(-22985*z/72657 - 30010/72657) + t^4*(825809*z/435942 + 1077019/435942) + t^3*(-1373179*z/217971 - 3581329/435942) + t^2*(1683061*z/145314 + 2196719/145314) + t*(-2420987*z/217971 - 3174010/217971) + 992471*z/217971 + 1358962/217971)*h0 + (457*z/62775648 + 199/20925216)*h2 + (99169*t^8/3923478 + 400093*t^7/3923478 + 85094*t^6/1961739 + 505910*t^5/1961739 - 350429*t^4/3923478 - 10631111*t^3/3923478 + 14660072*t^2/1961739 - 17377462*t/1961739 + 8021438/1961739)*hf
  norm_num at hh

private lemma pair_12_39_53 (z t : ℝ) (_hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z + 2:ℝ)=0) (h1 : (t - z - 3:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/5)*h0 + (-1/5)*h1
  norm_num at hh

private lemma pair_12_45_53 (z t : ℝ) (_hf : z^2 - z - 3=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z + 1)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z + 2:ℝ)=0) (h1 : (t - z - 3:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/5)*h0 + (-1/5)*h1
  norm_num at hh

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_0 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 0) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_0 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_1 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 1) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_1 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_2 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 2) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_2 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_3 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 3) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_3 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 192*t^7*z - 128*t^7 + 144*t^6*z^4 - 640*t^6*z^3 + 192*t^6*z^2 + 1152*t^6*z + 448*t^6 + 112*t^5*z^6 - 640*t^5*z^5 + 448*t^5*z^4 + 2144*t^5*z^3 - 1168*t^5*z^2 - 2880*t^5*z - 896*t^5 + 32*t^4*z^8 - 128*t^4*z^7 - 496*t^4*z^6 + 2672*t^4*z^5 - 1232*t^4*z^4 - 5152*t^4*z^3 + 928*t^4*z^2 + 3840*t^4*z + 1120*t^4 + 64*t^3*z^9 - 592*t^3*z^8 + 1648*t^3*z^7 - 224*t^3*z^6 - 4288*t^3*z^5 + 128*t^3*z^4 + 7872*t^3*z^3 + 1328*t^3*z^2 - 2880*t^3*z - 896*t^3 + 32*t^2*z^10 - 320*t^2*z^9 + 1008*t^2*z^8 - 272*t^2*z^7 - 4064*t^2*z^6 + 5024*t^2*z^5 + 3696*t^2*z^4 - 5568*t^2*z^3 - 2432*t^2*z^2 + 1152*t^2*z + 448*t^2 + 32*t*z^10 - 352*t*z^9 + 1488*t*z^8 - 2992*t*z^7 + 2544*t*z^6 + 960*t*z^5 - 3904*t*z^4 + 1248*t*z^3 + 1296*t*z^2 - 192*t*z - 128*t + 32*z^9 - 272*z^8 + 720*z^7 - 432*z^6 - 656*z^5 + 720*z^4 + 96*z^3 - 224*z^2 + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 + 496*t^6*z - 128*t^6 - 112*t^5*z^4 + 528*t^5*z^3 - 256*t^5*z^2 - 816*t^5*z - 416*t^5 - 32*t^4*z^6 + 96*t^4*z^5 + 496*t^4*z^4 - 1888*t^4*z^3 + 832*t^4*z^2 + 320*t^4*z + 1888*t^4 - 64*t^3*z^7 + 528*t^3*z^6 - 1312*t^3*z^5 + 496*t^3*z^4 + 848*t^3*z^3 + 2208*t^3*z^2 - 3120*t^3*z + 2176*t^3 - 32*t^2*z^8 + 288*t^2*z^7 - 816*t^2*z^6 + 320*t^2*z^5 + 1936*t^2*z^4 - 2128*t^2*z^3 - 16*t^2*z^2 - 832*t^2*z + 1552*t^2 - 32*t*z^8 + 320*t*z^7 - 1264*t*z^6 + 2688*t*z^5 - 3648*t*z^4 + 3456*t*z^3 - 3584*t*z^2 + 5536*t*z - 6512*t - 32*z^7 + 240*z^6 - 576*z^5 + 576*z^4 - 496*z^3 + 512*z^2 - 1072*z + 688)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_4 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 4) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_4 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_5 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 5) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : (t - 2*z - 3:ℝ)=0 := by
  apply cell_12_5 z t hf hn0 hn1 hn2 hn3
  · have hr : (288*t*z^11 - 1344*t*z^10 - 480*t*z^9 + 6144*t*z^8 - 3840*t*z^7 - 3840*t*z^6 + 3072*t*z^5 + 576*z^12 - 96*z^11 - 2688*z^10 + 1056*z^9 + 2688*z^8 - 768*z^7 - 768*z^6:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-288*t*z^9 + 1056*t*z^8 + 672*t*z^7 - 2304*t*z^6 + 3552*t*z^5 + 480*t*z^4 + 8064*t*z^3 + 9504*t*z^2 + 33696*t*z + 62208*t - 576*z^10 - 480*z^9 + 480*z^8 - 2016*z^7 - 3264*z^6 - 8544*z^5 - 17568*z^4 - 43200*z^3 - 95904*z^2 - 225504*z - 513216)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_6 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 6) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_6 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 4*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_7 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 7) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_7 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 6*t*z - 4*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 144*t^7*z^2 - 320*t^7*z - 128*t^7 + 480*t^6*z^4 - 2080*t^6*z^3 + 1472*t^6*z^2 + 2048*t^6*z + 448*t^6 + 704*t^5*z^6 - 4384*t^5*z^5 + 7744*t^5*z^4 + 1536*t^5*z^3 - 9040*t^5*z^2 - 5568*t^5*z - 896*t^5 + 384*t^4*z^8 - 2816*t^4*z^7 + 7440*t^4*z^6 - 4112*t^4*z^5 - 13680*t^4*z^4 + 8800*t^4*z^3 + 18848*t^4*z^2 + 8320*t^4*z + 1120*t^4 + 384*t^3*z^9 - 2224*t^3*z^8 + 4656*t^3*z^7 - 5552*t^3*z^6 + 6720*t^3*z^5 + 4288*t^3*z^4 - 16128*t^3*z^3 - 19472*t^3*z^2 - 7360*t^3*z - 896*t^3 + 96*t^2*z^10 + 96*t^2*z^9 - 1712*t^2*z^8 + 3056*t^2*z^7 - 3904*t^2*z^6 + 3104*t^2*z^5 + 3776*t^2*z^4 + 10400*t^2*z^3 + 10624*t^2*z^2 + 3840*t^2*z + 448*t^2 + 208*t*z^10 - 624*t*z^9 + 1488*t*z^8 - 2864*t*z^7 + 656*t*z^6 - 1312*t*z^5 - 3200*t*z^4 - 2816*t*z^3 - 2864*t*z^2 - 1088*t*z - 128*t + 96*z^10 - 96*z^9 + 80*z^8 + 784*z^7 - 368*z^6 - 16*z^5 + 592*z^4 + 288*z^3 + 288*z^2 + 128*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-144*t^7 - 480*t^6*z^2 + 1600*t^6*z - 1312*t^6 - 704*t^5*z^4 + 3680*t^5*z^3 - 6176*t^5*z^2 + 3328*t^5*z - 6160*t^5 - 384*t^4*z^6 + 2432*t^4*z^5 - 6160*t^4*z^4 + 5248*t^4*z^3 + 448*t^4*z^2 + 7392*t^4*z - 10112*t^4 - 384*t^3*z^7 + 1840*t^3*z^6 - 3968*t^3*z^5 + 7104*t^3*z^4 - 11520*t^3*z^3 + 5504*t^3*z^2 - 12928*t^3*z + 23056*t^3 - 96*t^2*z^8 - 192*t^2*z^7 + 1232*t^2*z^6 - 2400*t^2*z^5 + 5200*t^2*z^4 - 5104*t^2*z^3 + 6720*t^2*z^2 - 18992*t^2*z - 9456*t^2 - 208*t*z^8 + 416*t*z^7 - 1696*t*z^6 + 2416*t*z^5 - 3328*t*z^4 + 5232*t*z^3 - 1552*t*z^2 + 16960*t*z + 15168*t - 96*z^8 - 368*z^6 - 1152*z^5 - 1888*z^4 - 5328*z^3 - 11584*z^2 - 27856*z - 62896)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_8 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 8) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_8 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_9 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 9) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_9 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 4*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_10 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 10) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_10 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 6*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_11 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 11) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_11 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 8*t*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 144*t^7*z^2 - 384*t^7*z + 480*t^6*z^4 - 2512*t^6*z^3 + 3392*t^6*z^2 - 64*t^6*z + 704*t^5*z^6 - 5344*t^5*z^5 + 14224*t^5*z^4 - 13744*t^5*z^3 + 1280*t^5*z^2 + 384*t^4*z^8 - 3520*t^4*z^7 + 13488*t^4*z^6 - 26816*t^4*z^5 + 26112*t^4*z^4 - 8032*t^4*z^3 - 32*t^4*z^2 + 384*t^3*z^9 - 2736*t^3*z^8 + 5680*t^3*z^7 + 1936*t^3*z^6 - 18960*t^3*z^5 + 15728*t^3*z^4 + 128*t^3*z^3 + 96*t^2*z^10 + 16*t^2*z^9 - 3376*t^2*z^8 + 11088*t^2*z^7 - 11344*t^2*z^6 + 2032*t^2*z^5 + 192*t^2*z^3 + 208*t*z^10 - 944*t*z^9 + 736*t*z^8 + 1616*t*z^7 - 2944*t*z^6 + 2864*t*z^5 - 1536*t*z^4 + 96*z^10 - 336*z^9 + 96*z^8 + 624*z^7 - 528*z^6 - 96*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-144*t^7 - 480*t^6*z^2 + 2032*t^6*z - 2800*t^6 - 704*t^5*z^4 + 4640*t^5*z^3 - 11696*t^5*z^2 + 15968*t^5*z - 20400*t^5 - 384*t^4*z^6 + 3136*t^4*z^5 - 11504*t^4*z^4 + 24720*t^4*z^3 - 35904*t^4*z^2 + 46288*t^4*z - 61392*t^4 - 384*t^3*z^7 + 2352*t^3*z^6 - 4480*t^3*z^5 + 640*t^3*z^4 + 6160*t^3*z^3 - 7648*t^3*z^2 + 10704*t^3*z - 12240*t^3 - 96*t^2*z^8 - 112*t^2*z^7 + 2976*t^2*z^6 - 8448*t^2*z^5 + 11824*t^2*z^4 - 15552*t^2*z^3 + 19920*t^2*z^2 - 26928*t^2*z + 32832*t^2 - 208*t*z^8 + 736*t*z^7 - 624*t*z^6 - 32*t*z^5 + 1040*t*z^4 - 1920*t*z^3 + 2736*t*z^2 - 3024*t*z + 5184*t - 96*z^8 + 240*z^7 - 144*z^6 - 48*z^5 + 48*z^4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_12 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 12) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_12 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 + 64*t^7*z - 128*t^7 + 128*t^6*z^3 - 128*t^6*z^2 - 640*t^6*z + 448*t^6 + 32*t^5*z^5 + 208*t^5*z^4 - 1056*t^5*z^3 - 208*t^5*z^2 + 2496*t^5*z - 896*t^5 + 144*t^4*z^6 - 304*t^4*z^5 - 1712*t^4*z^4 + 3424*t^4*z^3 + 3168*t^4*z^2 - 5120*t^4*z + 1120*t^4 + 16*t^3*z^8 + 112*t^3*z^7 - 1024*t^3*z^6 + 512*t^3*z^5 + 5280*t^3*z^4 - 3648*t^3*z^3 - 8592*t^3*z^2 + 6080*t^3*z - 896*t^3 + 32*t^2*z^9 - 80*t^2*z^8 - 848*t^2*z^7 + 3040*t^2*z^6 + 736*t^2*z^5 - 8416*t^2*z^4 - 1984*t^2*z^3 + 10432*t^2*z^2 - 4224*t^2*z + 448*t^2 + 32*t*z^10 - 288*t*z^9 + 752*t*z^8 - 48*t*z^7 - 1280*t*z^6 - 2464*t*z^5 + 4752*t*z^4 + 5728*t*z^3 - 6064*t*z^2 + 1600*t*z - 128*t + 32*z^10 - 320*z^9 + 976*z^8 - 240*z^7 - 3440*z^6 + 4560*z^5 - 112*z^4 - 2592*z^3 + 1376*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 - 128*t^6*z - 32*t^5*z^3 - 240*t^5*z^2 + 720*t^5*z + 208*t^5 - 144*t^4*z^4 + 160*t^4*z^3 + 1440*t^4*z^2 - 1504*t^4*z - 352*t^4 - 16*t^3*z^6 - 128*t^3*z^5 + 848*t^3*z^4 - 48*t^3*z^3 - 2784*t^3*z^2 + 720*t^3*z + 960*t^3 - 32*t^2*z^7 + 48*t^2*z^6 + 800*t^2*z^5 - 2096*t^2*z^4 - 432*t^2*z^3 + 1696*t^2*z^2 + 2384*t^2*z - 2960*t^2 - 32*t*z^8 + 256*t*z^7 - 592*t*z^6 + 224*t*z^5 - 272*t*z^4 + 2864*t*z^3 - 2704*t*z^2 + 160*t*z - 1888*t - 32*z^8 + 288*z^7 - 784*z^6 + 320*z^5 + 1408*z^4 - 2192*z^3 + 2144*z^2 - 1840*z + 3216)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_13 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 13) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_13 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 6*t*z - 4*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 64*t^7*z - 128*t^7 + 144*t^6*z^4 - 96*t^6*z^3 - 640*t^6*z^2 + 256*t^6*z + 448*t^6 + 112*t^5*z^6 + 176*t^5*z^5 - 1520*t^5*z^4 + 256*t^5*z^3 + 2672*t^5*z^2 - 192*t^5*z - 896*t^5 + 32*t^4*z^8 + 384*t^4*z^7 - 1424*t^4*z^6 - 1232*t^4*z^5 + 5552*t^4*z^4 + 1056*t^4*z^3 - 5792*t^4*z^2 - 640*t^4*z + 1120*t^4 + 176*t^3*z^9 - 80*t^3*z^8 - 2832*t^3*z^7 + 3984*t^3*z^6 + 7072*t^3*z^5 - 10656*t^3*z^4 - 5888*t^3*z^3 + 6448*t^3*z^2 + 1600*t^3*z - 896*t^3 + 336*t^2*z^10 - 1408*t^2*z^9 - 448*t^2*z^8 + 7632*t^2*z^7 - 3488*t^2*z^6 - 14240*t^2*z^5 + 8368*t^2*z^4 + 9184*t^2*z^3 - 3392*t^2*z^2 - 1536*t^2*z + 448*t^2 + 256*t*z^11 - 1392*t*z^10 + 944*t*z^9 + 6464*t*z^8 - 10800*t*z^7 - 4192*t*z^6 + 14384*t*z^5 - 240*t*z^4 - 5632*t*z^3 + 528*t*z^2 + 704*t*z - 128*t + 64*z^12 - 352*z^11 + 224*z^10 + 1728*z^9 - 3088*z^8 - 272*z^7 + 3984*z^6 - 2064*z^5 - 1648*z^4 + 1120*z^3 + 96*z^2 - 128*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 - 48*t^6*z + 160*t^6 - 112*t^5*z^4 - 288*t^5*z^3 + 896*t^5*z^2 - 224*t^5*z - 208*t^5 - 32*t^4*z^6 - 416*t^4*z^5 + 912*t^4*z^4 + 896*t^4*z^3 - 1920*t^4*z^2 - 288*t^4*z - 256*t^4 - 176*t^3*z^7 - 96*t^3*z^6 + 2208*t^3*z^5 - 2064*t^3*z^4 - 2512*t^3*z^3 + 1952*t^3*z^2 + 304*t^3*z - 288*t^3 - 336*t^2*z^8 + 1072*t^2*z^7 + 512*t^2*z^6 - 3904*t^2*z^5 + 1120*t^2*z^4 + 3648*t^2*z^3 - 1360*t^2*z^2 + 400*t^2*z - 288*t^2 - 256*t*z^9 + 1136*t*z^8 - 576*t*z^7 - 3632*t*z^6 + 5440*t*z^5 - 1264*t*z^4 + 672*t*z^3 - 2880*t*z^2 + 4768*t*z - 4400*t - 64*z^10 + 288*z^9 - 128*z^8 - 992*z^7 + 1712*z^6 - 992*z^5 + 160*z^4 - 752*z^3 + 1376*z^2 - 2000*z + 2032)*hf
  · have hr : (16*t^8 + 144*t^7*z^2 - 320*t^7*z - 128*t^7 + 480*t^6*z^4 - 2080*t^6*z^3 + 1472*t^6*z^2 + 2048*t^6*z + 448*t^6 + 704*t^5*z^6 - 4384*t^5*z^5 + 7744*t^5*z^4 + 1536*t^5*z^3 - 9040*t^5*z^2 - 5568*t^5*z - 896*t^5 + 384*t^4*z^8 - 2816*t^4*z^7 + 7440*t^4*z^6 - 4112*t^4*z^5 - 13680*t^4*z^4 + 8800*t^4*z^3 + 18848*t^4*z^2 + 8320*t^4*z + 1120*t^4 + 384*t^3*z^9 - 2224*t^3*z^8 + 4656*t^3*z^7 - 5552*t^3*z^6 + 6720*t^3*z^5 + 4288*t^3*z^4 - 16128*t^3*z^3 - 19472*t^3*z^2 - 7360*t^3*z - 896*t^3 + 96*t^2*z^10 + 96*t^2*z^9 - 1712*t^2*z^8 + 3056*t^2*z^7 - 3904*t^2*z^6 + 3104*t^2*z^5 + 3776*t^2*z^4 + 10400*t^2*z^3 + 10624*t^2*z^2 + 3840*t^2*z + 448*t^2 + 208*t*z^10 - 624*t*z^9 + 1488*t*z^8 - 2864*t*z^7 + 656*t*z^6 - 1312*t*z^5 - 3200*t*z^4 - 2816*t*z^3 - 2864*t*z^2 - 1088*t*z - 128*t + 96*z^10 - 96*z^9 + 80*z^8 + 784*z^7 - 368*z^6 - 16*z^5 + 592*z^4 + 288*z^3 + 288*z^2 + 128*z + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-144*t^7 - 480*t^6*z^2 + 1600*t^6*z - 1312*t^6 - 704*t^5*z^4 + 3680*t^5*z^3 - 6176*t^5*z^2 + 3328*t^5*z - 6160*t^5 - 384*t^4*z^6 + 2432*t^4*z^5 - 6160*t^4*z^4 + 5248*t^4*z^3 + 448*t^4*z^2 + 7392*t^4*z - 10112*t^4 - 384*t^3*z^7 + 1840*t^3*z^6 - 3968*t^3*z^5 + 7104*t^3*z^4 - 11520*t^3*z^3 + 5504*t^3*z^2 - 12928*t^3*z + 23056*t^3 - 96*t^2*z^8 - 192*t^2*z^7 + 1232*t^2*z^6 - 2400*t^2*z^5 + 5200*t^2*z^4 - 5104*t^2*z^3 + 6720*t^2*z^2 - 18992*t^2*z - 9456*t^2 - 208*t*z^8 + 416*t*z^7 - 1696*t*z^6 + 2416*t*z^5 - 3328*t*z^4 + 5232*t*z^3 - 1552*t*z^2 + 16960*t*z + 15168*t - 96*z^8 - 368*z^6 - 1152*z^5 - 1888*z^4 - 5328*z^3 - 11584*z^2 - 27856*z - 62896)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_14 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 14) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_14 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 8*t*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 128*t^7*z + 144*t^6*z^4 - 336*t^6*z^3 + 64*t^6*z^2 - 64*t^6*z + 112*t^5*z^6 - 112*t^5*z^5 - 848*t^5*z^4 + 912*t^5*z^3 + 512*t^5*z^2 + 32*t^4*z^8 + 272*t^4*z^7 - 1888*t^4*z^6 + 2624*t^4*z^5 - 192*t^4*z^4 - 96*t^4*z^3 - 32*t^4*z^2 + 176*t^3*z^9 - 640*t^3*z^8 - 720*t^3*z^7 + 3984*t^3*z^6 - 656*t^3*z^5 - 4176*t^3*z^4 - 128*t^3*z^3 + 336*t^2*z^10 - 2400*t^2*z^9 + 5424*t^2*z^8 - 2896*t^2*z^7 - 2784*t^2*z^6 + 1008*t^2*z^5 + 256*t^2*z^4 + 192*t^2*z^3 + 256*t*z^11 - 2128*t*z^10 + 5760*t*z^9 - 3424*t*z^8 - 7808*t*z^7 + 8160*t*z^6 + 2544*t*z^5 - 768*t*z^4 + 64*z^12 - 544*z^11 + 1472*z^10 - 720*z^9 - 2624*z^8 + 3280*z^7 - 208*z^6 - 864*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 + 192*t^6*z - 304*t^6 - 112*t^5*z^4 + 512*t^5*z^2 - 400*t^5*z + 624*t^5 - 32*t^4*z^6 - 304*t^4*z^5 + 1488*t^4*z^4 - 2048*t^4*z^3 + 2608*t^4*z^2 - 3440*t^4*z + 4416*t^4 - 176*t^3*z^7 + 464*t^3*z^6 + 656*t^3*z^5 - 1936*t^3*z^4 + 688*t^3*z^3 - 944*t^3*z^2 + 1248*t^3*z - 1584*t^3 - 336*t^2*z^8 + 2064*t^2*z^7 - 4368*t^2*z^6 + 4720*t^2*z^5 - 5600*t^2*z^4 + 7552*t^2*z^3 - 9504*t^2*z^2 + 12960*t^2*z - 15552*t^2 - 256*t*z^9 + 1872*t*z^8 - 4656*t*z^7 + 4384*t*z^6 - 1776*t*z^5 + 3216*t*z^4 - 4656*t*z^3 + 5760*t*z^2 - 8208*t*z + 9072*t - 64*z^10 + 480*z^9 - 1184*z^8 + 976*z^7 + 48*z^6 - 304*z^5 + 48*z^4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_15 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 15) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : (t + z - 3:ℝ)=0 := by
  apply cell_12_15 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 8*t*z + 2*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8*z^4 + 80*t^7*z^5 - 192*t^7*z^4 + 176*t^6*z^6 - 768*t^6*z^5 + 704*t^6*z^4 + 240*t^5*z^7 - 1472*t^5*z^6 + 2416*t^5*z^5 - 576*t^5*z^4 + 208*t^4*z^8 - 1616*t^4*z^7 + 3792*t^4*z^6 - 2016*t^4*z^5 - 1312*t^4*z^4 + 112*t^3*z^9 - 1008*t^3*z^8 + 2784*t^3*z^7 - 1408*t^3*z^6 - 3280*t^3*z^5 + 1728*t^3*z^4 + 32*t^2*z^10 - 304*t^2*z^9 + 784*t^2*z^8 + 608*t^2*z^7 - 4912*t^2*z^6 + 4800*t^2*z^5 + 448*t^2*z^4 + 32*t*z^10 - 400*t*z^9 + 1840*t*z^8 - 3536*t*z^7 + 1600*t*z^6 + 2320*t*z^5 - 960*t*z^4 + 16*z^9 - 160*z^8 + 496*z^7 - 336*z^6 - 480*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 16*t^8*z - 64*t^8 - 80*t^7*z^3 + 112*t^7*z^2 - 128*t^7*z + 208*t^7 - 176*t^6*z^4 + 592*t^6*z^3 - 640*t^6*z^2 + 1136*t^6*z - 784*t^6 - 240*t^5*z^5 + 1232*t^5*z^4 - 1904*t^5*z^3 + 2368*t^5*z^2 - 3344*t^5*z + 3760*t^5 - 208*t^4*z^6 + 1408*t^4*z^5 - 3008*t^4*z^4 + 3232*t^4*z^3 - 4480*t^4*z^2 + 5216*t^4*z - 8224*t^4 - 112*t^3*z^7 + 896*t^3*z^6 - 2224*t^3*z^5 + 1872*t^3*z^4 - 1520*t^3*z^3 + 2368*t^3*z^2 - 2192*t^3*z + 4912*t^3 - 32*t^2*z^8 + 272*t^2*z^7 - 608*t^2*z^6 - 400*t^2*z^5 + 2688*t^2*z^4 - 3312*t^2*z^3 + 4304*t^2*z^2 - 5632*t^2*z + 7280*t^2 - 32*t*z^8 + 368*t*z^7 - 1568*t*z^6 + 3072*t*z^5 - 3232*t*z^4 + 3664*t*z^3 - 5072*t*z^2 + 5920*t*z - 9296*t - 16*z^7 + 144*z^6 - 400*z^5 + 368*z^4 - 352*z^3 + 608*z^2 - 448*z + 1376)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_16 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 16) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_16 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*z^3 - 2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4*z - 2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_17 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 17) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_17 z t hf hn0 hn1 hn2 hn3
  · have hr : (16*t*z^10 - 240*t*z^9 + 1280*t*z^8 - 2560*t*z^7 + 4096*t*z^5:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t*z^8 + 224*t*z^7 - 1104*t*z^6 + 2128*t*z^5 - 1184*t*z^4 + 1104*t*z^3 - 2448*t*z^2 + 864*t*z - 6480*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_18 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 18) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_18 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_19 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 19) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_19 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 - 2*t*z - 4*t + 4*z^3 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 4*z - 4)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 192*t^7*z - 128*t^7 - 64*t^6*z^3 + 640*t^6*z^2 + 1152*t^6*z + 448*t^6 + 32*t^5*z^5 - 176*t^5*z^4 - 736*t^5*z^3 - 2512*t^5*z^2 - 2880*t^5*z - 896*t^5 - 112*t^4*z^6 + 848*t^4*z^5 + 720*t^4*z^4 + 608*t^4*z^3 + 3168*t^4*z^2 + 3840*t^4*z + 1120*t^4 + 16*t^3*z^8 - 16*t^3*z^7 - 896*t^3*z^6 - 96*t^3*z^4 + 2112*t^3*z^3 - 912*t^3*z^2 - 2880*t^3*z - 896*t^3 - 32*t^2*z^9 + 240*t^2*z^8 + 304*t^2*z^7 - 1440*t^2*z^6 + 480*t^2*z^5 + 1056*t^2*z^4 - 2688*t^2*z^3 - 1088*t^2*z^2 + 1152*t^2*z + 448*t^2 + 32*t*z^10 - 416*t*z^9 + 1392*t*z^8 - 1712*t*z^7 + 128*t*z^6 + 2144*t*z^5 - 1776*t*z^4 + 672*t*z^3 + 848*t*z^2 - 192*t*z - 128*t + 32*z^10 - 128*z^9 + 16*z^8 + 400*z^7 - 240*z^6 - 432*z^5 + 272*z^4 + 96*z^3 - 160*z^2 + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 64*t^6*z - 576*t^6 - 32*t^5*z^3 + 144*t^5*z^2 + 784*t^5*z + 3728*t^5 + 112*t^4*z^4 - 736*t^4*z^3 - 1120*t^4*z^2 - 3936*t^4*z - 10464*t^4 - 16*t^3*z^6 + 848*t^3*z^4 + 848*t^3*z^3 + 3488*t^3*z^2 + 3920*t^3*z + 15296*t^3 + 32*t^2*z^7 - 208*t^2*z^6 - 416*t^2*z^5 + 400*t^2*z^4 - 1328*t^2*z^3 - 1184*t^2*z^2 - 2480*t^2*z - 4944*t^2 - 32*t*z^8 + 384*t*z^7 - 1104*t*z^6 + 1760*t*z^5 - 1680*t*z^4 + 1456*t*z^3 - 1808*t*z^2 + 1888*t*z - 4384*t - 32*z^8 + 96*z^7 - 16*z^6 - 128*z^5 + 64*z^4 + 112*z^3 + 32*z^2 + 272*z + 528)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 + 64*t^7*z - 128*t^7 + 48*t^6*z^4 - 64*t^6*z^3 + 320*t^6*z^2 - 640*t^6*z + 448*t^6 - 16*t^5*z^6 - 64*t^5*z^5 - 32*t^5*z^4 + 672*t^5*z^3 - 1552*t^5*z^2 + 2496*t^5*z - 896*t^5 + 64*t^4*z^7 - 48*t^4*z^6 - 80*t^4*z^5 + 48*t^4*z^4 - 2336*t^4*z^3 + 5408*t^4*z^2 - 5120*t^4*z + 1120*t^4 - 112*t^3*z^8 + 240*t^3*z^7 + 160*t^3*z^6 + 192*t^3*z^5 - 1856*t^3*z^4 + 5952*t^3*z^3 - 10832*t^3*z^2 + 6080*t^3*z - 896*t^3 + 96*t^2*z^9 - 176*t^2*z^8 - 784*t^2*z^7 + 1568*t^2*z^6 - 736*t^2*z^5 + 4112*t^2*z^4 - 10624*t^2*z^3 + 11776*t^2*z^2 - 4224*t^2*z + 448*t^2 - 32*t*z^10 - 96*t*z^9 + 1392*t*z^8 - 2864*t*z^7 + 752*t*z^6 + 2048*t*z^5 - 5024*t*z^4 + 9760*t*z^3 - 6512*t*z^2 + 1600*t*z - 128*t + 96*z^10 - 576*z^9 + 560*z^8 + 2320*z^7 - 4976*z^6 + 1712*z^5 + 2704*z^4 - 3360*z^3 + 1440*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 + 16*t^6*z - 448*t^6 + 16*t^5*z^4 + 80*t^5*z^3 + 160*t^5*z^2 - 272*t^5*z + 1760*t^5 - 64*t^4*z^5 - 16*t^4*z^4 - 128*t^4*z^3 - 224*t^4*z^2 + 1728*t^4*z - 4352*t^4 + 112*t^3*z^6 - 128*t^3*z^5 + 48*t^3*z^4 - 528*t^3*z^3 + 1472*t^3*z^2 - 6064*t^3*z + 9184*t^3 - 96*t^2*z^7 + 80*t^2*z^6 + 576*t^2*z^5 - 752*t^2*z^4 + 1712*t^2*z^3 - 4656*t^2*z^2 + 11104*t^2*z - 14640*t^2 + 32*t*z^8 + 128*t*z^7 - 1168*t*z^6 + 2080*t*z^5 - 2176*t*z^4 + 2016*t*z^3 + 512*t*z^2 - 3200*t*z + 4848*t - 96*z^8 + 480*z^7 - 368*z^6 - 1248*z^5 + 2624*z^4 - 2832*z^3 + 2336*z^2 - 2800*z + 2768)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_20 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 20) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_20 z t hf hn0 hn1 hn2 hn3
  · have hr : (16*t*z^10 - 240*t*z^9 + 1280*t*z^8 - 2560*t*z^7 + 4096*t*z^5:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t*z^8 + 224*t*z^7 - 1104*t*z^6 + 2128*t*z^5 - 1184*t*z^4 + 1104*t*z^3 - 2448*t*z^2 + 864*t*z - 6480*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_21 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 21) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_21 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 6*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_22 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 22) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_22 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 6*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_23 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 23) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_23 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t*z - 4*t + 2*z^3 - 2*z^2 + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 320*t^7*z - 128*t^7 + 144*t^6*z^4 - 1184*t^6*z^3 + 1920*t^6*z^2 + 2048*t^6*z + 448*t^6 + 112*t^5*z^6 - 1456*t^5*z^5 + 5584*t^5*z^4 - 3264*t^5*z^3 - 10384*t^5*z^2 - 5568*t^5*z - 896*t^5 + 32*t^4*z^8 - 640*t^4*z^7 + 4272*t^4*z^6 - 9744*t^4*z^5 - 2896*t^4*z^4 + 19360*t^4*z^3 + 21088*t^4*z^2 + 8320*t^4*z + 1120*t^4 - 48*t^3*z^9 + 752*t^3*z^8 - 3856*t^3*z^7 + 5136*t^3*z^6 + 10464*t^3*z^5 - 12064*t^3*z^4 - 28288*t^3*z^3 - 21712*t^3*z^2 - 7360*t^3*z - 896*t^3 + 16*t^2*z^10 - 192*t^2*z^9 + 448*t^2*z^8 + 2384*t^2*z^7 - 10272*t^2*z^6 + 2016*t^2*z^5 + 14768*t^2*z^4 + 18080*t^2*z^3 + 11968*t^2*z^2 + 3840*t^2*z + 448*t^2 - 16*t*z^10 + 240*t*z^9 - 1216*t*z^8 + 1936*t*z^7 + 1312*t*z^6 - 1456*t*z^5 - 6448*t*z^4 - 5312*t*z^3 - 3312*t*z^2 - 1088*t*z - 128*t - 16*z^8 + 176*z^7 - 560*z^6 + 176*z^5 + 912*z^4 + 608*z^3 + 352*z^2 + 128*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 + 1040*t^6*z - 1312*t^6 - 112*t^5*z^4 + 1344*t^5*z^3 - 4576*t^5*z^2 + 2720*t^5*z - 624*t^5 - 32*t^4*z^6 + 608*t^4*z^5 - 3760*t^4*z^4 + 7808*t^4*z^3 - 576*t^4*z^2 + 3488*t^4*z - 19328*t^4 + 48*t^3*z^7 - 704*t^3*z^6 + 3296*t^3*z^5 - 3952*t^3*z^4 - 4528*t^3*z^3 - 4320*t^3*z^2 + 10384*t^3*z + 19136*t^3 - 16*t^2*z^8 + 176*t^2*z^7 - 320*t^2*z^6 - 2176*t^2*z^5 + 7136*t^2*z^4 - 1408*t^2*z^3 + 5232*t^2*z^2 - 17072*t^2*z - 13344*t^2 + 16*t*z^8 - 224*t*z^7 + 1040*t*z^6 - 1568*t*z^5 + 240*t*z^4 - 3008*t*z^3 + 4160*t*z^2 + 448*t*z + 16240*t + 16*z^6 - 160*z^5 + 448*z^4 - 208*z^3 + 224*z^2 - 1008*z - 688)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 64*t^7*z - 128*t^7 + 32*t^6*z^3 - 192*t^6*z^2 + 256*t^6*z + 448*t^6 + 32*t^5*z^5 - 224*t^5*z^4 + 64*t^5*z^3 + 1328*t^5*z^2 - 192*t^5*z - 896*t^5 + 16*t^4*z^6 - 208*t^4*z^5 + 784*t^4*z^4 + 96*t^4*z^3 - 3552*t^4*z^2 - 640*t^4*z + 1120*t^4 + 16*t^3*z^8 - 144*t^3*z^7 + 144*t^3*z^6 + 1600*t^3*z^5 - 3200*t^3*z^4 - 2688*t^3*z^3 + 4208*t^3*z^2 + 1600*t^3*z - 896*t^3 - 16*t^2*z^8 + 112*t^2*z^7 + 256*t^2*z^6 - 3040*t^2*z^5 + 3808*t^2*z^4 + 5344*t^2*z^3 - 2048*t^2*z^2 - 1536*t^2*z + 448*t^2 + 16*t*z^10 - 240*t*z^9 + 1264*t*z^8 - 2352*t*z^7 - 1008*t*z^6 + 6048*t*z^5 - 32*t*z^4 - 3520*t*z^3 + 80*t*z^2 + 704*t*z - 128*t + 16*z^8 - 176*z^7 + 592*z^6 - 336*z^5 - 1136*z^4 + 672*z^3 + 160*z^2 - 128*z + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 - 32*t^6*z + 160*t^6 - 32*t^5*z^3 + 192*t^5*z^2 + 32*t^5*z - 720*t^5 - 16*t^4*z^4 + 192*t^4*z^3 - 640*t^4*z^2 - 160*t^4*z + 1472*t^4 - 16*t^3*z^6 + 128*t^3*z^5 - 64*t^3*z^4 - 1280*t^3*z^3 + 1728*t^3*z^2 + 576*t^3*z + 1552*t^3 + 16*t^2*z^6 - 96*t^2*z^5 - 304*t^2*z^4 + 2448*t^2*z^3 - 2272*t^2*z^2 - 272*t^2*z - 5040*t^2 - 16*t*z^8 + 224*t*z^7 - 1088*t*z^6 + 1936*t*z^5 - 320*t*z^4 - 560*t*z^3 - 1488*t*z^2 + 352*t*z - 4192*t - 16*z^6 + 160*z^5 - 480*z^4 + 336*z^3 + 32*z^2 + 368*z + 304)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_24 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 24) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_24 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_25 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 25) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_25 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 6*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_26 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 26) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_26 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 6*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_27 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 27) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_27 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t*z + 2*z^3:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 2)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 384*t^7*z + 144*t^6*z^4 - 1424*t^6*z^3 + 3520*t^6*z^2 - 64*t^6*z + 112*t^5*z^6 - 1744*t^5*z^5 + 9040*t^5*z^4 - 15856*t^5*z^3 + 1280*t^5*z^2 + 32*t^4*z^8 - 752*t^4*z^7 + 6496*t^4*z^6 - 24896*t^4*z^5 + 37760*t^4*z^4 - 8416*t^4*z^3 - 32*t^4*z^2 - 48*t^3*z^9 + 992*t^3*z^8 - 7856*t^3*z^7 + 28976*t^3*z^6 - 46672*t^3*z^5 + 20912*t^3*z^4 + 128*t^3*z^3 + 16*t^2*z^10 - 352*t^2*z^9 + 2992*t^2*z^8 - 12112*t^2*z^7 + 22752*t^2*z^6 - 14928*t^2*z^5 - 128*t^2*z^4 + 192*t^2*z^3 + 16*t*z^10 - 256*t*z^9 + 1472*t*z^8 - 3424*t*z^7 + 1792*t*z^6 + 2928*t*z^5 - 1536*t*z^4 + 16*z^9 - 192*z^8 + 784*z^7 - 1168*z^6 + 288*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 + 1280*t^6*z - 2672*t^6 - 112*t^5*z^4 + 1632*t^5*z^3 - 7744*t^5*z^2 + 13008*t^5*z - 11504*t^5 - 32*t^4*z^6 + 720*t^4*z^5 - 5872*t^4*z^4 + 21184*t^4*z^3 - 34192*t^4*z^2 + 37776*t^4*z - 64768*t^4 + 48*t^3*z^7 - 944*t^3*z^6 + 7056*t^3*z^5 - 24752*t^3*z^4 + 43088*t^3*z^3 - 52080*t^3*z^2 + 77056*t^3*z - 79184*t^3 - 16*t^2*z^8 + 336*t^2*z^7 - 2704*t^2*z^6 + 10416*t^2*z^5 - 20448*t^2*z^4 + 25728*t^2*z^3 - 35488*t^2*z^2 + 41504*t^2*z - 64960*t^2 - 16*t*z^8 + 240*t*z^7 - 1280*t*z^6 + 2864*t*z^5 - 2768*t*z^4 + 2896*t*z^3 - 3872*t*z^2 + 4816*t*z - 6800*t - 16*z^7 + 176*z^6 - 656*z^5 + 1040*z^4 - 1216*z^3 + 1760*z^2 - 1888*z + 3392)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 128*t^7*z - 16*t^6*z^3 + 192*t^6*z^2 - 64*t^6*z + 32*t^5*z^5 - 272*t^5*z^4 + 336*t^5*z^3 + 512*t^5*z^2 - 48*t^4*z^6 + 448*t^4*z^5 - 832*t^4*z^4 - 480*t^4*z^3 - 32*t^4*z^2 + 16*t^3*z^8 - 144*t^3*z^7 + 176*t^3*z^6 + 1072*t^3*z^5 - 2064*t^3*z^4 - 128*t^3*z^3 - 16*t^2*z^9 + 176*t^2*z^8 - 496*t^2*z^7 - 240*t^2*z^6 + 1712*t^2*z^5 + 128*t^2*z^4 + 192*t^2*z^3 + 16*t*z^10 - 240*t*z^9 + 1280*t*z^8 - 2736*t*z^7 + 1248*t*z^6 + 2096*t*z^5 - 768*t*z^4 + 16*z^9 - 160*z^8 + 496*z^7 - 336*z^6 - 480*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 16*t^6*z - 176*t^6 - 32*t^5*z^3 + 240*t^5*z^2 - 192*t^5*z + 16*t^5 + 48*t^4*z^4 - 400*t^4*z^3 + 576*t^4*z^2 - 144*t^4*z + 1616*t^4 - 16*t^3*z^6 + 128*t^3*z^5 - 96*t^3*z^4 - 784*t^3*z^3 + 992*t^3*z^2 - 1232*t^3*z + 1744*t^3 + 16*t^2*z^7 - 160*t^2*z^6 + 384*t^2*z^5 + 144*t^2*z^4 - 416*t^2*z^3 - 112*t^2*z^2 - 1552*t^2*z - 1888*t^2 - 16*t*z^8 + 224*t*z^7 - 1104*t*z^6 + 2304*t*z^5 - 2256*t*z^4 + 2560*t*z^3 - 3440*t*z^2 + 4240*t*z - 6080*t - 16*z^7 + 144*z^6 - 400*z^5 + 368*z^4 - 352*z^3 + 608*z^2 - 448*z + 1376)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_28 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 28) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_28 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 - 2*t*z - 4*t + 4*z^3 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 4*z - 4)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 + 64*t^7*z - 128*t^7 + 48*t^6*z^4 - 64*t^6*z^3 + 320*t^6*z^2 - 640*t^6*z + 448*t^6 - 16*t^5*z^6 - 64*t^5*z^5 - 32*t^5*z^4 + 672*t^5*z^3 - 1552*t^5*z^2 + 2496*t^5*z - 896*t^5 + 64*t^4*z^7 - 48*t^4*z^6 - 80*t^4*z^5 + 48*t^4*z^4 - 2336*t^4*z^3 + 5408*t^4*z^2 - 5120*t^4*z + 1120*t^4 - 112*t^3*z^8 + 240*t^3*z^7 + 160*t^3*z^6 + 192*t^3*z^5 - 1856*t^3*z^4 + 5952*t^3*z^3 - 10832*t^3*z^2 + 6080*t^3*z - 896*t^3 + 96*t^2*z^9 - 176*t^2*z^8 - 784*t^2*z^7 + 1568*t^2*z^6 - 736*t^2*z^5 + 4112*t^2*z^4 - 10624*t^2*z^3 + 11776*t^2*z^2 - 4224*t^2*z + 448*t^2 - 32*t*z^10 - 96*t*z^9 + 1392*t*z^8 - 2864*t*z^7 + 752*t*z^6 + 2048*t*z^5 - 5024*t*z^4 + 9760*t*z^3 - 6512*t*z^2 + 1600*t*z - 128*t + 96*z^10 - 576*z^9 + 560*z^8 + 2320*z^7 - 4976*z^6 + 1712*z^5 + 2704*z^4 - 3360*z^3 + 1440*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 + 16*t^6*z - 448*t^6 + 16*t^5*z^4 + 80*t^5*z^3 + 160*t^5*z^2 - 272*t^5*z + 1760*t^5 - 64*t^4*z^5 - 16*t^4*z^4 - 128*t^4*z^3 - 224*t^4*z^2 + 1728*t^4*z - 4352*t^4 + 112*t^3*z^6 - 128*t^3*z^5 + 48*t^3*z^4 - 528*t^3*z^3 + 1472*t^3*z^2 - 6064*t^3*z + 9184*t^3 - 96*t^2*z^7 + 80*t^2*z^6 + 576*t^2*z^5 - 752*t^2*z^4 + 1712*t^2*z^3 - 4656*t^2*z^2 + 11104*t^2*z - 14640*t^2 + 32*t*z^8 + 128*t*z^7 - 1168*t*z^6 + 2080*t*z^5 - 2176*t*z^4 + 2016*t*z^3 + 512*t*z^2 - 3200*t*z + 4848*t - 96*z^8 + 480*z^7 - 368*z^6 - 1248*z^5 + 2624*z^4 - 2832*z^3 + 2336*z^2 - 2800*z + 2768)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 192*t^7*z - 128*t^7 - 64*t^6*z^3 + 640*t^6*z^2 + 1152*t^6*z + 448*t^6 + 32*t^5*z^5 - 176*t^5*z^4 - 736*t^5*z^3 - 2512*t^5*z^2 - 2880*t^5*z - 896*t^5 - 112*t^4*z^6 + 848*t^4*z^5 + 720*t^4*z^4 + 608*t^4*z^3 + 3168*t^4*z^2 + 3840*t^4*z + 1120*t^4 + 16*t^3*z^8 - 16*t^3*z^7 - 896*t^3*z^6 - 96*t^3*z^4 + 2112*t^3*z^3 - 912*t^3*z^2 - 2880*t^3*z - 896*t^3 - 32*t^2*z^9 + 240*t^2*z^8 + 304*t^2*z^7 - 1440*t^2*z^6 + 480*t^2*z^5 + 1056*t^2*z^4 - 2688*t^2*z^3 - 1088*t^2*z^2 + 1152*t^2*z + 448*t^2 + 32*t*z^10 - 416*t*z^9 + 1392*t*z^8 - 1712*t*z^7 + 128*t*z^6 + 2144*t*z^5 - 1776*t*z^4 + 672*t*z^3 + 848*t*z^2 - 192*t*z - 128*t + 32*z^10 - 128*z^9 + 16*z^8 + 400*z^7 - 240*z^6 - 432*z^5 + 272*z^4 + 96*z^3 - 160*z^2 + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 64*t^6*z - 576*t^6 - 32*t^5*z^3 + 144*t^5*z^2 + 784*t^5*z + 3728*t^5 + 112*t^4*z^4 - 736*t^4*z^3 - 1120*t^4*z^2 - 3936*t^4*z - 10464*t^4 - 16*t^3*z^6 + 848*t^3*z^4 + 848*t^3*z^3 + 3488*t^3*z^2 + 3920*t^3*z + 15296*t^3 + 32*t^2*z^7 - 208*t^2*z^6 - 416*t^2*z^5 + 400*t^2*z^4 - 1328*t^2*z^3 - 1184*t^2*z^2 - 2480*t^2*z - 4944*t^2 - 32*t*z^8 + 384*t*z^7 - 1104*t*z^6 + 1760*t*z^5 - 1680*t*z^4 + 1456*t*z^3 - 1808*t*z^2 + 1888*t*z - 4384*t - 32*z^8 + 96*z^7 - 16*z^6 - 128*z^5 + 64*z^4 + 112*z^3 + 32*z^2 + 272*z + 528)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_29 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 29) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_29 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t*z - 4*t + 2*z^3 - 2*z^2 + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 64*t^7*z - 128*t^7 + 32*t^6*z^3 - 192*t^6*z^2 + 256*t^6*z + 448*t^6 + 32*t^5*z^5 - 224*t^5*z^4 + 64*t^5*z^3 + 1328*t^5*z^2 - 192*t^5*z - 896*t^5 + 16*t^4*z^6 - 208*t^4*z^5 + 784*t^4*z^4 + 96*t^4*z^3 - 3552*t^4*z^2 - 640*t^4*z + 1120*t^4 + 16*t^3*z^8 - 144*t^3*z^7 + 144*t^3*z^6 + 1600*t^3*z^5 - 3200*t^3*z^4 - 2688*t^3*z^3 + 4208*t^3*z^2 + 1600*t^3*z - 896*t^3 - 16*t^2*z^8 + 112*t^2*z^7 + 256*t^2*z^6 - 3040*t^2*z^5 + 3808*t^2*z^4 + 5344*t^2*z^3 - 2048*t^2*z^2 - 1536*t^2*z + 448*t^2 + 16*t*z^10 - 240*t*z^9 + 1264*t*z^8 - 2352*t*z^7 - 1008*t*z^6 + 6048*t*z^5 - 32*t*z^4 - 3520*t*z^3 + 80*t*z^2 + 704*t*z - 128*t + 16*z^8 - 176*z^7 + 592*z^6 - 336*z^5 - 1136*z^4 + 672*z^3 + 160*z^2 - 128*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 - 32*t^6*z + 160*t^6 - 32*t^5*z^3 + 192*t^5*z^2 + 32*t^5*z - 720*t^5 - 16*t^4*z^4 + 192*t^4*z^3 - 640*t^4*z^2 - 160*t^4*z + 1472*t^4 - 16*t^3*z^6 + 128*t^3*z^5 - 64*t^3*z^4 - 1280*t^3*z^3 + 1728*t^3*z^2 + 576*t^3*z + 1552*t^3 + 16*t^2*z^6 - 96*t^2*z^5 - 304*t^2*z^4 + 2448*t^2*z^3 - 2272*t^2*z^2 - 272*t^2*z - 5040*t^2 - 16*t*z^8 + 224*t*z^7 - 1088*t*z^6 + 1936*t*z^5 - 320*t*z^4 - 560*t*z^3 - 1488*t*z^2 + 352*t*z - 4192*t - 16*z^6 + 160*z^5 - 480*z^4 + 336*z^3 + 32*z^2 + 368*z + 304)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_30 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 30) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_30 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t*z + 2*z^3:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 2)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 128*t^7*z - 16*t^6*z^3 + 192*t^6*z^2 - 64*t^6*z + 32*t^5*z^5 - 272*t^5*z^4 + 336*t^5*z^3 + 512*t^5*z^2 - 48*t^4*z^6 + 448*t^4*z^5 - 832*t^4*z^4 - 480*t^4*z^3 - 32*t^4*z^2 + 16*t^3*z^8 - 144*t^3*z^7 + 176*t^3*z^6 + 1072*t^3*z^5 - 2064*t^3*z^4 - 128*t^3*z^3 - 16*t^2*z^9 + 176*t^2*z^8 - 496*t^2*z^7 - 240*t^2*z^6 + 1712*t^2*z^5 + 128*t^2*z^4 + 192*t^2*z^3 + 16*t*z^10 - 240*t*z^9 + 1280*t*z^8 - 2736*t*z^7 + 1248*t*z^6 + 2096*t*z^5 - 768*t*z^4 + 16*z^9 - 160*z^8 + 496*z^7 - 336*z^6 - 480*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 16*t^6*z - 176*t^6 - 32*t^5*z^3 + 240*t^5*z^2 - 192*t^5*z + 16*t^5 + 48*t^4*z^4 - 400*t^4*z^3 + 576*t^4*z^2 - 144*t^4*z + 1616*t^4 - 16*t^3*z^6 + 128*t^3*z^5 - 96*t^3*z^4 - 784*t^3*z^3 + 992*t^3*z^2 - 1232*t^3*z + 1744*t^3 + 16*t^2*z^7 - 160*t^2*z^6 + 384*t^2*z^5 + 144*t^2*z^4 - 416*t^2*z^3 - 112*t^2*z^2 - 1552*t^2*z - 1888*t^2 - 16*t*z^8 + 224*t*z^7 - 1104*t*z^6 + 2304*t*z^5 - 2256*t*z^4 + 2560*t*z^3 - 3440*t*z^2 + 4240*t*z - 6080*t - 16*z^7 + 144*z^6 - 400*z^5 + 368*z^4 - 352*z^3 + 608*z^2 - 448*z + 1376)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_31 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 31) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_31 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 4*t*z^2 - 8*t*z + 4*z^3 + 2*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4*t - 4*z - 6)*hf
  · have hr : (16*t^8*z^4 - 48*t^7*z^5 - 192*t^7*z^4 + 80*t^6*z^6 + 512*t^6*z^5 + 704*t^6*z^4 - 80*t^5*z^7 - 800*t^5*z^6 - 1424*t^5*z^5 - 576*t^5*z^4 + 48*t^4*z^8 + 816*t^4*z^7 + 1616*t^4*z^6 + 416*t^4*z^5 - 1312*t^4*z^4 - 16*t^3*z^9 - 528*t^3*z^8 - 1440*t^3*z^7 + 1216*t^3*z^6 + 1200*t^3*z^5 + 1728*t^3*z^4 + 240*t^2*z^9 + 688*t^2*z^8 - 928*t^2*z^7 - 2448*t^2*z^6 + 704*t^2*z^5 + 448*t^2*z^4 - 32*t*z^10 - 464*t*z^9 + 1360*t*z^8 - 16*t*z^7 - 1696*t*z^6 + 1808*t*z^5 - 960*t*z^4 + 96*z^10 - 336*z^9 + 96*z^8 + 624*z^7 - 528*z^6 - 96*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 16*t^8*z - 64*t^8 + 48*t^7*z^3 + 240*t^7*z^2 + 384*t^7*z + 1104*t^7 - 80*t^6*z^4 - 592*t^6*z^3 - 1536*t^6*z^2 - 3312*t^6*z - 7920*t^6 + 80*t^5*z^5 + 880*t^5*z^4 + 2544*t^5*z^3 + 5760*t^5*z^2 + 13392*t^5*z + 30672*t^5 - 48*t^4*z^6 - 864*t^4*z^5 - 2624*t^4*z^4 - 5632*t^4*z^3 - 12192*t^4*z^2 - 29088*t^4*z - 65664*t^4 + 16*t^3*z^7 + 544*t^3*z^6 + 2032*t^3*z^5 + 2448*t^3*z^4 + 7344*t^3*z^3 + 12960*t^3*z^2 + 34992*t^3*z + 73872*t^3 - 240*t^2*z^7 - 928*t^2*z^6 - 720*t^2*z^5 - 1056*t^2*z^4 - 3920*t^2*z^3 - 7536*t^2*z^2 - 19296*t^2*z - 41904*t^2 + 32*t*z^8 + 496*t*z^7 - 768*t*z^6 + 736*t*z^5 + 128*t*z^4 + 528*t*z^3 + 1872*t*z^2 + 3456*t*z + 9072*t - 96*z^8 + 240*z^7 - 144*z^6 - 48*z^5 + 48*z^4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_32 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 32) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_32 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*z^3 - 8*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 4*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_33 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 33) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_33 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 6*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_34 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 34) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_34 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 4*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_35 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 35) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_35 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 - 4*t + 4*z^3 - 6*z^2 + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 4*z + 2)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 128*t^7*z - 128*t^7 - 16*t^6*z^3 + 96*t^6*z^2 + 768*t^6*z + 448*t^6 + 32*t^5*z^5 - 272*t^5*z^4 + 384*t^5*z^3 - 208*t^5*z^2 - 1920*t^5*z - 896*t^5 - 48*t^4*z^6 + 320*t^4*z^5 + 352*t^4*z^4 - 2048*t^4*z^3 - 672*t^4*z^2 + 2560*t^4*z + 1120*t^4 + 16*t^3*z^8 - 144*t^3*z^7 + 304*t^3*z^6 - 96*t^3*z^5 - 1296*t^3*z^4 + 3904*t^3*z^3 + 2288*t^3*z^2 - 1920*t^3*z - 896*t^3 - 16*t^2*z^9 + 144*t^2*z^8 - 176*t^2*z^7 - 816*t^2*z^6 + 704*t^2*z^5 + 3200*t^2*z^4 - 3024*t^2*z^3 - 2528*t^2*z^2 + 768*t^2*z + 448*t^2 + 16*t*z^10 - 224*t*z^9 + 1088*t*z^8 - 2224*t*z^7 + 1520*t*z^6 + 1280*t*z^5 - 3136*t*z^4 + 704*t*z^3 + 1232*t*z^2 - 128*t*z - 128*t + 32*z^9 - 272*z^8 + 720*z^7 - 432*z^6 - 656*z^5 + 720*z^4 + 96*z^3 - 224*z^2 + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 16*t^6*z - 80*t^6 - 32*t^5*z^3 + 240*t^5*z^2 - 240*t^5*z + 688*t^5 + 48*t^4*z^4 - 272*t^4*z^3 - 480*t^4*z^2 + 752*t^4*z - 16*t^4 - 16*t^3*z^6 + 128*t^3*z^5 - 224*t^3*z^4 + 256*t^3*z^3 + 880*t^3*z^2 - 2256*t^3*z - 1904*t^3 + 16*t^2*z^7 - 128*t^2*z^6 + 96*t^2*z^5 + 528*t^2*z^4 + 112*t^2*z^3 - 1504*t^2*z^2 + 1856*t^2*z - 128*t^2 - 16*t*z^8 + 208*t*z^7 - 928*t*z^6 + 1920*t*z^5 - 2384*t*z^4 + 2096*t*z^3 - 1920*t*z^2 + 3664*t*z - 3328*t - 32*z^7 + 240*z^6 - 576*z^5 + 576*z^4 - 496*z^3 + 512*z^2 - 1072*z + 688)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 + 128*t^7*z - 128*t^7 + 48*t^6*z^4 - 208*t^6*z^3 + 544*t^6*z^2 - 1024*t^6*z + 448*t^6 - 16*t^5*z^6 + 32*t^5*z^5 - 128*t^5*z^4 + 1216*t^5*z^3 - 3088*t^5*z^2 + 3456*t^5*z - 896*t^5 + 48*t^4*z^7 - 224*t^4*z^6 + 192*t^4*z^5 + 576*t^4*z^4 - 3840*t^4*z^3 + 9248*t^4*z^2 - 6400*t^4*z + 1120*t^4 - 64*t^3*z^8 + 336*t^3*z^7 - 128*t^3*z^6 - 1088*t^3*z^5 - 944*t^3*z^4 + 8896*t^3*z^3 - 15312*t^3*z^2 + 7040*t^3*z - 896*t^3 + 48*t^2*z^9 - 288*t^2*z^8 + 256*t^2*z^7 + 432*t^2*z^6 + 1184*t^2*z^5 + 176*t^2*z^4 - 12688*t^2*z^3 + 14176*t^2*z^2 - 4608*t^2*z + 448*t^2 - 16*t*z^10 + 64*t*z^9 + 352*t*z^8 - 2224*t*z^7 + 3904*t*z^6 - 3296*t*z^5 - 48*t*z^4 + 9216*t*z^3 - 6896*t*z^2 + 1664*t*z - 128*t + 32*z^10 - 320*z^9 + 976*z^8 - 240*z^7 - 3440*z^6 + 4560*z^5 - 112*z^4 - 2592*z^3 + 1376*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 + 160*t^6*z - 528*t^6 + 16*t^5*z^4 - 16*t^5*z^3 + 160*t^5*z^2 - 1104*t^5*z + 2464*t^5 - 48*t^4*z^5 + 176*t^4*z^4 - 160*t^4*z^3 - 208*t^4*z^2 + 3152*t^4*z - 6720*t^4 + 64*t^3*z^6 - 272*t^3*z^5 + 48*t^3*z^4 + 320*t^3*z^3 + 1408*t^3*z^2 - 6528*t^3*z + 13008*t^3 - 48*t^2*z^7 + 240*t^2*z^6 - 160*t^2*z^5 + 128*t^2*z^4 - 1536*t^2*z^3 - 1328*t^2*z^2 + 6752*t^2*z - 11408*t^2 + 16*t*z^8 - 48*t*z^7 - 352*t*z^6 + 1728*t*z^5 - 3232*t*z^4 + 5248*t*z^3 - 4400*t*z^2 + 2128*t*z - 4176*t - 32*z^8 + 288*z^7 - 784*z^6 + 320*z^5 + 1408*z^4 - 2192*z^3 + 2144*z^2 - 1840*z + 3216)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_36 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 36) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_36 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 6*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_37 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 37) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_37 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 8*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(6 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_38 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 38) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_38 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 8*z^2 + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(6 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_39 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 39) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : (t - z + 2:ℝ)=0 := by
  apply cell_12_39 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^3 - 6*z^2 + 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*z)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 256*t^7*z - 128*t^7 + 144*t^6*z^4 - 944*t^6*z^3 + 1056*t^6*z^2 + 1664*t^6*z + 448*t^6 + 112*t^5*z^6 - 1168*t^5*z^5 + 3424*t^5*z^4 - 224*t^5*z^3 - 6544*t^5*z^2 - 4608*t^5*z - 896*t^5 + 32*t^4*z^8 - 528*t^4*z^7 + 2848*t^4*z^6 - 4544*t^4*z^5 - 5056*t^4*z^4 + 9024*t^4*z^3 + 14368*t^4*z^2 + 7040*t^4*z + 1120*t^4 - 48*t^3*z^9 + 624*t^3*z^8 - 2528*t^3*z^7 + 1568*t^3*z^6 + 8832*t^3*z^5 - 3888*t^3*z^4 - 16896*t^3*z^3 - 15952*t^3*z^2 - 6400*t^3*z - 896*t^3 + 16*t^2*z^10 - 160*t^2*z^9 + 192*t^2*z^8 + 2464*t^2*z^7 - 7344*t^2*z^6 - 1056*t^2*z^5 + 9296*t^2*z^4 + 12944*t^2*z^3 + 9568*t^2*z^2 + 3456*t^2*z + 448*t^2 - 16*t*z^10 + 224*t*z^9 - 1040*t*z^8 + 1392*t*z^7 + 1408*t*z^6 - 656*t*z^5 - 5264*t*z^4 - 4512*t*z^3 - 2928*t*z^2 - 1024*t*z - 128*t - 16*z^8 + 176*z^7 - 560*z^6 + 176*z^5 + 912*z^4 + 608*z^3 + 352*z^2 + 128*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 + 800*t^6*z - 688*t^6 - 112*t^5*z^4 + 1056*t^5*z^3 - 2704*t^5*z^2 + 688*t^5*z - 880*t^5 - 32*t^4*z^6 + 496*t^4*z^5 - 2448*t^4*z^4 + 3584*t^4*z^3 + 1296*t^4*z^2 + 3024*t^4*z - 7456*t^4 + 48*t^3*z^7 - 576*t^3*z^6 + 2096*t^3*z^5 - 1200*t^3*z^4 - 3744*t^3*z^3 - 3456*t^3*z^2 + 2208*t^3*z + 7792*t^3 - 16*t^2*z^8 + 144*t^2*z^7 - 96*t^2*z^6 - 2128*t^2*z^5 + 4928*t^2*z^4 - 400*t^2*z^3 + 5088*t^2*z^2 - 9056*t^2*z - 3360*t^2 + 16*t*z^8 - 208*t*z^7 + 880*t*z^6 - 1136*t*z^5 + 96*t*z^4 - 2656*t*z^3 + 2896*t*z^2 - 560*t*z + 11056*t + 16*z^6 - 160*z^5 + 448*z^4 - 208*z^3 + 224*z^2 - 1008*z - 688)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_40 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 40) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_40 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 4*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_41 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 41) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_41 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 8*z^2 + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(6 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_42 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 42) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_42 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 8*z^2 + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(6 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_43 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 43) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_43 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t*z + 2*z^3 - 4*z^2 + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2 - 2*z)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 320*t^7*z + 144*t^6*z^4 - 1184*t^6*z^3 + 2464*t^6*z^2 - 128*t^6*z + 112*t^5*z^6 - 1456*t^5*z^5 + 6400*t^5*z^4 - 9984*t^5*z^3 + 2048*t^5*z^2 + 32*t^4*z^8 - 640*t^4*z^7 + 4784*t^4*z^6 - 16432*t^4*z^5 + 24720*t^4*z^4 - 11136*t^4*z^3 + 256*t^4*z^2 - 48*t^3*z^9 + 864*t^3*z^8 - 6128*t^3*z^7 + 21360*t^3*z^6 - 36672*t^3*z^5 + 25856*t^3*z^4 - 3072*t^3*z^3 + 16*t^2*z^10 - 320*t^2*z^9 + 2608*t^2*z^8 - 10960*t^2*z^7 + 24512*t^2*z^6 - 26368*t^2*z^5 + 9216*t^2*z^4 + 16*t*z^10 - 272*t*z^9 + 1792*t*z^8 - 5632*t*z^7 + 8192*t*z^6 - 4096*t*z^5:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 + 1040*t^6*z - 1856*t^6 - 112*t^5*z^4 + 1344*t^5*z^3 - 5392*t^5*z^2 + 8624*t^5*z - 9600*t^5 - 32*t^4*z^6 + 608*t^4*z^5 - 4272*t^4*z^4 + 13984*t^4*z^3 - 23552*t^4*z^2 + 29536*t^4*z - 41376*t^4 + 48*t^3*z^7 - 816*t^3*z^6 + 5456*t^3*z^5 - 18352*t^3*z^4 + 34688*t^3*z^3 - 46224*t^3*z^2 + 60912*t^3*z - 77760*t^3 - 16*t^2*z^8 + 304*t^2*z^7 - 2352*t^2*z^6 + 9520*t^2*z^5 - 22048*t^2*z^4 + 32880*t^2*z^3 - 42480*t^2*z^2 + 56160*t^2*z - 71280*t^2 - 16*t*z^8 + 256*t*z^7 - 1584*t*z^6 + 4816*t*z^5 - 8128*t*z^4 + 10416*t*z^3 - 13968*t*z^2 + 17280*t*z - 24624*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_44 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 44) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_44 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 - 4*t + 4*z^3 - 6*z^2 + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 4*z + 2)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 + 128*t^7*z - 128*t^7 + 48*t^6*z^4 - 208*t^6*z^3 + 544*t^6*z^2 - 1024*t^6*z + 448*t^6 - 16*t^5*z^6 + 32*t^5*z^5 - 128*t^5*z^4 + 1216*t^5*z^3 - 3088*t^5*z^2 + 3456*t^5*z - 896*t^5 + 48*t^4*z^7 - 224*t^4*z^6 + 192*t^4*z^5 + 576*t^4*z^4 - 3840*t^4*z^3 + 9248*t^4*z^2 - 6400*t^4*z + 1120*t^4 - 64*t^3*z^8 + 336*t^3*z^7 - 128*t^3*z^6 - 1088*t^3*z^5 - 944*t^3*z^4 + 8896*t^3*z^3 - 15312*t^3*z^2 + 7040*t^3*z - 896*t^3 + 48*t^2*z^9 - 288*t^2*z^8 + 256*t^2*z^7 + 432*t^2*z^6 + 1184*t^2*z^5 + 176*t^2*z^4 - 12688*t^2*z^3 + 14176*t^2*z^2 - 4608*t^2*z + 448*t^2 - 16*t*z^10 + 64*t*z^9 + 352*t*z^8 - 2224*t*z^7 + 3904*t*z^6 - 3296*t*z^5 - 48*t*z^4 + 9216*t*z^3 - 6896*t*z^2 + 1664*t*z - 128*t + 32*z^10 - 320*z^9 + 976*z^8 - 240*z^7 - 3440*z^6 + 4560*z^5 - 112*z^4 - 2592*z^3 + 1376*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 + 160*t^6*z - 528*t^6 + 16*t^5*z^4 - 16*t^5*z^3 + 160*t^5*z^2 - 1104*t^5*z + 2464*t^5 - 48*t^4*z^5 + 176*t^4*z^4 - 160*t^4*z^3 - 208*t^4*z^2 + 3152*t^4*z - 6720*t^4 + 64*t^3*z^6 - 272*t^3*z^5 + 48*t^3*z^4 + 320*t^3*z^3 + 1408*t^3*z^2 - 6528*t^3*z + 13008*t^3 - 48*t^2*z^7 + 240*t^2*z^6 - 160*t^2*z^5 + 128*t^2*z^4 - 1536*t^2*z^3 - 1328*t^2*z^2 + 6752*t^2*z - 11408*t^2 + 16*t*z^8 - 48*t*z^7 - 352*t*z^6 + 1728*t*z^5 - 3232*t*z^4 + 5248*t*z^3 - 4400*t*z^2 + 2128*t*z - 4176*t - 32*z^8 + 288*z^7 - 784*z^6 + 320*z^5 + 1408*z^4 - 2192*z^3 + 2144*z^2 - 1840*z + 3216)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 128*t^7*z - 128*t^7 - 16*t^6*z^3 + 96*t^6*z^2 + 768*t^6*z + 448*t^6 + 32*t^5*z^5 - 272*t^5*z^4 + 384*t^5*z^3 - 208*t^5*z^2 - 1920*t^5*z - 896*t^5 - 48*t^4*z^6 + 320*t^4*z^5 + 352*t^4*z^4 - 2048*t^4*z^3 - 672*t^4*z^2 + 2560*t^4*z + 1120*t^4 + 16*t^3*z^8 - 144*t^3*z^7 + 304*t^3*z^6 - 96*t^3*z^5 - 1296*t^3*z^4 + 3904*t^3*z^3 + 2288*t^3*z^2 - 1920*t^3*z - 896*t^3 - 16*t^2*z^9 + 144*t^2*z^8 - 176*t^2*z^7 - 816*t^2*z^6 + 704*t^2*z^5 + 3200*t^2*z^4 - 3024*t^2*z^3 - 2528*t^2*z^2 + 768*t^2*z + 448*t^2 + 16*t*z^10 - 224*t*z^9 + 1088*t*z^8 - 2224*t*z^7 + 1520*t*z^6 + 1280*t*z^5 - 3136*t*z^4 + 704*t*z^3 + 1232*t*z^2 - 128*t*z - 128*t + 32*z^9 - 272*z^8 + 720*z^7 - 432*z^6 - 656*z^5 + 720*z^4 + 96*z^3 - 224*z^2 + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 16*t^6*z - 80*t^6 - 32*t^5*z^3 + 240*t^5*z^2 - 240*t^5*z + 688*t^5 + 48*t^4*z^4 - 272*t^4*z^3 - 480*t^4*z^2 + 752*t^4*z - 16*t^4 - 16*t^3*z^6 + 128*t^3*z^5 - 224*t^3*z^4 + 256*t^3*z^3 + 880*t^3*z^2 - 2256*t^3*z - 1904*t^3 + 16*t^2*z^7 - 128*t^2*z^6 + 96*t^2*z^5 + 528*t^2*z^4 + 112*t^2*z^3 - 1504*t^2*z^2 + 1856*t^2*z - 128*t^2 - 16*t*z^8 + 208*t*z^7 - 928*t*z^6 + 1920*t*z^5 - 2384*t*z^4 + 2096*t*z^3 - 1920*t*z^2 + 3664*t*z - 3328*t - 32*z^7 + 240*z^6 - 576*z^5 + 576*z^4 - 496*z^3 + 512*z^2 - 1072*z + 688)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_45 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 45) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : (t - z + 2:ℝ)=0 := by
  apply cell_12_45 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^3 - 6*z^2 + 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*z)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 128*t^7 + 80*t^6*z^3 - 288*t^6*z^2 - 128*t^6*z + 448*t^6 + 32*t^5*z^5 - 80*t^5*z^4 - 544*t^5*z^3 + 1328*t^5*z^2 + 768*t^5*z - 896*t^5 + 80*t^4*z^6 - 544*t^4*z^5 + 480*t^4*z^4 + 2432*t^4*z^3 - 2592*t^4*z^2 - 1920*t^4*z + 1120*t^4 + 16*t^3*z^8 - 80*t^3*z^7 - 336*t^3*z^6 + 2240*t^3*z^5 - 1360*t^3*z^4 - 5504*t^3*z^3 + 2288*t^3*z^2 + 2560*t^3*z - 896*t^3 + 16*t^2*z^9 - 144*t^2*z^8 + 176*t^2*z^7 + 1616*t^2*z^6 - 4608*t^2*z^5 + 320*t^2*z^4 + 6160*t^2*z^3 - 608*t^2*z^2 - 1920*t^2*z + 448*t^2 + 16*t*z^10 - 224*t*z^9 + 1088*t*z^8 - 1744*t*z^7 - 1424*t*z^6 + 4800*t*z^5 + 1344*t*z^4 - 3296*t*z^3 - 304*t*z^2 + 768*t*z - 128*t + 16*z^8 - 176*z^7 + 592*z^6 - 336*z^5 - 1136*z^4 + 672*z^3 + 160*z^2 - 128*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 - 80*t^6*z + 208*t^6 - 32*t^5*z^3 + 48*t^5*z^2 + 496*t^5*z - 688*t^5 - 80*t^4*z^4 + 464*t^4*z^3 - 256*t^4*z^2 - 1296*t^4*z + 528*t^4 - 16*t^3*z^6 + 64*t^3*z^5 + 352*t^3*z^4 - 1696*t^3*z^3 + 720*t^3*z^2 + 1136*t^3*z + 1008*t^3 - 16*t^2*z^7 + 128*t^2*z^6 - 96*t^2*z^5 - 1328*t^2*z^4 + 2992*t^2*z^3 - 1312*t^2*z^2 + 1504*t^2*z - 1824*t^2 - 16*t*z^8 + 208*t*z^7 - 928*t*z^6 + 1440*t*z^5 + 80*t*z^4 - 400*t*z^3 - 1504*t*z^2 + 592*t*z - 3616*t - 16*z^6 + 160*z^5 - 480*z^4 + 336*z^3 + 32*z^2 + 368*z + 304)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_46 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 46) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_46 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t*z + 2*z^3 - 4*z^2 + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2 - 2*z)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 64*t^7*z + 32*t^6*z^3 - 96*t^6*z^2 - 128*t^6*z + 32*t^5*z^5 - 224*t^5*z^4 + 256*t^5*z^3 + 512*t^5*z^2 + 16*t^4*z^6 - 80*t^4*z^5 - 112*t^4*z^4 + 640*t^4*z^3 + 256*t^4*z^2 + 16*t^3*z^8 - 144*t^3*z^7 + 208*t^3*z^6 + 1088*t^3*z^5 - 2304*t^3*z^4 - 1024*t^3*z^3 + 16*t^2*z^8 - 176*t^2*z^7 + 576*t^2*z^6 - 256*t^2*z^5 - 1024*t^2*z^4 + 16*t*z^10 - 240*t*z^9 + 1280*t*z^8 - 2560*t*z^7 + 4096*t*z^5:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 - 32*t^6*z + 64*t^6 - 32*t^5*z^3 + 192*t^5*z^2 - 160*t^5*z - 96*t^5 - 16*t^4*z^4 + 64*t^4*z^3 + 128*t^4*z^2 - 320*t^4*z - 192*t^4 - 16*t^3*z^6 + 128*t^3*z^5 - 128*t^3*z^4 - 832*t^3*z^3 + 1088*t^3*z^2 - 384*t^3*z + 2880*t^3 - 16*t^2*z^6 + 160*t^2*z^5 - 464*t^2*z^4 + 272*t^2*z^3 - 96*t^2*z^2 + 720*t^2*z + 432*t^2 - 16*t*z^8 + 224*t*z^7 - 1104*t*z^6 + 2128*t*z^5 - 1184*t*z^4 + 1104*t*z^3 - 2448*t*z^2 + 864*t*z - 6480*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_47 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 47) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_47 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 4*t*z^2 - 4*t*z + 4*z^3 - 4*z^2 + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4*t - 4*z)*hf
  · have hr : (16*t^8*z^4 - 48*t^7*z^5 - 64*t^7*z^4 + 80*t^6*z^6 + 160*t^6*z^5 - 128*t^6*z^4 - 80*t^5*z^7 - 272*t^5*z^6 + 448*t^5*z^5 + 512*t^5*z^4 + 48*t^4*z^8 + 336*t^4*z^7 - 816*t^4*z^6 - 768*t^4*z^5 + 256*t^4*z^4 - 16*t^3*z^9 - 256*t^3*z^8 + 608*t^3*z^7 + 1408*t^3*z^6 - 1792*t^3*z^5 - 1024*t^3*z^4 + 144*t^2*z^9 - 352*t^2*z^8 - 1024*t^2*z^7 + 2176*t^2*z^6 + 512*t^2*z^5 - 16*t*z^10 - 112*t*z^9 + 1152*t*z^8 - 1920*t*z^7 - 1280*t*z^6 + 3072*t*z^5 + 32*z^10 - 224*z^9 + 384*z^8 + 256*z^7 - 768*z^6:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 16*t^8*z - 64*t^8 + 48*t^7*z^3 + 112*t^7*z^2 + 256*t^7*z + 592*t^7 - 80*t^6*z^4 - 240*t^6*z^3 - 352*t^6*z^2 - 1072*t^6*z - 2128*t^6 + 80*t^5*z^5 + 352*t^5*z^4 + 144*t^5*z^3 + 688*t^5*z^2 + 1120*t^5*z + 3184*t^5 - 48*t^4*z^6 - 384*t^4*z^5 + 288*t^4*z^4 - 96*t^4*z^3 + 512*t^4*z^2 + 224*t^4*z + 1760*t^4 + 16*t^3*z^7 + 272*t^3*z^6 - 288*t^3*z^5 - 880*t^3*z^4 + 48*t^3*z^3 - 1568*t^3*z^2 - 1424*t^3*z - 6128*t^3 - 144*t^2*z^7 + 208*t^2*z^6 + 800*t^2*z^5 - 752*t^2*z^4 + 1136*t^2*z^3 - 1120*t^2*z^2 + 2288*t^2*z - 1072*t^2 + 16*t*z^8 + 128*t*z^7 - 976*t*z^6 + 1328*t*z^5 - 320*t*z^4 + 592*t*z^3 - 368*t*z^2 + 1408*t*z + 304*t - 32*z^8 + 192*z^7 - 288*z^6 + 32*z^5 - 64*z^4 + 32*z^3 - 160*z^2 - 64*z - 544)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_48 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 48) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_48 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z + 2*t*z^2 - 8*t*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8*z^4 - 48*t^7*z^5 - 192*t^7*z^4 + 80*t^6*z^6 + 512*t^6*z^5 + 704*t^6*z^4 - 80*t^5*z^7 - 800*t^5*z^6 - 1424*t^5*z^5 - 576*t^5*z^4 + 48*t^4*z^8 + 816*t^4*z^7 + 1616*t^4*z^6 + 416*t^4*z^5 - 1312*t^4*z^4 - 16*t^3*z^9 - 528*t^3*z^8 - 1440*t^3*z^7 + 1216*t^3*z^6 + 1200*t^3*z^5 + 1728*t^3*z^4 + 240*t^2*z^9 + 688*t^2*z^8 - 928*t^2*z^7 - 2448*t^2*z^6 + 704*t^2*z^5 + 448*t^2*z^4 - 32*t*z^10 - 464*t*z^9 + 1360*t*z^8 - 16*t*z^7 - 1696*t*z^6 + 1808*t*z^5 - 960*t*z^4 + 96*z^10 - 336*z^9 + 96*z^8 + 624*z^7 - 528*z^6 - 96*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 16*t^8*z - 64*t^8 + 48*t^7*z^3 + 240*t^7*z^2 + 384*t^7*z + 1104*t^7 - 80*t^6*z^4 - 592*t^6*z^3 - 1536*t^6*z^2 - 3312*t^6*z - 7920*t^6 + 80*t^5*z^5 + 880*t^5*z^4 + 2544*t^5*z^3 + 5760*t^5*z^2 + 13392*t^5*z + 30672*t^5 - 48*t^4*z^6 - 864*t^4*z^5 - 2624*t^4*z^4 - 5632*t^4*z^3 - 12192*t^4*z^2 - 29088*t^4*z - 65664*t^4 + 16*t^3*z^7 + 544*t^3*z^6 + 2032*t^3*z^5 + 2448*t^3*z^4 + 7344*t^3*z^3 + 12960*t^3*z^2 + 34992*t^3*z + 73872*t^3 - 240*t^2*z^7 - 928*t^2*z^6 - 720*t^2*z^5 - 1056*t^2*z^4 - 3920*t^2*z^3 - 7536*t^2*z^2 - 19296*t^2*z - 41904*t^2 + 32*t*z^8 + 496*t*z^7 - 768*t*z^6 + 736*t*z^5 + 128*t*z^4 + 528*t*z^3 + 1872*t*z^2 + 3456*t*z + 9072*t - 96*z^8 + 240*z^7 - 144*z^6 - 48*z^5 + 48*z^4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_49 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 49) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_49 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 8*t*z + 2*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8*z^4 - 112*t^7*z^5 - 192*t^7*z^4 + 384*t^6*z^6 + 1088*t^6*z^5 + 704*t^6*z^4 - 816*t^5*z^7 - 3008*t^5*z^6 - 2768*t^5*z^5 - 576*t^5*z^4 + 1168*t^4*z^8 + 5008*t^4*z^7 + 5040*t^4*z^6 + 288*t^4*z^5 - 1312*t^4*z^4 - 1152*t^3*z^9 - 5328*t^3*z^8 - 4944*t^3*z^7 + 2816*t^3*z^6 + 3312*t^3*z^5 + 1728*t^3*z^4 + 768*t^2*z^10 + 3568*t^2*z^9 + 2320*t^2*z^8 - 5120*t^2*z^7 - 4320*t^2*z^6 + 768*t^2*z^5 + 448*t^2*z^4 - 320*t*z^11 - 1344*t*z^10 - 320*t*z^9 + 4400*t*z^8 - 480*t*z^7 - 1600*t*z^6 + 1616*t*z^5 - 960*t*z^4 + 64*z^12 + 224*z^11 - 256*z^10 - 656*z^9 + 320*z^8 + 464*z^7 - 336*z^6 - 96*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 16*t^8*z - 64*t^8 + 112*t^7*z^3 + 304*t^7*z^2 + 640*t^7*z + 1552*t^7 - 384*t^6*z^4 - 1472*t^6*z^3 - 3328*t^6*z^2 - 7744*t^6*z - 17728*t^6 + 816*t^5*z^5 + 3824*t^5*z^4 + 9040*t^5*z^3 + 21088*t^5*z^2 + 48208*t^5*z + 111472*t^5 - 1168*t^4*z^6 - 6176*t^4*z^5 - 14720*t^4*z^4 - 33536*t^4*z^3 - 76384*t^4*z^2 - 176992*t^4*z - 406144*t^4 + 1152*t^3*z^7 + 6480*t^3*z^6 + 14880*t^3*z^5 + 31504*t^3*z^4 + 72832*t^3*z^3 + 165616*t^3*z^2 + 384112*t^3*z + 880960*t^3 - 768*t^2*z^8 - 4336*t^2*z^7 - 8960*t^2*z^6 - 16848*t^2*z^5 - 39408*t^2*z^4 - 90720*t^2*z^3 - 209392*t^2*z^2 - 481552*t^2*z - 1109728*t^2 + 320*t*z^9 + 1664*t*z^8 + 2944*t*z^7 + 3536*t*z^6 + 12848*t*z^5 + 25056*t*z^4 + 61984*t*z^3 + 138112*t*z^2 + 324064*t*z + 738400*t - 64*z^10 - 288*z^9 - 224*z^8 - 432*z^7 - 1424*z^6 - 3184*z^5 - 7120*z^4 - 16576*z^3 - 38080*z^2 - 87808*z - 202048)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_50 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 50) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_50 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 6*t*z + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8*z^4 - 112*t^7*z^5 - 128*t^7*z^4 + 384*t^6*z^6 + 688*t^6*z^5 + 160*t^6*z^4 + 64*t^6*z^3 - 816*t^5*z^7 - 1808*t^5*z^6 - 176*t^5*z^5 + 304*t^5*z^4 - 384*t^5*z^3 + 1168*t^4*z^8 + 2832*t^4*z^7 - 784*t^4*z^6 - 2192*t^4*z^5 + 272*t^4*z^4 + 192*t^4*z^3 + 96*t^4*z^2 - 1152*t^3*z^9 - 2768*t^3*z^8 + 2544*t^3*z^7 + 5040*t^3*z^6 - 2176*t^3*z^5 - 144*t^3*z^4 + 1200*t^3*z^3 - 384*t^3*z^2 + 768*t^2*z^10 + 1616*t^2*z^9 - 3344*t^2*z^8 - 4720*t^2*z^7 + 4560*t^2*z^6 + 1568*t^2*z^5 - 1440*t^2*z^4 - 272*t^2*z^3 - 96*t^2*z^2 + 64*t^2*z - 320*t*z^11 - 448*t*z^10 + 2000*t*z^9 + 2448*t*z^8 - 6224*t*z^7 - 96*t*z^6 + 5872*t*z^5 - 3280*t*z^4 - 608*t*z^3 + 784*t*z^2 - 128*t*z + 64*z^12 + 32*z^11 - 640*z^10 + 352*z^9 + 1264*z^8 - 1488*z^7 + 80*z^6 + 1072*z^5 - 1200*z^4 + 352*z^3 + 224*z^2 - 128*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 16*t^8*z - 64*t^8 + 112*t^7*z^3 + 240*t^7*z^2 + 576*t^7*z + 1296*t^7 - 384*t^6*z^4 - 1072*t^6*z^3 - 2384*t^6*z^2 - 5664*t^6*z - 12816*t^6 + 816*t^5*z^5 + 2624*t^5*z^4 + 5248*t^5*z^3 + 12816*t^5*z^2 + 28944*t^5*z + 67392*t^5 - 1168*t^4*z^6 - 4000*t^4*z^5 - 6720*t^4*z^4 - 16528*t^4*z^3 - 36960*t^4*z^2 - 86736*t^4*z - 197712*t^4 + 1152*t^3*z^7 + 3920*t^3*z^6 + 4832*t^3*z^5 + 11552*t^3*z^4 + 28224*t^3*z^3 + 63024*t^3*z^2 + 146496*t^3*z + 335952*t^3 - 768*t^2*z^8 - 2384*t^2*z^7 - 1344*t^2*z^6 - 3776*t^2*z^5 - 12368*t^2*z^4 - 25264*t^2*z^3 - 60928*t^2*z^2 - 136448*t^2*z - 319136*t^2 + 320*t*z^9 + 768*t*z^8 - 272*t*z^7 - 416*t*z^6 + 4992*t*z^5 + 3840*t*z^4 + 12944*t*z^3 + 27744*t*z^2 + 67184*t*z + 149632*t - 64*z^10 - 96*z^9 + 352*z^8 - 288*z^7 - 496*z^6 + 128*z^5 - 1440*z^4 - 2128*z^3 - 5248*z^2 - 11984*z - 27952)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_51 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 51) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_51 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 6*t*z - 4*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 192*t^7*z - 128*t^7 - 64*t^6*z^3 + 640*t^6*z^2 + 1152*t^6*z + 448*t^6 + 32*t^5*z^5 - 176*t^5*z^4 - 736*t^5*z^3 - 2512*t^5*z^2 - 2880*t^5*z - 896*t^5 - 112*t^4*z^6 + 848*t^4*z^5 + 720*t^4*z^4 + 608*t^4*z^3 + 3168*t^4*z^2 + 3840*t^4*z + 1120*t^4 + 16*t^3*z^8 - 16*t^3*z^7 - 896*t^3*z^6 - 96*t^3*z^4 + 2112*t^3*z^3 - 912*t^3*z^2 - 2880*t^3*z - 896*t^3 - 32*t^2*z^9 + 240*t^2*z^8 + 304*t^2*z^7 - 1440*t^2*z^6 + 480*t^2*z^5 + 1056*t^2*z^4 - 2688*t^2*z^3 - 1088*t^2*z^2 + 1152*t^2*z + 448*t^2 + 32*t*z^10 - 416*t*z^9 + 1392*t*z^8 - 1712*t*z^7 + 128*t*z^6 + 2144*t*z^5 - 1776*t*z^4 + 672*t*z^3 + 848*t*z^2 - 192*t*z - 128*t + 32*z^10 - 128*z^9 + 16*z^8 + 400*z^7 - 240*z^6 - 432*z^5 + 272*z^4 + 96*z^3 - 160*z^2 + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 64*t^6*z - 576*t^6 - 32*t^5*z^3 + 144*t^5*z^2 + 784*t^5*z + 3728*t^5 + 112*t^4*z^4 - 736*t^4*z^3 - 1120*t^4*z^2 - 3936*t^4*z - 10464*t^4 - 16*t^3*z^6 + 848*t^3*z^4 + 848*t^3*z^3 + 3488*t^3*z^2 + 3920*t^3*z + 15296*t^3 + 32*t^2*z^7 - 208*t^2*z^6 - 416*t^2*z^5 + 400*t^2*z^4 - 1328*t^2*z^3 - 1184*t^2*z^2 - 2480*t^2*z - 4944*t^2 - 32*t*z^8 + 384*t*z^7 - 1104*t*z^6 + 1760*t*z^5 - 1680*t*z^4 + 1456*t*z^3 - 1808*t*z^2 + 1888*t*z - 4384*t - 32*z^8 + 96*z^7 - 16*z^6 - 128*z^5 + 64*z^4 + 112*z^3 + 32*z^2 + 272*z + 528)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 + 64*t^7*z - 128*t^7 + 48*t^6*z^4 - 64*t^6*z^3 + 320*t^6*z^2 - 640*t^6*z + 448*t^6 - 16*t^5*z^6 - 64*t^5*z^5 - 32*t^5*z^4 + 672*t^5*z^3 - 1552*t^5*z^2 + 2496*t^5*z - 896*t^5 + 64*t^4*z^7 - 48*t^4*z^6 - 80*t^4*z^5 + 48*t^4*z^4 - 2336*t^4*z^3 + 5408*t^4*z^2 - 5120*t^4*z + 1120*t^4 - 112*t^3*z^8 + 240*t^3*z^7 + 160*t^3*z^6 + 192*t^3*z^5 - 1856*t^3*z^4 + 5952*t^3*z^3 - 10832*t^3*z^2 + 6080*t^3*z - 896*t^3 + 96*t^2*z^9 - 176*t^2*z^8 - 784*t^2*z^7 + 1568*t^2*z^6 - 736*t^2*z^5 + 4112*t^2*z^4 - 10624*t^2*z^3 + 11776*t^2*z^2 - 4224*t^2*z + 448*t^2 - 32*t*z^10 - 96*t*z^9 + 1392*t*z^8 - 2864*t*z^7 + 752*t*z^6 + 2048*t*z^5 - 5024*t*z^4 + 9760*t*z^3 - 6512*t*z^2 + 1600*t*z - 128*t + 96*z^10 - 576*z^9 + 560*z^8 + 2320*z^7 - 4976*z^6 + 1712*z^5 + 2704*z^4 - 3360*z^3 + 1440*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 + 16*t^6*z - 448*t^6 + 16*t^5*z^4 + 80*t^5*z^3 + 160*t^5*z^2 - 272*t^5*z + 1760*t^5 - 64*t^4*z^5 - 16*t^4*z^4 - 128*t^4*z^3 - 224*t^4*z^2 + 1728*t^4*z - 4352*t^4 + 112*t^3*z^6 - 128*t^3*z^5 + 48*t^3*z^4 - 528*t^3*z^3 + 1472*t^3*z^2 - 6064*t^3*z + 9184*t^3 - 96*t^2*z^7 + 80*t^2*z^6 + 576*t^2*z^5 - 752*t^2*z^4 + 1712*t^2*z^3 - 4656*t^2*z^2 + 11104*t^2*z - 14640*t^2 + 32*t*z^8 + 128*t*z^7 - 1168*t*z^6 + 2080*t*z^5 - 2176*t*z^4 + 2016*t*z^3 + 512*t*z^2 - 3200*t*z + 4848*t - 96*z^8 + 480*z^7 - 368*z^6 - 1248*z^5 + 2624*z^4 - 2832*z^3 + 2336*z^2 - 2800*z + 2768)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_52 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 52) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_52 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 8*t*z + 2*z^2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8*z^4 - 112*t^7*z^5 - 192*t^7*z^4 + 320*t^6*z^6 + 1344*t^6*z^5 + 704*t^6*z^4 - 480*t^5*z^7 - 3776*t^5*z^6 - 5072*t^5*z^5 - 576*t^5*z^4 + 400*t^4*z^8 + 5488*t^4*z^7 + 14064*t^4*z^6 + 5664*t^4*z^5 - 1312*t^4*z^4 - 176*t^3*z^9 - 4368*t^3*z^8 - 19440*t^3*z^7 - 17152*t^3*z^6 + 3824*t^3*z^5 + 1728*t^3*z^4 + 32*t^2*z^10 + 1808*t^2*z^9 + 14128*t^2*z^8 + 22784*t^2*z^7 - 1696*t^2*z^6 - 7680*t^2*z^5 + 448*t^2*z^4 - 304*t*z^10 - 5056*t*z^9 - 13904*t*z^8 - 2576*t*z^7 + 8896*t*z^6 + 1360*t*z^5 - 960*t*z^4 + 672*z^10 + 3184*z^9 + 1760*z^8 - 2960*z^7 - 1680*z^6 + 672*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 16*t^8*z - 64*t^8 + 112*t^7*z^3 + 304*t^7*z^2 + 640*t^7*z + 1552*t^7 - 320*t^6*z^4 - 1664*t^6*z^3 - 3328*t^6*z^2 - 8320*t^6*z - 18304*t^6 + 480*t^5*z^5 + 4256*t^5*z^4 + 10768*t^5*z^3 + 24112*t^5*z^2 + 56416*t^5*z + 128752*t^5 - 400*t^4*z^6 - 5888*t^4*z^5 - 21152*t^4*z^4 - 44480*t^4*z^3 - 106624*t^4*z^2 - 240064*t^4*z - 559936*t^4 + 176*t^3*z^7 + 4544*t^3*z^6 + 24512*t^3*z^5 + 55296*t^3*z^4 + 125008*t^3*z^3 + 289168*t^3*z^2 + 664192*t^3*z + 1531696*t^3 - 32*t^2*z^8 - 1840*t^2*z^7 - 16064*t^2*z^6 - 44368*t^2*z^5 - 90864*t^2*z^4 - 216288*t^2*z^3 - 489328*t^2*z^2 - 1138192*t^2*z - 2606176*t^2 + 304*t*z^8 + 5360*t*z^7 + 20176*t*z^6 + 38832*t*z^5 + 90464*t*z^4 + 205600*t*z^3 + 477952*t*z^2 + 1094752*t*z + 2528608*t - 672*z^8 - 3856*z^7 - 7632*z^6 - 16240*z^5 - 37456*z^4 - 86848*z^3 - 199360*z^2 - 459904*z - 1057984)*hf
  · have hr : (16*t^8*z^4 - 112*t^7*z^5 - 192*t^7*z^4 + 384*t^6*z^6 + 1088*t^6*z^5 + 704*t^6*z^4 - 816*t^5*z^7 - 3008*t^5*z^6 - 2768*t^5*z^5 - 576*t^5*z^4 + 1168*t^4*z^8 + 5008*t^4*z^7 + 5040*t^4*z^6 + 288*t^4*z^5 - 1312*t^4*z^4 - 1152*t^3*z^9 - 5328*t^3*z^8 - 4944*t^3*z^7 + 2816*t^3*z^6 + 3312*t^3*z^5 + 1728*t^3*z^4 + 768*t^2*z^10 + 3568*t^2*z^9 + 2320*t^2*z^8 - 5120*t^2*z^7 - 4320*t^2*z^6 + 768*t^2*z^5 + 448*t^2*z^4 - 320*t*z^11 - 1344*t*z^10 - 320*t*z^9 + 4400*t*z^8 - 480*t*z^7 - 1600*t*z^6 + 1616*t*z^5 - 960*t*z^4 + 64*z^12 + 224*z^11 - 256*z^10 - 656*z^9 + 320*z^8 + 464*z^7 - 336*z^6 - 96*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 16*t^8*z - 64*t^8 + 112*t^7*z^3 + 304*t^7*z^2 + 640*t^7*z + 1552*t^7 - 384*t^6*z^4 - 1472*t^6*z^3 - 3328*t^6*z^2 - 7744*t^6*z - 17728*t^6 + 816*t^5*z^5 + 3824*t^5*z^4 + 9040*t^5*z^3 + 21088*t^5*z^2 + 48208*t^5*z + 111472*t^5 - 1168*t^4*z^6 - 6176*t^4*z^5 - 14720*t^4*z^4 - 33536*t^4*z^3 - 76384*t^4*z^2 - 176992*t^4*z - 406144*t^4 + 1152*t^3*z^7 + 6480*t^3*z^6 + 14880*t^3*z^5 + 31504*t^3*z^4 + 72832*t^3*z^3 + 165616*t^3*z^2 + 384112*t^3*z + 880960*t^3 - 768*t^2*z^8 - 4336*t^2*z^7 - 8960*t^2*z^6 - 16848*t^2*z^5 - 39408*t^2*z^4 - 90720*t^2*z^3 - 209392*t^2*z^2 - 481552*t^2*z - 1109728*t^2 + 320*t*z^9 + 1664*t*z^8 + 2944*t*z^7 + 3536*t*z^6 + 12848*t*z^5 + 25056*t*z^4 + 61984*t*z^3 + 138112*t*z^2 + 324064*t*z + 738400*t - 64*z^10 - 288*z^9 - 224*z^8 - 432*z^7 - 1424*z^6 - 3184*z^5 - 7120*z^4 - 16576*z^3 - 38080*z^2 - 87808*z - 202048)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_53 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 53) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : (t - z - 3:ℝ)=0 := by
  apply cell_12_53 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 2*t*z^2 - 8*t*z + 2*z^3:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 2*z - 2)*hf
  · have hr : (16*t^8*z^4 - 176*t^7*z^5 - 192*t^7*z^4 + 880*t^6*z^6 + 1792*t^6*z^5 + 704*t^6*z^4 - 2608*t^5*z^7 - 7424*t^5*z^6 - 5264*t^5*z^5 - 576*t^5*z^4 + 5008*t^4*z^8 + 17648*t^4*z^7 + 16720*t^4*z^6 + 2848*t^4*z^5 - 1312*t^4*z^4 - 6384*t^3*z^9 - 25904*t^3*z^8 - 28896*t^3*z^7 - 4096*t^3*z^6 + 5680*t^3*z^5 + 1728*t^3*z^4 + 5280*t^2*z^10 + 23440*t^2*z^9 + 28240*t^2*z^8 + 608*t^2*z^7 - 11120*t^2*z^6 - 3392*t^2*z^5 + 448*t^2*z^4 - 2592*t*z^11 - 12096*t*z^10 - 14576*t*z^9 + 3696*t*z^8 + 8720*t*z^7 + 1024*t*z^6 + 1296*t*z^5 - 960*t*z^4 + 576*z^12 + 2784*z^11 + 2784*z^10 - 1904*z^9 - 2208*z^8 - 80*z^7 - 592*z^6 + 288*z^5 + 144*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 16*t^8*z - 64*t^8 + 176*t^7*z^3 + 368*t^7*z^2 + 896*t^7*z + 2000*t^7 - 880*t^6*z^4 - 2672*t^6*z^3 - 6016*t^6*z^2 - 14032*t^6*z - 32080*t^6 + 2608*t^5*z^5 + 10032*t^5*z^4 + 23120*t^5*z^3 + 53792*t^5*z^2 + 123152*t^5*z + 284528*t^5 - 5008*t^4*z^6 - 22656*t^4*z^5 - 54400*t^4*z^4 - 125216*t^4*z^3 - 287104*t^4*z^2 - 662752*t^4*z - 1524064*t^4 + 6384*t^3*z^7 + 32288*t^3*z^6 + 80336*t^3*z^5 + 181296*t^3*z^4 + 416624*t^3*z^3 + 958784*t^3*z^2 + 2208656*t^3*z + 5085008*t^3 - 5280*t^2*z^8 - 28720*t^2*z^7 - 72800*t^2*z^6 - 159568*t^2*z^5 - 366848*t^2*z^4 - 842160*t^2*z^3 - 1943152*t^2*z^2 - 4469632*t^2*z - 10299088*t^2 + 2592*t*z^9 + 14688*t*z^8 + 37040*t*z^7 + 77408*t*z^6 + 179808*t*z^5 + 411008*t*z^4 + 949136*t*z^3 + 2183120*t*z^2 + 5030528*t*z + 11579888*t - 576*z^10 - 3360*z^9 - 7872*z^8 - 16048*z^7 - 37456*z^6 - 85520*z^5 - 197296*z^4 - 454144*z^3 - 1046176*z^2 - 2408608*z - 5547136)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_54 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 54) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_54 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 2*t*z^2 - 6*t*z + 2*z^3 - 2*z^2 + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 2*z)*hf
  · have hr : (16*t^8*z^4 - 176*t^7*z^5 - 128*t^7*z^4 + 880*t^6*z^6 + 1136*t^6*z^5 + 288*t^6*z^4 + 64*t^6*z^3 - 2608*t^5*z^7 - 4448*t^5*z^6 - 1808*t^5*z^5 - 656*t^5*z^4 - 384*t^5*z^3 + 5008*t^4*z^8 + 9888*t^4*z^7 + 4608*t^4*z^6 + 2128*t^4*z^5 + 2000*t^4*z^4 + 576*t^4*z^3 + 96*t^4*z^2 - 6384*t^3*z^9 - 13328*t^3*z^8 - 5968*t^3*z^7 - 2736*t^3*z^6 - 4960*t^3*z^5 - 1296*t^3*z^4 - 528*t^3*z^3 - 384*t^3*z^2 + 5280*t^2*z^10 + 10752*t^2*z^9 + 3696*t^2*z^8 + 1600*t^2*z^7 + 6096*t^2*z^6 + 1024*t^2*z^5 + 336*t^2*z^4 + 688*t^2*z^3 + 288*t^2*z^2 + 64*t^2*z - 2592*t*z^11 - 4704*t*z^10 - 656*t*z^9 - 224*t*z^8 - 4656*t*z^7 + 656*t*z^6 + 1152*t*z^5 - 1728*t*z^4 + 384*t*z^3 - 48*t*z^2 - 128*t*z + 576*z^12 + 864*z^11 - 448*z^10 + 832*z^9 + 304*z^8 - 304*z^7 + 336*z^6 - 528*z^5 + 16*z^4 + 224*z^3 - 96*z^2 + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 16*t^8*z - 64*t^8 + 176*t^7*z^3 + 304*t^7*z^2 + 832*t^7*z + 1744*t^7 - 880*t^6*z^4 - 2016*t^6*z^3 - 4944*t^6*z^2 - 11056*t^6*z - 25888*t^6 + 2608*t^5*z^5 + 7056*t^5*z^4 + 16688*t^5*z^3 + 38512*t^5*z^2 + 88960*t^5*z + 204496*t^5 - 5008*t^4*z^6 - 14896*t^4*z^5 - 34528*t^4*z^4 - 81344*t^4*z^3 - 186928*t^4*z^2 - 431536*t^4*z - 992416*t^4 + 6384*t^3*z^7 + 19712*t^3*z^6 + 44832*t^3*z^5 + 106704*t^3*z^4 + 246160*t^3*z^3 + 567568*t^3*z^2 + 1306576*t^3*z + 3009664*t^3 - 5280*t^2*z^8 - 16032*t^2*z^7 - 35568*t^2*z^6 - 85264*t^2*z^5 - 198064*t^2*z^4 - 454880*t^2*z^3 - 1049408*t^2*z^2 - 2414736*t^2*z - 5563248*t^2 + 2592*t*z^9 + 7296*t*z^8 + 15728*t*z^7 + 37840*t*z^6 + 89680*t*z^5 + 202544*t*z^4 + 470432*t*z^3 + 1079792*t*z^2 + 2490704*t*z + 5730128*t - 576*z^10 - 1440*z^9 - 2720*z^8 - 7872*z^7 - 16336*z^6 - 39648*z^5 - 88992*z^4 - 207408*z^3 - 474400*z^2 - 1096848*z - 2519952)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_55 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 55) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_55 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z - 4*t + 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 320*t^7*z - 128*t^7 - 160*t^6*z^3 + 2368*t^6*z^2 + 2048*t^6*z + 448*t^6 + 32*t^5*z^5 + 352*t^5*z^4 - 8832*t^5*z^3 - 11728*t^5*z^2 - 5568*t^5*z - 896*t^5 - 240*t^4*z^6 + 944*t^4*z^5 + 19216*t^4*z^4 + 31840*t^4*z^3 + 23328*t^4*z^2 + 8320*t^4*z + 1120*t^4 + 16*t^3*z^8 + 496*t^3*z^7 - 5104*t^3*z^6 - 25408*t^3*z^5 - 46848*t^3*z^4 - 43008*t^3*z^3 - 23952*t^3*z^2 - 7360*t^3*z - 896*t^3 - 64*t^2*z^9 - 80*t^2*z^8 + 7984*t^2*z^7 + 18688*t^2*z^6 + 39328*t^2*z^5 + 40928*t^2*z^4 + 27680*t^2*z^3 + 13312*t^2*z^2 + 3840*t^2*z + 448*t^2 + 80*t*z^10 - 816*t*z^9 - 3664*t*z^8 - 9072*t*z^7 - 17264*t*z^6 - 17632*t*z^5 - 15840*t*z^4 - 8576*t*z^3 - 3760*t*z^2 - 1088*t*z - 128*t + 320*z^10 + 640*z^9 + 1744*z^8 + 3408*z^7 + 2896*z^6 + 2736*z^5 + 2192*z^4 + 1056*z^3 + 416*z^2 + 128*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 160*t^6*z - 2208*t^6 - 32*t^5*z^3 - 384*t^5*z^2 + 8352*t^5*z + 18928*t^5 + 240*t^4*z^4 - 704*t^4*z^3 - 19200*t^4*z^2 - 53152*t^4*z - 134080*t^4 - 16*t^3*z^6 - 512*t^3*z^5 + 4544*t^3*z^4 + 28416*t^3*z^3 + 88896*t^3*z^2 + 217152*t^3*z + 507792*t^3 + 64*t^2*z^7 + 144*t^2*z^6 - 7648*t^2*z^5 - 25904*t^2*z^4 - 88176*t^2*z^3 - 206816*t^2*z^2 - 499024*t^2*z - 1132784*t^2 - 80*t*z^8 + 736*t*z^7 + 4160*t*z^6 + 15440*t*z^5 + 45184*t*z^4 + 109136*t*z^3 + 260528*t*z^2 + 596512*t*z + 1381856*t - 320*z^8 - 960*z^7 - 3664*z^6 - 9952*z^5 - 23840*z^4 - 56432*z^3 - 130144*z^2 - 300496*z - 691344)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_56 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 56) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_56 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 6*t*z + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8*z^4 - 112*t^7*z^5 - 128*t^7*z^4 + 320*t^6*z^6 + 1008*t^6*z^5 - 96*t^6*z^4 + 64*t^6*z^3 - 480*t^5*z^7 - 3104*t^5*z^6 - 752*t^5*z^5 + 1840*t^5*z^4 - 384*t^5*z^3 + 400*t^4*z^8 + 4848*t^4*z^7 + 5456*t^4*z^6 - 10640*t^4*z^5 + 2000*t^4*z^4 - 576*t^4*z^3 + 96*t^4*z^2 - 176*t^3*z^9 - 4080*t^3*z^8 - 11568*t^3*z^7 + 17792*t^3*z^6 + 9888*t^3*z^5 - 13584*t^3*z^4 + 4272*t^3*z^3 - 384*t^3*z^2 + 32*t^2*z^10 + 1760*t^2*z^9 + 10896*t^2*z^8 - 8512*t^2*z^7 - 39504*t^2*z^6 + 47616*t^2*z^5 - 17312*t^2*z^4 + 4528*t^2*z^3 - 864*t^2*z^2 + 64*t^2*z - 304*t*z^10 - 4608*t*z^9 - 2720*t*z^8 + 37968*t*z^7 - 30864*t*z^6 - 22784*t*z^5 + 35616*t*z^4 - 14496*t*z^3 + 2320*t*z^2 - 128*t*z + 672*z^10 + 2144*z^9 - 9392*z^8 - 6768*z^7 + 51216*z^6 - 70544*z^5 + 46800*z^4 - 17376*z^3 + 3616*z^2 - 384*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 16*t^8*z - 64*t^8 + 112*t^7*z^3 + 240*t^7*z^2 + 576*t^7*z + 1296*t^7 - 320*t^6*z^4 - 1328*t^6*z^3 - 2192*t^6*z^2 - 6240*t^6*z - 12816*t^6 + 480*t^5*z^5 + 3584*t^5*z^4 + 5776*t^5*z^3 + 14688*t^5*z^2 + 32400*t^5*z + 76464*t^5 - 400*t^4*z^6 - 5248*t^4*z^5 - 11904*t^4*z^4 - 17008*t^4*z^3 - 54720*t^4*z^2 - 105168*t^4*z - 269424*t^4 + 176*t^3*z^7 + 4256*t^3*z^6 + 16352*t^3*z^5 + 11328*t^3*z^4 + 50496*t^3*z^3 + 98064*t^3*z^2 + 245280*t^3*z + 539856*t^3 - 32*t^2*z^8 - 1792*t^2*z^7 - 12784*t^2*z^6 - 9648*t^2*z^5 - 8496*t^2*z^4 - 85056*t^2*z^3 - 93232*t^2*z^2 - 352928*t^2*z - 631760*t^2 + 304*t*z^8 + 4912*t*z^7 + 8544*t*z^6 - 14688*t*z^5 + 41808*t*z^4 + 20528*t*z^3 + 110336*t*z^2 + 186416*t*z + 515104*t - 672*z^8 - 2816*z^7 + 4560*z^6 + 2880*z^5 - 34656*z^4 + 44528*z^3 - 106240*z^2 + 44720*z - 277616)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_57 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 57) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_57 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 2*t*z^2 - 6*t*z + 2*z^3 - 2*z^2 + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 2*z)*hf
  · have hr : (16*t^8*z^4 - 176*t^7*z^5 - 128*t^7*z^4 + 880*t^6*z^6 + 1200*t^6*z^5 + 32*t^6*z^4 + 64*t^6*z^3 - 2608*t^5*z^7 - 4976*t^5*z^6 - 80*t^5*z^5 + 880*t^5*z^4 - 384*t^5*z^3 + 5008*t^4*z^8 + 11808*t^4*z^7 - 672*t^4*z^6 - 7280*t^4*z^5 + 1424*t^4*z^4 - 192*t^4*z^3 + 96*t^4*z^2 - 6384*t^3*z^9 - 17248*t^3*z^8 + 3456*t^3*z^7 + 22080*t^3*z^6 - 3648*t^3*z^5 - 3984*t^3*z^4 + 2544*t^3*z^3 - 384*t^3*z^2 + 5280*t^2*z^10 + 15488*t^2*z^9 - 6880*t^2*z^8 - 33360*t^2*z^7 + 8944*t^2*z^6 + 15392*t^2*z^5 - 7664*t^2*z^4 + 1648*t^2*z^3 - 480*t^2*z^2 + 64*t^2*z - 2592*t*z^11 - 7920*t*z^10 + 6592*t*z^9 + 25600*t*z^8 - 13264*t*z^7 - 22848*t*z^6 + 17280*t*z^5 + 1840*t*z^4 - 5056*t*z^3 + 1488*t*z^2 - 128*t*z + 576*z^12 + 1824*z^11 - 2784*z^10 - 7584*z^9 + 8720*z^8 + 7568*z^7 - 13424*z^6 + 3536*z^5 + 4176*z^4 - 4000*z^3 + 1504*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 16*t^8*z - 64*t^8 + 176*t^7*z^3 + 304*t^7*z^2 + 832*t^7*z + 1744*t^7 - 880*t^6*z^4 - 2080*t^6*z^3 - 4752*t^6*z^2 - 11056*t^6*z - 25312*t^6 + 2608*t^5*z^5 + 7584*t^5*z^4 + 15488*t^5*z^3 + 37360*t^5*z^2 + 84208*t^5*z + 196288*t^5 - 5008*t^4*z^6 - 16816*t^4*z^5 - 31168*t^4*z^4 - 74336*t^4*z^3 - 169264*t^4*z^2 - 392080*t^4*z - 899968*t^4 + 6384*t^3*z^7 + 23632*t^3*z^6 + 39328*t^3*z^5 + 88144*t^3*z^4 + 209776*t^3*z^3 + 478192*t^3*z^2 + 1104976*t^3*z + 2539936*t^3 - 5280*t^2*z^8 - 20768*t^2*z^7 - 29728*t^2*z^6 - 58672*t^2*z^5 - 156800*t^2*z^4 - 348208*t^2*z^3 - 810944*t^2*z^2 - 1857216*t^2*z - 4289568*t^2 + 2592*t*z^9 + 10512*t*z^8 + 11696*t*z^7 + 17632*t*z^6 + 65984*t*z^5 + 141728*t*z^4 + 322400*t*z^3 + 745744*t*z^2 + 1718000*t*z + 3953744*t - 576*z^10 - 2400*z^9 - 1344*z^8 - 960*z^7 - 13712*z^6 - 24160*z^5 - 51872*z^4 - 127888*z^3 - 287680*z^2 - 667344*z - 1531888)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_58 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 58) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_58 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z - 2*t*z^2 - 4*t*z + 2*z^3 - 4*z^2 + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 2*z + 2)*hf
  · have hr : (16*t^8*z^4 - 176*t^7*z^5 - 64*t^7*z^4 + 880*t^6*z^6 + 544*t^6*z^5 - 128*t^6*z^4 - 2608*t^5*z^7 - 2000*t^5*z^6 + 1216*t^5*z^5 + 512*t^5*z^4 + 5008*t^4*z^8 + 4048*t^4*z^7 - 4912*t^4*z^6 - 2816*t^4*z^5 + 256*t^4*z^4 - 6384*t^3*z^9 - 4672*t^3*z^8 + 10528*t^3*z^7 + 6528*t^3*z^6 - 2816*t^3*z^5 - 1024*t^3*z^4 + 5280*t^2*z^10 + 2800*t^2*z^9 - 12832*t^2*z^8 - 6912*t^2*z^7 + 7808*t^2*z^6 + 2560*t^2*z^5 - 2592*t*z^11 - 528*t*z^10 + 8496*t*z^9 + 2688*t*z^8 - 8832*t*z^7 - 2304*t*z^6 + 3072*t*z^5 + 576*z^12 - 96*z^11 - 2688*z^10 + 1056*z^9 + 2688*z^8 - 768*z^7 - 768*z^6:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 - 16*t^8*z - 64*t^8 + 176*t^7*z^3 + 240*t^7*z^2 + 768*t^7*z + 1488*t^7 - 880*t^6*z^4 - 1424*t^6*z^3 - 3936*t^6*z^2 - 8208*t^6*z - 20016*t^6 + 2608*t^5*z^5 + 4608*t^5*z^4 + 11216*t^5*z^3 + 24528*t^5*z^2 + 58176*t^5*z + 131760*t^5 - 5008*t^4*z^6 - 9056*t^4*z^5 - 19168*t^4*z^4 - 43520*t^4*z^3 - 101280*t^4*z^2 - 231840*t^4*z - 535680*t^4 + 6384*t^3*z^7 + 11056*t^3*z^6 + 19680*t^3*z^5 + 46320*t^3*z^4 + 108176*t^3*z^3 + 248160*t^3*z^2 + 572688*t^3*z + 1317168*t^3 - 5280*t^2*z^8 - 8080*t^2*z^7 - 11088*t^2*z^6 - 28416*t^2*z^5 - 69488*t^2*z^4 - 157296*t^2*z^3 - 365760*t^2*z^2 - 837648*t^2*z - 1934928*t^2 + 2592*t*z^9 + 3120*t*z^8 + 2400*t*z^7 + 9072*t*z^6 + 25104*t*z^5 + 54624*t*z^4 + 126864*t*z^3 + 290736*t*z^2 + 671328*t*z + 1543536*t - 576*z^10 - 480*z^9 + 480*z^8 - 2016*z^7 - 3264*z^6 - 8544*z^5 - 17568*z^4 - 43200*z^3 - 95904*z^2 - 225504*z - 513216)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_59 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 59) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_59 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 320*t^7*z - 160*t^6*z^3 + 2464*t^6*z^2 - 128*t^6*z + 32*t^5*z^5 + 352*t^5*z^4 - 9600*t^5*z^3 + 2048*t^5*z^2 - 240*t^4*z^6 + 1072*t^4*z^5 + 20240*t^4*z^4 - 11136*t^4*z^3 + 256*t^4*z^2 + 16*t^3*z^8 + 496*t^3*z^7 - 5808*t^3*z^6 - 20544*t^3*z^5 + 25344*t^3*z^4 - 3072*t^3*z^3 - 64*t^2*z^9 - 48*t^2*z^8 + 8848*t^2*z^7 + 3264*t^2*z^6 - 22784*t^2*z^5 + 9216*t^2*z^4 + 80*t*z^10 - 880*t*z^9 - 3328*t*z^8 + 5120*t*z^7 + 4096*t*z^6 - 4096*t*z^5 + 320*z^10 + 64*z^9 - 1536*z^8 + 1024*z^7:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 160*t^6*z - 2304*t^6 - 32*t^5*z^3 - 384*t^5*z^2 + 9120*t^5*z + 5920*t^5 + 240*t^4*z^4 - 832*t^4*z^3 - 20352*t^4*z^2 - 11712*t^4*z - 73024*t^4 - 16*t^3*z^6 - 512*t^3*z^5 + 5248*t^3*z^4 + 24256*t^3*z^3 + 14656*t^3*z^2 + 90496*t^3*z + 134464*t^3 + 64*t^2*z^7 + 112*t^2*z^6 - 8544*t^2*z^5 - 11472*t^2*z^4 - 14320*t^2*z^3 - 57952*t^2*z^2 - 100912*t^2*z - 274768*t^2 - 80*t*z^8 + 800*t*z^7 + 3888*t*z^6 + 1168*t*z^5 + 8736*t*z^4 + 16336*t*z^3 + 42544*t*z^2 + 91552*t*z + 219184*t - 320*z^8 - 384*z^7 + 192*z^6 - 1984*z^5 - 1408*z^4 - 7360*z^3 - 11584*z^2 - 33664*z - 68416)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_60 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 60) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_60 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 6*t*z - 4*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 + 64*t^7*z - 128*t^7 + 48*t^6*z^4 - 64*t^6*z^3 + 320*t^6*z^2 - 640*t^6*z + 448*t^6 - 16*t^5*z^6 - 64*t^5*z^5 - 32*t^5*z^4 + 672*t^5*z^3 - 1552*t^5*z^2 + 2496*t^5*z - 896*t^5 + 64*t^4*z^7 - 48*t^4*z^6 - 80*t^4*z^5 + 48*t^4*z^4 - 2336*t^4*z^3 + 5408*t^4*z^2 - 5120*t^4*z + 1120*t^4 - 112*t^3*z^8 + 240*t^3*z^7 + 160*t^3*z^6 + 192*t^3*z^5 - 1856*t^3*z^4 + 5952*t^3*z^3 - 10832*t^3*z^2 + 6080*t^3*z - 896*t^3 + 96*t^2*z^9 - 176*t^2*z^8 - 784*t^2*z^7 + 1568*t^2*z^6 - 736*t^2*z^5 + 4112*t^2*z^4 - 10624*t^2*z^3 + 11776*t^2*z^2 - 4224*t^2*z + 448*t^2 - 32*t*z^10 - 96*t*z^9 + 1392*t*z^8 - 2864*t*z^7 + 752*t*z^6 + 2048*t*z^5 - 5024*t*z^4 + 9760*t*z^3 - 6512*t*z^2 + 1600*t*z - 128*t + 96*z^10 - 576*z^9 + 560*z^8 + 2320*z^7 - 4976*z^6 + 1712*z^5 + 2704*z^4 - 3360*z^3 + 1440*z^2 - 256*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 + 16*t^6*z - 448*t^6 + 16*t^5*z^4 + 80*t^5*z^3 + 160*t^5*z^2 - 272*t^5*z + 1760*t^5 - 64*t^4*z^5 - 16*t^4*z^4 - 128*t^4*z^3 - 224*t^4*z^2 + 1728*t^4*z - 4352*t^4 + 112*t^3*z^6 - 128*t^3*z^5 + 48*t^3*z^4 - 528*t^3*z^3 + 1472*t^3*z^2 - 6064*t^3*z + 9184*t^3 - 96*t^2*z^7 + 80*t^2*z^6 + 576*t^2*z^5 - 752*t^2*z^4 + 1712*t^2*z^3 - 4656*t^2*z^2 + 11104*t^2*z - 14640*t^2 + 32*t*z^8 + 128*t*z^7 - 1168*t*z^6 + 2080*t*z^5 - 2176*t*z^4 + 2016*t*z^3 + 512*t*z^2 - 3200*t*z + 4848*t - 96*z^8 + 480*z^7 - 368*z^6 - 1248*z^5 + 2624*z^4 - 2832*z^3 + 2336*z^2 - 2800*z + 2768)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 192*t^7*z - 128*t^7 - 64*t^6*z^3 + 640*t^6*z^2 + 1152*t^6*z + 448*t^6 + 32*t^5*z^5 - 176*t^5*z^4 - 736*t^5*z^3 - 2512*t^5*z^2 - 2880*t^5*z - 896*t^5 - 112*t^4*z^6 + 848*t^4*z^5 + 720*t^4*z^4 + 608*t^4*z^3 + 3168*t^4*z^2 + 3840*t^4*z + 1120*t^4 + 16*t^3*z^8 - 16*t^3*z^7 - 896*t^3*z^6 - 96*t^3*z^4 + 2112*t^3*z^3 - 912*t^3*z^2 - 2880*t^3*z - 896*t^3 - 32*t^2*z^9 + 240*t^2*z^8 + 304*t^2*z^7 - 1440*t^2*z^6 + 480*t^2*z^5 + 1056*t^2*z^4 - 2688*t^2*z^3 - 1088*t^2*z^2 + 1152*t^2*z + 448*t^2 + 32*t*z^10 - 416*t*z^9 + 1392*t*z^8 - 1712*t*z^7 + 128*t*z^6 + 2144*t*z^5 - 1776*t*z^4 + 672*t*z^3 + 848*t*z^2 - 192*t*z - 128*t + 32*z^10 - 128*z^9 + 16*z^8 + 400*z^7 - 240*z^6 - 432*z^5 + 272*z^4 + 96*z^3 - 160*z^2 + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 64*t^6*z - 576*t^6 - 32*t^5*z^3 + 144*t^5*z^2 + 784*t^5*z + 3728*t^5 + 112*t^4*z^4 - 736*t^4*z^3 - 1120*t^4*z^2 - 3936*t^4*z - 10464*t^4 - 16*t^3*z^6 + 848*t^3*z^4 + 848*t^3*z^3 + 3488*t^3*z^2 + 3920*t^3*z + 15296*t^3 + 32*t^2*z^7 - 208*t^2*z^6 - 416*t^2*z^5 + 400*t^2*z^4 - 1328*t^2*z^3 - 1184*t^2*z^2 - 2480*t^2*z - 4944*t^2 - 32*t*z^8 + 384*t*z^7 - 1104*t*z^6 + 1760*t*z^5 - 1680*t*z^4 + 1456*t*z^3 - 1808*t*z^2 + 1888*t*z - 4384*t - 32*z^8 + 96*z^7 - 16*z^6 - 128*z^5 + 64*z^4 + 112*z^3 + 32*z^2 + 272*z + 528)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_61 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 61) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_61 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z - 4*t + 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 - 64*t^7*z - 128*t^7 + 48*t^6*z^4 + 288*t^6*z^3 + 256*t^6*z^2 + 256*t^6*z + 448*t^6 - 16*t^5*z^6 - 400*t^5*z^5 - 464*t^5*z^4 - 896*t^5*z^3 - 16*t^5*z^2 - 192*t^5*z - 896*t^5 + 192*t^4*z^7 + 880*t^4*z^6 + 624*t^4*z^5 - 336*t^4*z^4 + 1056*t^4*z^3 - 1312*t^4*z^2 - 640*t^4*z + 1120*t^4 - 16*t^3*z^9 - 624*t^3*z^8 - 528*t^3*z^7 - 304*t^3*z^6 + 1824*t^3*z^5 + 1184*t^3*z^4 - 2048*t^3*z^3 + 1968*t^3*z^2 + 1600*t^3*z - 896*t^3 + 80*t^2*z^10 + 736*t^2*z^9 - 64*t^2*z^8 - 2352*t^2*z^7 + 1440*t^2*z^6 - 1824*t^2*z^5 - 944*t^2*z^4 + 3424*t^2*z^3 - 704*t^2*z^2 - 1536*t^2*z + 448*t^2 - 128*t*z^11 - 272*t*z^10 + 368*t*z^9 + 2304*t*z^8 - 1712*t*z^7 - 3104*t*z^6 + 2800*t*z^5 + 1712*t*z^4 - 2176*t*z^3 - 368*t*z^2 + 704*t*z - 128*t + 64*z^12 + 32*z^11 - 640*z^10 + 352*z^9 + 1264*z^8 - 1488*z^7 + 80*z^6 + 1072*z^5 - 1200*z^4 + 352*z^3 + 224*z^2 - 128*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 - 336*t^6*z - 736*t^6 + 16*t^5*z^4 + 416*t^5*z^3 + 928*t^5*z^2 + 3072*t^5*z + 5872*t^5 - 192*t^4*z^5 - 1072*t^4*z^4 - 2272*t^4*z^3 - 5152*t^4*z^2 - 13024*t^4*z - 27168*t^4 + 16*t^3*z^7 + 640*t^3*z^6 + 1216*t^3*z^5 + 3440*t^3*z^4 + 5264*t^3*z^3 + 14400*t^3*z^2 + 32240*t^3*z + 73472*t^3 - 80*t^2*z^8 - 816*t^2*z^7 - 992*t^2*z^6 - 1088*t^2*z^5 - 5504*t^2*z^4 - 6944*t^2*z^3 - 22512*t^2*z^2 - 46768*t^2*z - 113600*t^2 + 128*t*z^9 + 400*t*z^8 + 416*t*z^7 - 688*t*z^6 + 2272*t*z^5 + 3312*t*z^4 + 7328*t*z^3 + 15552*t*z^2 + 39712*t*z + 86736*t - 64*z^10 - 96*z^9 + 352*z^8 - 288*z^7 - 496*z^6 + 128*z^5 - 1440*z^4 - 2128*z^3 - 5248*z^2 - 11984*z - 27952)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_62 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 62) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_62 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 - 64*t^7*z + 48*t^6*z^4 + 288*t^6*z^3 - 96*t^6*z^2 - 128*t^6*z - 16*t^5*z^6 - 400*t^5*z^5 - 128*t^5*z^4 + 640*t^5*z^3 + 512*t^5*z^2 + 192*t^4*z^7 + 752*t^4*z^6 - 1264*t^4*z^5 - 1520*t^4*z^4 + 640*t^4*z^3 + 256*t^4*z^2 - 16*t^3*z^9 - 608*t^3*z^8 + 336*t^3*z^7 + 2224*t^3*z^6 + 832*t^3*z^5 - 2816*t^3*z^4 - 1024*t^3*z^3 + 80*t^2*z^10 + 608*t^2*z^9 - 1648*t^2*z^8 - 2256*t^2*z^7 + 4416*t^2*z^6 + 1280*t^2*z^5 - 1024*t^2*z^4 - 128*t*z^11 + 16*t*z^10 + 1008*t*z^9 + 1024*t*z^8 - 5120*t*z^7 + 4096*t*z^5 + 64*z^12 - 160*z^11 - 416*z^10 + 1216*z^9 - 1024*z^7:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 - 336*t^6*z - 384*t^6 + 16*t^5*z^4 + 416*t^5*z^3 + 592*t^5*z^2 + 1200*t^5*z + 2464*t^5 - 192*t^4*z^5 - 944*t^4*z^4 - 256*t^4*z^3 - 1568*t^4*z^2 - 2976*t^4*z - 7936*t^4 + 16*t^3*z^7 + 624*t^3*z^6 + 336*t^3*z^5 - 16*t^3*z^4 + 160*t^3*z^3 + 2928*t^3*z^2 + 4432*t^3*z + 13216*t^3 - 80*t^2*z^8 - 688*t^2*z^7 + 720*t^2*z^6 + 912*t^2*z^5 - 1344*t^2*z^4 + 112*t^2*z^3 - 2896*t^2*z^2 - 2560*t^2*z - 11248*t^2 + 128*t*z^9 + 112*t*z^8 - 512*t*z^7 - 1200*t*z^6 + 2384*t*z^5 - 1216*t*z^4 + 1840*t*z^3 - 1808*t*z^2 + 3712*t*z - 1712*t - 64*z^10 + 96*z^9 + 320*z^8 - 608*z^7 + 352*z^6 - 448*z^5 + 608*z^4 - 736*z^3 + 1088*z^2 - 1120*z + 2144)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_12_63 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z) (profile4 (z + 1) (z) t 63) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : False := by
  apply cell_12_63 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t*z^2 - 8*t*z + 2*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (32*t*z^10 - 352*t*z^9 + 1280*t*z^8 - 1280*t*z^7 - 1792*t*z^6 + 3072*t*z^5 + 32*z^10 - 224*z^9 + 384*z^8 + 256*z^7 - 768*z^6:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-32*t*z^8 + 320*t*z^7 - 1056*t*z^6 + 1184*t*z^5 - 192*t*z^4 + 288*t*z^3 - 288*t*z^2 + 576*t*z - 288*t - 32*z^8 + 192*z^7 - 288*z^6 + 32*z^5 - 64*z^4 + 32*z^3 - 160*z^2 - 64*z - 544)*hf


private def limit12 (z t : ℝ) : Fin 64→Prop := ![False,False,False,False,False,((t - 2*z - 3:ℝ)=0),False,False,False,False,False,False,False,False,False,((t + z - 3:ℝ)=0),False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,((t - z + 2:ℝ)=0),False,False,False,False,False,((t - z + 2:ℝ)=0),False,False,False,False,False,False,False,((t - z - 3:ℝ)=0),False,False,False,False,False,False,False,False,False,False]

private def hue12 : Fin 64→Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_12_5_15 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit12 z t 5) (hj : limit12 z t 15) (_he : edge4 (1) (1) (z) (profile4 (z + 1) (z) t 5) (profile4 (z + 1) (z) t 15) (z + 1) (z) t=0) : False := by
  apply pair_12_5_15 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_12_5_39 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit12 z t 5) (hj : limit12 z t 39) (_he : edge4 (1) (1) (z) (profile4 (z + 1) (z) t 5) (profile4 (z + 1) (z) t 39) (z + 1) (z) t=0) : False := by
  apply pair_12_5_39 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_12_5_45 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit12 z t 5) (hj : limit12 z t 45) (_he : edge4 (1) (1) (z) (profile4 (z + 1) (z) t 5) (profile4 (z + 1) (z) t 45) (z + 1) (z) t=0) : False := by
  apply pair_12_5_45 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_12_5_53 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit12 z t 5) (hj : limit12 z t 53) (_he : edge4 (1) (1) (z) (profile4 (z + 1) (z) t 5) (profile4 (z + 1) (z) t 53) (z + 1) (z) t=0) : False := by
  apply pair_12_5_53 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_12_15_39 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit12 z t 15) (hj : limit12 z t 39) (_he : edge4 (1) (1) (z) (profile4 (z + 1) (z) t 15) (profile4 (z + 1) (z) t 39) (z + 1) (z) t=0) : False := by
  apply pair_12_15_39 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_12_15_45 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit12 z t 15) (hj : limit12 z t 45) (_he : edge4 (1) (1) (z) (profile4 (z + 1) (z) t 15) (profile4 (z + 1) (z) t 45) (z + 1) (z) t=0) : False := by
  apply pair_12_15_45 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_12_15_53 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit12 z t 15) (hj : limit12 z t 53) (_he : edge4 (1) (1) (z) (profile4 (z + 1) (z) t 15) (profile4 (z + 1) (z) t 53) (z + 1) (z) t=0) : False := by
  apply pair_12_15_53 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_12_39_45 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit12 z t 39) (_hj : limit12 z t 45) (he : edge4 (1) (1) (z) (profile4 (z + 1) (z) t 39) (profile4 (z + 1) (z) t 45) (z + 1) (z) t=0) : False := by
  apply pair_12_39_45 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (16*t^8*z^4 - 256*t^8*z^3 + 1536*t^8*z^2 - 4096*t^8*z + 4096*t^8 - 144*t^7*z^5 + 2176*t^7*z^4 - 11776*t^7*z^3 + 24576*t^7*z^2 - 4096*t^7*z - 32768*t^7 + 512*t^6*z^6 - 7232*t^6*z^5 + 34240*t^6*z^4 - 46080*t^6*z^3 - 71680*t^6*z^2 + 131072*t^6*z + 114688*t^6 - 912*t^5*z^7 + 11840*t^5*z^6 - 46256*t^5*z^5 + 12160*t^5*z^4 + 222720*t^5*z^3 - 90112*t^5*z^2 - 471040*t^5*z - 229376*t^5 + 848*t^4*z^8 - 9776*t^4*z^7 + 26864*t^4*z^6 + 53216*t^4*z^5 - 233376*t^4*z^4 - 201216*t^4*z^3 + 570368*t^4*z^2 + 819200*t^4*z + 286720*t^4 - 384*t^3*z^9 + 3536*t^3*z^8 - 1392*t^3*z^7 - 59200*t^3*z^6 + 80400*t^3*z^5 + 304000*t^3*z^4 - 127488*t^3*z^3 - 892928*t^3*z^2 - 815104*t^3*z - 229376*t^3 + 64*t^2*z^10 - 176*t^2*z^9 - 4432*t^2*z^8 + 22272*t^2*z^7 + 9376*t^2*z^6 - 131328*t^2*z^5 - 123456*t^2*z^4 + 304128*t^2*z^3 + 673792*t^2*z^2 + 475136*t^2*z + 114688*t^2 - 96*t*z^10 + 928*t*z^9 - 1008*t*z^8 - 11552*t*z^7 + 16768*t*z^6 + 59696*t*z^5 - 4992*t*z^4 - 173568*t*z^3 - 253952*t*z^2 - 151552*t*z - 32768*t + 32*z^10 - 368*z^9 + 1056*z^8 + 1360*z^7 - 6160*z^6 - 8352*z^5 + 9232*z^4 + 33536*z^3 + 38400*z^2 + 20480*z + 4096:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-16*t^8*z^2 + 240*t^8*z - 1344*t^8 + 144*t^7*z^3 - 2032*t^7*z^2 + 10176*t^7*z - 20496*t^7 - 512*t^6*z^4 + 6720*t^6*z^3 - 29056*t^6*z^2 + 37184*t^6*z + 21696*t^6 + 912*t^5*z^5 - 10928*t^5*z^4 + 38064*t^5*z^3 - 6880*t^5*z^2 - 115408*t^5*z - 45936*t^5 - 848*t^4*z^6 + 8928*t^4*z^5 - 20480*t^4*z^4 - 46912*t^4*z^3 + 125024*t^4*z^2 + 185504*t^4*z - 9792*t^4 + 384*t^3*z^7 - 3152*t^3*z^6 - 608*t^3*z^5 + 49136*t^3*z^4 - 33088*t^3*z^3 - 189680*t^3*z^2 - 161456*t^3*z + 162432*t^3 - 64*t^2*z^8 + 112*t^2*z^7 + 4352*t^2*z^6 - 17584*t^2*z^5 - 13904*t^2*z^4 + 64672*t^2*z^3 + 146416*t^2*z^2 + 36304*t^2*z - 198240*t^2 + 96*t*z^8 - 832*t*z^7 + 464*t*z^6 + 9520*t*z^5 - 5856*t*z^4 - 36992*t*z^3 - 49568*t*z^2 + 13024*t*z + 118272*t - 32*z^8 + 336*z^7 - 816*z^6 - 1168*z^5 + 2544*z^4 + 7392*z^3 + 5792*z^2 - 5568*z - 26592)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_12_39_53 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit12 z t 39) (hj : limit12 z t 53) (_he : edge4 (1) (1) (z) (profile4 (z + 1) (z) t 39) (profile4 (z + 1) (z) t 53) (z + 1) (z) t=0) : False := by
  apply pair_12_39_53 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_12_45_53 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit12 z t 45) (hj : limit12 z t 53) (_he : edge4 (1) (1) (z) (profile4 (z + 1) (z) t 45) (profile4 (z + 1) (z) t 53) (z + 1) (z) t=0) : False := by
  apply pair_12_45_53 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma exclude_field_12 (z t : ℝ) (hf : z^2 - z - 3=0) (hn0 : t-(1)≠0) (hn1 : t-(z + 1)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (g : Fin 5→Fin 64) (hinj : Function.Injective g)
    (hc : ∀ i, cell (1) (1) (z) (profile4 (z + 1) (z) t (g i)) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t)
    (he : ∀ i j : Fin 5, i≠j → edge4 (1) (1) (z) (profile4 (z + 1) (z) t (g i)) (profile4 (z + 1) (z) t (g j)) (z + 1) (z) t=0) : False := by
  have row (k : Fin 64) (hh : cell (1) (1) (z) (profile4 (z + 1) (z) t k) ((z + 1),(1),(z + 1)) ((z + 1),(z + 1),(1)) (z + 1) (z) t) : limit12 z t k := by
    fin_cases k
    · exact row_12_0 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_1 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_2 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_3 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_4 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_5 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_6 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_7 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_8 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_9 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_10 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_11 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_12 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_13 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_14 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_15 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_16 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_17 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_18 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_19 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_20 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_21 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_22 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_23 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_24 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_25 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_26 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_27 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_28 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_29 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_30 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_31 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_32 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_33 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_34 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_35 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_36 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_37 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_38 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_39 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_40 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_41 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_42 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_43 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_44 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_45 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_46 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_47 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_48 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_49 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_50 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_51 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_52 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_53 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_54 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_55 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_56 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_57 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_58 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_59 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_60 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_61 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_62 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_12_63 z t hf hn0 hn1 hn2 hn3 hh
  have allowed (k : Fin 64) (hh : limit12 z t k) : k∈([5,15,39,45,53]:List (Fin 64)) := by
    fin_cases k <;> first | decide | exact False.elim hh
  have cert : ∀ i j : Fin 64, i∈([5,15,39,45,53]:List (Fin 64)) → j∈([5,15,39,45,53]:List (Fin 64)) → i<j → hue12 i=hue12 j → (i,j)∈([(5,15),(5,39),(5,45),(5,53),(15,39),(15,45),(15,53),(39,45),(39,53),(45,53)]:List (Fin 64×Fin 64)) := by decide
  have bad (i j : Fin 64) (hi : limit12 z t i) (hj : limit12 z t j) (hlt : i<j) (hc : hue12 i=hue12 j) (hb : edge4 (1) (1) (z) (profile4 (z + 1) (z) t i) (profile4 (z + 1) (z) t j) (z + 1) (z) t=0) : False := by
    have h := cert i j (allowed i hi) (allowed j hj) hlt hc
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact rowpair_12_5_15 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_12_5_39 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_12_5_45 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_12_5_53 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_12_15_39 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_12_15_45 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_12_15_53 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_12_39_45 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_12_39_53 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_12_45_53 z t hf hn0 hn1 hn2 hn3 hi hj hb
  have hi : Function.Injective (fun i : Fin 5 => hue12 (g i)) := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne (show g i≠g j from fun e => hne (hinj e)) with hl|hl
    · exact bad _ _ (row _ (hc i)) (row _ (hc j)) hl h (he i j hne)
    · exact bad _ _ (row _ (hc j)) (row _ (hc i)) hl h.symm (he j i (Ne.symm hne))
  have hh := Fintype.card_le_of_injective _ hi
  norm_num at hh

private lemma no_0011201102 (x y t : ℝ) (H : admissible ![0,0,1,1,2,0,1,1,0,2] x y) (E : hasExtension ![0,0,1,1,2,0,1,1,0,2] x y t)
    (t1 : t-1≠0) (tx : t-x≠0) (ty : t-y≠0) (t0 : t≠0) : False := by
  obtain ⟨h0,h1⟩ := shape_0011201102 x y H
  by_cases G0 : y^2 - 5*y + 3=0
  · have ex : x=1 - y := by linear_combination (1)*h0 + (-y/3 - 2/3)*G0
    obtain ⟨u,hu,hc,he⟩ := E
    change ∀ i, cell (1) (1) (y) (profile4 x y t (u i)) ((x),(1),(x)) ((x),(x),(1)) x y t at hc
    change ∀ i j, i≠j → edge4 (1) (1) (y) (profile4 x y t (u i)) (profile4 x y t (u j)) x y t=0 at he
    simp only [ex] at hc he tx ty
    apply exclude_field_11 y t (by linear_combination (1)*G0) t1 tx ty (by simpa using t0) u hu hc he
  by_cases G1 : y^2 - y - 3=0
  · have ex : x=y + 1 := by linear_combination (1)*h0 + (2/3 - y/3)*G1
    obtain ⟨u,hu,hc,he⟩ := E
    change ∀ i, cell (1) (1) (y) (profile4 x y t (u i)) ((x),(1),(x)) ((x),(x),(1)) x y t at hc
    change ∀ i j, i≠j → edge4 (1) (1) (y) (profile4 x y t (u i)) (profile4 x y t (u j)) x y t=0 at he
    simp only [ex] at hc he tx ty
    apply exclude_field_12 y t (by linear_combination (1)*G1) t1 tx ty (by simpa using t0) u hu hc he
  apply (mul_ne_zero G0 G1)
  linear_combination (1)*h1

private lemma no_0011101102 (x y t : ℝ) (H : admissible ![0,0,1,1,1,0,1,1,0,2] x y) (E : hasExtension ![0,0,1,1,1,0,1,1,0,2] x y t)
    (t1 : t-1≠0) (tx : t-x≠0) (ty : t-y≠0) (t0 : t≠0) : False := by
  obtain ⟨h0,h1⟩ := shape_0011101102 x y H
  by_cases G0 : y + 4=0
  · have ex : x=-1 := by linear_combination (1)*h0
    have ey : y=-4 := by linear_combination (1)*G0
    apply H.2.1 0 3 4 (by decide) (by decide)
    change area (x) (x) (y)=0
    simp only [ex,ey,area]
    ring
  apply G0
  linear_combination (1)*h1

end Erdos1082Ten

open Erdos1082Ten EuclideanGeometry

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H2_R1.H1 := by
  intro A hn hA hd M hm B hBA hB hf hthree p r c hc hh
  obtain ⟨x,y,t,H,E,t1,tx,ty,t0⟩ := given_extension A B M hm hBA hA hB hd hthree hn hf p r c hc
  change colorCode c∈([3440,3197]:List ℕ) at hh
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with eq|eq
  · have cc : c=![0,0,1,1,2,0,1,1,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact no_0011201102 x y t H E t1 tx ty t0
  · have cc : c=![0,0,1,1,1,0,1,1,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact no_0011101102 x y t H E t1 tx ty t0
