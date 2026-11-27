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
private lemma base_0011012212 (x y : ℝ) (g0 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (g1 : -x^2 + 2*x*y - 4*x - y^2 + y + (2:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : 4*x - (1:ℝ)≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : 4*x*y - y^2≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 4*x*y≠0) (_n14 : -x^2 + 4*x*y≠0) : (x - 1/(2:ℝ)=0) ∧ (y^2 - 2*y + 1/(4:ℝ)=0) := by
  have h1 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 2*x*y + 4*x + y^2 - y - (2:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : 2*x - (1:ℝ)=0 := by linear_combination (1/3)*h2 + (-1/3)*h3
  have h5 : 4*y^2 - 8*y + (1:ℝ)=0 := by linear_combination (-2*x/3 + 4*y/3 + 1)*h2 + (2*x/3 - 4*y/3 + 3)*h3
  have h6 : x - 1/(2:ℝ)=0 := by linear_combination (1/2)*h4
  have h7 : y^2 - 2*y + 1/(4:ℝ)=0 := by linear_combination (1/4)*h5
  exact ⟨h6, h7⟩



private lemma shape_0011012212 (x y : ℝ) (ha : admissible ![0,0,1,1,0,1,2,2,1,2] x y) : (x - 1/2=0) ∧ (y^2 - 2*y + 1/4=0) := by
  apply base_0011012212 x y
  · have hg : gram 1 1 1 x x y x x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x y x y x y=0 := ha.2.2.2.1
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
  · have hn : area x x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
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
  · have hn : area x y y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring

private lemma base_0011102202 (x y : ℝ) (g0 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : 4*x^3 - 3*x^2*y - 6*x^2 + x*y^2 + 2*x*y + x - 2*y^2 + 4*y - (2:ℝ)=0) (g2 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : 4*x*y - y^2≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 4*y - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : (x + 937*y^5/164738 - 12413*y^4/82369 + 118469*y^3/82369 - 23509*y^2/4018 + 1428039*y/164738 - 611243/(164738:ℝ)=0) ∧ (y^6 - 26*y^5 + 242*y^4 - 965*y^3 + 1577*y^2 - 927*y + (162:ℝ)=0) := by
  have h1 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g0
  have h2 : x^3 - 3*x^2*y/4 - 3*x^2/2 + x*y^2/4 + x*y/2 + x/4 - y^2/2 + y - 1/(2:ℝ)=0 := by linear_combination (1/4)*g1
  have h3 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g2
  have h4 : x + 32469*y^7/5271616 - 909651*y^6/5271616 + 2397341*y^5/1317904 - 47967611*y^4/5271616 + 8710831*y^3/376544 - 41042065*y^2/1317904 + 111635865*y/5271616 - 15081905/(2635808:ℝ)=0 := by linear_combination (-32469*x^2*y^3/658952 + 20358*x^2*y^2/82369 - 680921*x^2*y/658952 + 56033*x^2/329476 + 32469*x*y^4/1317904 - 260271*x*y^3/1317904 + 325319*x*y^2/1317904 + 1754945*x*y/1317904 + 280165*x/658952 + 162345*y^4/1317904 - 115833*y^3/82369 + 8096749*y^2/1317904 - 900057*y/94136 + 939117/164738)*h2 + (32469*x^2*y^3/658952 - 20358*x^2*y^2/82369 + 680921*x^2*y/658952 - 56033*x^2/329476 - 97407*x*y^4/2635808 + 341703*x*y^3/1317904 - 1331559*x*y^2/2635808 - 106182*x*y/82369 - 280165*x/658952 + 32469*y^5/2635808 - 74289*y^4/376544 + 4160813*y^3/2635808 - 7597231*y^2/1317904 + 26106649*y/2635808 - 184609/32144)*h3
  have h5 : y^8 - 28*y^7 + 295*y^6 - 1475*y^5 + 3749*y^4 - 5046*y^3 + 3593*y^2 - 1251*y + (162:ℝ)=0 := by linear_combination (-8*x^2*y^4 + 40*x^2*y^3 - 168*x^2*y^2 + 24*x^2*y - 16*x^2 + 4*x*y^5 - 32*x*y^4 + 40*x*y^3 + 216*x*y^2 + 68*x*y - 40*x + 20*y^5 - 228*y^4 + 996*y^3 - 1548*y^2 + 920*y - 160)*h2 + (8*x^2*y^4 - 40*x^2*y^3 + 168*x^2*y^2 - 24*x^2*y + 16*x^2 - 6*x*y^5 + 42*x*y^4 - 82*x*y^3 - 210*x*y^2 - 72*x*y + 40*x + 2*y^6 - 32*y^5 + 256*y^4 - 934*y^3 + 1606*y^2 - 934*y + 164)*h3
  have h7 : y - (1:ℝ)≠0 := by
    intro he
    apply n3
    linear_combination (1)*he
  have h8 : ((y - 1) * (y - 1))*(y^6 - 26*y^5 + 242*y^4 - 965*y^3 + 1577*y^2 - 927*y + 162)=0 := by linear_combination (1)*h5
  have h6 := (mul_eq_zero.mp h8).resolve_left (mul_ne_zero h7 h7)
  have h9 : x + 937*y^5/164738 - 12413*y^4/82369 + 118469*y^3/82369 - 23509*y^2/4018 + 1428039*y/164738 - 611243/(164738:ℝ)=0 := by linear_combination (1)*h4 + (9351/753088 - 32469*y/5271616)*h6
  exact ⟨h9, h6⟩



private lemma shape_0011102202 (x y : ℝ) (ha : admissible ![0,0,1,1,1,0,2,2,0,2] x y) : (x + 937*y^5/164738 - 12413*y^4/82369 + 118469*y^3/82369 - 23509*y^2/4018 + 1428039*y/164738 - 611243/164738=0) ∧ (y^6 - 26*y^5 + 242*y^4 - 965*y^3 + 1577*y^2 - 927*y + 162=0) := by
  apply base_0011102202 x y
  · have hg : gram 1 1 x x 1 y x 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 y x y 1 y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x y 1 x y 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
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
  · have hn : area x 1 y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring

private lemma cell_8_0 (z t : ℝ) (_hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_8_1 (z t : ℝ) (_hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-5/2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-2/5)*h0
  norm_num at hh

private lemma cell_8_2 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z - 1/2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (8*z/13 - 18/13)*h0 + (4/13)*hf
  norm_num at hh

private lemma cell_8_3 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 112) + t^6*(1584*z + 72) + t^5*(1032 - 7584*z) + t^4*(17712*z - 2916) + t^3*(2988 - 20808*z) + t^2*(11772*z - 1350) + t*(324 - 2592*z):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(10/1053 - 4*z/351) + t^5*(160*z/1053 - 64/1053) + t^4*(50/351 - 320*z/351) + t^3*(994*z/351 - 109/351) + t^2*(115/234 - 485*z/117) + t*(319*z/117 - 107/234) - 25*z/39 - 1/13)*h0 + (z/702 - 5/4212)*h1 + (16*t^7/351 - 22*t^6/39 + 316*t^5/117 - 82*t^4/13 + 289*t^3/39 - 109*t^2/26 + 12*t/13)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_8_4 (z t : ℝ) (_hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-5/2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-2/5)*h0
  norm_num at hh

private lemma cell_8_5 (z t : ℝ) (_hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-3/2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-2/3)*h0
  norm_num at hh

private lemma cell_8_6 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (4*z - 8)*h0 + (1)*hf
  norm_num at hh

private lemma cell_8_7 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 5*t + 1/2:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 80) + t^6*(1360*z - 72) + t^5*(944 - 5520*z) + t^4*(10592*z - 1747) + t^3*(1182 - 9388*z) + t^2*(3120*z - 260) + t*(190*z - 107/4) - 845*z/4 + 435/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(2624/243 - 1408*z/243) + t^6*(25280*z/729 - 46976/729) + t^5*(5488/81 - 9088*z/243) + t^4*(35096/243 - 17840*z/243) + t^3*(74800*z/729 - 149452/729) + t^2*(11036*z/243 - 5954/81) + t*(2678/27 - 13318*z/243) - 3940*z/729 + 13721/1458)*h0 + (t*(176*z/243 - 328/243) - 1264*z/729 + 2356/729)*h1 + (5632*t^8/243 - 219968*t^7/729 + 1158400*t^6/729 - 1047488*t^5/243 + 4586288*t^4/729 - 3378448*t^3/729 + 106760*t^2/81 + 87925*t/729 - 66755/729)*hf
  norm_num at hh

private lemma cell_8_8 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z - 1/2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (8*z/13 - 18/13)*h0 + (4/13)*hf
  norm_num at hh

private lemma cell_8_9 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (4*z - 8)*h0 + (1)*hf
  norm_num at hh

private lemma cell_8_10 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (3/2 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (26/23 - 16*z/23)*h0 + (-16/23)*hf
  norm_num at hh

private lemma cell_8_11 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 3/2:ℝ)=0) (h1 : (16*t^8 + t^7*(-192*z - 48) + t^6*(2400*z - 288) + t^5*(1944 - 13248*z) + t^4*(40932*z - 5625) + t^3*(9828 - 73656*z) + t^2*(75033*z - 20007/2) + t*(20979/4 - 39366*z) + 32319*z/4 - 17253/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(640*z/747 - 10816/6723) + t^6*(127744/20169 - 66112*z/20169) + t^5*(4096/6723 - 8672*z/6723) + t^4*(85264*z/6723 - 110056/6723) + t^3*(14216/2241 - 8696*z/747) + t^2*(14348*z/2241 + 10522/2241) + t*(-920*z/249 - 329/249) - 62*z/249 + 243/166)*h0 + (t*(1352/6723 - 80*z/747) + 3200*z/20169 - 5972/20169)*h1 + (-3520*t^8/747 + 1416544*t^7/20169 - 3028976*t^6/6723 + 10943192*t^5/6723 - 896756*t^4/249 + 11056354*t^3/2241 - 3011900*t^2/747 + 442634*t/249 - 26600/83)*hf
  norm_num at hh

private lemma cell_8_12 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 208) + t^6*(960 - 480*z) + t^5*(1200*z - 1920) + t^4*(1440 - 1008*z) + t^3*(144 - 144*z) + t^2*(432*z - 486) + t*(108 - 108*z):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(10/81 - 4*z/81) + t^5*(16*z/27 - 32/27) + t^4*(94/27 - 52*z/27) + t^3*(2*z - 31/9) + t*(1 - 2*z/3) + z/6 - 5/12)*h0 + (z/162 - 5/324)*h1 + (-8*t^7/81 + 20*t^6/27 - 50*t^5/27 + 14*t^4/9 + 2*t^3/9 - 2*t^2/3 + t/6)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_8_13 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 5*t + 1/2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 176) + t^6*(624 - 320*z) + t^5*(456*z - 748) + t^4*(-4*z - 157) + t^3*(675 - 274*z) + t^2*(-3*z - 205/2) + t*(-z/2 - 97/2) + 103*z/4 + 87/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(256/243 - 128*z/243) + t^6*(1408*z/243 - 896/81) + t^5*(9280/243 - 4960*z/243) + t^4*(1904*z/81 - 10544/243) + t^3*(1816*z/243 - 3560/243) + t^2*(10288/243 - 5428*z/243) + t*(296*z/243 - 74/27) + 145*z/81 - 899/243)*h0 + (t*(16*z/243 - 32/243) - 40*z/243 + 80/243)*h1 + (-256*t^8/243 + 640*t^7/81 - 5024*t^6/243 + 4576*t^5/243 + 352*t^4/81 - 2728*t^3/243 - 28*t^2/243 - 4*t/9 + 515/486)*hf
  norm_num at hh

private lemma cell_8_14 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 3/2:ℝ)=0) (h1 : (16*t^8 - 144*t^7 + t^6*(408 - 48*z) + t^5*(360*z - 324) + t^4*(-648*z - 279) + t^3*(459 - 270*z) + t^2*(918*z - 108) + t*(405*z/2 - 81) - 243*z/4 + 243/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(5824/4779 - 8704*z/14337) + t^6*(72448*z/14337 - 145984/14337) + t^5*(116176/4779 - 58304*z/4779) + t^4*(24400*z/4779 - 35104/4779) + t^3*(18848*z/1593 - 47108/1593) + t^2*(2716/177 - 4876*z/531) + t*(256*z/531 + 3866/531) + 121*z/59 - 107/177)*h0 + (t*(1088*z/14337 - 728/4779) - 1432*z/14337 + 3232/14337)*h1 + (-4352*t^8/14337 + 49280*t^7/14337 - 67520*t^6/4779 + 113912*t^5/4779 - 8192*t^4/1593 - 15266*t^3/531 + 1140*t^2/59 + 2561*t/354 - 179/118)*hf
  norm_num at hh

private lemma cell_8_15 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 144) + t^6*(704*z + 368) + t^5*(-2832*z - 16) + t^4*(5152*z - 1032) + t^3*(1048 - 4016*z) + t^2*(624*z - 86) + t*(572*z - 132) - 184*z + 32:ℝ)=0) : (t - 2*z:ℝ)=0 := by
  have hh : (t - 2*z:ℝ)=0 := by linear_combination (t^6*(8/243 - 56*z/243) + t^5*(232*z/81 - 32/81) + t^4*(136/81 - 112*z/9) + t^3*(5672*z/243 - 758/243) + t^2*(184/81 - 1388*z/81) + t*(4*z/9 - 8/81) + 841*z/243 - 145/243)*h0 + (7*z/243 - 1/243)*h1 + (112*t^7/243 - 1232*t^6/243 + 1652*t^5/81 - 9016*t^4/243 + 7028*t^3/243 - 364*t^2/81 - 1001*t/243 + 322/243)*hf
  exact hh

private lemma cell_8_16 (z t : ℝ) (_hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-5/2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-2/5)*h0
  norm_num at hh

private lemma cell_8_17 (z t : ℝ) (_hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-3/2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-2/3)*h0
  norm_num at hh

private lemma cell_8_18 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (4*z - 8)*h0 + (1)*hf
  norm_num at hh

private lemma cell_8_19 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 5*t + 1/2:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 80) + t^6*(1360*z - 72) + t^5*(944 - 5520*z) + t^4*(10592*z - 1747) + t^3*(1182 - 9388*z) + t^2*(3120*z - 260) + t*(190*z - 107/4) - 845*z/4 + 435/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(2624/243 - 1408*z/243) + t^6*(25280*z/729 - 46976/729) + t^5*(5488/81 - 9088*z/243) + t^4*(35096/243 - 17840*z/243) + t^3*(74800*z/729 - 149452/729) + t^2*(11036*z/243 - 5954/81) + t*(2678/27 - 13318*z/243) - 3940*z/729 + 13721/1458)*h0 + (t*(176*z/243 - 328/243) - 1264*z/729 + 2356/729)*h1 + (5632*t^8/243 - 219968*t^7/729 + 1158400*t^6/729 - 1047488*t^5/243 + 4586288*t^4/729 - 3378448*t^3/729 + 106760*t^2/81 + 87925*t/729 - 66755/729)*hf
  norm_num at hh

private lemma cell_8_20 (z t : ℝ) (_hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-3/2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-2/3)*h0
  norm_num at hh

private lemma cell_8_21 (z t : ℝ) (_hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-1:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1)*h0
  norm_num at hh

private lemma cell_8_22 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h1 : (648*t*z:ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (1/81 - z/162)*h1 + (t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_8_23 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 4*t + 1/2:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 48) + t^6*(1136*z - 184) + t^5*(772 - 3648*z) + t^4*(4780*z - 684) + t^3*(-1456*z - 133) + t^2*(395/2 - 1023*z) + t*(586*z + 39/4) - 259*z/4 + 131/16:ℝ)=0) : (t + z - 2:ℝ)=0 := by
  have hh : (t + z - 2:ℝ)=0 := by linear_combination (t^6*(104/81 - 56*z/81) + t^5*(40*z/27 - 8/3) + t^4*(110*z/27 - 220/27) + t^3*(560/81 - 248*z/81) + t^2*(227/18 - 383*z/54) + t*(71*z/54 - 157/54) + 1415*z/648 - 1351/324)*h0 + (7*z/81 - 13/81)*h1 + (224*t^7/81 - 1988*t^6/81 + 2128*t^5/27 - 8365*t^4/81 + 2548*t^3/81 + 2387*t^2/108 - 2051*t/162 + 1813/1296)*hf
  exact hh

private lemma cell_8_24 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (4*z - 8)*h0 + (1)*hf
  norm_num at hh

private lemma cell_8_25 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h2 : (648*t*z:ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (1/81 - z/162)*h2 + (t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_8_26 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (1 - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3/2 - z)*h0 + (-1/2)*hf
  norm_num at hh

private lemma cell_8_27 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 3) + z + 1:ℝ)=0) (h2 : (16*t^8 - 112*t^7 + t^6*(184 - 48*z) + t^5*(288*z + 140) + t^4*(-252*z - 440) + t^3*(71 - 744*z) + t^2*(639*z + 329/2) + t*(612*z - 259/4) - 165*z/4 + 55/16:ℝ)=0) : (t - z - 1:ℝ)=0 := by
  have hh : (t - z - 1:ℝ)=0 := by linear_combination (t^6*(10/81 - 4*z/81) + t^5*(8*z/27 - 2/3) + t^4*(13/54 - 7*z/27) + t^3*(170/81 - 62*z/81) + t^2*(71*z/108 - 29/72) + t*(17*z/27 - 419/216) - 55*z/1296 - 2647/2592)*h0 + (z/162 - 5/324)*h2 + (-2*t^7/81 + 19*t^6/81 - 35*t^5/54 + 23*t^4/324 + 1081*t^3/648 - 361*t^2/432 - 2911*t/2592 + 385/5184)*hf
  exact hh

private lemma cell_8_28 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 5*t + 1/2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 176) + t^6*(672 - 416*z) + t^5*(816*z - 1072) + t^4*(527 - 220*z) + t^3*(330 - 700*z) + t^2*(249*z - 691/2) + t*(283*z + 85/4) - 245*z/4 + 171/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(448/729 - 256*z/729) + t^6*(2624*z/729 - 4736/729) + t^5*(5840/243 - 3104*z/243) + t^4*(13696*z/729 - 26920/729) + t^3*(12548/729 - 6728*z/729) + t^2*(2654/243 - 872*z/243) + t*(4394*z/729 - 8630/729) - 1549*z/729 + 1979/1458)*h0 + (t*(32*z/729 - 56/729) - 88*z/729 + 148/729)*h1 + (-512*t^8/729 + 4736*t^7/729 - 15680*t^6/729 + 19712*t^5/729 + 760*t^4/729 - 17392*t^3/729 + 3214*t^2/729 + 6716*t/729 - 2695/1458)*hf
  norm_num at hh

private lemma cell_8_29 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 4*t + 1/2:ℝ)=0) (h2 : (16*t^8 + t^7*(-128*z - 48) + t^6*(1136*z - 184) + t^5*(772 - 3648*z) + t^4*(4780*z - 684) + t^3*(-1456*z - 133) + t^2*(395/2 - 1023*z) + t*(586*z + 39/4) - 259*z/4 + 131/16:ℝ)=0) : (t + z - 2:ℝ)=0 := by
  have hh : (t + z - 2:ℝ)=0 := by linear_combination (t^6*(104/81 - 56*z/81) + t^5*(40*z/27 - 8/3) + t^4*(110*z/27 - 220/27) + t^3*(560/81 - 248*z/81) + t^2*(227/18 - 383*z/54) + t*(71*z/54 - 157/54) + 1415*z/648 - 1351/324)*h0 + (7*z/81 - 13/81)*h2 + (224*t^7/81 - 1988*t^6/81 + 2128*t^5/27 - 8365*t^4/81 + 2548*t^3/81 + 2387*t^2/108 - 2051*t/162 + 1813/1296)*hf
  exact hh

private lemma cell_8_30 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 3) + z + 1:ℝ)=0) (h1 : (16*t^8 - 112*t^7 + t^6*(184 - 48*z) + t^5*(288*z + 140) + t^4*(-252*z - 440) + t^3*(71 - 744*z) + t^2*(639*z + 329/2) + t*(612*z - 259/4) - 165*z/4 + 55/16:ℝ)=0) : (t - z - 1:ℝ)=0 := by
  have hh : (t - z - 1:ℝ)=0 := by linear_combination (t^6*(10/81 - 4*z/81) + t^5*(8*z/27 - 2/3) + t^4*(13/54 - 7*z/27) + t^3*(170/81 - 62*z/81) + t^2*(71*z/108 - 29/72) + t*(17*z/27 - 419/216) - 55*z/1296 - 2647/2592)*h0 + (z/162 - 5/324)*h1 + (-2*t^7/81 + 19*t^6/81 - 35*t^5/54 + 23*t^4/324 + 1081*t^3/648 - 361*t^2/432 - 2911*t/2592 + 385/5184)*hf
  exact hh

private lemma cell_8_31 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t + 3/2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 80) + 480*t^6*z + t^5*(408 - 1128*z) + t^4*(684*z - 360) + t^3*(684*z - 279) + t^2*(270 - 810*z) + t*(297*z/2 + 27/2) + 81*z/4 - 81/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(20/81 - 8*z/81) + t^6*(20*z/81 - 34/27) + t^5*(142*z/81 + 29/81) + t^4*(85/18 - 55*z/9) + t^3*(19*z/6 - 13/4) + t^2*(179*z/36 - 301/72) + t*(259/144 - 239*z/72) - 19*z/48 + 27/32)*h0 + (t*(z/81 - 5/162) - 5*z/162 + 1/12)*h1 + (16*t^8/81 - 160*t^7/81 + 194*t^6/27 - 292*t^5/27 + 19*t^4/6 + 70*t^3/9 - 161*t^2/24 + 13*t/12 + 5/32)*hf
  norm_num at hh

private lemma cell_8_32 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z - 1/2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (8*z/13 - 18/13)*h0 + (4/13)*hf
  norm_num at hh

private lemma cell_8_33 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (4*z - 8)*h0 + (1)*hf
  norm_num at hh

private lemma cell_8_34 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (3/2 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (26/23 - 16*z/23)*h0 + (-16/23)*hf
  norm_num at hh

private lemma cell_8_35 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 3/2:ℝ)=0) (h1 : (16*t^8 + t^7*(-192*z - 48) + t^6*(2400*z - 288) + t^5*(1944 - 13248*z) + t^4*(40932*z - 5625) + t^3*(9828 - 73656*z) + t^2*(75033*z - 20007/2) + t*(20979/4 - 39366*z) + 32319*z/4 - 17253/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(640*z/747 - 10816/6723) + t^6*(127744/20169 - 66112*z/20169) + t^5*(4096/6723 - 8672*z/6723) + t^4*(85264*z/6723 - 110056/6723) + t^3*(14216/2241 - 8696*z/747) + t^2*(14348*z/2241 + 10522/2241) + t*(-920*z/249 - 329/249) - 62*z/249 + 243/166)*h0 + (t*(1352/6723 - 80*z/747) + 3200*z/20169 - 5972/20169)*h1 + (-3520*t^8/747 + 1416544*t^7/20169 - 3028976*t^6/6723 + 10943192*t^5/6723 - 896756*t^4/249 + 11056354*t^3/2241 - 3011900*t^2/747 + 442634*t/249 - 26600/83)*hf
  norm_num at hh

private lemma cell_8_36 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (4*z - 8)*h0 + (1)*hf
  norm_num at hh

private lemma cell_8_37 (z t : ℝ) (_hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) : ((0:ℝ):ℝ)=0 := by
  rfl

private lemma cell_8_38 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (1 - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3/2 - z)*h0 + (-1/2)*hf
  norm_num at hh

private lemma cell_8_39 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 3) + z + 1:ℝ)=0) (h2 : (16*t^8 - 112*t^7 + t^6*(144*z + 184) + t^5*(140 - 720*z) + t^4*(1548*z - 548) + t^3*(395 - 1872*z) + t^2*(1683*z - 319/2) + t*(281/4 - 855*z) + 657*z/4 - 269/16:ℝ)=0) : False := by
  have hh : ((t-(1/2)))*(1:ℝ)=0 := by linear_combination (t^6*(52/243 - 28*z/243) + t^5*(50*z/81 - 31/27) + t^4*(13/18 - 32*z/81) + t^3*(1171/486 - 311*z/243) + t^2*(167*z/324 - 55/54) + t*(377*z/648 - 479/432) + 157*z/1944 - 2629/7776)*h0 + (7*z/486 - 13/486)*h2 + (-14*t^7/243 - 44*t^6/243 + 121*t^5/54 - 1486*t^4/243 + 14227*t^3/1944 - 637*t^2/108 + 23123*t/7776 - 1189/1944)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_8_40 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (3/2 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (26/23 - 16*z/23)*h0 + (-16/23)*hf
  norm_num at hh

private lemma cell_8_41 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (1 - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3/2 - z)*h0 + (-1/2)*hf
  norm_num at hh

private lemma cell_8_42 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 6*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (10/11 - 6*z/11)*h0 + (-9/11)*hf
  norm_num at hh

private lemma cell_8_43 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 3/2:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 256*z) + t^6*(3216*z - 552) + t^5*(2748 - 19776*z) + t^4*(71172*z - 9288) + t^3*(20151 - 151560*z) + t^2*(185355*z - 49923/2) + t*(64233/4 - 119394*z) + 124659*z/4 - 66825/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(832*z/14337 - 1448/14337) + t^6*(1592/14337 - 2216*z/14337) + t^5*(2504*z/4779 + 3362/4779) + t^4*(724/4779 - 20830*z/4779) + t^3*(20576*z/1593 - 11699/3186) + t^2*(8179/3186 - 53059*z/3186) + t*(11509*z/1062 + 839/4248) - 5459*z/1416 + 415/354)*h0 + (t*(181/14337 - 104*z/14337) + 107*z/14337 - 197/14337)*h1 + (-5824*t^8/14337 + 29416*t^7/4779 - 197564*t^6/4779 + 772330*t^5/4779 - 23289*t^4/59 + 639607*t^3/1062 - 390475*t^2/708 + 390005*t/1416 - 54891/944)*hf
  norm_num at hh

private lemma cell_8_44 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 3/2:ℝ)=0) (h1 : (16*t^8 - 144*t^7 + t^6*(48*z + 456) + t^5*(-288*z - 648) + t^4*(648*z + 369) + t^3*(108 - 648*z) + t^2*(162*z - 243) + t*(243*z + 243/4) - 729*z/4 + 243/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(70016*z/11583 - 392320/34749) + t^6*(3349376/34749 - 1793216*z/34749) + t^5*(1748192*z/11583 - 362896/1287) + t^4*(4121192/11583 - 2204192*z/11583) + t^3*(330280*z/3861 - 619708/3861) + t^2*(4640*z/99 - 8606/99) + t*(149495/1287 - 80072*z/1287) + 3083*z/429 - 11813/858)*h0 + (t*(49040/34749 - 8752*z/11583) + 43832*z/34749 - 81956/34749)*h1 + (35008*t^8/11583 - 581536*t^7/34749 + 68624*t^6/11583 + 124336*t^5/1053 - 1096444*t^4/3861 + 332536*t^3/1287 - 46708*t^2/1287 - 92203*t/858 + 16437/286)*hf
  norm_num at hh

private lemma cell_8_45 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 3) + z + 1:ℝ)=0) (h1 : (16*t^8 - 112*t^7 + t^6*(144*z + 184) + t^5*(140 - 720*z) + t^4*(1548*z - 548) + t^3*(395 - 1872*z) + t^2*(1683*z - 319/2) + t*(281/4 - 855*z) + 657*z/4 - 269/16:ℝ)=0) : False := by
  have hh : ((t-(1/2)))*(1:ℝ)=0 := by linear_combination (t^6*(52/243 - 28*z/243) + t^5*(50*z/81 - 31/27) + t^4*(13/18 - 32*z/81) + t^3*(1171/486 - 311*z/243) + t^2*(167*z/324 - 55/54) + t*(377*z/648 - 479/432) + 157*z/1944 - 2629/7776)*h0 + (7*z/486 - 13/486)*h1 + (-14*t^7/243 - 44*t^6/243 + 121*t^5/54 - 1486*t^4/243 + 14227*t^3/1944 - 637*t^2/108 + 23123*t/7776 - 1189/1944)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_8_46 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 3/2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 80) + 480*t^6*z + t^5*(408 - 1128*z) + t^4*(684*z - 360) + t^3*(684*z - 279) + t^2*(270 - 810*z) + t*(297*z/2 + 27/2) + 81*z/4 - 81/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(104*z/2673 - 100/2673) + t^6*(130/891 - 92*z/297) + t^5*(866*z/891 + 71/891) + t^4*(-505*z/297 - 139/594) + t^3*(83*z/66 - 119/132) + t^2*(1423*z/1188 + 445/2376) + t*(2081/1584 - 515*z/264) - 45*z/176 + 249/352)*h0 + (t*(25/5346 - 13*z/2673) + 49*z/5346 + 31/10692)*h1 + (-104*t^8/2673 + 1124*t^7/2673 - 1336*t^6/891 + 139*t^5/81 + 155*t^4/297 - 1609*t^3/1188 + 17*t^2/198 - 905*t/1584 - 49/1056)*hf
  norm_num at hh

private lemma cell_8_47 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 2*z + 3/2:ℝ)=0) (h1 : (16*t^8 + t^7*(-192*z - 16) + t^6*(2112*z - 368) + t^5*(1616 - 10584*z) + t^4*(30684*z - 3992) + t^3*(6869 - 53052*z) + t^2*(52488*z - 7067) + t*(3638 - 53457*z/2) + 21021*z/4 - 11297/16:ℝ)=0) : False := by
  have hh : ((t-(1/2)))*(1:ℝ)=0 := by linear_combination (t^6*(38/243 - 20*z/243) - 4*t^5/81 + t^4*(7*z/9 - 181/162) + t^3*(-94*z/243 - 98/243) + t^2*(65*z/108 + 559/648) + t*(175/324 - 67*z/54) + 1831*z/3888 - 2849/7776)*h0 + (5*z/486 - 19/972)*h1 + (100*t^7/243 - 1310*t^6/243 + 28*t^5 - 19366*t^4/243 + 133403*t^3/972 - 3277*t^2/24 + 33941*t/486 - 13367/972)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_8_48 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 208) + t^6*(960 - 480*z) + t^5*(1200*z - 1920) + t^4*(1440 - 1008*z) + t^3*(144 - 144*z) + t^2*(432*z - 486) + t*(108 - 108*z):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(10/81 - 4*z/81) + t^5*(16*z/27 - 32/27) + t^4*(94/27 - 52*z/27) + t^3*(2*z - 31/9) + t*(1 - 2*z/3) + z/6 - 5/12)*h0 + (z/162 - 5/324)*h1 + (-8*t^7/81 + 20*t^6/27 - 50*t^5/27 + 14*t^4/9 + 2*t^3/9 - 2*t^2/3 + t/6)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_8_49 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 5*t + 1/2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 176) + t^6*(624 - 320*z) + t^5*(456*z - 748) + t^4*(-4*z - 157) + t^3*(675 - 274*z) + t^2*(-3*z - 205/2) + t*(-z/2 - 97/2) + 103*z/4 + 87/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(256/243 - 128*z/243) + t^6*(1408*z/243 - 896/81) + t^5*(9280/243 - 4960*z/243) + t^4*(1904*z/81 - 10544/243) + t^3*(1816*z/243 - 3560/243) + t^2*(10288/243 - 5428*z/243) + t*(296*z/243 - 74/27) + 145*z/81 - 899/243)*h0 + (t*(16*z/243 - 32/243) - 40*z/243 + 80/243)*h1 + (-256*t^8/243 + 640*t^7/81 - 5024*t^6/243 + 4576*t^5/243 + 352*t^4/81 - 2728*t^3/243 - 28*t^2/243 - 4*t/9 + 515/486)*hf
  norm_num at hh

private lemma cell_8_50 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 3/2:ℝ)=0) (h1 : (16*t^8 - 144*t^7 + t^6*(408 - 48*z) + t^5*(360*z - 324) + t^4*(-648*z - 279) + t^3*(459 - 270*z) + t^2*(918*z - 108) + t*(405*z/2 - 81) - 243*z/4 + 243/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(5824/4779 - 8704*z/14337) + t^6*(72448*z/14337 - 145984/14337) + t^5*(116176/4779 - 58304*z/4779) + t^4*(24400*z/4779 - 35104/4779) + t^3*(18848*z/1593 - 47108/1593) + t^2*(2716/177 - 4876*z/531) + t*(256*z/531 + 3866/531) + 121*z/59 - 107/177)*h0 + (t*(1088*z/14337 - 728/4779) - 1432*z/14337 + 3232/14337)*h1 + (-4352*t^8/14337 + 49280*t^7/14337 - 67520*t^6/4779 + 113912*t^5/4779 - 8192*t^4/1593 - 15266*t^3/531 + 1140*t^2/59 + 2561*t/354 - 179/118)*hf
  norm_num at hh

private lemma cell_8_51 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 144) + t^6*(704*z + 368) + t^5*(-2832*z - 16) + t^4*(5152*z - 1032) + t^3*(1048 - 4016*z) + t^2*(624*z - 86) + t*(572*z - 132) - 184*z + 32:ℝ)=0) (h2 : (16*t^8 + t^7*(128*z - 240) + t^6*(1256 - 784*z) + t^5*(1632*z - 2968) + t^4*(3132 - 1232*z) + t^3*(280*z - 1028) + t^2*(-420*z - 230) + t*(368*z + 132) - 16*z - 16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(1504*z/216513 - 2800/216513) + t^12*(53744/216513 - 28832*z/216513) + t^11*(74848*z/72171 - 139648/72171) + t^10*(1697120/216513 - 909152*z/216513) + t^9*(1983592*z/216513 - 3703204/216513) + t^8*(404912/24057 - 217040*z/24057) + t^7*(244522/72171 - 129628*z/72171) + t^6*(88444*z/6561 - 165286/6561) + t^5*(1074824/24057 - 581684*z/24057) + t^4*(11575750*z/216513 - 20841691/216513) + t^3*(4418885/39366 - 1276705*z/19683) + t^2*(116579*z/6561 - 332851/13122) + t*(2135392*z/216513 - 8233817/433026) - 671060*z/216513 + 1824187/433026)*h0 + (t^7*(350/216513 - 188*z/216513) + t^6*(2560*z/216513 - 4780/216513) + t^5*(724/6561 - 388*z/6561) + t^4*(28790*z/216513 - 53729/216513) + t^3*(100997/433026 - 27097*z/216513) + t^2*(1411*z/72171 - 5411/144342) + t*(4084*z/216513 - 16763/433026) - 2576*z/216513 + 3853/433026)*h1 + (469/1188 - 377*z/1782)*h2 + (-3008*t^14/216513 + 74048*t^13/216513 - 788528*t^12/216513 + 4768768*t^11/216513 - 18051856*t^10/216513 + 44311240*t^9/216513 - 23391184*t^8/72171 + 23043844*t^7/72171 - 13611010*t^6/72171 + 15375754*t^5/216513 - 2151007*t^4/216513 - 1868804*t^3/216513 - 9594031*t^2/433026 + 4770338*t/216513 - 301718/216513)*hf
  norm_num at hh

private lemma cell_8_52 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 5*t + 1/2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 176) + t^6*(672 - 416*z) + t^5*(816*z - 1072) + t^4*(527 - 220*z) + t^3*(330 - 700*z) + t^2*(249*z - 691/2) + t*(283*z + 85/4) - 245*z/4 + 171/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(448/729 - 256*z/729) + t^6*(2624*z/729 - 4736/729) + t^5*(5840/243 - 3104*z/243) + t^4*(13696*z/729 - 26920/729) + t^3*(12548/729 - 6728*z/729) + t^2*(2654/243 - 872*z/243) + t*(4394*z/729 - 8630/729) - 1549*z/729 + 1979/1458)*h0 + (t*(32*z/729 - 56/729) - 88*z/729 + 148/729)*h1 + (-512*t^8/729 + 4736*t^7/729 - 15680*t^6/729 + 19712*t^5/729 + 760*t^4/729 - 17392*t^3/729 + 3214*t^2/729 + 6716*t/729 - 2695/1458)*hf
  norm_num at hh

private lemma cell_8_53 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 4*t + 1/2:ℝ)=0) : (t + z - 2:ℝ)=0 := by
  have hh : ((t-(z)))*(t + z - 2:ℝ)=0 := by linear_combination (1/2)*h0 + (-1/4)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  exact hv

private lemma cell_8_54 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 3) + z + 1:ℝ)=0) (h1 : (16*t^8 - 112*t^7 + t^6*(184 - 48*z) + t^5*(288*z + 140) + t^4*(-252*z - 440) + t^3*(71 - 744*z) + t^2*(639*z + 329/2) + t*(612*z - 259/4) - 165*z/4 + 55/16:ℝ)=0) (h2 : (16*t^8 - 112*t^7 + t^6*(144*z + 184) + t^5*(140 - 720*z) + t^4*(1548*z - 548) + t^3*(395 - 1872*z) + t^2*(1683*z - 319/2) + t*(281/4 - 855*z) + 657*z/4 - 269/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(1552/19683 - 832*z/19683) + t^12*(9344*z/19683 - 17432/19683) + t^11*(6776/2187 - 3632*z/2187) + t^10*(13448*z/19683 - 25076/19683) + t^9*(128168*z/19683 - 239153/19683) + t^8*(6643/486 - 5342*z/729) + t^7*(118691/6561 - 63566*z/6561) + t^6*(72085*z/6561 - 269105/13122) + t^5*(26473*z/2916 - 197267/11664) + t^4*(5061923/629856 - 338905*z/78732) + t^3*(5206151/629856 - 1444507*z/314928) + t^2*(157835/139968 - 48823*z/69984) + t*(7213201/5038848 - 42415*z/78732) - 1035293*z/2519424 + 11536253/10077696)*h0 + (t^7*(104*z/19683 - 194/19683) + t^6*(1138/19683 - 610*z/19683) + t^5*(70*z/2187 - 29/486) + t^4*(1991*z/39366 - 3719/39366) + t^3*(16165/157464 - 2161*z/39366) + t^2*(161/5832 - 259*z/17496) + t*(841*z/157464 - 5911/629856) - 5147*z/629856 + 10451/629856)*h1 + (11*z/486 - 41/972)*h2 + (-416*t^14/19683 + 6128*t^13/19683 - 33488*t^12/19683 + 72928*t^11/19683 + 8222*t^10/19683 - 279185*t^9/19683 + 92147*t^8/6561 + 96298*t^7/6561 - 1256789*t^6/52488 - 256691*t^5/314928 + 562913*t^4/314928 + 843703*t^3/78732 - 23386531*t^2/2519424 + 30598565*t/5038848 - 4590077/5038848)*hf
  norm_num at hh

private lemma cell_8_55 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t + 3/2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 80) + 480*t^6*z + t^5*(408 - 1128*z) + t^4*(684*z - 360) + t^3*(684*z - 279) + t^2*(270 - 810*z) + t*(297*z/2 + 27/2) + 81*z/4 - 81/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(20/81 - 8*z/81) + t^6*(20*z/81 - 34/27) + t^5*(142*z/81 + 29/81) + t^4*(85/18 - 55*z/9) + t^3*(19*z/6 - 13/4) + t^2*(179*z/36 - 301/72) + t*(259/144 - 239*z/72) - 19*z/48 + 27/32)*h0 + (t*(z/81 - 5/162) - 5*z/162 + 1/12)*h1 + (16*t^8/81 - 160*t^7/81 + 194*t^6/27 - 292*t^5/27 + 19*t^4/6 + 70*t^3/9 - 161*t^2/24 + 13*t/12 + 5/32)*hf
  norm_num at hh

private lemma cell_8_56 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 3/2:ℝ)=0) (h1 : (16*t^8 - 144*t^7 + t^6*(48*z + 456) + t^5*(-288*z - 648) + t^4*(648*z + 369) + t^3*(108 - 648*z) + t^2*(162*z - 243) + t*(243*z + 243/4) - 729*z/4 + 243/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(70016*z/11583 - 392320/34749) + t^6*(3349376/34749 - 1793216*z/34749) + t^5*(1748192*z/11583 - 362896/1287) + t^4*(4121192/11583 - 2204192*z/11583) + t^3*(330280*z/3861 - 619708/3861) + t^2*(4640*z/99 - 8606/99) + t*(149495/1287 - 80072*z/1287) + 3083*z/429 - 11813/858)*h0 + (t*(49040/34749 - 8752*z/11583) + 43832*z/34749 - 81956/34749)*h1 + (35008*t^8/11583 - 581536*t^7/34749 + 68624*t^6/11583 + 124336*t^5/1053 - 1096444*t^4/3861 + 332536*t^3/1287 - 46708*t^2/1287 - 92203*t/858 + 16437/286)*hf
  norm_num at hh

private lemma cell_8_57 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 3) + z + 1:ℝ)=0) (h1 : (16*t^8 - 112*t^7 + t^6*(144*z + 184) + t^5*(140 - 720*z) + t^4*(1548*z - 548) + t^3*(395 - 1872*z) + t^2*(1683*z - 319/2) + t*(281/4 - 855*z) + 657*z/4 - 269/16:ℝ)=0) (h2 : (16*t^8 - 112*t^7 + t^6*(184 - 48*z) + t^5*(288*z + 140) + t^4*(-252*z - 440) + t^3*(71 - 744*z) + t^2*(639*z + 329/2) + t*(612*z - 259/4) - 165*z/4 + 55/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(832*z/19683 - 1552/19683) + t^12*(18416/19683 - 9872*z/19683) + t^11*(12784*z/6561 - 23848/6561) + t^10*(58460/19683 - 31352*z/19683) + t^9*(239945/19683 - 128576*z/19683) + t^8*(25033*z/2187 - 46696/2187) + t^7*(46562*z/6561 - 87035/6561) + t^6*(453071/13122 - 121351*z/6561) + t^5*(357833/34992 - 47711*z/8748) + t^4*(3658441*z/314928 - 6808117/314928) + t^3*(1594621*z/314928 - 6096335/629856) + t^2*(1796357/419904 - 520333*z/209952) + t*(17680199/5038848 - 1108435*z/629856) - 772913*z/5038848 + 1780207/2519424)*h0 + (t^7*(194/19683 - 104*z/19683) + t^6*(676*z/19683 - 1261/19683) + t^5*(1015/13122 - 272*z/6561) + t^4*(11707/78732 - 1570*z/19683) + t^3*(4591*z/39366 - 34249/157464) + t^2*(1783*z/26244 - 13273/104976) + t*(57235/629856 - 3839*z/78732) - 1189*z/39366 + 70637/1259712)*h1 + (2/81 - z/81)*h2 + (416*t^14/19683 - 1400*t^13/19683 - 21412*t^12/19683 + 166040*t^11/19683 - 457094*t^10/19683 + 910945*t^9/39366 + 396817*t^8/26244 - 357571*t^7/6561 + 2395325*t^6/52488 - 7008197*t^5/629856 - 15951899*t^4/1259712 + 7125199*t^3/629856 + 3043039*t^2/2519424 - 22187821*t/10077696 + 23204369/20155392)*hf
  norm_num at hh

private lemma cell_8_58 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 3/2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 80) + 480*t^6*z + t^5*(408 - 1128*z) + t^4*(684*z - 360) + t^3*(684*z - 279) + t^2*(270 - 810*z) + t*(297*z/2 + 27/2) + 81*z/4 - 81/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(104*z/2673 - 100/2673) + t^6*(130/891 - 92*z/297) + t^5*(866*z/891 + 71/891) + t^4*(-505*z/297 - 139/594) + t^3*(83*z/66 - 119/132) + t^2*(1423*z/1188 + 445/2376) + t*(2081/1584 - 515*z/264) - 45*z/176 + 249/352)*h0 + (t*(25/5346 - 13*z/2673) + 49*z/5346 + 31/10692)*h1 + (-104*t^8/2673 + 1124*t^7/2673 - 1336*t^6/891 + 139*t^5/81 + 155*t^4/297 - 1609*t^3/1188 + 17*t^2/198 - 905*t/1584 - 49/1056)*hf
  norm_num at hh

private lemma cell_8_59 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 2*z + 3/2:ℝ)=0) (h1 : (16*t^8 + t^7*(-192*z - 16) + t^6*(2112*z - 368) + t^5*(1616 - 10584*z) + t^4*(30684*z - 3992) + t^3*(6869 - 53052*z) + t^2*(52488*z - 7067) + t*(3638 - 53457*z/2) + 21021*z/4 - 11297/16:ℝ)=0) (h2 : (16*t^8 - 112*t^7 + t^6*(184 - 48*z) + t^5*(288*z + 140) + t^4*(-252*z - 440) + t^3*(71 - 744*z) + t^2*(639*z + 329/2) + t*(612*z - 259/4) - 165*z/4 + 55/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(608*z/19683 - 1136/19683) + t^12*(7768/19683 - 4144*z/19683) + t^11*(560*z/6561 - 1160/6561) + t^10*(34232*z/19683 - 62156/19683) + t^9*(62863/19683 - 35902*z/19683) + t^8*(44081/4374 - 11761*z/2187) + t^7*(34762*z/6561 - 58183/6561) + t^6*(51055*z/6561 - 219455/13122) + t^5*(294655/34992 - 72515*z/17496) + t^4*(8564045/629856 - 1738165*z/314928) + t^3*(-104359*z/314928 - 1830499/629856) + t^2*(390277*z/209952 - 2070449/419904) + t*(4745383*z/2519424 - 27839/5038848) - 5193487*z/5038848 + 7798703/10077696)*h0 + (t^7*(142/19683 - 76*z/19683) + t^6*(494*z/19683 - 923/19683) + t^5*(743/13122 - 199*z/6561) + t^4*(8567/78732 - 2287*z/39366) + t^3*(6703*z/78732 - 25067/157464) + t^2*(2575*z/52488 - 9707/104976) + t*(41879/629856 - 11167*z/314928) - 13565*z/629856 + 51613/1259712)*h1 + (2/81 - z/81)*h2 + (-3040*t^14/19683 + 59392*t^13/19683 - 486832*t^12/19683 + 2183840*t^11/19683 - 5745938*t^10/19683 + 8176736*t^9/19683 - 696146*t^8/6561 - 4594012*t^7/6561 + 62402453*t^6/52488 - 11856898*t^5/19683 - 95095835*t^4/314928 + 62252197*t^3/157464 - 39969239*t^2/2519424 - 7669121*t/78732 + 36132539/1259712)*hf
  norm_num at hh

private lemma cell_8_60 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(128*z - 240) + t^6*(1256 - 784*z) + t^5*(1632*z - 2968) + t^4*(3132 - 1232*z) + t^3*(280*z - 1028) + t^2*(-420*z - 230) + t*(368*z + 132) - 16*z - 16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(7300/8019 - 3808*z/8019) + t^6*(53564*z/8019 - 99914/8019) + t^5*(15136/243 - 8152*z/243) + t^4*(601816*z/8019 - 1122736/8019) + t^3*(1054202/8019 - 559490*z/8019) + t^2*(29695*z/2673 - 113111/5346) + t*(86873*z/8019 - 350821/16038) - 15382*z/8019 + 69581/16038)*h0 + (t*(476*z/8019 - 1825/16038) - 3551*z/16038 + 13615/32076)*h1 + (-15232*t^8/8019 + 150112*t^7/8019 - 542206*t^6/8019 + 871012*t^5/8019 - 580174*t^4/8019 + 174265*t^3/8019 - 460439*t^2/16038 + 165250*t/8019 - 7102/8019)*hf
  norm_num at hh

private lemma cell_8_61 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t + 3/2:ℝ)=0) (h1 : (16*t^8 + t^7*(128*z - 176) + t^6*(552 - 336*z) + t^5*(96*z - 492) + t^4*(396*z - 396) + t^3*(603 - 144*z) + t^2*(135/2 - 459*z) + t*(324*z - 405/4) - 243*z/4 + 243/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(704/243 - 416*z/243) + t^6*(1144*z/81 - 2236/81) + t^5*(6728/81 - 3560*z/81) + t^4*(334*z/9 - 1705/27) + t^3*(1066*z/27 - 2116/27) + t^2*(2995/36 - 875*z/18) + t*(137/6 - 11*z/2) - 11*z/8 - 163/48)*h0 + (t*(52*z/243 - 88/243) - 47*z/81 + 53/54)*h1 + (-1664*t^8/243 + 2960*t^7/81 - 4364*t^6/81 - 196*t^5/27 + 1759*t^4/27 + 11*t^3/3 - 1007*t^2/12 + 201*t/4 - 141/16)*hf
  norm_num at hh

private lemma cell_8_62 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 2*z + 3/2:ℝ)=0) (h1 : (16*t^8 - 112*t^7 + t^6*(184 - 48*z) + t^5*(288*z + 140) + t^4*(-252*z - 440) + t^3*(71 - 744*z) + t^2*(639*z + 329/2) + t*(612*z - 259/4) - 165*z/4 + 55/16:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(2072*z/8019 - 3844/8019) + t^6*(686/297 - 10004*z/8019) + t^5*(13/243 - 2*z/81) + t^4*(29833*z/8019 - 109381/16038) + t^3*(6385*z/16038 - 8993/10692) + t^2*(80437/21384 - 2573*z/1188) + t*(213167/128304 - 53897*z/64152) - 2311*z/11664 + 4561/7776)*h0 + (t*(961/16038 - 259*z/8019) + 61*z/16038 - 169/32076)*h1 + (2072*t^8/8019 - 524*t^7/297 + 23818*t^6/8019 + 11419*t^5/8019 - 38651*t^4/5346 + 112337*t^3/32076 + 293611*t^2/64152 - 29641*t/42768 + 1613/11664)*hf
  norm_num at hh

private lemma cell_8_63 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 6*t:ℝ)=0) (h1 : (t*(60 - 72*z) + 28*z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2/3 - 2*z/3)*h0 + (11/156 - z/78)*h1 + (7/78 - 3*t/13)*hf
  norm_num at hh

private lemma pair_8_15_23 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z:ℝ)=0) (h1 : (t + z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (16/23 - 12*z/23)*h0 + (12*z/23 - 16/23)*h1 + (-9/23)*hf
  norm_num at hh

private lemma pair_8_15_27 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z:ℝ)=0) (h1 : (t - z - 1:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (4/3 - 4*z/3)*h0 + (4*z/3 - 4/3)*h1 + (-1/3)*hf
  norm_num at hh

private lemma pair_8_23_27 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + z - 2:ℝ)=0) (h1 : (t - z - 1:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z - 3/2)*h0 + (3/2 - z)*h1 + (-1/2)*hf
  norm_num at hh

private lemma pair_8_29_30 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(1/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + z - 2:ℝ)=0) (h1 : (t - z - 1:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z - 3/2)*h0 + (3/2 - z)*h1 + (-1/2)*hf
  norm_num at hh

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_0 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 0) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_0 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_1 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 1) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_1 z t hf hn0 hn1 hn2 hn3
  · have hr : (-5/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_2 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 2) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_2 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_3 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 3) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_3 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z - 112*t^7 + 448*t^6*z^2 + 688*t^6*z + 184*t^6 - 896*t^5*z^3 - 1776*t^5*z^2 - 672*t^5*z + 140*t^5 + 1120*t^4*z^4 + 2480*t^4*z^3 + 744*t^4*z^2 - 916*t^4*z - 440*t^4 - 896*t^3*z^5 - 2000*t^3*z^4 + 64*t^3*z^3 + 1976*t^3*z^2 + 704*t^3*z + 71*t^3 + 448*t^2*z^6 + 912*t^2*z^5 - 696*t^2*z^4 - 1832*t^2*z^3 + 96*t^2*z^2 + 489*t^2*z + 329*t^2/2 - 128*t*z^7 - 208*t*z^6 + 480*t*z^5 + 700*t*z^4 - 544*t*z^3 - 615*t*z^2 + 400*t*z - 259*t/4 + 16*z^8 + 16*z^7 - 104*z^6 - 68*z^5 + 184*z^4 + 55*z^3 - 139*z^2/2 - 71*z/4 + 55/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 224*t^5*z + 892*t^5 - 280*t^4*z^2 - 1180*t^4*z - 2476*t^4 + 224*t^3*z^3 + 948*t^3*z^2 + 1824*t^3*z + 2917*t^3 - 112*t^2*z^4 - 452*t^2*z^3 - 702*t^2*z^2 - 833*t^2*z - 3029*t^2/2 + 32*t*z^5 + 116*t*z^4 + 104*t*z^3 + 4*t*z^2 + 118*t*z + 1555*t/4 - 4*z^6 - 12*z^5 + 3*z^4 + 26*z^3 + 21*z^2/4 - 39*z/4 - 55/16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_4 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 4) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_4 z t hf hn0 hn1 hn2 hn3
  · have hr : (-5/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_5 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 5) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_5 z t hf hn0 hn1 hn2 hn3
  · have hr : (-3/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_6 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 6) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_6 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 5*z + 1/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_7 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 7) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_7 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 5*t + 1/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z - 80*t^7 + 448*t^6*z^2 + 464*t^6*z + 40*t^6 - 896*t^5*z^3 - 1104*t^5*z^2 + 48*t^5*z + 220*t^5 + 1120*t^4*z^4 + 1360*t^4*z^3 - 696*t^4*z^2 - 956*t^4*z - 191*t^4 - 896*t^3*z^5 - 880*t^3*z^4 + 1504*t^3*z^3 + 1480*t^3*z^2 - 124*t^3*z - 89*t^3 + 448*t^2*z^6 + 240*t^2*z^5 - 1416*t^2*z^4 - 904*t^2*z^3 + 978*t^2*z^2 + 411*t^2*z + 88*t^2 - 128*t*z^7 + 16*t*z^6 + 624*t*z^5 + 92*t*z^4 - 820*t*z^3 - 267*t*z^2 + 436*t*z - 53*t + 16*z^8 - 16*z^7 - 104*z^6 + 68*z^5 + 157*z^4 - 55*z^3 - 29*z^2 - 59*z/2 + 55/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 224*t^5*z + 724*t^5 - 280*t^4*z^2 - 900*t^4*z - 1556*t^4 + 224*t^3*z^3 + 668*t^3*z^2 + 904*t^3*z + 1271*t^3 - 112*t^2*z^4 - 284*t^2*z^3 - 186*t^2*z^2 - 75*t^2*z - 348*t^2 + 32*t*z^5 + 60*t*z^4 - 44*t*z^3 - 126*t*z^2 - 36*t*z + 105*t/4 - 4*z^6 - 4*z^5 + 19*z^4 + 22*z^3 + 33*z/4 + 95/4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_8 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 8) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_8 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_9 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 9) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_9 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 5*z + 1/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_10 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 10) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_10 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_11 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 11) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_11 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 192*t^7*z - 48*t^7 + 1056*t^6*z^2 + 288*t^6*z - 24*t^6 - 3456*t^5*z^3 - 432*t^5*z^2 + 576*t^5*z + 108*t^5 + 7344*t^4*z^4 - 1296*t^4*z^3 - 2592*t^4*z^2 - 432*t^4*z - 36*t^4 - 10368*t^3*z^5 + 6480*t^3*z^4 + 4752*t^3*z^3 - 432*t^3*z^2 - 540*t^3*z + 27*t^3 + 9504*t^2*z^6 - 11664*t^2*z^5 - 2592*t^2*z^4 + 3024*t^2*z^3 + 1242*t^2*z^2 + 54*t^2*z + 27*t^2/2 - 5184*t*z^7 + 10368*t*z^6 - 2592*t*z^5 - 3564*t*z^4 + 324*t*z^3 + 567*t*z^2 + 162*t*z - 243*t/4 + 1296*z^8 - 3888*z^7 + 3240*z^6 + 324*z^5 - 1539*z^4 + 729*z^3 - 81*z^2 - 81*z + 243/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-264*t^6 + 864*t^5*z + 1836*t^5 - 1836*t^4*z^2 - 3348*t^4*z - 5589*t^4 + 2592*t^3*z^3 + 3564*t^3*z^2 + 5292*t^3*z + 9801*t^3 - 2376*t^2*z^4 - 1836*t^2*z^3 - 2430*t^2*z^2 - 5157*t^2*z - 10017*t^2 + 1296*t*z^5 + 324*t*z^3 + 1539*t*z^2 + 2916*t*z + 10611*t/2 - 324*z^6 + 324*z^5 - 81*z^4 - 324*z^3 - 243*z^2 - 2349*z/4 - 2187/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_12 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 12) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_12 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 208*t^7 + 160*t^6*z^2 - 800*t^6*z + 1000*t^6 + 256*t^5*z^3 - 1776*t^5*z^2 + 3792*t^5*z - 2236*t^5 + 304*t^4*z^4 - 2512*t^4*z^3 + 7296*t^4*z^2 - 8308*t^4*z + 2293*t^4 + 256*t^3*z^5 - 2480*t^3*z^4 + 8800*t^3*z^3 - 13432*t^3*z^2 + 7736*t^3*z - 691*t^3 + 160*t^2*z^6 - 1680*t^2*z^5 + 6720*t^2*z^4 - 12560*t^2*z^3 + 9978*t^2*z^2 - 1419*t^2*z - 389*t^2 + 64*t*z^7 - 736*t*z^6 + 3216*t*z^5 - 6488*t*z^4 + 5660*t*z^3 - 1110*t*z^2 - 677*t*z + 385*t/2 + 16*z^8 - 176*z^7 + 712*z^6 - 1364*z^5 + 1252*z^4 - 317*z^3 - 625*z^2/2 + 637*z/4 - 245/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 - 64*t^5*z + 316*t^5 - 76*t^4*z^2 + 476*t^4*z - 853*t^4 - 64*t^3*z^3 + 492*t^3*z^2 - 1200*t^3*z + 835*t^3 - 40*t^2*z^4 + 340*t^2*z^3 - 990*t^2*z^2 + 1075*t^2*z - 97*t^2 - 16*t*z^5 + 152*t*z^4 - 496*t*z^3 + 592*t*z^2 - 107*t*z - 169*t/2 - 4*z^6 + 36*z^5 - 105*z^4 + 122*z^3 - 171*z^2/4 - 147*z/4 + 245/16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_13 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 13) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_13 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 5*t + 1/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 176*t^7 + 160*t^6*z^2 - 640*t^6*z + 664*t^6 + 256*t^5*z^3 - 1392*t^5*z^2 + 2280*t^5*z - 968*t^5 + 304*t^4*z^4 - 1904*t^4*z^3 + 4128*t^4*z^2 - 3248*t^4*z + 208*t^4 + 256*t^3*z^5 - 1840*t^3*z^4 + 4648*t^3*z^3 - 4424*t^3*z^2 + 680*t^3*z + 616*t^3 + 160*t^2*z^6 - 1200*t^2*z^5 + 3264*t^2*z^4 - 3568*t^2*z^3 + 240*t^2*z^2 + 1824*t^2*z - 344*t^2 + 64*t*z^7 - 512*t*z^6 + 1416*t*z^5 - 1288*t*z^4 - 544*t*z^3 + 1200*t*z^2 - 272*t*z - 32*t + 16*z^8 - 112*z^7 + 232*z^6 - 112*z^5 - 152*z^4 + 248*z^3 - 128*z^2 - 40*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 - 64*t^5*z + 220*t^5 - 76*t^4*z^2 + 324*t^4*z - 365*t^4 - 64*t^3*z^3 + 332*t^3*z^2 - 482*t^3*z + 59*t^3 - 40*t^2*z^4 + 220*t^2*z^3 - 366*t^2*z^2 + 105*t^2*z + 483*t^2/2 - 16*t*z^5 + 96*t*z^4 - 158*t*z^3 - 18*t*z^2 + 279*t*z/2 - 33*t/2 - 4*z^6 + 20*z^5 - 17*z^4 - 11*z^3 + 81*z^2/4 - 75*z/4 - 169/16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_14 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 14) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_14 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 144*t^7 - 48*t^6*z + 408*t^6 + 360*t^5*z - 324*t^5 - 648*t^4*z - 279*t^4 - 270*t^3*z + 459*t^3 + 918*t^2*z - 108*t^2 + 405*t*z/2 - 81*t - 243*z/4 + 243/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_15 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 15) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : (t - 2*z:ℝ)=0 := by
  apply cell_8_15 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z - 144*t^7 + 160*t^6*z^2 + 384*t^6*z + 408*t^6 - 256*t^5*z^3 - 720*t^5*z^2 - 432*t^5*z - 324*t^5 + 304*t^4*z^4 + 720*t^4*z^3 + 432*t^4*z^2 - 540*t^4*z - 279*t^4 - 256*t^3*z^5 - 528*t^3*z^4 + 384*t^3*z^3 + 648*t^3*z^2 + 288*t^3*z + 459*t^3 + 160*t^2*z^6 + 144*t^2*z^5 - 432*t^2*z^4 - 864*t^2*z^3 + 162*t^2*z^2 + 783*t^2*z - 108*t^2 - 64*t*z^7 + 432*t*z^5 - 684*t*z^3 + 108*t*z^2 + 189*t*z - 81*t + 16*z^8 - 48*z^7 - 24*z^6 + 108*z^5 - 36*z^4 + 27*z^3 + 27*z^2/2 - 243*z/4 + 243/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 64*t^5*z + 308*t^5 - 76*t^4*z^2 - 332*t^4*z - 753*t^4 + 64*t^3*z^3 + 260*t^3*z^2 + 408*t^3*z + 589*t^3 - 40*t^2*z^4 - 116*t^2*z^3 - 114*t^2*z^2 + 17*t^2*z + 22*t^2 + 16*t*z^5 + 32*t*z^4 - 48*t*z^3 - 104*t*z^2 - 25*t*z - 51*t - 4*z^6 + 4*z^5 + 15*z^4 + 2*z^3 + 37*z^2/4 + 45*z/4 + 269/16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_16 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 16) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_16 z t hf hn0 hn1 hn2 hn3
  · have hr : (-5/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_17 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 17) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_17 z t hf hn0 hn1 hn2 hn3
  · have hr : (-3/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_18 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 18) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_18 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 5*z + 1/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_19 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 19) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_19 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 5*t + 1/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z - 80*t^7 + 448*t^6*z^2 + 464*t^6*z + 40*t^6 - 896*t^5*z^3 - 1104*t^5*z^2 + 48*t^5*z + 220*t^5 + 1120*t^4*z^4 + 1360*t^4*z^3 - 696*t^4*z^2 - 956*t^4*z - 191*t^4 - 896*t^3*z^5 - 880*t^3*z^4 + 1504*t^3*z^3 + 1480*t^3*z^2 - 124*t^3*z - 89*t^3 + 448*t^2*z^6 + 240*t^2*z^5 - 1416*t^2*z^4 - 904*t^2*z^3 + 978*t^2*z^2 + 411*t^2*z + 88*t^2 - 128*t*z^7 + 16*t*z^6 + 624*t*z^5 + 92*t*z^4 - 820*t*z^3 - 267*t*z^2 + 436*t*z - 53*t + 16*z^8 - 16*z^7 - 104*z^6 + 68*z^5 + 157*z^4 - 55*z^3 - 29*z^2 - 59*z/2 + 55/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 224*t^5*z + 724*t^5 - 280*t^4*z^2 - 900*t^4*z - 1556*t^4 + 224*t^3*z^3 + 668*t^3*z^2 + 904*t^3*z + 1271*t^3 - 112*t^2*z^4 - 284*t^2*z^3 - 186*t^2*z^2 - 75*t^2*z - 348*t^2 + 32*t*z^5 + 60*t*z^4 - 44*t*z^3 - 126*t*z^2 - 36*t*z + 105*t/4 - 4*z^6 - 4*z^5 + 19*z^4 + 22*z^3 + 33*z/4 + 95/4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_20 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 20) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_20 z t hf hn0 hn1 hn2 hn3
  · have hr : (-3/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_21 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 21) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_21 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_22 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 22) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_22 z t hf hn0 hn1 hn2 hn3
  · have hr : (648*t*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_23 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 23) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : (t + z - 2:ℝ)=0 := by
  apply cell_8_23 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t + 1/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 448*t^6*z^2 + 240*t^6*z - 72*t^6 - 896*t^5*z^3 - 432*t^5*z^2 + 576*t^5*z + 216*t^5 + 1120*t^4*z^4 + 240*t^4*z^3 - 1656*t^4*z^2 - 648*t^4*z + 72*t^4 - 896*t^3*z^5 + 240*t^3*z^4 + 2304*t^3*z^3 + 432*t^3*z^2 - 936*t^3*z - 216*t^3 + 448*t^2*z^6 - 432*t^2*z^5 - 1656*t^2*z^4 + 432*t^2*z^3 + 1728*t^2*z^2 + 216*t^2*z - 128*t*z^7 + 240*t*z^6 + 576*t*z^5 - 648*t*z^4 - 936*t*z^3 + 216*t*z^2 + 648*t*z + 16*z^8 - 48*z^7 - 72*z^6 + 216*z^5 + 72*z^4 - 216*z^3:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 224*t^5*z + 556*t^5 - 280*t^4*z^2 - 620*t^4*z - 756*t^4 + 224*t^3*z^3 + 388*t^3*z^2 + 144*t^3*z + 83*t^3 - 112*t^2*z^4 - 116*t^2*z^3 + 210*t^2*z^2 + 341*t^2*z + 395*t^2/2 + 32*t*z^5 + 4*t*z^4 - 144*t*z^3 - 127*t*z^2 + 16*t*z + 39*t/4 - 4*z^6 + 4*z^5 + 27*z^4 - z^3 - 107*z^2/4 + 3*z/4 + 131/16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_24 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 24) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_24 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 5*z + 1/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_25 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 25) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_25 z t hf hn0 hn1 hn2 hn3
  · have hr : (648*t*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_26 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 26) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_26 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z + 3/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_27 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 27) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : (t - z - 1:ℝ)=0 := by
  apply cell_8_27 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 3*t + 2*z^2 - 3*z + 3/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 112*t^7 - 48*t^6*z + 184*t^6 + 288*t^5*z + 140*t^5 - 252*t^4*z - 440*t^4 - 744*t^3*z + 71*t^3 + 639*t^2*z + 329*t^2/2 + 612*t*z - 259*t/4 - 165*z/4 + 55/16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_28 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 28) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_28 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 5*t + 1/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 176*t^7 + 160*t^6*z^2 - 736*t^6*z + 712*t^6 + 256*t^5*z^3 - 1680*t^5*z^2 + 3216*t^5*z - 1364*t^5 + 304*t^4*z^4 - 2480*t^4*z^3 + 6720*t^4*z^2 - 6488*t^4*z + 1252*t^4 + 256*t^3*z^5 - 2512*t^3*z^4 + 8800*t^3*z^3 - 12560*t^3*z^2 + 5660*t^3*z - 317*t^3 + 160*t^2*z^6 - 1776*t^2*z^5 + 7296*t^2*z^4 - 13432*t^2*z^3 + 9978*t^2*z^2 - 1110*t^2*z - 625*t^2/2 + 64*t*z^7 - 800*t*z^6 + 3792*t*z^5 - 8308*t*z^4 + 7736*t*z^3 - 1419*t*z^2 - 677*t*z + 637*t/4 + 16*z^8 - 208*z^7 + 1000*z^6 - 2236*z^5 + 2293*z^4 - 691*z^3 - 389*z^2 + 385*z/2 - 245/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 - 64*t^5*z + 292*t^5 - 76*t^4*z^2 + 468*t^4*z - 725*t^4 - 64*t^3*z^3 + 500*t^3*z^2 - 1184*t^3*z + 647*t^3 - 40*t^2*z^4 + 364*t^2*z^3 - 1086*t^2*z^2 + 1095*t^2*z - 33*t^2 - 16*t*z^5 + 168*t*z^4 - 608*t*z^3 + 819*t*z^2 - 144*t*z - 138*t - 4*z^6 + 44*z^5 - 161*z^4 + 226*z^3 - 81*z^2 - 183*z/4 + 26)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_29 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 29) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : (t + z - 2:ℝ)=0 := by
  apply cell_8_29 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t + 1/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 448*t^6*z^2 + 240*t^6*z - 72*t^6 - 896*t^5*z^3 - 432*t^5*z^2 + 576*t^5*z + 216*t^5 + 1120*t^4*z^4 + 240*t^4*z^3 - 1656*t^4*z^2 - 648*t^4*z + 72*t^4 - 896*t^3*z^5 + 240*t^3*z^4 + 2304*t^3*z^3 + 432*t^3*z^2 - 936*t^3*z - 216*t^3 + 448*t^2*z^6 - 432*t^2*z^5 - 1656*t^2*z^4 + 432*t^2*z^3 + 1728*t^2*z^2 + 216*t^2*z - 128*t*z^7 + 240*t*z^6 + 576*t*z^5 - 648*t*z^4 - 936*t*z^3 + 216*t*z^2 + 648*t*z + 16*z^8 - 48*z^7 - 72*z^6 + 216*z^5 + 72*z^4 - 216*z^3:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 224*t^5*z + 556*t^5 - 280*t^4*z^2 - 620*t^4*z - 756*t^4 + 224*t^3*z^3 + 388*t^3*z^2 + 144*t^3*z + 83*t^3 - 112*t^2*z^4 - 116*t^2*z^3 + 210*t^2*z^2 + 341*t^2*z + 395*t^2/2 + 32*t*z^5 + 4*t*z^4 - 144*t*z^3 - 127*t*z^2 + 16*t*z + 39*t/4 - 4*z^6 + 4*z^5 + 27*z^4 - z^3 - 107*z^2/4 + 3*z/4 + 131/16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_30 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 30) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : (t - z - 1:ℝ)=0 := by
  apply cell_8_30 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 3*t + 2*z^2 - 3*z + 3/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 112*t^7 - 48*t^6*z + 184*t^6 + 288*t^5*z + 140*t^5 - 252*t^4*z - 440*t^4 - 744*t^3*z + 71*t^3 + 639*t^2*z + 329*t^2/2 + 612*t*z - 259*t/4 - 165*z/4 + 55/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_31 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 31) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_31 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t + 3/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z - 80*t^7 + 160*t^6*z^2 + 160*t^6*z + 40*t^6 - 256*t^5*z^3 - 240*t^5*z^2 + 312*t^5*z + 220*t^5 + 304*t^4*z^4 + 80*t^4*z^3 - 624*t^4*z^2 - 496*t^4*z - 191*t^4 - 256*t^3*z^5 + 80*t^3*z^4 + 1016*t^3*z^3 + 220*t^3*z^2 - 782*t^3*z - 89*t^3 + 160*t^2*z^6 - 240*t^2*z^5 - 624*t^2*z^4 + 220*t^2*z^3 + 762*t^2*z^2 + 444*t^2*z + 88*t^2 - 64*t*z^7 + 160*t*z^6 + 312*t*z^5 - 496*t*z^4 - 782*t*z^3 + 444*t*z^2 + 1201*t*z/2 - 53*t + 16*z^8 - 80*z^7 + 40*z^6 + 220*z^5 - 191*z^4 - 89*z^3 + 88*z^2 - 53*z + 55/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 64*t^5*z + 188*t^5 - 76*t^4*z^2 - 172*t^4*z - 169*t^4 + 64*t^3*z^3 + 108*t^3*z^2 - 54*t^3*z - 190*t^3 - 40*t^2*z^4 - 20*t^2*z^3 + 126*t^2*z^2 + 202*t^2*z + 182*t^2 + 16*t*z^5 - 8*t*z^4 - 98*t*z^3 - 70*t*z^2 + 80*t*z + 133*t/2 - 4*z^6 + 12*z^5 + 15*z^4 - 28*z^3 - 12*z^2 + 21*z/4 - 17/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_32 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 32) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_32 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_33 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 33) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_33 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 5*z + 1/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_34 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 34) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_34 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_35 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 35) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_35 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 192*t^7*z - 48*t^7 + 1056*t^6*z^2 + 288*t^6*z - 24*t^6 - 3456*t^5*z^3 - 432*t^5*z^2 + 576*t^5*z + 108*t^5 + 7344*t^4*z^4 - 1296*t^4*z^3 - 2592*t^4*z^2 - 432*t^4*z - 36*t^4 - 10368*t^3*z^5 + 6480*t^3*z^4 + 4752*t^3*z^3 - 432*t^3*z^2 - 540*t^3*z + 27*t^3 + 9504*t^2*z^6 - 11664*t^2*z^5 - 2592*t^2*z^4 + 3024*t^2*z^3 + 1242*t^2*z^2 + 54*t^2*z + 27*t^2/2 - 5184*t*z^7 + 10368*t*z^6 - 2592*t*z^5 - 3564*t*z^4 + 324*t*z^3 + 567*t*z^2 + 162*t*z - 243*t/4 + 1296*z^8 - 3888*z^7 + 3240*z^6 + 324*z^5 - 1539*z^4 + 729*z^3 - 81*z^2 - 81*z + 243/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-264*t^6 + 864*t^5*z + 1836*t^5 - 1836*t^4*z^2 - 3348*t^4*z - 5589*t^4 + 2592*t^3*z^3 + 3564*t^3*z^2 + 5292*t^3*z + 9801*t^3 - 2376*t^2*z^4 - 1836*t^2*z^3 - 2430*t^2*z^2 - 5157*t^2*z - 10017*t^2 + 1296*t*z^5 + 324*t*z^3 + 1539*t*z^2 + 2916*t*z + 10611*t/2 - 324*z^6 + 324*z^5 - 81*z^4 - 324*z^3 - 243*z^2 - 2349*z/4 - 2187/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_36 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 36) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_36 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 5*z + 1/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_37 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (_hc : cell (1) (1) (1) (profile4 (1/2) (z) t 37) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : ((0:ℝ):ℝ)=0 := by
  apply cell_8_37 z t hf hn0 hn1 hn2 hn3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_38 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 38) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_38 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z + 3/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_39 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 39) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_39 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 3*t + 2*z^2 - 3*z + 3/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 112*t^7 + 192*t^6*z^2 - 240*t^6*z + 232*t^6 - 1008*t^5*z^2 + 1296*t^5*z - 112*t^5 + 864*t^4*z^4 - 2160*t^4*z^3 + 2664*t^4*z^2 - 1728*t^4*z - 152*t^4 - 3024*t^3*z^4 + 7776*t^3*z^3 - 4800*t^3*z^2 - 264*t^3*z + 248*t^3 + 1728*t^2*z^6 - 6480*t^2*z^5 + 9720*t^2*z^4 - 7776*t^2*z^3 + 2016*t^2*z^2 + 1296*t^2*z - 128*t^2 - 3024*t*z^6 + 11664*t*z^5 - 13392*t*z^4 + 2376*t*z^3 + 2880*t*z^2 - 432*t*z - 40*t + 1296*z^8 - 6480*z^7 + 11448*z^6 - 7776*z^5 + 216*z^4 + 1944*z^3 - 672*z^2 - 24*z + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-48*t^6 + 252*t^5 - 216*t^4*z^2 + 108*t^4*z - 396*t^4 + 756*t^3*z^2 - 432*t^3*z + 147*t^3 - 432*t^2*z^4 + 756*t^2*z^3 - 810*t^2*z^2 + 135*t^2*z - 63*t^2/2 + 756*t*z^4 - 1404*t*z^3 + 351*t*z^2 + 459*t*z + 441*t/4 - 324*z^6 + 972*z^5 - 837*z^4 + 27*z^3 + 837*z^2/4 - 297*z/4 - 525/16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_40 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 40) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_40 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_41 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 41) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_41 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z + 3/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_42 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 42) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_42 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_43 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 43) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_43 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 256*t^7*z + 16*t^7 + 1792*t^6*z^2 - 368*t^6*z - 104*t^6 - 7168*t^5*z^3 + 3072*t^5*z^2 + 960*t^5*z - 68*t^5 + 17920*t^4*z^4 - 13120*t^4*z^3 - 3072*t^4*z^2 + 1076*t^4*z + 184*t^4 - 28672*t^3*z^5 + 32000*t^3*z^4 + 2816*t^3*z^3 - 5312*t^3*z^2 - 968*t^3*z + 55*t^3 + 28672*t^2*z^6 - 45312*t^2*z^5 + 4992*t^2*z^4 + 11488*t^2*z^3 + 528*t^2*z^2 - 717*t^2*z - 139*t^2/2 - 16384*t*z^7 + 34816*t*z^6 - 12288*t*z^5 - 11200*t*z^4 + 3616*t*z^3 + 1056*t*z^2 + 422*t*z - 71*t/4 + 4096*z^8 - 11264*z^7 + 7168*z^6 + 3904*z^5 - 4544*z^4 + 316*z^3 + 424*z^2 - 353*z/4 + 55/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 1792*t^5*z + 2816*t^5 - 4480*t^4*z^2 - 5680*t^4*z - 9472*t^4 + 7168*t^3*z^3 + 6336*t^3*z^2 + 10176*t^3*z + 20096*t^3 - 7168*t^2*z^4 - 3008*t^2*z^3 - 5472*t^2*z^2 - 13064*t^2*z - 24892*t^2 + 4096*t*z^5 - 512*t*z^4 + 1024*t*z^3 + 4976*t*z^2 + 8792*t*z + 16076*t - 1024*z^6 + 768*z^5 - 1168*z^3 - 1200*z^2 - 2187*z - 4180)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_44 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 44) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_44 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 144*t^7 + 192*t^6*z^2 - 336*t^6*z + 504*t^6 - 1296*t^5*z^2 + 2304*t^5*z - 972*t^5 + 864*t^4*z^4 - 3024*t^4*z^3 + 5832*t^4*z^2 - 5724*t^4*z + 1125*t^4 - 3888*t^3*z^4 + 13824*t^3*z^3 - 16200*t^3*z^2 + 7128*t^3*z - 675*t^3 + 1728*t^2*z^6 - 9072*t^2*z^5 + 21384*t^2*z^4 - 29160*t^2*z^3 + 20358*t^2*z^2 - 4509*t^2*z + 81*t^2 - 3888*t*z^6 + 20736*t*z^5 - 39852*t*z^4 + 33048*t*z^3 - 10773*t*z^2 + 729*t*z + 243*t/2 + 1296*z^8 - 9072*z^7 + 25272*z^6 - 35964*z^5 + 27621*z^4 - 10611*z^3 + 1215*z^2 + 243*z - 729/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-48*t^6 + 324*t^5 - 216*t^4*z^2 + 324*t^4*z - 756*t^4 + 972*t^3*z^2 - 1512*t^3*z + 783*t^3 - 432*t^2*z^4 + 1404*t^2*z^3 - 2430*t^2*z^2 + 2079*t^2*z - 324*t^2 + 972*t*z^4 - 3240*t*z^3 + 3240*t*z^2 - 972*t*z - 243*t/4 - 324*z^6 + 1620*z^5 - 2997*z^4 + 2592*z^3 - 972*z^2 + 243*z/4 + 243/4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_45 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 45) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_45 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 3*t + 2*z^2 - 3*z + 3/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 112*t^7 + 192*t^6*z^2 - 240*t^6*z + 232*t^6 - 1008*t^5*z^2 + 1296*t^5*z - 112*t^5 + 864*t^4*z^4 - 2160*t^4*z^3 + 2664*t^4*z^2 - 1728*t^4*z - 152*t^4 - 3024*t^3*z^4 + 7776*t^3*z^3 - 4800*t^3*z^2 - 264*t^3*z + 248*t^3 + 1728*t^2*z^6 - 6480*t^2*z^5 + 9720*t^2*z^4 - 7776*t^2*z^3 + 2016*t^2*z^2 + 1296*t^2*z - 128*t^2 - 3024*t*z^6 + 11664*t*z^5 - 13392*t*z^4 + 2376*t*z^3 + 2880*t*z^2 - 432*t*z - 40*t + 1296*z^8 - 6480*z^7 + 11448*z^6 - 7776*z^5 + 216*z^4 + 1944*z^3 - 672*z^2 - 24*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-48*t^6 + 252*t^5 - 216*t^4*z^2 + 108*t^4*z - 396*t^4 + 756*t^3*z^2 - 432*t^3*z + 147*t^3 - 432*t^2*z^4 + 756*t^2*z^3 - 810*t^2*z^2 + 135*t^2*z - 63*t^2/2 + 756*t*z^4 - 1404*t*z^3 + 351*t*z^2 + 459*t*z + 441*t/4 - 324*z^6 + 972*z^5 - 837*z^4 + 27*z^3 + 837*z^2/4 - 297*z/4 - 525/16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_46 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 46) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_46 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 80*t^7 + 160*t^6*z^2 + 160*t^6*z + 40*t^6 - 256*t^5*z^3 - 240*t^5*z^2 + 312*t^5*z + 220*t^5 + 304*t^4*z^4 + 80*t^4*z^3 - 624*t^4*z^2 - 496*t^4*z - 191*t^4 - 256*t^3*z^5 + 80*t^3*z^4 + 1016*t^3*z^3 + 220*t^3*z^2 - 782*t^3*z - 89*t^3 + 160*t^2*z^6 - 240*t^2*z^5 - 624*t^2*z^4 + 220*t^2*z^3 + 762*t^2*z^2 + 444*t^2*z + 88*t^2 - 64*t*z^7 + 160*t*z^6 + 312*t*z^5 - 496*t*z^4 - 782*t*z^3 + 444*t*z^2 + 1201*t*z/2 - 53*t + 16*z^8 - 80*z^7 + 40*z^6 + 220*z^5 - 191*z^4 - 89*z^3 + 88*z^2 - 53*z + 55/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 64*t^5*z + 188*t^5 - 76*t^4*z^2 - 172*t^4*z - 169*t^4 + 64*t^3*z^3 + 108*t^3*z^2 - 54*t^3*z - 190*t^3 - 40*t^2*z^4 - 20*t^2*z^3 + 126*t^2*z^2 + 202*t^2*z + 182*t^2 + 16*t*z^5 - 8*t*z^4 - 98*t*z^3 - 70*t*z^2 + 80*t*z + 133*t/2 - 4*z^6 + 12*z^5 + 15*z^4 - 28*z^3 - 12*z^2 + 21*z/4 - 17/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_47 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 47) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_47 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 192*t^7*z - 16*t^7 + 1056*t^6*z^2 - 104*t^6 - 3456*t^5*z^3 + 720*t^5*z^2 + 936*t^5*z + 68*t^5 + 7344*t^4*z^4 - 3888*t^4*z^3 - 3168*t^4*z^2 + 192*t^4*z + 157*t^4 - 10368*t^3*z^5 + 9936*t^3*z^4 + 4968*t^3*z^3 - 2316*t^3*z^2 - 1170*t^3*z - 55*t^3 + 9504*t^2*z^6 - 14256*t^2*z^5 - 2592*t^2*z^4 + 5940*t^2*z^3 + 1638*t^2*z^2 - 360*t^2*z - 29*t^2 - 5184*t*z^7 + 11232*t*z^6 - 1944*t*z^5 - 6264*t*z^4 + 486*t*z^3 + 1098*t*z^2 + 1011*t*z/2 - 59*t/2 + 1296*z^8 - 3888*z^7 + 2376*z^6 + 2268*z^5 - 2295*z^4 + 27*z^3 + 300*z^2 - 153*z/2 + 55/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-264*t^6 + 864*t^5*z + 1548*t^5 - 1836*t^4*z^2 - 2700*t^4*z - 4149*t^4 + 2592*t^3*z^3 + 2700*t^3*z^2 + 3510*t^3*z + 6924*t^3 - 2376*t^2*z^4 - 1188*t^2*z^3 - 1134*t^2*z^2 - 3456*t^2*z - 7038*t^2 + 1296*t*z^5 - 216*t*z^4 - 270*t*z^3 + 1080*t*z^2 + 2106*t*z + 7335*t/2 - 324*z^6 + 324*z^5 + 135*z^4 - 378*z^3 - 216*z^2 - 1377*z/4 - 1419/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_48 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 48) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_48 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 208*t^7 + 160*t^6*z^2 - 800*t^6*z + 1000*t^6 + 256*t^5*z^3 - 1776*t^5*z^2 + 3792*t^5*z - 2236*t^5 + 304*t^4*z^4 - 2512*t^4*z^3 + 7296*t^4*z^2 - 8308*t^4*z + 2293*t^4 + 256*t^3*z^5 - 2480*t^3*z^4 + 8800*t^3*z^3 - 13432*t^3*z^2 + 7736*t^3*z - 691*t^3 + 160*t^2*z^6 - 1680*t^2*z^5 + 6720*t^2*z^4 - 12560*t^2*z^3 + 9978*t^2*z^2 - 1419*t^2*z - 389*t^2 + 64*t*z^7 - 736*t*z^6 + 3216*t*z^5 - 6488*t*z^4 + 5660*t*z^3 - 1110*t*z^2 - 677*t*z + 385*t/2 + 16*z^8 - 176*z^7 + 712*z^6 - 1364*z^5 + 1252*z^4 - 317*z^3 - 625*z^2/2 + 637*z/4 - 245/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 - 64*t^5*z + 316*t^5 - 76*t^4*z^2 + 476*t^4*z - 853*t^4 - 64*t^3*z^3 + 492*t^3*z^2 - 1200*t^3*z + 835*t^3 - 40*t^2*z^4 + 340*t^2*z^3 - 990*t^2*z^2 + 1075*t^2*z - 97*t^2 - 16*t*z^5 + 152*t*z^4 - 496*t*z^3 + 592*t*z^2 - 107*t*z - 169*t/2 - 4*z^6 + 36*z^5 - 105*z^4 + 122*z^3 - 171*z^2/4 - 147*z/4 + 245/16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_49 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 49) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_49 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 5*t + 1/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 176*t^7 + 160*t^6*z^2 - 640*t^6*z + 664*t^6 + 256*t^5*z^3 - 1392*t^5*z^2 + 2280*t^5*z - 968*t^5 + 304*t^4*z^4 - 1904*t^4*z^3 + 4128*t^4*z^2 - 3248*t^4*z + 208*t^4 + 256*t^3*z^5 - 1840*t^3*z^4 + 4648*t^3*z^3 - 4424*t^3*z^2 + 680*t^3*z + 616*t^3 + 160*t^2*z^6 - 1200*t^2*z^5 + 3264*t^2*z^4 - 3568*t^2*z^3 + 240*t^2*z^2 + 1824*t^2*z - 344*t^2 + 64*t*z^7 - 512*t*z^6 + 1416*t*z^5 - 1288*t*z^4 - 544*t*z^3 + 1200*t*z^2 - 272*t*z - 32*t + 16*z^8 - 112*z^7 + 232*z^6 - 112*z^5 - 152*z^4 + 248*z^3 - 128*z^2 - 40*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 - 64*t^5*z + 220*t^5 - 76*t^4*z^2 + 324*t^4*z - 365*t^4 - 64*t^3*z^3 + 332*t^3*z^2 - 482*t^3*z + 59*t^3 - 40*t^2*z^4 + 220*t^2*z^3 - 366*t^2*z^2 + 105*t^2*z + 483*t^2/2 - 16*t*z^5 + 96*t*z^4 - 158*t*z^3 - 18*t*z^2 + 279*t*z/2 - 33*t/2 - 4*z^6 + 20*z^5 - 17*z^4 - 11*z^3 + 81*z^2/4 - 75*z/4 - 169/16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_50 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 50) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_50 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 144*t^7 - 48*t^6*z + 408*t^6 + 360*t^5*z - 324*t^5 - 648*t^4*z - 279*t^4 - 270*t^3*z + 459*t^3 + 918*t^2*z - 108*t^2 + 405*t*z/2 - 81*t - 243*z/4 + 243/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_51 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 51) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_51 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z - 144*t^7 + 160*t^6*z^2 + 384*t^6*z + 408*t^6 - 256*t^5*z^3 - 720*t^5*z^2 - 432*t^5*z - 324*t^5 + 304*t^4*z^4 + 720*t^4*z^3 + 432*t^4*z^2 - 540*t^4*z - 279*t^4 - 256*t^3*z^5 - 528*t^3*z^4 + 384*t^3*z^3 + 648*t^3*z^2 + 288*t^3*z + 459*t^3 + 160*t^2*z^6 + 144*t^2*z^5 - 432*t^2*z^4 - 864*t^2*z^3 + 162*t^2*z^2 + 783*t^2*z - 108*t^2 - 64*t*z^7 + 432*t*z^5 - 684*t*z^3 + 108*t*z^2 + 189*t*z - 81*t + 16*z^8 - 48*z^7 - 24*z^6 + 108*z^5 - 36*z^4 + 27*z^3 + 27*z^2/2 - 243*z/4 + 243/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 64*t^5*z + 308*t^5 - 76*t^4*z^2 - 332*t^4*z - 753*t^4 + 64*t^3*z^3 + 260*t^3*z^2 + 408*t^3*z + 589*t^3 - 40*t^2*z^4 - 116*t^2*z^3 - 114*t^2*z^2 + 17*t^2*z + 22*t^2 + 16*t*z^5 + 32*t*z^4 - 48*t*z^3 - 104*t*z^2 - 25*t*z - 51*t - 4*z^6 + 4*z^5 + 15*z^4 + 2*z^3 + 37*z^2/4 + 45*z/4 + 269/16)*hf
  · have hr : (16*t^8 + 128*t^7*z - 240*t^7 + 448*t^6*z^2 - 1680*t^6*z + 1368*t^6 + 896*t^5*z^3 - 5040*t^5*z^2 + 8352*t^5*z - 3780*t^5 + 1120*t^4*z^4 - 8400*t^4*z^3 + 21096*t^4*z^2 - 19764*t^4*z + 5256*t^4 + 896*t^3*z^5 - 8400*t^3*z^4 + 28224*t^3*z^3 - 40392*t^3*z^2 + 22320*t^3*z - 3321*t^3 + 448*t^2*z^6 - 5040*t^2*z^5 + 21096*t^2*z^4 - 40392*t^2*z^3 + 34128*t^2*z^2 - 9963*t^2*z + 1053*t^2/2 + 128*t*z^7 - 1680*t*z^6 + 8352*t*z^5 - 19764*t*z^4 + 22320*t*z^3 - 9963*t*z^2 + 972*t*z + 729*t/4 + 16*z^8 - 240*z^7 + 1368*z^6 - 3780*z^5 + 5256*z^4 - 3321*z^3 + 1053*z^2/2 + 729*z/4 - 729/16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 - 224*t^5*z + 812*t^5 - 280*t^4*z^2 + 1540*t^4*z - 2124*t^4 - 224*t^3*z^3 + 1652*t^3*z^2 - 3696*t^3*z + 2293*t^3 - 112*t^2*z^4 + 1036*t^2*z^3 - 3174*t^2*z^2 + 3491*t^2*z - 1513*t^2/2 - 32*t*z^5 + 356*t*z^4 - 1368*t*z^3 + 2116*t*z^2 - 1006*t*z - 201*t/4 - 4*z^6 + 52*z^5 - 237*z^4 + 458*z^3 - 1355*z^2/4 + 153*z/4 + 473/16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_52 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 52) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_52 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 5*t + 1/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 176*t^7 + 160*t^6*z^2 - 736*t^6*z + 712*t^6 + 256*t^5*z^3 - 1680*t^5*z^2 + 3216*t^5*z - 1364*t^5 + 304*t^4*z^4 - 2480*t^4*z^3 + 6720*t^4*z^2 - 6488*t^4*z + 1252*t^4 + 256*t^3*z^5 - 2512*t^3*z^4 + 8800*t^3*z^3 - 12560*t^3*z^2 + 5660*t^3*z - 317*t^3 + 160*t^2*z^6 - 1776*t^2*z^5 + 7296*t^2*z^4 - 13432*t^2*z^3 + 9978*t^2*z^2 - 1110*t^2*z - 625*t^2/2 + 64*t*z^7 - 800*t*z^6 + 3792*t*z^5 - 8308*t*z^4 + 7736*t*z^3 - 1419*t*z^2 - 677*t*z + 637*t/4 + 16*z^8 - 208*z^7 + 1000*z^6 - 2236*z^5 + 2293*z^4 - 691*z^3 - 389*z^2 + 385*z/2 - 245/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 - 64*t^5*z + 292*t^5 - 76*t^4*z^2 + 468*t^4*z - 725*t^4 - 64*t^3*z^3 + 500*t^3*z^2 - 1184*t^3*z + 647*t^3 - 40*t^2*z^4 + 364*t^2*z^3 - 1086*t^2*z^2 + 1095*t^2*z - 33*t^2 - 16*t*z^5 + 168*t*z^4 - 608*t*z^3 + 819*t*z^2 - 144*t*z - 138*t - 4*z^6 + 44*z^5 - 161*z^4 + 226*z^3 - 81*z^2 - 183*z/4 + 26)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_53 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 53) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : (t + z - 2:ℝ)=0 := by
  apply cell_8_53 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t + 1/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_54 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 54) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_54 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 3*t + 2*z^2 - 3*z + 3/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 112*t^7 - 48*t^6*z + 184*t^6 + 288*t^5*z + 140*t^5 - 252*t^4*z - 440*t^4 - 744*t^3*z + 71*t^3 + 639*t^2*z + 329*t^2/2 + 612*t*z - 259*t/4 - 165*z/4 + 55/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 112*t^7 + 192*t^6*z^2 - 240*t^6*z + 232*t^6 - 1008*t^5*z^2 + 1296*t^5*z - 112*t^5 + 864*t^4*z^4 - 2160*t^4*z^3 + 2664*t^4*z^2 - 1728*t^4*z - 152*t^4 - 3024*t^3*z^4 + 7776*t^3*z^3 - 4800*t^3*z^2 - 264*t^3*z + 248*t^3 + 1728*t^2*z^6 - 6480*t^2*z^5 + 9720*t^2*z^4 - 7776*t^2*z^3 + 2016*t^2*z^2 + 1296*t^2*z - 128*t^2 - 3024*t*z^6 + 11664*t*z^5 - 13392*t*z^4 + 2376*t*z^3 + 2880*t*z^2 - 432*t*z - 40*t + 1296*z^8 - 6480*z^7 + 11448*z^6 - 7776*z^5 + 216*z^4 + 1944*z^3 - 672*z^2 - 24*z + 16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-48*t^6 + 252*t^5 - 216*t^4*z^2 + 108*t^4*z - 396*t^4 + 756*t^3*z^2 - 432*t^3*z + 147*t^3 - 432*t^2*z^4 + 756*t^2*z^3 - 810*t^2*z^2 + 135*t^2*z - 63*t^2/2 + 756*t*z^4 - 1404*t*z^3 + 351*t*z^2 + 459*t*z + 441*t/4 - 324*z^6 + 972*z^5 - 837*z^4 + 27*z^3 + 837*z^2/4 - 297*z/4 - 525/16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_55 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 55) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_55 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t + 3/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z - 80*t^7 + 160*t^6*z^2 + 160*t^6*z + 40*t^6 - 256*t^5*z^3 - 240*t^5*z^2 + 312*t^5*z + 220*t^5 + 304*t^4*z^4 + 80*t^4*z^3 - 624*t^4*z^2 - 496*t^4*z - 191*t^4 - 256*t^3*z^5 + 80*t^3*z^4 + 1016*t^3*z^3 + 220*t^3*z^2 - 782*t^3*z - 89*t^3 + 160*t^2*z^6 - 240*t^2*z^5 - 624*t^2*z^4 + 220*t^2*z^3 + 762*t^2*z^2 + 444*t^2*z + 88*t^2 - 64*t*z^7 + 160*t*z^6 + 312*t*z^5 - 496*t*z^4 - 782*t*z^3 + 444*t*z^2 + 1201*t*z/2 - 53*t + 16*z^8 - 80*z^7 + 40*z^6 + 220*z^5 - 191*z^4 - 89*z^3 + 88*z^2 - 53*z + 55/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 64*t^5*z + 188*t^5 - 76*t^4*z^2 - 172*t^4*z - 169*t^4 + 64*t^3*z^3 + 108*t^3*z^2 - 54*t^3*z - 190*t^3 - 40*t^2*z^4 - 20*t^2*z^3 + 126*t^2*z^2 + 202*t^2*z + 182*t^2 + 16*t*z^5 - 8*t*z^4 - 98*t*z^3 - 70*t*z^2 + 80*t*z + 133*t/2 - 4*z^6 + 12*z^5 + 15*z^4 - 28*z^3 - 12*z^2 + 21*z/4 - 17/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_56 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 56) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_56 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 144*t^7 + 192*t^6*z^2 - 336*t^6*z + 504*t^6 - 1296*t^5*z^2 + 2304*t^5*z - 972*t^5 + 864*t^4*z^4 - 3024*t^4*z^3 + 5832*t^4*z^2 - 5724*t^4*z + 1125*t^4 - 3888*t^3*z^4 + 13824*t^3*z^3 - 16200*t^3*z^2 + 7128*t^3*z - 675*t^3 + 1728*t^2*z^6 - 9072*t^2*z^5 + 21384*t^2*z^4 - 29160*t^2*z^3 + 20358*t^2*z^2 - 4509*t^2*z + 81*t^2 - 3888*t*z^6 + 20736*t*z^5 - 39852*t*z^4 + 33048*t*z^3 - 10773*t*z^2 + 729*t*z + 243*t/2 + 1296*z^8 - 9072*z^7 + 25272*z^6 - 35964*z^5 + 27621*z^4 - 10611*z^3 + 1215*z^2 + 243*z - 729/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-48*t^6 + 324*t^5 - 216*t^4*z^2 + 324*t^4*z - 756*t^4 + 972*t^3*z^2 - 1512*t^3*z + 783*t^3 - 432*t^2*z^4 + 1404*t^2*z^3 - 2430*t^2*z^2 + 2079*t^2*z - 324*t^2 + 972*t*z^4 - 3240*t*z^3 + 3240*t*z^2 - 972*t*z - 243*t/4 - 324*z^6 + 1620*z^5 - 2997*z^4 + 2592*z^3 - 972*z^2 + 243*z/4 + 243/4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_57 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 57) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_57 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 3*t + 2*z^2 - 3*z + 3/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 112*t^7 + 192*t^6*z^2 - 240*t^6*z + 232*t^6 - 1008*t^5*z^2 + 1296*t^5*z - 112*t^5 + 864*t^4*z^4 - 2160*t^4*z^3 + 2664*t^4*z^2 - 1728*t^4*z - 152*t^4 - 3024*t^3*z^4 + 7776*t^3*z^3 - 4800*t^3*z^2 - 264*t^3*z + 248*t^3 + 1728*t^2*z^6 - 6480*t^2*z^5 + 9720*t^2*z^4 - 7776*t^2*z^3 + 2016*t^2*z^2 + 1296*t^2*z - 128*t^2 - 3024*t*z^6 + 11664*t*z^5 - 13392*t*z^4 + 2376*t*z^3 + 2880*t*z^2 - 432*t*z - 40*t + 1296*z^8 - 6480*z^7 + 11448*z^6 - 7776*z^5 + 216*z^4 + 1944*z^3 - 672*z^2 - 24*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-48*t^6 + 252*t^5 - 216*t^4*z^2 + 108*t^4*z - 396*t^4 + 756*t^3*z^2 - 432*t^3*z + 147*t^3 - 432*t^2*z^4 + 756*t^2*z^3 - 810*t^2*z^2 + 135*t^2*z - 63*t^2/2 + 756*t*z^4 - 1404*t*z^3 + 351*t*z^2 + 459*t*z + 441*t/4 - 324*z^6 + 972*z^5 - 837*z^4 + 27*z^3 + 837*z^2/4 - 297*z/4 - 525/16)*hf
  · have hr : (16*t^8 - 112*t^7 - 48*t^6*z + 184*t^6 + 288*t^5*z + 140*t^5 - 252*t^4*z - 440*t^4 - 744*t^3*z + 71*t^3 + 639*t^2*z + 329*t^2/2 + 612*t*z - 259*t/4 - 165*z/4 + 55/16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_58 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 58) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_58 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 80*t^7 + 160*t^6*z^2 + 160*t^6*z + 40*t^6 - 256*t^5*z^3 - 240*t^5*z^2 + 312*t^5*z + 220*t^5 + 304*t^4*z^4 + 80*t^4*z^3 - 624*t^4*z^2 - 496*t^4*z - 191*t^4 - 256*t^3*z^5 + 80*t^3*z^4 + 1016*t^3*z^3 + 220*t^3*z^2 - 782*t^3*z - 89*t^3 + 160*t^2*z^6 - 240*t^2*z^5 - 624*t^2*z^4 + 220*t^2*z^3 + 762*t^2*z^2 + 444*t^2*z + 88*t^2 - 64*t*z^7 + 160*t*z^6 + 312*t*z^5 - 496*t*z^4 - 782*t*z^3 + 444*t*z^2 + 1201*t*z/2 - 53*t + 16*z^8 - 80*z^7 + 40*z^6 + 220*z^5 - 191*z^4 - 89*z^3 + 88*z^2 - 53*z + 55/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 64*t^5*z + 188*t^5 - 76*t^4*z^2 - 172*t^4*z - 169*t^4 + 64*t^3*z^3 + 108*t^3*z^2 - 54*t^3*z - 190*t^3 - 40*t^2*z^4 - 20*t^2*z^3 + 126*t^2*z^2 + 202*t^2*z + 182*t^2 + 16*t*z^5 - 8*t*z^4 - 98*t*z^3 - 70*t*z^2 + 80*t*z + 133*t/2 - 4*z^6 + 12*z^5 + 15*z^4 - 28*z^3 - 12*z^2 + 21*z/4 - 17/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_59 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 59) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_59 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 192*t^7*z - 16*t^7 + 1056*t^6*z^2 - 104*t^6 - 3456*t^5*z^3 + 720*t^5*z^2 + 936*t^5*z + 68*t^5 + 7344*t^4*z^4 - 3888*t^4*z^3 - 3168*t^4*z^2 + 192*t^4*z + 157*t^4 - 10368*t^3*z^5 + 9936*t^3*z^4 + 4968*t^3*z^3 - 2316*t^3*z^2 - 1170*t^3*z - 55*t^3 + 9504*t^2*z^6 - 14256*t^2*z^5 - 2592*t^2*z^4 + 5940*t^2*z^3 + 1638*t^2*z^2 - 360*t^2*z - 29*t^2 - 5184*t*z^7 + 11232*t*z^6 - 1944*t*z^5 - 6264*t*z^4 + 486*t*z^3 + 1098*t*z^2 + 1011*t*z/2 - 59*t/2 + 1296*z^8 - 3888*z^7 + 2376*z^6 + 2268*z^5 - 2295*z^4 + 27*z^3 + 300*z^2 - 153*z/2 + 55/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-264*t^6 + 864*t^5*z + 1548*t^5 - 1836*t^4*z^2 - 2700*t^4*z - 4149*t^4 + 2592*t^3*z^3 + 2700*t^3*z^2 + 3510*t^3*z + 6924*t^3 - 2376*t^2*z^4 - 1188*t^2*z^3 - 1134*t^2*z^2 - 3456*t^2*z - 7038*t^2 + 1296*t*z^5 - 216*t*z^4 - 270*t*z^3 + 1080*t*z^2 + 2106*t*z + 7335*t/2 - 324*z^6 + 324*z^5 + 135*z^4 - 378*z^3 - 216*z^2 - 1377*z/4 - 1419/2)*hf
  · have hr : (16*t^8 - 112*t^7 - 48*t^6*z + 184*t^6 + 288*t^5*z + 140*t^5 - 252*t^4*z - 440*t^4 - 744*t^3*z + 71*t^3 + 639*t^2*z + 329*t^2/2 + 612*t*z - 259*t/4 - 165*z/4 + 55/16:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_60 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 60) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_60 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z - 240*t^7 + 448*t^6*z^2 - 1680*t^6*z + 1368*t^6 + 896*t^5*z^3 - 5040*t^5*z^2 + 8352*t^5*z - 3780*t^5 + 1120*t^4*z^4 - 8400*t^4*z^3 + 21096*t^4*z^2 - 19764*t^4*z + 5256*t^4 + 896*t^3*z^5 - 8400*t^3*z^4 + 28224*t^3*z^3 - 40392*t^3*z^2 + 22320*t^3*z - 3321*t^3 + 448*t^2*z^6 - 5040*t^2*z^5 + 21096*t^2*z^4 - 40392*t^2*z^3 + 34128*t^2*z^2 - 9963*t^2*z + 1053*t^2/2 + 128*t*z^7 - 1680*t*z^6 + 8352*t*z^5 - 19764*t*z^4 + 22320*t*z^3 - 9963*t*z^2 + 972*t*z + 729*t/4 + 16*z^8 - 240*z^7 + 1368*z^6 - 3780*z^5 + 5256*z^4 - 3321*z^3 + 1053*z^2/2 + 729*z/4 - 729/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 - 224*t^5*z + 812*t^5 - 280*t^4*z^2 + 1540*t^4*z - 2124*t^4 - 224*t^3*z^3 + 1652*t^3*z^2 - 3696*t^3*z + 2293*t^3 - 112*t^2*z^4 + 1036*t^2*z^3 - 3174*t^2*z^2 + 3491*t^2*z - 1513*t^2/2 - 32*t*z^5 + 356*t*z^4 - 1368*t*z^3 + 2116*t*z^2 - 1006*t*z - 201*t/4 - 4*z^6 + 52*z^5 - 237*z^4 + 458*z^3 - 1355*z^2/4 + 153*z/4 + 473/16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_61 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 61) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_61 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t + 3/2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z - 176*t^7 + 448*t^6*z^2 - 1232*t^6*z + 664*t^6 + 896*t^5*z^3 - 3696*t^5*z^2 + 4128*t^5*z - 968*t^5 + 1120*t^4*z^4 - 6160*t^4*z^3 + 10536*t^4*z^2 - 5416*t^4*z + 208*t^4 + 896*t^3*z^5 - 6160*t^3*z^4 + 14144*t^3*z^3 - 11408*t^3*z^2 + 1048*t^3*z + 616*t^3 + 448*t^2*z^6 - 3696*t^2*z^5 + 10536*t^2*z^4 - 11408*t^2*z^3 + 1680*t^2*z^2 + 2568*t^2*z - 344*t^2 + 128*t*z^7 - 1232*t*z^6 + 4128*t*z^5 - 5416*t*z^4 + 1048*t*z^3 + 2568*t*z^2 - 544*t*z - 32*t + 16*z^8 - 176*z^7 + 664*z^6 - 968*z^5 + 208*z^4 + 616*z^3 - 344*z^2 - 32*z + 16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 - 224*t^5*z + 476*t^5 - 280*t^4*z^2 + 980*t^4*z - 604*t^4 - 224*t^3*z^3 + 1092*t^3*z^2 - 1296*t^3*z - 13*t^3 - 112*t^2*z^4 + 700*t^2*z^3 - 1206*t^2*z^2 + 265*t^2*z + 823*t^2/2 - 32*t*z^5 + 244*t*z^4 - 536*t*z^3 + 221*t*z^2 + 314*t*z - 277*t/4 - 4*z^6 + 36*z^5 - 93*z^4 + 47*z^3 + 261*z^2/4 - 141*z/4 - 13/16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_62 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 62) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_62 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 112*t^7 - 48*t^6*z + 184*t^6 + 288*t^5*z + 140*t^5 - 252*t^4*z - 440*t^4 - 744*t^3*z + 71*t^3 + 639*t^2*z + 329*t^2/2 + 612*t*z - 259*t/4 - 165*z/4 + 55/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_8_63 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (1/2) (z) t 63) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : False := by
  apply cell_8_63 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (-48*t*z^6 + 288*t*z^5 - 252*t*z^4 - 744*t*z^3 + 639*t*z^2 + 612*t*z - 165*t/4 + 16*z^8 - 112*z^7 + 184*z^6 + 140*z^5 - 440*z^4 + 71*z^3 + 329*z^2/2 - 259*z/4 + 55/16:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(12*t*z^4 - 48*t*z^3 - 36*t*z^2 + 126*t*z + 405*t/4 - 4*z^6 + 20*z^5 - 5*z^4 - 50*z^3 + 45*z^2/4 + 69*z/4 - 151/16)*hf


private def limit8 (z t : ℝ) : Fin 64→Prop := ![False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,((t - 2*z:ℝ)=0),False,False,False,False,False,False,False,((t + z - 2:ℝ)=0),False,False,False,((t - z - 1:ℝ)=0),False,((t + z - 2:ℝ)=0),((t - z - 1:ℝ)=0),False,False,False,False,False,False,(((0:ℝ):ℝ)=0),False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,((t + z - 2:ℝ)=0),False,False,False,False,False,False,False,False,False,False]

private def hue8 : Fin 64→Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_8_15_23 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit8 z t 15) (hj : limit8 z t 23) (_he : edge4 (1) (1) (1) (profile4 (1/2) (z) t 15) (profile4 (1/2) (z) t 23) (1/2) (z) t=0) : False := by
  apply pair_8_15_23 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_8_15_27 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit8 z t 15) (hj : limit8 z t 27) (_he : edge4 (1) (1) (1) (profile4 (1/2) (z) t 15) (profile4 (1/2) (z) t 27) (1/2) (z) t=0) : False := by
  apply pair_8_15_27 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_8_23_27 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit8 z t 23) (hj : limit8 z t 27) (_he : edge4 (1) (1) (1) (profile4 (1/2) (z) t 23) (profile4 (1/2) (z) t 27) (1/2) (z) t=0) : False := by
  apply pair_8_23_27 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_8_29_30 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit8 z t 29) (hj : limit8 z t 30) (_he : edge4 (1) (1) (1) (profile4 (1/2) (z) t 29) (profile4 (1/2) (z) t 30) (1/2) (z) t=0) : False := by
  apply pair_8_29_30 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma exclude_field_8 (z t : ℝ) (hf : 4*z^2 - 8*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(1/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (g : Fin 5→Fin 64) (hinj : Function.Injective g)
    (hc : ∀ i, cell (1) (1) (1) (profile4 (1/2) (z) t (g i)) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t)
    (he : ∀ i j : Fin 5, i≠j → edge4 (1) (1) (1) (profile4 (1/2) (z) t (g i)) (profile4 (1/2) (z) t (g j)) (1/2) (z) t=0) : False := by
  have row (k : Fin 64) (hh : cell (1) (1) (1) (profile4 (1/2) (z) t k) ((1/2),(1/2),(z)) ((1/2),(z),(1/2)) (1/2) (z) t) : limit8 z t k := by
    fin_cases k
    · exact row_8_0 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_1 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_2 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_3 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_4 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_5 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_6 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_7 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_8 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_9 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_10 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_11 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_12 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_13 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_14 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_15 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_16 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_17 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_18 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_19 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_20 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_21 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_22 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_23 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_24 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_25 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_26 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_27 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_28 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_29 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_30 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_31 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_32 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_33 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_34 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_35 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_36 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_37 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_38 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_39 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_40 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_41 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_42 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_43 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_44 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_45 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_46 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_47 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_48 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_49 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_50 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_51 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_52 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_53 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_54 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_55 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_56 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_57 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_58 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_59 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_60 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_61 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_62 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_8_63 z t hf hn0 hn1 hn2 hn3 hh
  have allowed (k : Fin 64) (hh : limit8 z t k) : k∈([15,23,27,29,30,37,53]:List (Fin 64)) := by
    fin_cases k <;> first | decide | exact False.elim hh
  have cert : ∀ i j : Fin 64, i∈([15,23,27,29,30,37,53]:List (Fin 64)) → j∈([15,23,27,29,30,37,53]:List (Fin 64)) → i<j → hue8 i=hue8 j → (i,j)∈([(15,23),(15,27),(23,27),(29,30)]:List (Fin 64×Fin 64)) := by decide
  have bad (i j : Fin 64) (hi : limit8 z t i) (hj : limit8 z t j) (hlt : i<j) (hc : hue8 i=hue8 j) (hb : edge4 (1) (1) (1) (profile4 (1/2) (z) t i) (profile4 (1/2) (z) t j) (1/2) (z) t=0) : False := by
    have h := cert i j (allowed i hi) (allowed j hj) hlt hc
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact rowpair_8_15_23 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_8_15_27 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_8_23_27 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_8_29_30 z t hf hn0 hn1 hn2 hn3 hi hj hb
  have hi : Function.Injective (fun i : Fin 5 => hue8 (g i)) := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne (show g i≠g j from fun e => hne (hinj e)) with hl|hl
    · exact bad _ _ (row _ (hc i)) (row _ (hc j)) hl h (he i j hne)
    · exact bad _ _ (row _ (hc j)) (row _ (hc i)) hl h.symm (he j i (Ne.symm hne))
  have hh := Fintype.card_le_of_injective _ hi
  norm_num at hh

private lemma cell_10_0 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z^2 + 12*z - 8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^2/2 - 5*z/2 + 1/2)*h0 + (z - 5)*hf
  norm_num at hh

private lemma cell_10_1 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4*z^2 + 22*z - 12:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-3*z^2/2 + 8*z - 5/2)*h0 + (29 - 6*z)*hf
  norm_num at hh

private lemma cell_10_2 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^2/2 - 5*z/2)*h0 + (-1)*hf
  norm_num at hh

private lemma cell_10_3 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^2 + 10*z - 10) + 2*z:ℝ)=0) (h2 : (16*t^8 + t^7*(32*z^2 - 144*z - 112) + t^6*(-400*z^2 + 2000*z - 160) + t^5*(1760*z^2 - 9312*z + 2624) + t^4*(-3520*z^2 + 19248*z - 6608) + t^3*(3408*z^2 - 18960*z + 6480) + t^2*(-1600*z^2 + 8784*z - 2432) + t*(256*z^2 - 928*z - 336) - 224*z + 256:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-890*z^2/49 + 9535*z/98 - 1383/49) + t^6*(18141*z^2/98 - 48588*z/49 + 28191/98) + t^5*(-75007*z^2/98 + 200897*z/49 - 58293/49) + t^4*(81358*z^2/49 - 871651*z/98 + 126506/49) + t^3*(-100081*z^2/49 + 536138*z/49 - 155681/49) + t^2*(70197*z^2/49 - 376051*z/49 + 109204/49) + t*(-26240*z^2/49 + 140562*z/49 - 40791/49) + 8207*z^2/98 - 21972*z/49 + 12689/98)*h0 + (t*(445*z^2/196 - 9535*z/784 + 1383/392) - 759*z^2/784 + 4065*z/784 - 587/392)*h2 + (-5340*t^8*z/49 + 21485*t^8/49 + 64159*t^7*z/49 - 39569*t^7/7 - 289782*t^6*z/49 + 1301306*t^6/49 + 637806*t^5*z/49 - 2911316*t^5/49 - 746282*t^4*z/49 + 3380310*t^4/49 + 480061*t^3*z/49 - 2069524*t^3/49 - 156860*t^2*z/49 + 540961*t^2/49 + 20351*t*z/49 + 5465*t/49 - 18833/49)*hf
  norm_num at hh

private lemma cell_10_4 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4*z^2 + 22*z - 12:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-3*z^2/2 + 8*z - 5/2)*h0 + (29 - 6*z)*hf
  norm_num at hh

private lemma cell_10_5 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4*z^2 + 24*z - 14:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z^2 - 16*z + 9/2)*h0 + (12*z - 64)*hf
  norm_num at hh

private lemma cell_10_6 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (9*z^2/2 - 24*z + 13/2)*h0 + (-27)*hf
  norm_num at hh

private lemma cell_10_7 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z^2 + 22*z - 14):ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z^2 + 176*z - 112) + t^6*(-48*z^2 + 368*z - 208) + t^5*(256*z^2 - 1584*z + 912) + t^4*(208*z^2 - 384*z + 160) + t^3*(-560*z^2 + 2800*z - 1568) + t^2*(560*z^2 - 1232*z + 560):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(8791*z^2/2548 - 11773*z/637 + 13667/2548) + t^4*(99*z^2/52 - 3713*z/364 + 270/91) + t^3*(457*z^2/364 - 612*z/91 + 709/364) + t^2*(267*z^2/364 - 1431*z/364 + 102/91) + t*(141*z^2/182 - 1513*z/364 + 107/91) + 5*z^2/14 - 27*z/14 + 3/7)*h0 + (-8791*z^2/20384 + 11773*z/5096 - 13667/20384)*h1 + (-26373*t^6*z/1274 + 185231*t^6/1274 + 5783*t^5*z/49 - 413488*t^5/637 + 120681*t^4*z/1274 - 168555*t^4/1274 - 6203*t^3*z/26 + 94455*t^3/91 + 44519*t^2*z/182 - 5475*t^2/14 + 10*t*z/7 - 7*t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_10_8 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z^2/2 - 5*z/2)*h0 + (-1)*hf
  norm_num at hh

private lemma cell_10_9 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (9*z^2/2 - 24*z + 13/2)*h0 + (-27)*hf
  norm_num at hh

private lemma cell_10_10 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*z^2 - 10*z + 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (19*z^2/14 - 52*z/7 + 41/14)*h0 + (75/7 - 38*z/7)*hf
  norm_num at hh

private lemma cell_10_11 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^2 + 12*z - 10) + 2*z^2 - 10*z + 6:ℝ)=0) (h1 : (16*t^8 + t^7*(32*z^2 - 144*z + 16) + t^6*(-144*z^2 + 1136*z - 576) + t^5*(560*z^2 - 1680*z + 784) + t^4*(2880*z^2 - 5808*z + 2560) + t^3*(5600*z^2 - 1680*z - 1232) + t^2*(26592*z^2 - 21584*z + 2880) + t*(41136*z^2 - 42800*z + 10512) + 103824*z^2 - 98640*z + 20496:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-1829514*z^2/18473 + 9800410*z/18473 - 5688565/36946) + t^6*(7052088*z^2/18473 - 75554417*z/36946 + 21930469/36946) + t^5*(-10038684*z^2/18473 + 53777814*z/18473 - 31235909/36946) + t^4*(6152689*z^2/18473 - 65920635*z/36946 + 19144507/36946) + t^3*(-1978219*z^2/36946 + 10582473*z/36946 - 3001907/36946) + t^2*(-1144615*z^2/36946 + 6138361*z/36946 - 906835/18473) + t*(432545*z^2/36946 - 2296585*z/36946 + 285434/18473) + 8382*z^2/18473 - 46625*z/18473 + 42619/36946)*h0 + (t*(914757*z^2/73892 - 4900205*z/73892 + 5688565/295568) - 5298663*z^2/295568 + 3547981*z/36946 - 8236483/295568)*h1 + (-10977084*t^8*z/18473 + 47825376*t^8/18473 + 61291782*t^7*z/18473 - 370978772*t^7/18473 - 209935491*t^6*z/18473 + 116624076*t^6/2639 - 33906853*t^5*z/1421 + 493172*t^5/29 - 341184057*t^4*z/18473 - 1685227399*t^4/18473 - 4225938882*t^3*z/18473 + 1658784388*t^3/18473 - 599405922*t^2*z/18473 + 77467846*t^2/637 - 10120985900*t*z/18473 + 20628373*t/203 + 34383007443*z/18473 - 10550825339/18473)*hf
  norm_num at hh

private lemma cell_10_12 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^2 + 10*z - 10) + 2*z:ℝ)=0) (h1 : (16*t^8 + t^7*(32*z^2 - 144*z - 112) + t^6*(-400*z^2 + 2000*z - 160) + t^5*(1760*z^2 - 9312*z + 2624) + t^4*(-3520*z^2 + 19248*z - 6608) + t^3*(3408*z^2 - 18960*z + 6480) + t^2*(-1600*z^2 + 8784*z - 2432) + t*(256*z^2 - 928*z - 336) - 224*z + 256:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-890*z^2/49 + 9535*z/98 - 1383/49) + t^6*(18141*z^2/98 - 48588*z/49 + 28191/98) + t^5*(-75007*z^2/98 + 200897*z/49 - 58293/49) + t^4*(81358*z^2/49 - 871651*z/98 + 126506/49) + t^3*(-100081*z^2/49 + 536138*z/49 - 155681/49) + t^2*(70197*z^2/49 - 376051*z/49 + 109204/49) + t*(-26240*z^2/49 + 140562*z/49 - 40791/49) + 8207*z^2/98 - 21972*z/49 + 12689/98)*h0 + (t*(445*z^2/196 - 9535*z/784 + 1383/392) - 759*z^2/784 + 4065*z/784 - 587/392)*h1 + (-5340*t^8*z/49 + 21485*t^8/49 + 64159*t^7*z/49 - 39569*t^7/7 - 289782*t^6*z/49 + 1301306*t^6/49 + 637806*t^5*z/49 - 2911316*t^5/49 - 746282*t^4*z/49 + 3380310*t^4/49 + 480061*t^3*z/49 - 2069524*t^3/49 - 156860*t^2*z/49 + 540961*t^2/49 + 20351*t*z/49 + 5465*t/49 - 18833/49)*hf
  norm_num at hh

private lemma cell_10_13 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z^2 + 22*z - 14):ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z^2 + 240*z - 240) + t^6*(256*z^2 - 1440*z + 1072) + t^5*(-560*z^2 + 3136*z - 2128) + t^4*(416*z^2 - 2784*z + 1888) + t^3*(112*z^2 - 784*z + 336) + t^2*(-784*z^2 + 4032*z - 2240) + t*(672*z^2 - 2352*z + 1232):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(-3686*z^2/49 + 39491*z/98 - 11463/98) + t^5*(2858*z^2/7 - 15310*z/7 + 4444/7) + t^4*(-6135*z^2/7 + 65729*z/14 - 19079/14) + t^3*(6663*z^2/7 - 5099*z + 20721/14) + t^2*(-551*z^2 + 41323*z/14 - 11995/14) + t*(2213*z^2/14 - 11855*z/14 + 3441/14) - 227*z^2/14 + 608*z/7 - 355/14)*h0 + (1843*z^2/196 - 39491*z/784 + 11463/784)*h1 + (-29488*t^7/49 - 37928*t^6*z/49 + 198956*t^6/49 + 1760*t^5*z - 63523*t^5/7 - 5108*t^4*z/49 + 253340*t^4/49 - 22800*t^3*z/7 + 121795*t^3/7 + 56030*t^2*z/7 - 253702*t^2/7 - 44686*t*z/7 + 128571*t/7)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_10_14 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^2 + 12*z - 10) + 2*z^2 - 10*z + 6:ℝ)=0) (h1 : (16*t^8 + t^7*(32*z^2 - 80*z - 112) + t^6*(-160*z^2 + 1312*z - 192) + t^5*(1760*z^2 - 7376*z + 2784) + t^4*(-544*z^2 + 9232*z - 4192) + t^3*(2336*z^2 - 2624*z - 400) + t^2*(2368*z^2 - 6448*z + 3648) + t*(80*z^2 - 1888*z + 1072) - 352*z^2 + 640*z - 256:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-40367*z^2/1274 + 216243*z/1274 - 62775/1274) + t^6*(163080*z^2/637 - 873604*z/637 + 507179/1274) + t^5*(-527812*z^2/637 + 5654843*z/1274 - 820665/637) + t^4*(882844*z^2/637 - 9458593*z/1274 + 2745481/1274) + t^3*(-1647931*z^2/1274 + 4413958*z/637 - 2563133/1274) + t^2*(432182*z^2/637 - 4630285*z/1274 + 1343855/1274) + t*(-120095*z^2/637 + 1286533*z/1274 - 186380/637) + 2277*z^2/98 - 6101*z/49 + 1789/49)*h0 + (t*(40367*z^2/10192 - 216243*z/10192 + 62775/10192) - 9959*z^2/10192 + 26673*z/5096 - 15469/10192)*h1 + (-121101*t^8*z/637 + 366160*t^8/637 + 790115*t^7*z/637 - 5010567*t^7/637 - 5921744*t^6*z/637 + 3368878*t^6/91 + 5289280*t^5*z/637 - 40353184*t^5/637 - 9645807*t^4*z/637 + 24879466*t^4/637 - 2008007*t^3*z/637 - 82009*t^3/637 + 167543*t^2*z/637 + 6620872*t^2/637 + 1207660*t*z/637 - 3391673*t/637 - 248699*z/637 + 386409/637)*hf
  norm_num at hh

private lemma cell_10_15 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(2*z^2 - 10*z + 6) + t*(-8*z^2 + 40*z - 24) + 4*z^2 - 18*z + 10:ℝ)=0) (h1 : (t^8*(144*z^2 - 416*z + 208) + t^7*(-784*z^2 + 1648*z - 736) + t^6*(1200*z^2 + 128*z - 576) + t^5*(-160*z^2 - 5184*z + 3392) + t^4*(-384*z^2 - 480*z + 480) + t^3*(-80*z^2 + 8720*z - 5584) + t^2*(-624*z^2 - 416*z + 528) + t*(464*z^2 - 3632*z + 2144) + 160*z^2 + 96*z - 128:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(257*z^2/1421 - 89*z/98 + 859/2842) + t^6*(-3571*z^2/1421 + 641*z/49 - 11089/2842) + t^5*(42241*z^2/2842 - 3863*z/49 + 64349/2842) + t^4*(-63711*z^2/1421 + 23503*z/98 - 97981/1421) + t^3*(197391*z^2/2842 - 36539*z/98 + 154395/1421) + t^2*(-70947*z^2/1421 + 13147*z/49 - 224387/2842) + t*(15760*z^2/1421 - 5813*z/98 + 48009/2842) + 4759*z^2/2842 - 899*z/98 + 4198/1421)*h0 + (t*(-51299*z^2/22736 + 2369*z/196 - 39899/11368) + 204275*z^2/22736 - 18867*z/392 + 79437/5684)*h1 + (461177*t^9*z/1421 - 1034797*t^9/1421 - 4342928*t^8*z/1421 + 7757857*t^8/1421 + 475347*t^7*z/49 - 11413270*t^7/1421 - 15522945*t^6*z/1421 - 4253089*t^6/203 + 2859*t^5*z/203 + 68568295*t^5/1421 + 833201*t^4*z/203 + 32023491*t^4/1421 - 1973164*t^3*z/1421 - 2227485*t^3/29 + 9859505*t^2*z/1421 - 1880103*t^2/1421 - 5454989*t*z/1421 + 43355909*t/1421 - 2052268*z/1421 - 2501425/1421)*hf
  norm_num at hh

private lemma cell_10_16 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (12*z - 8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (9*z^2/4 - 12*z + 13/4)*h0 + (-27)*hf
  norm_num at hh

private lemma cell_10_17 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4*z^2 + 26*z - 14:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-19*z^2/26 + 103*z/26 - 17/13)*h0 + (225/13 - 38*z/13)*hf
  norm_num at hh

private lemma cell_10_18 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h1 : (t*(1456*z^2 - 6160*z + 3360):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (-405*z^2/392 + 4339*z/784 - 1259/784)*h1 + (10530*t*z/7 - 37777*t/7)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_10_19 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z^2 + 18*z - 14) + 4*z^2 - 6*z + 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z^2 + 48*z - 112) + t^6*(432*z^2 + 272*z - 144) + t^5*(-4976*z^2 + 1504*z + 880) + t^4*(31904*z^2 - 28672*z + 5328) + t^3*(-111648*z^2 + 112928*z - 26448) + t^2*(221104*z^2 - 213456*z + 45824) + t*(-235088*z^2 + 218784*z - 43472) + 103824*z^2 - 98640*z + 20496:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(891*z^2/7 - 4773*z/7 + 2771/14) + t^6*(-54895*z^2/98 + 294067*z/98 - 42681/49) + t^5*(80141*z^2/98 - 214651*z/49 + 124613/98) + t^4*(-20085*z^2/49 + 215147*z/98 - 31214/49) + t^3*(601*z^2/98 - 1538*z/49 + 885/98) + t^2*(2273*z^2/98 - 12487*z/98 + 3569/98) + t*(-121*z^2/49 + 1675*z/98 - 485/98) - 71*z^2/98 + 193*z/98 - 11/98)*h0 + (t*(-891*z^2/56 + 4773*z/56 - 2771/112) + 6763*z^2/784 - 36229*z/784 + 5259/392)*h1 + (-10692*t^8/7 + 30798*t^7*z/7 + 861888*t^7/49 - 3791943*t^6*z/49 - 2266940*t^6/49 + 26735827*t^5*z/49 - 5193604*t^5/49 - 2049948*t^4*z + 35438253*t^4/49 + 219573764*t^3*z/49 - 1489040*t^3 - 276743409*t^2*z/49 + 82835723*t^2/49 + 180312887*t*z/49 - 53425856*t/49 - 43884965*z/49 + 13473487/49)*hf
  norm_num at hh

private lemma cell_10_20 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4*z^2 + 26*z - 14:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-19*z^2/26 + 103*z/26 - 17/13)*h0 + (225/13 - 38*z/13)*hf
  norm_num at hh

private lemma cell_10_21 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-6*z^2 + 32*z - 18:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-7*z^2 + 75*z/2 - 11)*h0 + (197 - 42*z)*hf
  norm_num at hh

private lemma cell_10_22 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z^2 + 8*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-5*z^2/2 + 27*z/2 - 9/2)*h0 + (17 - 5*z)*hf
  norm_num at hh

private lemma cell_10_23 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-6*z^2 + 30*z - 18) + 2*z^2 - 4*z + 2:ℝ)=0) (h2 : (16*t^8 + t^7*(-96*z^2 + 496*z - 368) + t^6*(688*z^2 - 3440*z + 2112) + t^5*(-1728*z^2 + 8160*z - 4704) + t^4*(1376*z^2 - 5744*z + 3184) + t^3*(1040*z^2 - 4816*z + 2672) + t^2*(-2048*z^2 + 7728*z - 4128) + t*(416*z^2 - 1088*z + 528) + 288*z^2 - 832*z + 416:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-43139*z^2/637 + 231090*z/637 - 67073/637) + t^6*(418017*z^2/1274 - 2239243*z/1274 + 649823/1274) + t^5*(-341697*z^2/637 + 1830363*z/637 - 1061787/1274) + t^4*(356543*z^2/1274 - 954838*z/637 + 552649/1274) + t^3*(39278*z^2/637 - 421009*z/1274 + 123187/1274) + t^2*(-58725*z^2/1274 + 314469*z/1274 - 90217/1274) + t*(-21341*z^2/1274 + 57277*z/637 - 17300/637) - 1805*z^2/637 + 19319*z/1274 - 2803/637)*h0 + (t*(43139*z^2/5096 - 115545*z/2548 + 67073/5096) + 9119*z^2/10192 - 48859*z/10192 + 14237/10192)*h2 + (258834*t^8*z/637 - 1213984*t^8/637 - 2314911*t^7*z/637 + 795037*t^7/49 + 6457708*t^6*z/637 - 26801085*t^6/637 - 4682033*t^5*z/637 + 16596935*t^5/637 - 6513179*t^4*z/637 + 24589294*t^4/637 + 10196118*t^3*z/637 - 31331549*t^3/637 - 1081294*t^2*z/637 + 969249*t^2/637 - 1779587*t*z/637 + 3973471*t/637 - 160532*z/637 + 363919/637)*hf
  norm_num at hh

private lemma cell_10_24 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h2 : (t*(1456*z^2 - 6160*z + 3360):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (-405*z^2/392 + 4339*z/784 - 1259/784)*h2 + (10530*t*z/7 - 37777*t/7)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_10_25 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z^2 + 8*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-5*z^2/2 + 27*z/2 - 9/2)*h0 + (17 - 5*z)*hf
  norm_num at hh

private lemma cell_10_26 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 14*z + 8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (4*z^2 - 43*z/2 + 13/2)*h0 + (51 - 8*z)*hf
  norm_num at hh

private lemma cell_10_27 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z^2 + 20*z - 14) + 4*z^2 - 20*z + 12:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z^2 + 112*z - 112) + t^6*(96*z^2 + 288*z - 176) + t^5*(-656*z^2 - 1408*z + 1184) + t^4*(4208*z^2 - 3840*z + 704) + t^3*(-11856*z^2 + 16064*z - 5424) + t^2*(17792*z^2 - 18304*z + 4416) + t*(-15488*z^2 + 12448*z - 1600) + 5936*z^2 - 5360*z + 992:ℝ)=0) (h2 : (16*t^8 + t^7*(-32*z^2 + 176*z - 240) + t^6*(80*z^2 - 496*z + 784) + t^5*(640*z^2 - 3072*z + 784) + t^4*(-2384*z^2 + 12272*z - 5936) + t^3*(1088*z^2 - 6992*z + 3472) + t^2*(2096*z^2 - 8896*z + 5040) + t*(80*z^2 + 624*z - 464) - 112*z^2 + 224*z - 96:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(4210783*z^2/8918 - 11278363*z/4459 + 6547591/8918) + t^12*(-20385101*z^2/4459 + 109200863*z/4459 - 31697977/4459) + t^11*(80645657*z^2/4459 - 432010386*z/4459 + 250801233/8918) + t^10*(-23532013*z^2/637 + 1764819611*z/8918 - 256139081/4459) + t^9*(174750697*z^2/4459 - 133731614*z/637 + 543460153/8918) + t^8*(-19499083*z^2/1274 + 731181873*z/8918 - 106120835/4459) + t^7*(-37221050*z^2/4459 + 398778689*z/8918 - 57877468/4459) + t^6*(45558011*z^2/4459 - 244049465*z/4459 + 141681133/8918) + t^5*(-22741519*z^2/8918 + 60911807*z/4459 - 17680261/4459) + t^4*(-2040130*z^2/4459 + 21857359*z/8918 - 3171919/4459) + t^3*(101068*z^2/637 - 3789584*z/4459 + 1098764/4459) + t^2*(742507*z^2/8918 - 568213*z/1274 + 1153623/8918) + t*(-21415*z^2/637 + 1605651*z/8918 - 232083/4459) + 14019*z^2/8918 - 75111*z/8918 + 11660/4459)*h0 + (t^7*(-4210783*z^2/71344 + 11278363*z/35672 - 6547591/71344) + t^6*(16323143*z^2/35672 - 87441377*z/35672 + 50763605/71344) + t^5*(-98442489*z^2/71344 + 527346161*z/71344 - 153073941/71344) + t^4*(18187431*z^2/8918 - 779425393*z/71344 + 56561389/17836) + t^3*(-109829891*z^2/71344 + 36771706*z/4459 - 42695229/17836) + t^2*(20695709*z^2/35672 - 110864757*z/35672 + 8045239/8918) + t*(-7510343*z^2/71344 + 40232119*z/71344 - 11678237/71344) + 70979*z^2/17836 - 760457*z/35672 + 441505/71344)*h1 + (-405*z^2/392 + 4339*z/784 - 1259/784)*h2 + (-12632349*t^14/4459 + 595300*t^13*z/4459 + 297462782*t^13/4459 - 161281765*t^12*z/4459 - 2393420763*t^12/4459 + 2346108493*t^11*z/4459 + 9031940994*t^11/4459 - 15477062788*t^10*z/4459 - 1168711090*t^10/343 + 60498912829*t^9*z/4459 - 2962003344*t^9/4459 - 156233238912*t^8*z/4459 + 62927205987*t^8/4459 + 281405852262*t^7*z/4459 - 128774110620*t^7/4459 - 362006353890*t^6*z/4459 + 10910905566*t^6/343 + 332194640296*t^5*z/4459 - 101721704603*t^5/4459 - 16304824073*t^4*z/343 + 52837765345*t^4/4459 + 89379332747*t^3*z/4459 - 20417687431*t^3/4459 - 22934371318*t^2*z/4459 + 5254222609*t^2/4459 + 3062164149*t*z/4459 - 767826929*t/4459 - 105876844*z/4459 + 28196185/4459)*hf
  norm_num at hh

private lemma cell_10_28 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z^2 + 18*z - 14) + 4*z^2 - 6*z + 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z^2 + 112*z - 240) + t^6*(288*z^2 - 320*z + 944) + t^5*(-1664*z^2 - 1984*z - 240) + t^4*(9488*z^2 + 5136*z - 3872) + t^3*(-37280*z^2 + 18352*z + 528) + t^2*(83152*z^2 - 75248*z + 15680) + t*(-98832*z^2 + 94912*z - 20656) + 50400*z^2 - 48192*z + 10208:ℝ)=0) (h2 : (16*t^8 + t^7*(-32*z^2 + 48*z - 112) + t^6*(432*z^2 + 272*z - 144) + t^5*(-4976*z^2 + 1504*z + 880) + t^4*(31904*z^2 - 28672*z + 5328) + t^3*(-111648*z^2 + 112928*z - 26448) + t^2*(221104*z^2 - 213456*z + 45824) + t*(-235088*z^2 + 218784*z - 43472) + 103824*z^2 - 98640*z + 20496:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(-1073757*z^2/4459 + 11504009*z/8918 - 3339295/8918) + t^12*(1201035*z^2/343 - 12867639*z/686 + 3735119/686) + t^11*(-99069872*z^2/4459 + 530706992*z/4459 - 308099047/8918) + t^10*(719678299*z^2/8918 - 1927620853*z/4459 + 1119069621/8918) + t^9*(-1647896063*z^2/8918 + 4413803766*z/4459 - 183029212/637) + t^8*(2464223089*z^2/8918 - 942899028*z/637 + 1915881567/4459) + t^7*(-1200379420*z^2/4459 + 6430307766*z/4459 - 3733080887/8918) + t^6*(1457239661*z^2/8918 - 7806282251*z/8918 + 1132974774/4459) + t^5*(-18413457*z^2/343 + 197278041*z/686 - 57264171/686) + t^4*(18268878*z^2/4459 - 195732007*z/8918 + 56812407/8918) + t^3*(26295877*z^2/8918 - 70428784*z/4459 + 40883553/8918) + t^2*(-9056855*z^2/8918 + 48509933*z/8918 - 1005895/637) + t*(948228*z^2/4459 - 725302*z/637 + 2949899/8918) - 166358*z^2/4459 + 889831*z/4459 - 256616/4459)*h0 + (t^7*(1073757*z^2/35672 - 11504009*z/71344 + 3339295/71344) + t^6*(-1410581*z^2/8918 + 60450685*z/71344 - 2506737/10192) + t^5*(20874171*z^2/71344 - 13977595*z/8918 + 8114615/17836) + t^4*(-14863839*z^2/71344 + 79624031*z/71344 - 23112613/71344) + t^3*(130593*z^2/5488 - 14277*z/112 + 101533/2744) + t^2*(1193363*z^2/71344 - 3196351*z/35672 + 115971/4459) + t*(8161*z^2/35672 - 87439*z/71344 + 12697/35672) + 39615*z^2/35672 - 53055*z/8918 + 30817/17836)*h1 + (-1259*z^2/784 + 843*z/98 - 489/196)*h2 + (4295028*t^14/4459 + 5524300*t^13*z/4459 - 161989216*t^13/4459 + 9480154*t^12*z/4459 + 253930675*t^12/637 - 78223528*t^11*z/343 - 9292618221*t^11/4459 + 1343173352*t^10*z/637 + 26475110964*t^10/4459 - 43182016489*t^9*z/4459 - 40367102057*t^9/4459 + 119787734579*t^8*z/4459 + 21287621002*t^8/4459 - 212752750510*t^7*z/4459 + 31092400739*t^7/4459 + 241113150086*t^6*z/4459 - 66302999510*t^6/4459 - 162616524745*t^5*z/4459 + 7333102643*t^5/637 + 51304947530*t^4*z/4459 - 16610386601*t^4/4459 + 179033203*t^3*z/637 - 204791505*t^3/4459 - 2464895133*t^2*z/4459 + 712742825*t^2/4459 - 1249831251*t*z/4459 + 350169938*t/4459 + 494529173*z/4459 - 21485545/637)*hf
  norm_num at hh

private lemma cell_10_29 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-6*z^2 + 30*z - 18) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-96*z^2 + 496*z - 368) + t^6*(688*z^2 - 3440*z + 2112) + t^5*(-1728*z^2 + 8160*z - 4704) + t^4*(1376*z^2 - 5744*z + 3184) + t^3*(1040*z^2 - 4816*z + 2672) + t^2*(-2048*z^2 + 7728*z - 4128) + t*(416*z^2 - 1088*z + 528) + 288*z^2 - 832*z + 416:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-43139*z^2/637 + 231090*z/637 - 67073/637) + t^6*(418017*z^2/1274 - 2239243*z/1274 + 649823/1274) + t^5*(-341697*z^2/637 + 1830363*z/637 - 1061787/1274) + t^4*(356543*z^2/1274 - 954838*z/637 + 552649/1274) + t^3*(39278*z^2/637 - 421009*z/1274 + 123187/1274) + t^2*(-58725*z^2/1274 + 314469*z/1274 - 90217/1274) + t*(-21341*z^2/1274 + 57277*z/637 - 17300/637) - 1805*z^2/637 + 19319*z/1274 - 2803/637)*h0 + (t*(43139*z^2/5096 - 115545*z/2548 + 67073/5096) + 9119*z^2/10192 - 48859*z/10192 + 14237/10192)*h1 + (258834*t^8*z/637 - 1213984*t^8/637 - 2314911*t^7*z/637 + 795037*t^7/49 + 6457708*t^6*z/637 - 26801085*t^6/637 - 4682033*t^5*z/637 + 16596935*t^5/637 - 6513179*t^4*z/637 + 24589294*t^4/637 + 10196118*t^3*z/637 - 31331549*t^3/637 - 1081294*t^2*z/637 + 969249*t^2/637 - 1779587*t*z/637 + 3973471*t/637 - 160532*z/637 + 363919/637)*hf
  norm_num at hh

private lemma cell_10_30 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z^2 + 20*z - 14) + 4*z^2 - 20*z + 12:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z^2 + 176*z - 240) + t^6*(80*z^2 - 496*z + 784) + t^5*(640*z^2 - 3072*z + 784) + t^4*(-2384*z^2 + 12272*z - 5936) + t^3*(1088*z^2 - 6992*z + 3472) + t^2*(2096*z^2 - 8896*z + 5040) + t*(80*z^2 + 624*z - 464) - 112*z^2 + 224*z - 96:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-81365*z^2/98 + 217932*z/49 - 63260/49) + t^6*(680769*z^2/98 - 1823405*z/49 + 529287/49) + t^5*(-2269633*z^2/98 + 12158189*z/98 - 3529191/98) + t^4*(1916767*z^2/49 - 10267918*z/49 + 2980477/49) + t^3*(-3443127*z^2/98 + 18444469*z/98 - 2676951/49) + t^2*(789641*z^2/49 - 8460059*z/98 + 1227880/49) + t*(-163647*z^2/49 + 1753277*z/98 - 254454/49) + 22409*z^2/98 - 60022*z/49 + 34861/98)*h0 + (t*(81365*z^2/784 - 54483*z/98 + 15815/98) - 82175*z^2/784 + 440203*z/784 - 127779/784)*h1 + (-81365*t^8/49 + 953093*t^7*z/49 - 3582164*t^7/49 - 8744529*t^6*z/49 + 5279292*t^6/7 + 27616719*t^5*z/49 - 17350831*t^5/7 - 32330217*t^4*z/49 + 21508521*t^4/7 + 4973903*t^3*z/49 - 5385269*t^3/7 + 6544948*t^2*z/49 - 3655384*t^2/7 + 1679836*t*z/49 - 351004*t/49 - 620043*z/49 + 975791/49)*hf
  norm_num at hh

private lemma cell_10_31 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(2*z^2 - 10*z + 6) + t*(-12*z^2 + 56*z - 32) + 10*z^2 - 34*z + 18:ℝ)=0) (h1 : (t^8*(144*z^2 - 416*z + 208) + t^7*(-2576*z^2 + 4592*z - 1888) + t^6*(23600*z^2 - 26720*z + 7424) + t^5*(-134976*z^2 + 125888*z - 25136) + t^4*(490928*z^2 - 454496*z + 89248) + t^3*(-1121088*z^2 + 1064288*z - 220784) + t^2*(1551760*z^2 - 1484160*z + 312688) + t*(-1189344*z^2 + 1131792*z - 235968) + 387072*z^2 - 368000*z + 76576:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(487*z^2/98 - 1305*z/49 + 759/98) + t^6*(-4931*z^2/98 + 26437*z/98 - 3842/49) + t^5*(7400*z^2/49 - 39736*z/49 + 23087/98) + t^4*(-8935*z^2/98 + 48795*z/98 - 14159/98) + t^3*(-20065*z^2/98 + 52387*z/49 - 30413/98) + t^2*(18441*z^2/98 - 94197*z/98 + 13621/49) + t*(355*z^2/7 - 2197*z/7 + 645/7) - 2965*z^2/98 + 8705*z/49 - 362/7)*h0 + (t*(-62595*z^2/784 + 335315*z/784 - 97333/784) + 33763*z^2/196 - 180865*z/196 + 105001/392)*h1 + (562868*t^9*z/49 - 180436*t^9/7 - 11285410*t^8*z/49 + 2025732*t^8/7 + 2327024*t^7*z - 69743712*t^7/49 - 727130730*t^6*z/49 + 249870046*t^6/49 + 3059793512*t^5*z/49 - 872493528*t^5/49 - 8529801132*t^4*z/49 + 2514930126*t^4/49 + 15533805612*t^3*z/49 - 4800678916*t^3/49 - 17751014370*t^2*z/49 + 5539621664*t^2/49 + 11553210968*t*z/49 - 3562782876*t/49 - 3267163159*z/49 + 1005023911/49)*hf
  norm_num at hh

private lemma cell_10_32 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z^2 - 2*z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (31*z^2/58 - 80*z/29 + 9/29)*h0 + (-93*z/29 - 47/29)*hf
  norm_num at hh

private lemma cell_10_33 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 + 6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-17*z^2/13 + 185*z/26 - 67/26)*h0 + (34*z/13 + 121/13)*hf
  norm_num at hh

private lemma cell_10_34 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 5/2)*h0 + (-1)*hf
  norm_num at hh

private lemma cell_10_35 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^2 + 4*z - 6) + 8*z^2 - 6*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(32*z^2 - 400*z + 144) + t^6*(1200*z^2 - 48*z - 224) + t^5*(-22816*z^2 + 21056*z - 4384) + t^4*(224160*z^2 - 213808*z + 44944) + t^3*(-1370960*z^2 + 1303952*z - 271600) + t^2*(5139104*z^2 - 4886960*z + 1017376) + t*(-10793664*z^2 + 10265952*z - 2138000) + 9728768*z^2 - 9253376*z + 1927232:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-1711*z^2/14 + 64159*z/98 - 18621/98) + t^6*(34422*z^2/49 - 368791*z/98 + 53527/49) + t^5*(-147215*z^2/98 + 788619*z/98 - 114467/49) + t^4*(139415*z^2/98 - 746821*z/98 + 216767/98) + t^3*(-49741*z^2/98 + 133194*z/49 - 77269/98) + t^2*(-653*z^2/98 + 3753*z/98 - 1093/98) + t*(674*z^2/49 - 7821*z/98 + 2235/98) + 41*z^2/98 + 397*z/98 - 80/49)*h0 + (t*(1711*z^2/112 - 64159*z/784 + 18621/784) - 19449*z^2/784 + 104185*z/784 - 7559/196)*h1 + (-5133*t^8*z/7 + 300270*t^8/49 - 742625*t^7*z/49 - 1101535*t^7/49 + 2587898*t^6*z/7 - 3668227*t^6/49 - 194803769*t^5*z/49 + 59634549*t^5/49 + 1298122334*t^4*z/49 - 57225274*t^4/7 - 787604256*t^3*z/7 + 242459893*t^3/7 + 14326638174*t^2*z/49 - 4410825379*t^2/49 - 20402969443*t*z/49 + 6283224907*t/49 + 11825925388*z/49 - 3641986881/49)*hf
  norm_num at hh

private lemma cell_10_36 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 + 6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-17*z^2/13 + 185*z/26 - 67/26)*h0 + (34*z/13 + 121/13)*hf
  norm_num at hh

private lemma cell_10_37 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (9*z^2/2 - 24*z + 13/2)*h0 + (-27)*hf
  norm_num at hh

private lemma cell_10_38 (z t : ℝ) (_hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) : ((0:ℝ):ℝ)=0 := by
  rfl

private lemma cell_10_39 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z^2 + 16*z - 10) + 6*z^2 - 10*z + 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z^2 - 16*z + 16) + t^6*(960*z^2 - 800*z + 112) + t^5*(-12656*z^2 + 11904*z - 2416) + t^4*(98752*z^2 - 94112*z + 19680) + t^3*(-474224*z^2 + 450544*z - 93616) + t^2*(1374416*z^2 - 1307040*z + 272128) + t*(-2198464*z^2 + 2092176*z - 436240) + 1488224*z^2 - 1415808*z + 295008:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(-2956*z^2/49 + 15835*z/49 - 9193/98) + t^5*(-627*z^2/49 + 6717*z/98 - 975/49) + t^4*(1307*z^2/98 - 3496*z/49 + 2029/98) + t^3*(-1019*z^2/98 + 5385*z/98 - 1563/98) + t^2*(-29*z^2/98 + 233*z/49 - 72/49) + t*(-107*z^2/98 - 83*z/98 + 27/98) + 87*z^2/98 + 93*z/98 - 29/49)*h0 + (739*z^2/98 - 15835*z/392 + 9193/784)*h1 + (53208*t^7/49 - 339492*t^6*z/49 + 57744*t^6/49 + 4682768*t^5*z/49 - 1403751*t^5/49 - 36494823*t^4*z/49 + 1617017*t^4/7 + 25032681*t^3*z/7 - 53790622*t^3/49 - 507846839*t^2*z/49 + 156354063*t^2/49 + 812332943*t*z/49 - 250646850*t/49 - 549899029*z/49 + 169500418/49)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_10_40 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z^2 - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 5/2)*h0 + (-1)*hf
  norm_num at hh

private lemma cell_10_41 (z t : ℝ) (_hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) : ((0:ℝ):ℝ)=0 := by
  rfl

private lemma cell_10_42 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z^2 - 11*z + 9/2)*h0 + (8)*hf
  norm_num at hh

private lemma cell_10_43 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^2 + 6*z - 6) + 4*z^2 - 8*z + 4:ℝ)=0) (h2 : (16*t^8 + t^7*(32*z^2 - 272*z + 16) + t^6*(-48*z^2 + 1872*z - 640) + t^5*(-1744*z^2 - 2768*z + 1424) + t^4*(11040*z^2 - 6640*z + 928) + t^3*(-30368*z^2 + 27952*z - 6224) + t^2*(44608*z^2 - 42352*z + 9088) + t*(-33392*z^2 + 32208*z - 6960) + 9552*z^2 - 9296*z + 2032:ℝ)=0) : False := by
  have hh : ((t-(z^2 - 5*z + 3)))*(1:ℝ)=0 := by linear_combination (t^6*(1518*z^2/49 - 8130*z/49 + 4703/98) + t^5*(-23199*z^2/98 + 62134*z/49 - 18020/49) + t^4*(68449*z^2/98 - 366707*z/98 + 106601/98) + t^3*(-97855*z^2/98 + 262112*z/49 - 76143/49) + t^2*(35129*z^2/49 - 376295*z/98 + 108895/98) + t*(-12168*z^2/49 + 65192*z/49 - 37935/98) + 3099*z^2/98 - 8284*z/49 + 4647/98)*h0 + (-759*z^2/196 + 4065*z/196 - 4703/784)*h2 + (9108*t^7*z/49 - 7836*t^7/7 - 38379*t^6*z/49 + 412247*t^6/49 - 216077*t^5*z/49 - 962736*t^5/49 + 1860087*t^4*z/49 + 506181*t^4/49 - 5496360*t^3*z/49 + 1160275*t^3/49 + 8299516*t^2*z/49 - 2335062*t^2/49 - 6284361*t*z/49 + 1955945*t/49 + 258042*z/7 - 587840/49)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_10_44 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^2 + 4*z - 6) + 8*z^2 - 6*z + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(32*z^2 - 336*z + 16) + t^6*(480*z^2 + 1856*z - 480) + t^5*(-12976*z^2 + 5376*z - 512) + t^4*(132336*z^2 - 114288*z + 22576) + t^3*(-821680*z^2 + 769440*z - 158624) + t^2*(3240672*z^2 - 3074720*z + 639120) + t*(-7515408*z^2 + 7145776*z - 1487856) + 7882368*z^2 - 7496736*z + 1561248:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(9694*z^2/637 - 103879*z/1274 + 15123/637) + t^6*(-13325*z^2/98 + 35694*z/49 - 20757/98) + t^5*(584121*z^2/1274 - 3129213*z/1274 + 908981/1274) + t^4*(-446431*z^2/637 + 2391518*z/637 - 1388729/1274) + t^3*(256261*z^2/637 - 1372692*z/637 + 796409/1274) + t^2*(68324*z^2/637 - 366312*z/637 + 107410/637) + t*(-132343*z^2/637 + 1418719*z/1274 - 206931/637) + 863*z^2/14 - 661*z/2 + 670/7)*h0 + (t*(-4847*z^2/2548 + 103879*z/10192 - 15123/5096) - 825*z^2/728 + 8833*z/1456 - 317/182)*h1 + (58164*t^8*z/637 - 31429*t^8/49 + 353963*t^7*z/637 + 2638378*t^7/637 - 14100147*t^6*z/637 - 2885081*t^6/637 + 147761752*t^5*z/637 - 36237465*t^5/637 - 68927440*t^4*z/49 + 271247636*t^4/637 + 3331820606*t^3*z/637 - 1032445055*t^3/637 - 6768246822*t^2*z/637 + 2105080492*t^2/637 + 4127411551*t*z/637 - 1301347638*t/637 + 62524948*z/7 - 19033883/7)*hf
  norm_num at hh

private lemma cell_10_45 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z^2 + 16*z - 10) + 6*z^2 - 10*z + 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z^2 + 48*z - 112) + t^6*(688*z^2 - 1072*z + 624) + t^5*(-6848*z^2 + 8464*z - 2864) + t^4*(43280*z^2 - 45664*z + 11616) + t^3*(-178032*z^2 + 175088*z - 39008) + t^2*(459344*z^2 - 442416*z + 94544) + t*(-672672*z^2 + 641984*z - 134656) + 426560*z^2 - 405984*z + 84672:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(32119*z^2/196 - 86029*z/98 + 49943/196) + t^5*(-83759*z^2/98 + 224344*z/49 - 260481/196) + t^4*(324791*z^2/196 - 869935*z/98 + 126257/49) + t^3*(-281999*z^2/196 + 1510637*z/196 - 219241/98) + t^2*(24701*z^2/49 - 132320*z/49 + 153611/196) + t*(-1026*z^2/49 + 5497*z/49 - 3189/98) - 1381*z^2/98 + 3700*z/49 - 2171/98)*h0 + (-32119*z^2/1568 + 86029*z/784 - 49943/1568)*h1 + (-160595*t^7/98 + 474862*t^6*z/49 - 20229*t^6/49 - 6297398*t^5*z/49 + 5455213*t^5/98 + 6095966*t^4*z/7 - 4700363*t^4/14 - 178172254*t^3*z/49 + 120109637*t^3/98 + 921799751*t^2*z/98 - 294778417*t^2/98 - 675170105*t*z/49 + 210164572*t/49 + 428150413*z/49 - 132153520/49)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_10_46 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^2 + 6*z - 6) + 4*z^2 - 8*z + 4:ℝ)=0) (h1 : (16*t^8 + t^7*(32*z^2 - 272*z + 16) + t^6*(-48*z^2 + 1872*z - 640) + t^5*(-1744*z^2 - 2768*z + 1424) + t^4*(11040*z^2 - 6640*z + 928) + t^3*(-30368*z^2 + 27952*z - 6224) + t^2*(44608*z^2 - 42352*z + 9088) + t*(-33392*z^2 + 32208*z - 6960) + 9552*z^2 - 9296*z + 2032:ℝ)=0) : False := by
  have hh : ((t-(z^2 - 5*z + 3)))*(1:ℝ)=0 := by linear_combination (t^6*(1518*z^2/49 - 8130*z/49 + 4703/98) + t^5*(-23199*z^2/98 + 62134*z/49 - 18020/49) + t^4*(68449*z^2/98 - 366707*z/98 + 106601/98) + t^3*(-97855*z^2/98 + 262112*z/49 - 76143/49) + t^2*(35129*z^2/49 - 376295*z/98 + 108895/98) + t*(-12168*z^2/49 + 65192*z/49 - 37935/98) + 3099*z^2/98 - 8284*z/49 + 4647/98)*h0 + (-759*z^2/196 + 4065*z/196 - 4703/784)*h1 + (9108*t^7*z/49 - 7836*t^7/7 - 38379*t^6*z/49 + 412247*t^6/49 - 216077*t^5*z/49 - 962736*t^5/49 + 1860087*t^4*z/49 + 506181*t^4/49 - 5496360*t^3*z/49 + 1160275*t^3/49 + 8299516*t^2*z/49 - 2335062*t^2/49 - 6284361*t*z/49 + 1955945*t/49 + 258042*z/7 - 587840/49)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_10_47 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(2*z^2 - 10*z + 6) + t*(-8*z^2 + 28*z - 16) + 12*z^2 - 20*z + 8:ℝ)=0) (h1 : (t^8*(144*z^2 - 416*z + 208) + t^7*(-3216*z^2 + 2416*z - 224) + t^6*(56816*z^2 - 52608*z + 10336) + t^5*(-550752*z^2 + 525952*z - 110464) + t^4*(3278592*z^2 - 3121856*z + 651712) + t^3*(-12358352*z^2 + 11752976*z - 2447184) + t^2*(28799984*z^2 - 27387712*z + 5701968) + t*(-37927568*z^2 + 36070480*z - 7510880) + 21610176*z^2 - 20552864*z + 4280032:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(15*z^2/196 - 109*z/196 + 165/196) + t^6*(293*z^2/49 - 6333*z/196 + 2203/196) + t^5*(-2477*z^2/98 + 26319*z/196 - 4077/98) + t^4*(2357*z^2/49 - 23777*z/98 + 6249/98) + t^3*(-2463*z^2/49 + 9880*z/49 - 5025/98) + t^2*(8209*z^2/196 - 6929*z/196 + 1137/98) + t*(-11059*z^2/196 + 1137*z/196 - 549/196) + 307*z^2/7 - 1069*z/28 + 253/28)*h0 + (t*(8791*z^2/1568 - 47085*z/1568 + 426/49) - 1917*z^2/112 + 2567*z/28 - 425/16)*h1 + (-39567*t^9*z/49 + 177711*t^9/98 + 2007421*t^8*z/98 - 727009*t^8/98 - 36601727*t^7*z/98 + 4673973*t^7/49 + 198934632*t^6*z/49 - 60454845*t^6/49 - 1362560870*t^5*z/49 + 421323737*t^5/49 + 877819007*t^4*z/7 - 1890675677*t^4/49 - 2610948492*t^3*z/7 + 11228342547*t^3/98 + 69147099219*t^2*z/98 - 21242186409*t^2/98 - 37746047356*t*z/49 + 1657023600*t/7 + 2589165528*z/7 - 795817951/7)*hf
  norm_num at hh

private lemma cell_10_48 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(2*z^2 - 10*z + 6) + t*(-4*z^2 + 22*z - 14):ℝ)=0) (h1 : (t^8*(144*z^2 - 416*z + 208) + t^7*(-1936*z^2 + 6768*z - 3552) + t^6*(10992*z^2 - 44736*z + 24224) + t^5*(-33216*z^2 + 151680*z - 83808) + t^4*(55424*z^2 - 276576*z + 154944) + t^3*(-48496*z^2 + 262640*z - 148848) + t^2*(19376*z^2 - 117824*z + 67760) + t*(-2352*z^2 + 18928*z - 11200):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(-3*z^2/49 + 31*z/98 - 17/98) + t^5*(6*z^2/7 - 32*z/7 + 18/7) + t^4*(-65*z^2/14 + 177*z/7 - 201/14) + t^3*(165*z^2/14 - 911*z/14 + 37) + t^2*(-193*z^2/14 + 77*z - 307/7) + t*(99*z^2/14 - 282*z/7 + 319/14) - 11*z^2/14 + 36*z/7 - 51/14)*h0 + (41*z^2/784 - 55*z/196 + 33/392)*h1 + (-363*t^8*z/49 + 807*t^8/49 + 695*t^7*z/7 - 13777*t^7/49 - 27544*t^6*z/49 + 93939*t^6/49 + 83051*t^5*z/49 - 324981*t^5/49 - 138363*t^4*z/49 + 600868*t^4/49 + 17268*t^3*z/7 - 82459*t^3/7 - 6884*t^2*z/7 + 37544*t^2/7 + 839*t*z/7 - 6250*t/7)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_10_49 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(2*z^2 - 10*z + 6) + t*(-6*z^2 + 30*z - 18) + 2*z:ℝ)=0) (h1 : (t^8*(144*z^2 - 416*z + 208) + t^7*(-2832*z^2 + 8240*z - 4128) + t^6*(22928*z^2 - 66544*z + 33312) + t^5*(-99040*z^2 + 284224*z - 141824) + t^4*(247392*z^2 - 696144*z + 345376) + t^3*(-362368*z^2 + 991536*z - 487792) + t^2*(301120*z^2 - 794736*z + 386560) + t*(-128528*z^2 + 325280*z - 156032) + 21264*z^2 - 51392*z + 24256:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-9*z^2/1421 + z/49 + 13/1421) + t^6*(-265*z^2/2842 + 73*z/98 - 677/1421) + t^5*(1224*z^2/1421 - 629*z/98 + 5134/1421) + t^4*(-6737*z^2/2842 + 1923*z/98 - 32989/2842) + t^3*(5134*z^2/1421 - 1678*z/49 + 59083/2842) + t^2*(-9861*z^2/2842 + 3569*z/98 - 30670/1421) + t*(2663*z^2/2842 - 1559*z/98 + 30077/2842) - 199*z^2/203 + 109*z/14 - 1555/406)*h0 + (t*(2431*z^2/11368 - 449*z/392 + 1887/5684) - 425*z^2/1624 + 157*z/112 - 1321/3248)*h1 + (-43740*t^9*z/1421 + 98202*t^9/1421 + 914335*t^8*z/1421 - 2071891*t^8/1421 - 8023639*t^7*z/1421 + 18143652*t^7/1421 + 38636211*t^6*z/1421 - 86349105*t^6/1421 - 112037223*t^5*z/1421 + 245370686*t^5/1421 + 28879163*t^4*z/203 - 61491055*t^4/203 - 226290686*t^3*z/1421 + 464915260*t^3/1421 + 151046221*t^2*z/1421 - 297318964*t^2/1421 - 54266306*t*z/1421 + 101717477*t/1421 + 1129650*z/203 - 2002839/203)*hf
  norm_num at hh

private lemma cell_10_50 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(2*z^2 - 10*z + 6) + t*(-4*z^2 + 16*z - 10) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (t^8*(144*z^2 - 416*z + 208) + t^7*(-3152*z^2 + 7152*z - 3296) + t^6*(30704*z^2 - 52512*z + 21072) + t^5*(-174064*z^2 + 226064*z - 73392) + t^4*(622000*z^2 - 660448*z + 167488) + t^3*(-1411776*z^2 + 1362288*z - 292208) + t^2*(1955712*z^2 - 1849008*z + 380256) + t*(-1493760*z^2 + 1415936*z - 292800) + 479712*z^2 - 456288*z + 95040:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-3*z^2/98 + 6*z/49 + 9/98) + t^6*(-53*z^2/98 + 359*z/98 - 289/98) + t^5*(579*z^2/98 - 3695*z/98 + 2099/98) + t^4*(-732*z^2/49 + 5252*z/49 - 2830/49) + t^3*(185*z^2/98 - 4206*z/49 + 5269/98) + t^2*(3239*z^2/98 - 2264*z/49 + 339/49) + t*(-3277*z^2/98 + 2557*z/49 - 933/49) + 466*z^2/49 + 45*z/98 - 5/49)*h0 + (t*(1347*z^2/784 - 7215*z/784 + 2091/784) - 4355*z^2/784 + 1458*z/49 - 3383/392)*h1 + (-12120*t^9*z/49 + 27210*t^9/49 + 304601*t^8*z/49 - 519616*t^8/49 - 491930*t^7*z/7 + 4155394*t^7/49 + 23013933*t^6*z/49 - 18530003*t^6/49 - 99746362*t^5*z/49 + 52970436*t^5/49 + 288153112*t^4*z/49 - 109044392*t^4/49 - 548904714*t^3*z/49 + 173258445*t^3/49 + 94009365*t^2*z/7 - 199056078*t^2/49 - 446963413*t*z/49 + 136236524*t/49 + 18652954*z/7 - 40190099/49)*hf
  norm_num at hh

private lemma cell_10_51 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^2 + 12*z - 12) + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-96*z^2 + 496*z - 368) + t^6*(688*z^2 - 3440*z + 2112) + t^5*(-1728*z^2 + 8160*z - 4704) + t^4*(1376*z^2 - 5744*z + 3184) + t^3*(1040*z^2 - 4816*z + 2672) + t^2*(-2048*z^2 + 7728*z - 4128) + t*(416*z^2 - 1088*z + 528) + 288*z^2 - 832*z + 416:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-28939*z^2/1274 + 155019*z/1274 - 44979/1274) + t^6*(146539*z^2/1274 - 784935*z/1274 + 113794/637) + t^5*(-131156*z^2/637 + 1404883*z/1274 - 203282/637) + t^4*(181427*z^2/1274 - 971275*z/1274 + 139757/637) + t^3*(-18173*z^2/1274 + 48519*z/637 - 26989/1274) + t^2*(-8480*z^2/637 + 90289*z/1274 - 24419/1274) + t*(-242*z^2/637 + 1577*z/637 - 2727/1274) - 25*z^2/91 + 149*z/91 - 17/26)*h0 + (t*(28939*z^2/10192 - 155019*z/10192 + 44979/10192) - 8583*z^2/1456 + 821*z/26 - 1905/208)*h1 + (144695*t^8*z/637 - 630400*t^8/637 - 208332*t^7*z/91 + 482084*t^7/49 + 5446583*t^6*z/637 - 22598880*t^6/637 - 8796075*t^5*z/637 + 34283614*t^5/637 + 251366*t^4*z/49 - 1521019*t^4/91 + 7592497*t^3*z/637 - 3868057*t^3/91 - 649482*t^2*z/49 + 25558427*t^2/637 + 1040854*t*z/637 - 146820*t/49 + 154494*z/91 - 49560/13)*hf
  norm_num at hh

private lemma cell_10_52 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(2*z^2 - 10*z + 6) + t*(-6*z^2 + 30*z - 18) + 2*z:ℝ)=0) (h1 : (t^8*(144*z^2 - 416*z + 208) + t^7*(-2832*z^2 + 8240*z - 4128) + t^6*(23504*z^2 - 66416*z + 32992) + t^5*(-107440*z^2 + 282160*z - 137024) + t^4*(297648*z^2 - 688080*z + 319408) + t^3*(-519776*z^2 + 997024*z - 426224) + t^2*(570816*z^2 - 874320*z + 326208) + t*(-364464*z^2 + 451328*z - 139520) + 102784*z^2 - 109376*z + 27840:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-43*z^2/1274 + 99*z/1274 - 20/637) + t^6*(333*z^2/637 - 653*z/637 + 275/637) + t^5*(-2319*z^2/637 + 4040*z/637 - 1597/637) + t^4*(8721*z^2/637 - 12099*z/637 + 8189/1274) + t^3*(-39519*z^2/1274 + 40441*z/1274 - 9207/1274) + t^2*(27368*z^2/637 - 41235*z/1274 + 1707/637) + t*(-1675*z^2/49 + 1184*z/49 - 51/98) + 14369*z^2/1274 - 4619*z/637 - 311/1274)*h0 + (t*(129*z^2/2548 - 2761*z/10192 + 115/1456) - 473*z^2/5096 + 633*z/1274 - 1465/10192)*h1 + (-4601*t^9*z/637 + 10345*t^9/637 + 99051*t^8*z/637 - 224725*t^8/637 - 918810*t^7*z/637 + 2023348*t^7/637 + 4823258*t^6*z/637 - 1408791*t^6/91 - 15859693*t^5*z/637 + 28515153*t^5/637 + 34187921*t^4*z/637 - 7228155*t^4/91 - 6990402*t^3*z/91 + 55405760*t^3/637 + 45358441*t^2*z/637 - 752714*t^2/13 - 24820611*t*z/637 + 14178299*t/637 + 6077104*z/637 - 2549737/637)*hf
  norm_num at hh

private lemma cell_10_53 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(2*z^2 - 10*z + 6) + t*(-8*z^2 + 38*z - 22) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (t^8*(144*z^2 - 416*z + 208) + t^7*(-3728*z^2 + 9712*z - 4704) + t^6*(41456*z^2 - 94880*z + 43872) + t^5*(-260288*z^2 + 510752*z - 220816) + t^4*(1015056*z^2 - 1680352*z + 660832) + t^3*(-2527520*z^2 + 3533280*z - 1226928) + t^2*(3927024*z^2 - 4745344*z + 1427600) + t*(-3470272*z^2 + 3769488*z - 988928) + 1328576*z^2 - 1350208*z + 318848:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(338*z^2/49 - 3621*z/98 + 526/49) + t^6*(-26*z^2/49 + 271*z/98 - 48/49) + t^5*(-3060*z^2/49 + 32873*z/98 - 4708/49) + t^4*(-612*z^2/49 + 6009*z/98 - 2201/98) + t^3*(14941*z^2/98 - 39059*z/49 + 11780/49) + t^2*(-733*z^2/98 + 45*z/49 - 951/98) + t*(-2811*z^2/49 + 34199*z/98 - 9433/98) - 536*z^2/49 + 3945*z/98 - 632/49)*h0 + (t*(-21729*z^2/196 + 29100*z/49 - 135151/784) + 80679*z^2/392 - 432189*z/392 + 250905/784)*h1 + (781568*t^9*z/49 - 1753807*t^9/49 - 21700894*t^8*z/49 + 42984299*t^8/49 + 262801006*t^7*z/49 - 444376252*t^7/49 - 261721610*t^6*z/7 + 2553297338*t^6/49 + 8138996183*t^5*z/49 - 9044661032*t^5/49 - 23966771677*t^4*z/49 + 20726398229*t^4/49 + 46822287133*t^3*z/49 - 31298990368*t^3/49 - 58454951917*t^2*z/49 + 30740510653*t^2/49 + 42214417646*t*z/49 - 18201220897*t/49 - 13398521816*z/49 + 5000033527/49)*hf
  norm_num at hh

private lemma cell_10_54 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(2*z^2 - 10*z + 6) + t*(-6*z^2 + 24*z - 14) + 4*z^2 - 8*z + 4:ℝ)=0) (h1 : (t^8*(144*z^2 - 416*z + 208) + t^7*(-4048*z^2 + 8624*z - 3872) + t^6*(53456*z^2 - 82768*z + 31120) + t^5*(-425360*z^2 + 510576*z - 152432) + t^4*(2171728*z^2 - 2248192*z + 547632) + t^3*(-7125984*z^2 + 6932752*z - 1511296) + t^2*(14479344*z^2 - 13827200*z + 2903920) + t*(-16551888*z^2 + 15746368*z - 3280976) + 8133808*z^2 - 7735040*z + 1610432:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(18*z^2/637 - 93*z/637 + 25/1274) + t^5*(289*z^2/1274 - 830*z/637 + 911/1274) + t^4*(-1291*z^2/1274 + 3828*z/637 - 2267/637) + t^3*(3053*z^2/1274 - 19065*z/1274 + 5490/637) + t^2*(-1923*z^2/1274 + 16715*z/1274 - 4994/637) + t*(-537*z^2/637 - 4097*z/1274 + 2515/1274) + 195*z^2/98 - 493*z/98 + 129/98)*h0 + (-6945*z^2/10192 + 18601*z/5096 - 10791/10192)*h1 + (62469*t^8*z/637 - 140208*t^8/637 - 251038*t^7*z/91 + 2613980*t^7/637 + 23205331*t^6*z/637 - 21008424*t^6/637 - 184640329*t^5*z/637 + 14696051*t^5/91 + 942679349*t^4*z/637 - 369459449*t^4/637 - 3093133231*t^3*z/637 + 1019374117*t^3/637 + 6284938344*t^2*z/637 - 150657315*t^2/49 - 7184544132*t*z/637 + 2212805905*t/637 + 504367995*z/91 - 1086132378/637)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_10_55 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-6*z^2 + 32*z - 20) + 2*z^2 - 10*z + 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-224*z^2 + 1136*z - 624) + t^6*(1776*z^2 - 7984*z + 4384) + t^5*(-8384*z^2 + 29760*z - 15680) + t^4*(27232*z^2 - 65296*z + 30736) + t^3*(-63952*z^2 + 94992*z - 34640) + t^2*(101184*z^2 - 105328*z + 25888) + t*(-91648*z^2 + 84640*z - 16528) + 34400*z^2 - 31776*z + 6208:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(-6642*z^2/49 + 71161*z/98 - 10328/49) + t^5*(-24195*z^2/98 + 64805*z/49 - 37623/98) + t^4*(-3538*z^2/49 + 18954*z/49 - 5500/49) + t^3*(5273*z^2/98 - 28267*z/98 + 4099/49) + t^2*(499*z^2/49 - 5273*z/98 + 1535/98) + t*(-391*z^2/98 + 1963*z/98 - 285/49) + 113*z^2/49 - 1107*z/98 + 309/98)*h0 + (3321*z^2/196 - 71161*z/784 + 1291/49)*h1 + (146124*t^7*z/49 - 636647*t^7/49 - 1533825*t^6*z/49 + 121694*t^6 + 6963783*t^5*z/49 - 20237551*t^5/49 - 3226639*t^4*z/7 + 39566731*t^4/49 + 53093869*t^3*z/49 - 44711566*t^3/49 - 84010187*t^2*z/49 + 33432022*t^2/49 + 76091821*t*z/49 - 21342497*t/49 - 582874*z + 1145065/7)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_10_56 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(2*z^2 - 10*z + 6) + t*(-4*z^2 + 16*z - 10) + 2*z^2 - 4*z + 2:ℝ)=0) (h1 : (t^8*(144*z^2 - 416*z + 208) + t^7*(-3152*z^2 + 7152*z - 3296) + t^6*(32176*z^2 - 54752*z + 21904) + t^5*(-202000*z^2 + 262016*z - 84960) + t^4*(844576*z^2 - 908752*z + 235120) + t^3*(-2363760*z^2 + 2325712*z - 518064) + t^2*(4256144*z^2 - 4067840*z + 855776) + t*(-4466096*z^2 + 4245280*z - 883056) + 2082448*z^2 - 1979600*z + 411824:ℝ)=0) (h2 : (t^8*(144*z^2 - 416*z + 208) + t^7*(-3152*z^2 + 7152*z - 3296) + t^6*(30704*z^2 - 52512*z + 21072) + t^5*(-174064*z^2 + 226064*z - 73392) + t^4*(622000*z^2 - 660448*z + 167488) + t^3*(-1411776*z^2 + 1362288*z - 292208) + t^2*(1955712*z^2 - 1849008*z + 380256) + t*(-1493760*z^2 + 1415936*z - 292800) + 479712*z^2 - 456288*z + 95040:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(23*z^2/1372 - 65*z/686 + 5/98) + t^12*(-555*z^2/1372 + 3153*z/1372 - 1769/1372) + t^11*(1528*z^2/343 - 34793*z/1372 + 4953/343) + t^10*(-9692*z^2/343 + 220841*z/1372 - 126107/1372) + t^9*(151749*z^2/1372 - 216271*z/343 + 493837/1372) + t^8*(-53113*z^2/196 + 2124137*z/1372 - 1212325/1372) + t^7*(551139*z^2/1372 - 226661*z/98 + 453123/343) + t^6*(-214645*z^2/686 + 2567945*z/1372 - 30083/28) + t^5*(27983*z^2/686 - 159365*z/343 + 96885/343) + t^4*(198411*z^2/1372 - 529279*z/1372 + 262877/1372) + t^3*(-238475*z^2/1372 + 549207*z/1372 - 129055/686) + t^2*(49753*z^2/343 - 198549*z/686 + 40578/343) + t*(-6739*z^2/98 + 34271*z/343 - 46647/1372) + 13821*z^2/1372 + 53*z/4 - 11723/1372)*h0 + (t^7*(-181*z^2/5488 + 1941*z/10976 - 143/2744) + t^6*(961*z^2/5488 - 645*z/686 + 1555/5488) + t^5*(261*z^2/5488 - 2683*z/10976 + 15/686) + t^4*(-10693*z^2/10976 + 28533*z/5488 - 7771/5488) + t^3*(1171*z^2/10976 - 6161*z/10976 + 1261/10976) + t^2*(20513*z^2/10976 - 54921*z/5488 + 15833/5488) + t*(-879*z^2/5488 + 9419*z/10976 - 1367/5488) - 10039*z^2/10976 + 3363*z/686 - 15765/10976)*h1 + (-4091*z^2/784 + 21915*z/784 - 6361/784)*h2 + (3235*t^15*z/686 - 3613*t^15/343 - 12573*t^14*z/98 + 152605*t^14/686 + 1094673*t^13*z/686 - 1352257*t^13/686 - 4092387*t^12*z/343 + 3282137*t^12/343 + 39971583*t^11*z/686 - 19241177*t^11/686 - 63040381*t^10*z/343 + 35590465*t^10/686 + 217944043*t^9*z/686 - 38077353*t^9/686 + 2469365*t^8*z/343 - 17091523*t^8/686 - 474504337*t^7*z/343 + 104141795*t^7/343 + 969215158*t^6*z/343 - 233473505*t^6/343 - 990145235*t^5*z/686 + 356413857*t^5/686 - 621100643*t^4*z/343 + 150736889*t^4/686 - 247480311*t^3*z/343 + 274186475*t^3/686 + 6510237607*t^2*z/686 - 996680204*t^2/343 - 7920365787*t*z/686 + 2429415857*t/686 + 1511890607*z/343 - 467384252/343)*hf
  norm_num at hh

private lemma cell_10_57 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(2*z^2 - 10*z + 6) + t*(-6*z^2 + 24*z - 14) + 4*z^2 - 8*z + 4:ℝ)=0) (h1 : (t^8*(144*z^2 - 416*z + 208) + t^7*(-4048*z^2 + 8624*z - 3872) + t^6*(54352*z^2 - 85136*z + 32272) + t^5*(-444896*z^2 + 548592*z - 168800) + t^4*(2360944*z^2 - 2520496*z + 644496) + t^3*(-8148800*z^2 + 8107744*z - 1843920) + t^2*(17657424*z^2 - 17057632*z + 3667024) + t*(-21834576*z^2 + 20865088*z - 4388016) + 11763616*z^2 - 11201792*z + 2338688:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(-3*z^2/196 + 3*z/49 + 4/49) + t^5*(-47*z^2/49 + 1067*z/196 - 299/98) + t^4*(1199*z^2/196 - 6763*z/196 + 905/49) + t^3*(-1405*z^2/98 + 4000*z/49 - 9399/196) + t^2*(2195*z^2/98 - 6210*z/49 + 7205/98) + t*(-906*z^2/49 + 20173*z/196 - 11255/196) + 597*z^2/98 - 6393*z/196 + 1681/98)*h0 + (489*z^2/392 - 10477*z/1568 + 759/392)*h1 + (-17601*t^8*z/98 + 19758*t^8/49 + 10103*t^7*z/2 - 368309*t^7/49 - 6646289*t^6*z/98 + 3069345*t^6/49 + 54395319*t^5*z/98 - 32084533*t^5/98 - 144320311*t^4*z/49 + 122409379*t^4/98 + 498106607*t^3*z/49 - 350037253*t^3/98 - 1079320465*t^2*z/49 + 695935495*t^2/98 + 1334643873*t*z/49 - 416336089*t/49 - 102721746*z/7 + 221886386/49)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_10_58 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(2*z^2 - 10*z + 6) + t*(-4*z^2 + 10*z - 6) + 6*z^2 - 10*z + 4:ℝ)=0) (h1 : (t^8*(144*z^2 - 416*z + 208) + t^7*(-4368*z^2 + 7536*z - 3040) + t^6*(71088*z^2 - 82240*z + 23488) + t^5*(-721664*z^2 + 711904*z - 159360) + t^4*(4672800*z^2 - 4453472*z + 931456) + t^3*(-19304400*z^2 + 18343856*z - 3813040) + t^2*(49403440*z^2 - 46978176*z + 9779440) + t*(-71547760*z^2 + 68048880*z - 14171584) + 44898656*z^2 - 42703040*z + 8893184:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(983*z^2/637 - 5269*z/637 + 1552/637) + t^6*(-7919*z^2/1274 + 42407*z/1274 - 6395/637) + t^5*(-3410*z^2/637 + 18995*z/637 - 4715/637) + t^4*(1324*z^2/49 - 15345*z/98 + 2188/49) + t^3*(21439*z^2/1274 - 18350*z/637 + 7083/1274) + t^2*(-100543*z^2/1274 + 305117*z/1274 - 82965/1274) + t*(94771*z^2/1274 - 123689*z/1274 + 31303/1274) - 27031*z^2/637 + 20661*z/1274 - 291/1274)*h0 + (t*(-31163*z^2/1274 + 667749*z/5096 - 193835/5096) + 379915*z^2/5096 - 4070329*z/10192 + 1181499/10192)*h1 + (2241770*t^9*z/637 - 5030398*t^9/637 - 74886611*t^8*z/637 + 88969105*t^8/637 + 1315076346*t^7*z/637 - 793568082*t^7/637 - 1124658201*t^6*z/49 + 5595807106*t^6/637 + 107080673389*t^5*z/637 - 34336495035*t^5/637 - 522699819951*t^4*z/637 + 1771094126*t^4/7 + 1686533230936*t^3*z/637 - 518518296265*t^3/637 - 3460959365657*t^2*z/637 + 1065518273653*t^2/637 + 45025784847*t*z/7 - 1261958246877*t/637 - 2132208949594*z/637 + 656705498957/637)*hf
  norm_num at hh

private lemma cell_10_59 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^2 + 8*z - 8) + 2*z^2 - 6*z + 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-96*z^2 + 368*z - 240) + t^6*(1040*z^2 - 1776*z + 736) + t^5*(-10608*z^2 + 9616*z - 1776) + t^4*(78816*z^2 - 72112*z + 13760) + t^3*(-365120*z^2 + 345744*z - 71344) + t^2*(1018752*z^2 - 970032*z + 202496) + t*(-1572816*z^2 + 1497552*z - 312592) + 1030512*z^2 - 980560*z + 204400:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-4201*z^2/98 + 22509*z/98 - 3278/49) + t^6*(10079*z^2/98 - 54029*z/98 + 7929/49) + t^5*(-34*z^2 + 2559*z/14 - 785/14) + t^4*(-137*z^2/2 + 5147*z/14 - 776/7) + t^3*(507*z^2/14 - 2735*z/14 + 475/7) + t^2*(92*z^2/7 - 1027*z/14 + 141/7) + t*(-37*z^2/7 + 246*z/7 - 113/7) + 15*z^2/14 - 151*z/14 + 109/14)*h0 + (t*(4201*z^2/784 - 22509*z/784 + 1639/196) - 3223*z^2/392 + 34541*z/784 - 2519/196)*h1 + (21005*t^8*z/49 - 66334*t^8/49 - 297461*t^7*z/49 + 370677*t^7/49 + 3190842*t^6*z/49 - 1148380*t^6/49 - 3567315*t^5*z/7 + 138688*t^5 + 127630078*t^4*z/49 - 37944918*t^4/49 - 59226579*t^3*z/7 + 18272206*t^3/7 + 117627201*t^2*z/7 - 36513627*t^2/7 - 129174490*t*z/7 + 40085928*t/7 + 59309631*z/7 - 2626927)*hf
  norm_num at hh

private lemma cell_10_60 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^2 + 12*z - 12) + 2:ℝ)=0) (h2 : (16*t^8 + t^7*(-96*z^2 + 496*z - 368) + t^6*(688*z^2 - 3440*z + 2112) + t^5*(-1728*z^2 + 8160*z - 4704) + t^4*(1376*z^2 - 5744*z + 3184) + t^3*(1040*z^2 - 4816*z + 2672) + t^2*(-2048*z^2 + 7728*z - 4128) + t*(416*z^2 - 1088*z + 528) + 288*z^2 - 832*z + 416:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-28939*z^2/1274 + 155019*z/1274 - 44979/1274) + t^6*(146539*z^2/1274 - 784935*z/1274 + 113794/637) + t^5*(-131156*z^2/637 + 1404883*z/1274 - 203282/637) + t^4*(181427*z^2/1274 - 971275*z/1274 + 139757/637) + t^3*(-18173*z^2/1274 + 48519*z/637 - 26989/1274) + t^2*(-8480*z^2/637 + 90289*z/1274 - 24419/1274) + t*(-242*z^2/637 + 1577*z/637 - 2727/1274) - 25*z^2/91 + 149*z/91 - 17/26)*h0 + (t*(28939*z^2/10192 - 155019*z/10192 + 44979/10192) - 8583*z^2/1456 + 821*z/26 - 1905/208)*h2 + (144695*t^8*z/637 - 630400*t^8/637 - 208332*t^7*z/91 + 482084*t^7/49 + 5446583*t^6*z/637 - 22598880*t^6/637 - 8796075*t^5*z/637 + 34283614*t^5/637 + 251366*t^4*z/49 - 1521019*t^4/91 + 7592497*t^3*z/637 - 3868057*t^3/91 - 649482*t^2*z/49 + 25558427*t^2/637 + 1040854*t*z/637 - 146820*t/49 + 154494*z/91 - 49560/13)*hf
  norm_num at hh

private lemma cell_10_61 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-6*z^2 + 32*z - 20) + 2*z^2 - 10*z + 6:ℝ)=0) (h2 : (16*t^8 + t^7*(-224*z^2 + 1136*z - 624) + t^6*(1776*z^2 - 7984*z + 4384) + t^5*(-8384*z^2 + 29760*z - 15680) + t^4*(27232*z^2 - 65296*z + 30736) + t^3*(-63952*z^2 + 94992*z - 34640) + t^2*(101184*z^2 - 105328*z + 25888) + t*(-91648*z^2 + 84640*z - 16528) + 34400*z^2 - 31776*z + 6208:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(-6642*z^2/49 + 71161*z/98 - 10328/49) + t^5*(-24195*z^2/98 + 64805*z/49 - 37623/98) + t^4*(-3538*z^2/49 + 18954*z/49 - 5500/49) + t^3*(5273*z^2/98 - 28267*z/98 + 4099/49) + t^2*(499*z^2/49 - 5273*z/98 + 1535/98) + t*(-391*z^2/98 + 1963*z/98 - 285/49) + 113*z^2/49 - 1107*z/98 + 309/98)*h0 + (3321*z^2/196 - 71161*z/784 + 1291/49)*h2 + (146124*t^7*z/49 - 636647*t^7/49 - 1533825*t^6*z/49 + 121694*t^6 + 6963783*t^5*z/49 - 20237551*t^5/49 - 3226639*t^4*z/7 + 39566731*t^4/49 + 53093869*t^3*z/49 - 44711566*t^3/49 - 84010187*t^2*z/49 + 33432022*t^2/49 + 76091821*t*z/49 - 21342497*t/49 - 582874*z + 1145065/7)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_10_62 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z^2 + 8*z - 8) + 2*z^2 - 6*z + 4:ℝ)=0) (h2 : (16*t^8 + t^7*(-96*z^2 + 368*z - 240) + t^6*(1040*z^2 - 1776*z + 736) + t^5*(-10608*z^2 + 9616*z - 1776) + t^4*(78816*z^2 - 72112*z + 13760) + t^3*(-365120*z^2 + 345744*z - 71344) + t^2*(1018752*z^2 - 970032*z + 202496) + t*(-1572816*z^2 + 1497552*z - 312592) + 1030512*z^2 - 980560*z + 204400:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-4201*z^2/98 + 22509*z/98 - 3278/49) + t^6*(10079*z^2/98 - 54029*z/98 + 7929/49) + t^5*(-34*z^2 + 2559*z/14 - 785/14) + t^4*(-137*z^2/2 + 5147*z/14 - 776/7) + t^3*(507*z^2/14 - 2735*z/14 + 475/7) + t^2*(92*z^2/7 - 1027*z/14 + 141/7) + t*(-37*z^2/7 + 246*z/7 - 113/7) + 15*z^2/14 - 151*z/14 + 109/14)*h0 + (t*(4201*z^2/784 - 22509*z/784 + 1639/196) - 3223*z^2/392 + 34541*z/784 - 2519/196)*h2 + (21005*t^8*z/49 - 66334*t^8/49 - 297461*t^7*z/49 + 370677*t^7/49 + 3190842*t^6*z/49 - 1148380*t^6/49 - 3567315*t^5*z/7 + 138688*t^5 + 127630078*t^4*z/49 - 37944918*t^4/49 - 59226579*t^3*z/7 + 18272206*t^3/7 + 117627201*t^2*z/7 - 36513627*t^2/7 - 129174490*t*z/7 + 40085928*t/7 + 59309631*z/7 - 2626927)*hf
  norm_num at hh

private lemma cell_10_63 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z^2 - 5*z + 3)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t*(-4*z^2 + 22*z - 14) + 2*z^2 - 10*z + 6:ℝ)=0) : (t - z^2/7 + 4*z/7 - 4/7:ℝ)=0 := by
  have hh : (t - z^2/7 + 4*z/7 - 4/7:ℝ)=0 := by linear_combination (5*z^2/14 - 27*z/14 + 3/7)*h0 + (10*t*z/7 - 7*t - 5*z/7 + 22/7)*hf
  exact hh

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_0 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 0) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_0 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 20*z^3 + 56*z^2 - 30*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_1 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 1) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_1 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 20*z^3 + 54*z^2 - 20*z - 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_2 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 2) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_2 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 22*z^3 + 70*z^2 - 50*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(10 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_3 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 3) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_3 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 + 10*t*z - 10*t + 2*z^4 - 20*z^3 + 58*z^2 - 40*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8 + 80*t^7*z^4 - 864*t^7*z^3 + 2736*t^7*z^2 - 2144*t^7*z + 272*t^7 + 144*t^6*z^8 - 3120*t^6*z^7 + 26912*t^6*z^6 - 116736*t^6*z^5 + 264784*t^6*z^4 - 299968*t^6*z^3 + 158816*t^6*z^2 - 33392*t^6*z + 2320*t^6 + 112*t^5*z^12 - 3648*t^5*z^11 + 51568*t^5*z^10 - 413840*t^5*z^9 + 2071072*t^5*z^8 - 6690752*t^5*z^7 + 14000624*t^5*z^6 - 18651232*t^5*z^5 + 15315120*t^5*z^4 - 7380944*t^5*z^3 + 1940704*t^5*z^2 - 252288*t^5*z + 12704*t^5 + 32*t^4*z^16 - 1392*t^4*z^15 + 27536*t^4*z^14 - 327472*t^4*z^13 + 2606608*t^4*z^12 - 14622192*t^4*z^11 + 59252912*t^4*z^10 - 174861104*t^4*z^9 + 374293232*t^4*z^8 - 573160624*t^4*z^7 + 614576896*t^4*z^6 - 449190864*t^4*z^5 + 216515152*t^4*z^4 - 65980608*t^4*z^3 + 12006784*t^4*z^2 - 1182304*t^4*z + 48208*t^4 + 144*t^3*z^18 - 6928*t^3*z^17 + 151712*t^3*z^16 - 2000160*t^3*z^15 + 17696992*t^3*z^14 - 110903840*t^3*z^13 + 506555600*t^3*z^12 - 1710358384*t^3*z^11 + 4289134480*t^3*z^10 - 7972663728*t^3*z^9 + 10908663728*t^3*z^8 - 10869336912*t^3*z^7 + 7774389808*t^3*z^6 - 3917609952*t^3*z^5 + 1356560880*t^3*z^4 - 311710576*t^3*z^3 + 44972368*t^3*z^2 - 3663856*t^3*z + 128624*t^3 + 224*t^2*z^20 - 11824*t^2*z^19 + 286288*t^2*z^18 - 4211328*t^2*z^17 + 42023664*t^2*z^16 - 300845184*t^2*z^15 + 1593988848*t^2*z^14 - 6359249072*t^2*z^13 + 19264484912*t^2*z^12 - 44418368976*t^2*z^11 + 77802570752*t^2*z^10 - 103025579840*t^2*z^9 + 102420931392*t^2*z^8 - 75751783664*t^2*z^7 + 41191211344*t^2*z^6 - 16204517808*t^2*z^5 + 4508146736*t^2*z^4 - 857000288*t^2*z^3 + 105151600*t^2*z^2 - 7458192*t^2*z + 230416*t^2 + 144*t*z^22 - 8288*t*z^21 + 220480*t*z^20 - 3595008*t*z^19 + 40174736*t*z^18 - 325986432*t*z^17 + 1985453376*t*z^16 - 9257253008*t*z^15 + 33415444352*t*z^14 - 93896335152*t*z^13 + 205694643712*t*z^12 - 350806114160*t*z^11 + 464221303776*t*z^10 - 474370113872*t*z^9 + 371993745872*t*z^8 - 222016935424*t*z^7 + 99698018416*t*z^6 - 33132415888*t*z^5 + 7949859888*t*z^4 - 1325372256*t*z^3 + 144095920*t*z^2 - 9078704*t*z + 247520*t + 32*z^24 - 2000*z^23 + 58160*z^22 - 1044544*z^21 + 12969952*z^20 - 118116016*z^19 + 816843440*z^18 - 4382985744*z^17 + 18492369296*z^16 - 61832665472*z^15 + 164506397616*z^14 - 348676810560*z^13 + 588338068000*z^12 - 788670076016*z^11 + 837311024464*z^10 - 701134295808*z^9 + 460449020784*z^8 - 235246118448*z^7 + 92393228736*z^6 - 27395087504*z^5 + 5962173376*z^4 - 910289184*z^3 + 90236672*z^2 - 5007392*z + 108160:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7*z + 384*t^7 - 144*t^6*z^5 + 2256*t^6*z^4 - 12656*t^6*z^3 + 29376*t^6*z^2 - 22992*t^6*z + 2480*t^6 - 112*t^5*z^9 + 2976*t^5*z^8 - 33152*t^5*z^7 + 199936*t^5*z^6 - 702720*t^5*z^5 + 1441600*t^5*z^4 - 1637488*t^5*z^3 + 915584*t^5*z^2 - 192576*t^5*z + 10080*t^5 - 32*t^4*z^13 + 1200*t^4*z^12 - 20176*t^4*z^11 + 200384*t^4*z^10 - 1302224*t^4*z^9 + 5786752*t^4*z^8 - 17820896*t^4*z^7 + 37699744*t^4*z^6 - 53203536*t^4*z^5 + 47619792*t^4*z^4 - 25140720*t^4*z^3 + 7044048*t^4*z^2 - 927472*t^4*z + 54816*t^4 - 144*t^3*z^15 + 6064*t^3*z^14 - 114608*t^3*z^13 + 1282048*t^3*z^12 - 9425600*t^3*z^11 + 47825392*t^3*z^10 - 171193200*t^3*z^9 + 434646624*t^3*z^8 - 777463344*t^3*z^7 + 963457344*t^3*z^6 - 805956320*t^3*z^5 + 438848928*t^3*z^4 - 148057296*t^3*z^3 + 29065216*t^3*z^2 - 3034176*t^3*z + 122144*t^3 - 224*t^2*z^17 + 10480*t^2*z^16 - 222288*t^2*z^15 + 2824976*t^2*z^14 - 23951888*t^2*z^13 + 142786688*t^2*z^12 - 614684304*t^2*z^11 + 1933257920*t^2*z^10 - 4448729184*t^2*z^9 + 7445019968*t^2*z^8 - 8955547104*t^2*z^7 + 7618468192*t^2*z^6 - 4487366752*t^2*z^5 + 1779695088*t^2*z^4 - 457738864*t^2*z^3 + 72242432*t^2*z^2 - 6302736*t^2*z + 232848*t^2 - 144*t*z^19 + 7424*t*z^18 - 175216*t*z^17 + 2506448*t*z^16 - 24252544*t*z^15 + 167763712*t*z^14 - 855101936*t*z^13 + 3263570288*t*z^12 - 9390749232*t*z^11 + 20378886384*t*z^10 - 33204008960*t*z^9 + 40296879248*t*z^8 - 36041097104*t*z^7 + 23435126048*t*z^6 - 10880624816*t*z^5 + 3516459184*t*z^4 - 761013184*t*z^3 + 103416048*t*z^2 - 7838496*t*z + 247856*t - 32*z^21 + 1808*z^20 - 47152*z^19 + 752560*z^18 - 8217024*z^17 + 65003920*z^16 - 384982240*z^15 + 1739855680*z^14 - 6063320096*z^13 + 16368484256*z^12 - 34239035920*z^11 + 55336853664*z^10 - 68753282160*z^9 + 65227078816*z^8 - 46845287104*z^7 + 25173896944*z^6 - 9952124784*z^5 + 2818597920*z^4 - 547120352*z^3 + 67251008*z^2 - 4467648*z + 107904)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_4 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 4) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_4 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 20*z^3 + 54*z^2 - 20*z - 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_5 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 5) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_5 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 30*z^5 + 162*z^4 - 370*z^3 + 318*z^2 - 90*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^3 + 18*z^2 - 44*z + 14)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_6 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 6) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_6 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^5 - 20*z^4 + 54*z^3 - 18*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 8*z + 4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_7 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 7) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_7 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^4 - 20*t*z^3 + 54*t*z^2 - 20*t*z - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t*z + 8*t)*hf
  · have hr : (16*t^8 + 144*t^7*z^4 - 1440*t^7*z^3 + 4144*t^7*z^2 - 2848*t^7*z + 464*t^7 + 480*t^6*z^8 - 9600*t^6*z^7 + 75792*t^6*z^6 - 297856*t^6*z^5 + 605296*t^6*z^4 - 613504*t^6*z^3 + 311856*t^6*z^2 - 74784*t^6*z + 6592*t^6 + 704*t^5*z^12 - 21120*t^5*z^11 + 273040*t^5*z^10 - 1988672*t^5*z^9 + 8962096*t^5*z^8 - 25895456*t^5*z^7 + 48349152*t^5*z^6 - 58039840*t^5*z^5 + 44469936*t^5*z^4 - 21319744*t^5*z^3 + 6094672*t^5*z^2 - 934272*t^5*z + 58496*t^5 + 384*t^4*z^16 - 15360*t^4*z^15 + 276864*t^4*z^14 - 2973312*t^4*z^13 + 21197728*t^4*z^12 - 105831664*t^4*z^11 + 380445072*t^4*z^10 - 997307760*t^4*z^9 + 1910458560*t^4*z^8 - 2658078384*t^4*z^7 + 2653587216*t^4*z^6 - 1870279856*t^4*z^5 + 910518160*t^4*z^4 - 296138384*t^4*z^3 + 60810144*t^4*z^2 - 7069520*t^4*z + 352432*t^4 + 1600*t^3*z^18 - 73216*t^3*z^17 + 1520832*t^3*z^16 - 18965808*t^3*z^15 + 158280448*t^3*z^14 - 933110400*t^3*z^13 + 4000359072*t^3*z^12 - 12661699952*t^3*z^11 + 29783354016*t^3*z^10 - 52133361616*t^3*z^9 + 67792272016*t^3*z^8 - 65250503568*t^3*z^7 + 46187427856*t^3*z^6 - 23769328944*t^3*z^5 + 8719204448*t^3*z^4 - 2205052192*t^3*z^3 + 362907408*t^3*z^2 - 34795440*t^3*z + 1469168*t^3 + 2432*t^2*z^20 - 125344*t^2*z^19 + 2960832*t^2*z^18 - 42456544*t^2*z^17 + 412656544*t^2*z^16 - 2875413232*t^2*z^15 + 14821314496*t^2*z^14 - 57518685472*t^2*z^13 + 169606218720*t^2*z^12 - 381386525520*t^2*z^11 + 654118328304*t^2*z^10 - 854180393648*t^2*z^9 + 846784588240*t^2*z^8 - 634394714160*t^2*z^7 + 356497551520*t^2*z^6 - 148403574192*t^2*z^5 + 44837509392*t^2*z^4 - 9507179936*t^2*z^3 + 1335299536*t^2*z^2 - 111127536*t^2*z + 4134400*t^2 + 1600*t*z^22 - 91744*t*z^21 + 2431552*t*z^20 - 39502976*t*z^19 + 439897856*t*z^18 - 3557639248*t*z^17 + 21604744512*t*z^16 - 100501758160*t*z^15 + 362320741584*t*z^14 - 1018537168208*t*z^13 + 2238080367536*t*z^12 - 3843964198400*t*z^11 + 5152517337136*t*z^10 - 5376032554528*t*z^9 + 4349172889056*t*z^8 - 2711656940928*t*z^7 + 1290805325168*t*z^6 - 462336455024*t*z^5 + 121828707952*t*z^4 - 22793114320*t*z^3 + 2852803088*t*z^2 - 213347536*t*z + 7181888*t + 384*z^24 - 24256*z^23 + 713280*z^22 - 12961888*z^21 + 162957440*z^20 - 1503723232*z^19 + 10546474752*z^18 - 57453240016*z^17 + 246429682112*z^16 - 839098348224*z^15 + 2278389656912*z^14 - 4942692505152*z^13 + 8567880986208*z^12 - 11854620515616*z^11 + 13065354636480*z^10 - 11434267023936*z^9 + 7908145454624*z^8 - 4291124400992*z^7 + 1806994052176*z^6 - 580950218416*z^5 + 139135637536*z^4 - 23895485056*z^3 + 2763840384*z^2 - 191502528*z + 5958400:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-144*t^7*z + 576*t^7 - 480*t^6*z^5 + 6720*t^6*z^4 - 33072*t^6*z^3 + 65344*t^6*z^2 - 41152*t^6*z + 6800*t^6 - 704*t^5*z^9 + 16896*t^5*z^8 - 168144*t^5*z^7 + 894624*t^5*z^6 - 2736736*t^5*z^5 + 4833776*t^5*z^4 - 4768192*t^5*z^3 + 2525072*t^5*z^2 - 644768*t^5*z + 57584*t^5 - 384*t^4*z^13 + 13056*t^4*z^12 - 196608*t^4*z^11 + 1728000*t^4*z^10 - 9833632*t^4*z^9 + 37993264*t^4*z^8 - 101589328*t^4*z^7 + 187971840*t^4*z^6 - 236687616*t^4*z^5 + 196504160*t^4*z^4 - 103152336*t^4*z^3 + 32157424*t^4*z^2 - 5307776*t^4*z + 352272*t^4 - 1600*t^3*z^15 + 63616*t^3*z^14 - 1131136*t^3*z^13 + 11859312*t^3*z^12 - 81405280*t^3*z^11 + 384251024*t^3*z^10 - 1275967216*t^3*z^9 + 3003236256*t^3*z^8 - 4999849376*t^3*z^7 + 5842116864*t^3*z^6 - 4737087696*t^3*z^5 + 2617543696*t^3*z^4 - 954610336*t^3*z^3 + 216860752*t^3*z^2 - 27444560*t^3*z + 1470736*t^3 - 2432*t^2*z^17 + 110752*t^2*z^16 - 2284160*t^2*z^15 + 28195392*t^2*z^14 - 231952640*t^2*z^13 + 1340436272*t^2*z^12 - 5590738272*t^2*z^11 + 17040121840*t^2*z^10 - 38071360048*t^2*z^9 + 62167017760*t^2*z^8 - 73719299664*t^2*z^7 + 62958146816*t^2*z^6 - 38272191264*t^2*z^5 + 16251532832*t^2*z^4 - 4669251392*t^2*z^3 + 858210416*t^2*z^2 - 90457104*t^2*z + 4133840*t^2 - 1600*t*z^19 + 82144*t*z^18 - 1930688*t*z^17 + 27506528*t*z^16 - 265123104*t*z^15 + 1827437296*t*z^14 - 9286998688*t*z^13 + 35377456448*t*z^12 - 101793572160*t*z^11 + 221601454320*t*z^10 - 364126324368*t*z^9 + 449405408432*t*z^8 - 413851810384*t*z^7 + 281768325696*t*z^6 - 139898474528*t*z^5 + 49572654896*t*z^4 - 12108697456*t*z^3 + 1922521280*t*z^2 - 177438096*t*z + 7181888*t - 384*z^21 + 21952*z^20 - 579648*z^19 + 9373856*z^18 - 103794112*z^17 + 833509632*z^16 - 5017072544*z^15 + 23079462480*z^14 - 82034034880*z^13 + 226479754000*z^12 - 486261496032*z^11 + 810690724080*z^10 - 1045949407568*z^9 + 1039208953776*z^8 - 789663151904*z^7 + 454293936064*z^6 - 194857124944*z^5 + 60848819104*z^4 - 13321576768*z^3 + 1919537344*z^2 - 161710528*z + 5958400)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_8 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 8) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_8 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^4 - 22*z^3 + 70*z^2 - 50*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(10 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_9 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 9) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_9 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^5 - 20*z^4 + 54*z^3 - 18*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 8*z + 4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_10 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 10) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_10 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*z^4 - 38*z^3 + 108*z^2 - 84*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(14 - 4*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_11 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 11) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_11 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^3 - 14*t*z^2 + 22*t*z - 12*t + 2*z^4 - 24*z^3 + 84*z^2 - 72*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t - 2*z + 12)*hf
  · have hr : (16*t^8 + 80*t^7*z^4 - 736*t^7*z^3 + 1968*t^7*z^2 - 1504*t^7*z + 272*t^7 + 144*t^6*z^8 - 2640*t^6*z^7 + 19232*t^6*z^6 - 71360*t^6*z^5 + 144400*t^6*z^4 - 159232*t^6*z^3 + 90848*t^6*z^2 - 23568*t^6*z + 1936*t^6 + 112*t^5*z^12 - 3072*t^5*z^11 + 36592*t^5*z^10 - 249408*t^5*z^9 + 1079488*t^5*z^8 - 3109952*t^5*z^7 + 6058640*t^5*z^6 - 7907584*t^5*z^5 + 6694416*t^5*z^4 - 3493984*t^5*z^3 + 1037344*t^5*z^2 - 151200*t^5*z + 7808*t^5 + 32*t^4*z^16 - 1168*t^4*z^15 + 19472*t^4*z^14 - 197296*t^4*z^13 + 1361584*t^4*z^12 - 6774144*t^4*z^11 + 24970064*t^4*z^10 - 68754576*t^4*z^9 + 140689104*t^4*z^8 - 210893872*t^4*z^7 + 226827040*t^4*z^6 - 170472320*t^4*z^5 + 86435760*t^4*z^4 - 28086688*t^4*z^3 + 5385760*t^4*z^2 - 527936*t^4*z + 19984*t^4 + 144*t^3*z^18 - 6080*t^3*z^17 + 116704*t^3*z^16 - 1349424*t^3*z^15 + 10502032*t^3*z^14 - 58233984*t^3*z^13 + 237585408*t^3*z^12 - 726186448*t^3*z^11 + 1677172048*t^3*z^10 - 2930182640*t^3*z^9 + 3851860800*t^3*z^8 - 3766627856*t^3*z^7 + 2692339264*t^3*z^6 - 1372011568*t^3*z^5 + 480966320*t^3*z^4 - 110027584*t^3*z^3 + 15153328*t^3*z^2 - 1102416*t^3*z + 31952*t^3 + 224*t^2*z^20 - 10720*t^2*z^19 + 234816*t^2*z^18 - 3120032*t^2*z^17 + 28101840*t^2*z^16 - 181662752*t^2*z^15 + 870804944*t^2*z^14 - 3154999232*t^2*z^13 + 8731994160*t^2*z^12 - 18548743872*t^2*z^11 + 30248560320*t^2*z^10 - 37734672320*t^2*z^9 + 35750451904*t^2*z^8 - 25431064848*t^2*z^7 + 13355321120*t^2*z^6 - 5052123328*t^2*z^5 + 1328040816*t^2*z^4 - 229952768*t^2*z^3 + 24143920*t^2*z^2 - 1330128*t^2*z + 25936*t^2 + 144*t*z^22 - 7696*t*z^21 + 189664*t*z^20 - 2858816*t*z^19 + 29479072*t*z^18 - 220410544*t*z^17 + 1236026832*t*z^16 - 5306327712*t*z^15 + 17653560592*t*z^14 - 45814905360*t*z^13 + 92983823952*t*z^12 - 147483298624*t*z^11 + 182198616768*t*z^10 - 174258713264*t*z^9 + 127862765728*t*z^8 - 71042411456*t*z^7 + 29338196368*t*z^6 - 8768256528*t*z^5 + 1823832448*t*z^4 - 248489600*t*z^3 + 19906864*t*z^2 - 720400*t*z + 1568*t + 32*z^24 - 1888*z^23 + 51712*z^22 - 872832*z^21 + 10164016*z^20 - 86640272*z^19 + 559894624*z^18 - 2803610384*z^17 + 11028917008*z^16 - 34369767888*z^15 + 85229357200*z^14 - 168437215376*z^13 + 265075035712*z^12 - 331230612480*z^11 + 327016779056*z^10 - 253206947568*z^9 + 152136406096*z^8 - 69859931616*z^7 + 23978608512*z^6 - 5949606832*z^5 + 1011250768*z^4 - 106776736*z^3 + 5541536*z^2 - 16128*z - 6272:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7*z + 256*t^7 - 144*t^6*z^5 + 1776*t^6*z^4 - 7856*t^6*z^3 + 15200*t^6*z^2 - 12144*t^6*z + 2512*t^6 - 112*t^5*z^9 + 2400*t^5*z^8 - 21632*t^5*z^7 + 107504*t^5*z^6 - 323904*t^5*z^5 + 607376*t^5*z^4 - 687360*t^5*z^3 + 422640*t^5*z^2 - 114400*t^5*z + 7024*t^5 - 32*t^4*z^13 + 976*t^4*z^12 - 13456*t^4*z^11 + 111648*t^4*z^10 - 623440*t^4*z^9 + 2461808*t^4*z^8 - 6970368*t^4*z^7 + 13999888*t^4*z^6 - 19376128*t^4*z^5 + 17667296*t^4*z^4 - 9942736*t^4*z^3 + 3103296*t^4*z^2 - 435008*t^4*z + 17424*t^4 - 144*t^3*z^15 + 5216*t^3*z^14 - 84688*t^3*z^13 + 815072*t^3*z^12 - 5182944*t^3*z^11 + 22976272*t^3*z^10 - 72997984*t^3*z^9 + 168134240*t^3*z^8 - 280400416*t^3*z^7 + 334110960*t^3*z^6 - 277058720*t^3*z^5 + 153320320*t^3*z^4 - 53012784*t^3*z^3 + 10274544*t^3*z^2 - 934816*t^3*z + 33184*t^3 - 224*t^2*z^17 + 9376*t^2*z^16 - 177440*t^2*z^15 + 2008288*t^2*z^14 - 15155536*t^2*z^13 + 80510656*t^2*z^12 - 309955040*t^2*z^11 + 877560176*t^2*z^10 - 1836347248*t^2*z^9 + 2832904464*t^2*z^8 - 3191837120*t^2*z^7 + 2582780032*t^2*z^6 - 1461681648*t^2*z^5 + 555237680*t^2*z^4 - 132706768*t^2*z^3 + 18012672*t^2*z^2 - 1193264*t^2*z + 23056*t^2 - 144*t*z^19 + 6832*t*z^18 - 147952*t*z^17 + 1936800*t*z^16 - 17111680*t*z^15 + 107908512*t*z^14 - 501080560*t*z^13 + 1743190112*t*z^12 - 4581108608*t*z^11 + 9111222592*t*z^10 - 13667755248*t*z^9 + 15339545568*t*z^8 - 12711344528*t*z^7 + 7625163008*t*z^6 - 3215519472*t*z^5 + 912135056*t*z^4 - 162625664*t*z^3 + 16307792*t*z^2 - 722320*t*z - 8944*t - 32*z^21 + 1696*z^20 - 41376*z^19 + 616064*z^18 - 6259056*z^17 + 45964240*z^16 - 252197840*z^15 + 1054343088*z^14 - 3395905040*z^13 + 8470424368*z^12 - 16372942704*z^11 + 24451532272*z^10 - 28030704192*z^9 + 24415783264*z^8 - 15917026240*z^7 + 7595169616*z^6 - 2564473936*z^5 + 580213680*z^4 - 79787136*z^3 + 5341680*z^2 - 51328*z - 26768)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_12 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 12) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_12 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 + 10*t*z - 10*t + 2*z^4 - 20*z^3 + 58*z^2 - 40*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8 + 80*t^7*z^4 - 864*t^7*z^3 + 2736*t^7*z^2 - 2144*t^7*z + 272*t^7 + 144*t^6*z^8 - 3120*t^6*z^7 + 26912*t^6*z^6 - 116736*t^6*z^5 + 264784*t^6*z^4 - 299968*t^6*z^3 + 158816*t^6*z^2 - 33392*t^6*z + 2320*t^6 + 112*t^5*z^12 - 3648*t^5*z^11 + 51568*t^5*z^10 - 413840*t^5*z^9 + 2071072*t^5*z^8 - 6690752*t^5*z^7 + 14000624*t^5*z^6 - 18651232*t^5*z^5 + 15315120*t^5*z^4 - 7380944*t^5*z^3 + 1940704*t^5*z^2 - 252288*t^5*z + 12704*t^5 + 32*t^4*z^16 - 1392*t^4*z^15 + 27536*t^4*z^14 - 327472*t^4*z^13 + 2606608*t^4*z^12 - 14622192*t^4*z^11 + 59252912*t^4*z^10 - 174861104*t^4*z^9 + 374293232*t^4*z^8 - 573160624*t^4*z^7 + 614576896*t^4*z^6 - 449190864*t^4*z^5 + 216515152*t^4*z^4 - 65980608*t^4*z^3 + 12006784*t^4*z^2 - 1182304*t^4*z + 48208*t^4 + 144*t^3*z^18 - 6928*t^3*z^17 + 151712*t^3*z^16 - 2000160*t^3*z^15 + 17696992*t^3*z^14 - 110903840*t^3*z^13 + 506555600*t^3*z^12 - 1710358384*t^3*z^11 + 4289134480*t^3*z^10 - 7972663728*t^3*z^9 + 10908663728*t^3*z^8 - 10869336912*t^3*z^7 + 7774389808*t^3*z^6 - 3917609952*t^3*z^5 + 1356560880*t^3*z^4 - 311710576*t^3*z^3 + 44972368*t^3*z^2 - 3663856*t^3*z + 128624*t^3 + 224*t^2*z^20 - 11824*t^2*z^19 + 286288*t^2*z^18 - 4211328*t^2*z^17 + 42023664*t^2*z^16 - 300845184*t^2*z^15 + 1593988848*t^2*z^14 - 6359249072*t^2*z^13 + 19264484912*t^2*z^12 - 44418368976*t^2*z^11 + 77802570752*t^2*z^10 - 103025579840*t^2*z^9 + 102420931392*t^2*z^8 - 75751783664*t^2*z^7 + 41191211344*t^2*z^6 - 16204517808*t^2*z^5 + 4508146736*t^2*z^4 - 857000288*t^2*z^3 + 105151600*t^2*z^2 - 7458192*t^2*z + 230416*t^2 + 144*t*z^22 - 8288*t*z^21 + 220480*t*z^20 - 3595008*t*z^19 + 40174736*t*z^18 - 325986432*t*z^17 + 1985453376*t*z^16 - 9257253008*t*z^15 + 33415444352*t*z^14 - 93896335152*t*z^13 + 205694643712*t*z^12 - 350806114160*t*z^11 + 464221303776*t*z^10 - 474370113872*t*z^9 + 371993745872*t*z^8 - 222016935424*t*z^7 + 99698018416*t*z^6 - 33132415888*t*z^5 + 7949859888*t*z^4 - 1325372256*t*z^3 + 144095920*t*z^2 - 9078704*t*z + 247520*t + 32*z^24 - 2000*z^23 + 58160*z^22 - 1044544*z^21 + 12969952*z^20 - 118116016*z^19 + 816843440*z^18 - 4382985744*z^17 + 18492369296*z^16 - 61832665472*z^15 + 164506397616*z^14 - 348676810560*z^13 + 588338068000*z^12 - 788670076016*z^11 + 837311024464*z^10 - 701134295808*z^9 + 460449020784*z^8 - 235246118448*z^7 + 92393228736*z^6 - 27395087504*z^5 + 5962173376*z^4 - 910289184*z^3 + 90236672*z^2 - 5007392*z + 108160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7*z + 384*t^7 - 144*t^6*z^5 + 2256*t^6*z^4 - 12656*t^6*z^3 + 29376*t^6*z^2 - 22992*t^6*z + 2480*t^6 - 112*t^5*z^9 + 2976*t^5*z^8 - 33152*t^5*z^7 + 199936*t^5*z^6 - 702720*t^5*z^5 + 1441600*t^5*z^4 - 1637488*t^5*z^3 + 915584*t^5*z^2 - 192576*t^5*z + 10080*t^5 - 32*t^4*z^13 + 1200*t^4*z^12 - 20176*t^4*z^11 + 200384*t^4*z^10 - 1302224*t^4*z^9 + 5786752*t^4*z^8 - 17820896*t^4*z^7 + 37699744*t^4*z^6 - 53203536*t^4*z^5 + 47619792*t^4*z^4 - 25140720*t^4*z^3 + 7044048*t^4*z^2 - 927472*t^4*z + 54816*t^4 - 144*t^3*z^15 + 6064*t^3*z^14 - 114608*t^3*z^13 + 1282048*t^3*z^12 - 9425600*t^3*z^11 + 47825392*t^3*z^10 - 171193200*t^3*z^9 + 434646624*t^3*z^8 - 777463344*t^3*z^7 + 963457344*t^3*z^6 - 805956320*t^3*z^5 + 438848928*t^3*z^4 - 148057296*t^3*z^3 + 29065216*t^3*z^2 - 3034176*t^3*z + 122144*t^3 - 224*t^2*z^17 + 10480*t^2*z^16 - 222288*t^2*z^15 + 2824976*t^2*z^14 - 23951888*t^2*z^13 + 142786688*t^2*z^12 - 614684304*t^2*z^11 + 1933257920*t^2*z^10 - 4448729184*t^2*z^9 + 7445019968*t^2*z^8 - 8955547104*t^2*z^7 + 7618468192*t^2*z^6 - 4487366752*t^2*z^5 + 1779695088*t^2*z^4 - 457738864*t^2*z^3 + 72242432*t^2*z^2 - 6302736*t^2*z + 232848*t^2 - 144*t*z^19 + 7424*t*z^18 - 175216*t*z^17 + 2506448*t*z^16 - 24252544*t*z^15 + 167763712*t*z^14 - 855101936*t*z^13 + 3263570288*t*z^12 - 9390749232*t*z^11 + 20378886384*t*z^10 - 33204008960*t*z^9 + 40296879248*t*z^8 - 36041097104*t*z^7 + 23435126048*t*z^6 - 10880624816*t*z^5 + 3516459184*t*z^4 - 761013184*t*z^3 + 103416048*t*z^2 - 7838496*t*z + 247856*t - 32*z^21 + 1808*z^20 - 47152*z^19 + 752560*z^18 - 8217024*z^17 + 65003920*z^16 - 384982240*z^15 + 1739855680*z^14 - 6063320096*z^13 + 16368484256*z^12 - 34239035920*z^11 + 55336853664*z^10 - 68753282160*z^9 + 65227078816*z^8 - 46845287104*z^7 + 25173896944*z^6 - 9952124784*z^5 + 2818597920*z^4 - 547120352*z^3 + 67251008*z^2 - 4467648*z + 107904)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_13 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 13) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_13 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^4 - 20*t*z^3 + 54*t*z^2 - 20*t*z - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t*z + 8*t)*hf
  · have hr : (16*t^8 + 144*t^7*z^4 - 1504*t^7*z^3 + 4528*t^7*z^2 - 3104*t^7*z + 400*t^7 + 480*t^6*z^8 - 10032*t^6*z^7 + 82800*t^6*z^6 - 339024*t^6*z^5 + 708800*t^6*z^4 - 713616*t^6*z^3 + 339968*t^6*z^2 - 70592*t^6*z + 5488*t^6 + 704*t^5*z^12 - 22080*t^5*z^11 + 298432*t^5*z^10 - 2268576*t^5*z^9 + 10621456*t^5*z^8 - 31590800*t^5*z^7 + 59722176*t^5*z^6 - 70774720*t^5*z^5 + 51962784*t^5*z^4 - 23195456*t^5*z^3 + 6055504*t^5*z^2 - 849072*t^5*z + 48640*t^5 + 384*t^4*z^16 - 16064*t^4*z^15 + 302688*t^4*z^14 - 3391408*t^4*z^13 + 25125248*t^4*z^12 - 129507120*t^4*z^11 + 476145024*t^4*z^10 - 1260925248*t^4*z^9 + 2404878496*t^4*z^8 - 3281369392*t^4*z^7 + 3169128960*t^4*z^6 - 2136835968*t^4*z^5 + 986722736*t^4*z^4 - 302715280*t^4*z^3 + 58526448*t^4*z^2 - 6422960*t^4*z + 305776*t^4 + 1600*t^3*z^18 - 74688*t^3*z^17 + 1582864*t^3*z^16 - 20135856*t^3*z^15 + 171304272*t^3*z^14 - 1028085712*t^3*z^13 + 4476805776*t^3*z^12 - 14342786384*t^3*z^11 + 33981978096*t^3*z^10 - 59524214256*t^3*z^9 + 76852441568*t^3*z^8 - 72836498224*t^3*z^7 + 50377266592*t^3*z^6 - 25182295152*t^3*z^5 + 8944988768*t^3*z^4 - 2191791904*t^3*z^3 + 350999504*t^3*z^2 - 32948960*t^3*z + 1367824*t^3 + 2432*t^2*z^20 - 125344*t^2*z^19 + 2961552*t^2*z^18 - 42485904*t^2*z^17 + 413190000*t^2*z^16 - 2881095696*t^2*z^15 + 14860577248*t^2*z^14 - 57702342096*t^2*z^13 + 170194018048*t^2*z^12 - 382650020240*t^2*z^11 + 655819498224*t^2*z^10 - 855267539248*t^2*z^9 + 846289605184*t^2*z^8 - 632674836128*t^2*z^7 + 354831869760*t^2*z^6 - 147533557792*t^2*z^5 + 44591743200*t^2*z^4 - 9483980320*t^2*z^3 + 1341823904*t^2*z^2 - 113256816*t^2*z + 4318864*t^2 + 1600*t*z^22 - 90272*t*z^21 + 2354784*t*z^20 - 37665232*t*z^19 + 413144304*t*z^18 - 3293100976*t*z^17 + 19724985056*t*z^16 - 90593931056*t*z^15 + 322883345232*t*z^14 - 898883440768*t*z^13 + 1960430724528*t*z^12 - 3351671111696*t*z^11 + 4488424409984*t*z^10 - 4699774800992*t*z^9 + 3836091532592*t*z^8 - 2428205007360*t*z^7 + 1181746984352*t*z^6 - 436063028480*t*z^5 + 119320522624*t*z^4 - 23361996976*t*z^3 + 3081241376*t*z^2 - 244157264*t*z + 8742496*t + 384*z^24 - 23552*z^23 + 672672*z^22 - 11877568*z^21 + 145177888*z^20 - 1303470304*z^19 + 8904327056*z^18 - 47311655120*z^17 + 198285990992*z^16 - 661270629872*z^15 + 1763920388752*z^14 - 3773776190944*z^13 + 6482571077536*z^12 - 8941261580640*z^11 + 9893754989344*z^10 - 8766244227008*z^9 + 6198025204128*z^8 - 3476416891104*z^7 + 1532288437120*z^6 - 522941896880*z^5 + 135049542992*z^4 - 25448192240*z^3 + 3291970208*z^2 - 260514080*z + 9471616:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-144*t^7*z + 640*t^7 - 480*t^6*z^5 + 7152*t^6*z^4 - 37488*t^6*z^3 + 77856*t^6*z^2 - 47072*t^6*z + 4416*t^6 - 704*t^5*z^9 + 17856*t^5*z^8 - 187776*t^5*z^7 + 1051936*t^5*z^6 - 3353104*t^5*z^5 + 6024720*t^5*z^4 - 5756400*t^5*z^3 + 2759616*t^5*z^2 - 598368*t^5*z + 50768*t^5 - 384*t^4*z^13 + 13760*t^4*z^12 - 218208*t^4*z^11 + 2012976*t^4*z^10 - 11942592*t^4*z^9 + 47568480*t^4*z^8 - 129008208*t^4*z^7 + 237091008*t^4*z^6 - 289722928*t^4*z^5 + 228568576*t^4*z^4 - 112011856*t^4*z^3 + 32199024*t^4*z^2 - 4900736*t^4*z + 303888*t^4 - 1600*t^3*z^15 + 65088*t^3*z^14 - 1184336*t^3*z^13 + 12702800*t^3*z^12 - 89100704*t^3*z^11 + 428783152*t^3*z^10 - 1445900544*t^3*z^9 + 3434366656*t^3*z^8 - 5717492288*t^3*z^7 + 6601526704*t^3*z^6 - 5221453248*t^3*z^5 + 2782652928*t^3*z^4 - 972556080*t^3*z^3 + 212240784*t^3*z^2 - 26110736*t^3*z + 1367488*t^3 - 2432*t^2*z^17 + 110752*t^2*z^16 - 2284880*t^2*z^15 + 28220432*t^2*z^14 - 232332256*t^2*z^13 + 1343715120*t^2*z^12 - 5608404816*t^2*z^11 + 17101005344*t^2*z^10 - 38202246784*t^2*z^9 + 62323108000*t^2*z^8 - 73768610960*t^2*z^7 + 62838086704*t^2*z^6 - 38094922160*t^2*z^5 + 16146258688*t^2*z^4 - 4641620128*t^2*z^3 + 857621424*t^2*z^2 - 91655328*t^2*z + 4321104*t^2 - 1600*t*z^19 + 80672*t*z^18 - 1862752*t*z^17 + 26083760*t*z^16 - 247247312*t*z^15 + 1677335552*t*z^14 - 8398651424*t*z^13 + 31568097440*t*z^12 - 89804167920*t*z^11 + 193819294624*t*z^10 - 316926019744*t*z^9 + 391214352192*t*z^8 - 362688903488*t*z^7 + 250643599360*t*z^6 - 127571066800*t*z^5 + 46871706272*t*z^4 - 12017813360*t*z^3 + 2026550160*t*z^2 - 200448592*t*z + 8741264*t - 384*z^21 + 21248*z^20 - 543264*z^19 + 8511360*z^18 - 91372160*z^17 + 712137280*z^16 - 4166131216*z^15 + 18662809264*z^14 - 64766342048*z^13 + 175192400048*z^12 - 370271468960*z^11 + 611419034896*z^10 - 787507123312*z^9 + 788852197328*z^8 - 611687153920*z^7 + 364353193536*z^6 - 164618075984*z^5 + 55255313600*z^4 - 13312982064*z^3 + 2169360512*z^2 - 213156000*z + 9471616)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_14 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 14) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_14 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^3 - 14*t*z^2 + 22*t*z - 12*t + 2*z^4 - 24*z^3 + 84*z^2 - 72*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t - 2*z + 12)*hf
  · have hr : (16*t^8 + 80*t^7*z^4 - 800*t^7*z^3 + 2352*t^7*z^2 - 1760*t^7*z + 208*t^7 + 144*t^6*z^8 - 2880*t^6*z^7 + 22976*t^6*z^6 - 92624*t^6*z^5 + 197216*t^6*z^4 - 213328*t^6*z^3 + 108528*t^6*z^2 - 21488*t^6*z + 1216*t^6 + 112*t^5*z^12 - 3360*t^5*z^11 + 43840*t^5*z^10 - 325936*t^5*z^9 + 1519840*t^5*z^8 - 4612400*t^5*z^7 + 9161024*t^5*z^6 - 11704864*t^5*z^5 + 9262464*t^5*z^4 - 4272368*t^5*z^3 + 1041088*t^5*z^2 - 114672*t^5*z + 4432*t^5 + 32*t^4*z^16 - 1280*t^4*z^15 + 23360*t^4*z^14 - 257520*t^4*z^13 + 1911728*t^4*z^12 - 10072912*t^4*z^11 + 38627040*t^4*z^10 - 108640384*t^4*z^9 + 222923584*t^4*z^8 - 328421040*t^4*z^7 + 338832336*t^4*z^6 - 236960864*t^4*z^5 + 107636432*t^4*z^4 - 29923376*t^4*z^3 + 4676528*t^4*z^2 - 363824*t^4*z + 10960*t^4 + 144*t^3*z^18 - 6448*t^3*z^17 + 131520*t^3*z^16 - 1616928*t^3*z^15 + 13361904*t^3*z^14 - 78371936*t^3*z^13 + 335900576*t^3*z^12 - 1067481168*t^3*z^11 + 2527810880*t^3*z^10 - 4449827824*t^3*z^9 + 5774712560*t^3*z^8 - 5448742416*t^3*z^7 + 3664978352*t^3*z^6 - 1709941536*t^3*z^5 + 532673216*t^3*z^4 - 105012848*t^3*z^3 + 12152832*t^3*z^2 - 738896*t^3*z + 18016*t^3 + 224*t^2*z^20 - 11088*t^2*z^19 + 251792*t^2*z^18 - 3474688*t^2*z^17 + 32539408*t^2*z^16 - 218723488*t^2*z^15 + 1088792192*t^2*z^14 - 4083921376*t^2*z^13 + 11639316208*t^2*z^12 - 25257395216*t^2*z^11 + 41618826800*t^2*z^10 - 51738729568*t^2*z^9 + 48048383392*t^2*z^8 - 32881134080*t^2*z^7 + 16274338848*t^2*z^6 - 5677599152*t^2*z^5 + 1347165216*t^2*z^4 - 206777536*t^2*z^3 + 19053632*t^2*z^2 - 917808*t^2*z + 16288*t^2 + 144*t*z^22 - 7808*t*z^21 + 195664*t*z^20 - 3005136*t*z^19 + 31631440*t*z^18 - 241741120*t*z^17 + 1386672416*t*z^16 - 6088526208*t*z^15 + 20690997040*t*z^14 - 54706534576*t*z^13 + 112631858208*t*z^12 - 180126712992*t*z^11 + 222614907408*t*z^10 - 211005543088*t*z^9 + 151812836624*t*z^8 - 81754587424*t*z^7 + 32323533168*t*z^6 - 9131489056*t*z^5 + 1772457824*t*z^4 - 222774128*t*z^3 + 16388272*t*z^2 - 558464*t*z + 1792*t + 32*z^24 - 1888*z^23 + 51824*z^22 - 878464*z^21 + 10293728*z^20 - 88452688*z^19 + 577051248*z^18 - 2919994880*z^17 + 11612716352*z^16 - 36573305840*z^15 + 91541378640*z^14 - 182187791424*z^13 + 287787093008*z^12 - 359451251584*z^11 + 353039531184*z^10 - 270615614112*z^9 + 160247054592*z^8 - 72269668560*z^7 + 24318375328*z^6 - 5918567680*z^5 + 990271088*z^4 - 103656528*z^3 + 5389248*z^2 - 16352*z - 6272:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7*z + 320*t^7 - 144*t^6*z^5 + 2016*t^6*z^4 - 10160*t^6*z^3 + 21440*t^6*z^2 - 15760*t^6*z + 1408*t^6 - 112*t^5*z^9 + 2688*t^5*z^8 - 27152*t^5*z^7 + 149472*t^5*z^6 - 484560*t^5*z^5 + 930528*t^5*z^4 - 1005584*t^5*z^3 + 534160*t^5*z^2 - 99056*t^5*z + 1648*t^5 - 32*t^4*z^13 + 1088*t^4*z^12 - 16672*t^4*z^11 + 152016*t^4*z^10 - 915184*t^4*z^9 + 3805056*t^4*z^8 - 11068768*t^4*z^7 + 22287312*t^4*z^6 - 30050816*t^4*z^5 + 25610816*t^4*z^4 - 12626048*t^4*z^3 + 3099680*t^4*z^2 - 297296*t^4*z + 15152*t^4 - 144*t^3*z^15 + 5584*t^3*z^14 - 97296*t^3*z^13 + 1005088*t^3*z^12 - 6839312*t^3*z^11 + 32213328*t^3*z^10 - 107418960*t^3*z^9 + 255061456*t^3*z^8 - 428134016*t^3*z^7 + 498297488*t^3*z^6 - 389196096*t^3*z^5 + 193944384*t^3*z^4 - 57034080*t^3*z^3 + 8819040*t^3*z^2 - 644192*t^3*z + 18416*t^3 - 224*t^2*z^17 + 9744*t^2*z^16 - 192208*t^2*z^15 + 2272496*t^2*z^14 - 17933648*t^2*z^13 + 99566912*t^2*z^12 - 399449984*t^2*z^11 + 1171453264*t^2*z^10 - 2513779792*t^2*z^9 + 3918000160*t^2*z^8 - 4370473616*t^2*z^7 + 3412107280*t^2*z^6 - 1805371472*t^2*z^5 + 617895232*t^2*z^4 - 128002816*t^2*z^3 + 14734624*t^2*z^2 - 848160*t^2*z + 12640*t^2 - 144*t*z^19 + 6944*t*z^18 - 153280*t*z^17 + 2050592*t*z^16 - 18554544*t*z^15 + 120007616*t*z^14 - 571803408*t*z^13 + 2039113136*t*z^12 - 5477293568*t*z^11 + 11075404080*t*z^10 - 16753852752*t*z^9 + 18749282512*t*z^8 - 15274544496*t*z^7 + 8858010800*t*z^6 - 3542766832*t*z^5 + 933387936*t*z^4 - 151360592*t*z^3 + 13618992*t*z^2 - 552976*t*z + 720*t - 32*z^21 + 1696*z^20 - 41488*z^19 + 621024*z^18 - 6358448*z^17 + 47155392*z^16 - 261705632*z^15 + 1107625680*z^14 - 3611278720*z^13 + 9105799488*z^12 - 17742562432*z^11 + 26592140672*z^10 - 30415637328*z^9 + 26254161824*z^8 - 16844232928*z^7 + 7863770096*z^6 - 2589107552*z^5 + 571939840*z^4 - 77428432*z^3 + 5190336*z^2 - 47072*z - 6016)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_15 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 15) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_15 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z^2 - 10*t^2*z + 6*t^2 - 8*t*z^2 + 40*t*z - 24*t + 2*z^4 - 20*z^3 + 62*z^2 - 60*z + 18:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8*z^8 - 320*t^8*z^7 + 2592*t^8*z^6 - 10880*t^8*z^5 + 25264*t^8*z^4 - 32640*t^8*z^3 + 23328*t^8*z^2 - 8640*t^8*z + 1296*t^8 + 144*t^7*z^10 - 3664*t^7*z^9 + 39184*t^7*z^8 - 228448*t^7*z^7 + 789008*t^7*z^6 - 1651376*t^7*z^5 + 2087216*t^7*z^4 - 1579872*t^7*z^3 + 691632*t^7*z^2 - 158544*t^7*z + 14256*t^7 + 560*t^6*z^12 - 17280*t^6*z^11 + 230256*t^6*z^10 - 1732288*t^6*z^9 + 8081280*t^6*z^8 - 24220864*t^6*z^7 + 46984432*t^6*z^6 - 58643904*t^6*z^5 + 46694528*t^6*z^4 - 23216000*t^6*z^3 + 6847344*t^6*z^2 - 1067904*t^6*z + 65232*t^6 + 1248*t^5*z^14 - 45200*t^5*z^13 + 721328*t^5*z^12 - 6665328*t^5*z^11 + 39425792*t^5*z^10 - 155952800*t^5*z^9 + 419392432*t^5*z^8 - 767702320*t^5*z^7 + 950590208*t^5*z^6 - 789639200*t^5*z^5 + 433425808*t^5*z^4 - 152388720*t^5*z^3 + 32289408*t^5*z^2 - 3649104*t^5*z + 163296*t^5 + 1744*t^4*z^16 - 72432*t^4*z^15 + 1346176*t^4*z^14 - 14762176*t^4*z^13 + 106053008*t^4*z^12 - 524254480*t^4*z^11 + 1824442336*t^4*z^10 - 4504654768*t^4*z^9 + 7880290688*t^4*z^8 - 9708587088*t^4*z^7 + 8358565824*t^4*z^6 - 4969217648*t^4*z^5 + 1996989936*t^4*z^4 - 522302688*t^4*z^3 + 83143392*t^4*z^2 - 7107120*t^4*z + 243216*t^4 + 1552*t^3*z^18 - 72640*t^3*z^17 + 1540112*t^3*z^16 - 19549552*t^3*z^15 + 165446432*t^3*z^14 - 984055536*t^3*z^13 + 4227130080*t^3*z^12 - 13281479568*t^3*z^11 + 30628382608*t^3*z^10 - 51716743232*t^3*z^9 + 63582406368*t^3*z^8 - 56508926880*t^3*z^7 + 35941582720*t^3*z^6 - 16098522096*t^3*z^5 + 4945197216*t^3*z^4 - 997646224*t^3*z^3 + 122981568*t^3*z^2 - 8126640*t^3*z + 210384*t^3 + 848*t^2*z^20 - 44128*t^2*z^19 + 1050560*t^2*z^18 - 15148800*t^2*z^17 + 147648576*t^2*z^16 - 1028002000*t^2*z^15 + 5270242496*t^2*z^14 - 20220753312*t^2*z^13 + 58488424432*t^2*z^12 - 127702100784*t^2*z^11 + 209890531104*t^2*z^10 - 258365794160*t^2*z^9 + 236619842672*t^2*z^8 - 159807909488*t^2*z^7 + 78560079360*t^2*z^6 - 27549361872*t^2*z^5 + 6679103904*t^2*z^4 - 1065452160*t^2*z^3 + 102970240*t^2*z^2 - 5142416*t^2*z + 86160*t^2 + 256*t*z^22 - 14656*t*z^21 + 387008*t*z^20 - 6248496*t*z^19 + 68944400*t*z^18 - 550452688*t*z^17 + 3285188400*t*z^16 - 14934901728*t*z^15 + 52250026176*t*z^14 - 141284802288*t*z^13 + 295328989856*t*z^12 - 475939061088*t*z^11 + 588644225104*t*z^10 - 555420128048*t*z^9 + 396690728256*t*z^8 - 212100458576*t*z^7 + 83521261648*t*z^6 - 23633012432*t*z^5 + 4625851040*t*z^4 - 588725264*t*z^3 + 43455104*t*z^2 - 1402672*t*z + 672*t + 32*z^24 - 2000*z^23 + 58048*z^22 - 1038176*z^21 + 12802800*z^20 - 115430224*z^19 + 787308096*z^18 - 4147516304*z^17 + 17085619248*z^16 - 55410239504*z^15 + 141846492816*z^14 - 286539207584*z^13 + 455655039680*z^12 - 568165964848*z^11 + 552656100608*z^10 - 416512919232*z^9 + 240947945328*z^8 - 105545994960*z^7 + 34305596944*z^6 - 8017530576*z^5 + 1279461104*z^4 - 126691120*z^3 + 6163584*z^2 - 15232*z - 6272:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^5 + 224*t^8*z^4 - 1168*t^8*z^3 + 2736*t^8*z^2 - 2784*t^8*z + 1088*t^8 - 144*t^7*z^7 + 2800*t^7*z^6 - 21664*t^7*z^5 + 84320*t^7*z^4 - 171968*t^7*z^3 + 176304*t^7*z^2 - 85232*t^7*z + 14992*t^7 - 560*t^6*z^9 + 13920*t^6*z^8 - 143936*t^6*z^7 + 798512*t^6*z^6 - 2556608*t^6*z^5 + 4744720*t^6*z^4 - 4934560*t^6*z^3 + 2756336*t^6*z^2 - 738992*t^6*z + 65808*t^6 - 1248*t^5*z^11 + 37712*t^5*z^10 - 488816*t^5*z^9 + 3542624*t^5*z^8 - 15688256*t^5*z^7 + 43621328*t^5*z^6 - 75680560*t^5*z^5 + 79824064*t^5*z^4 - 49621696*t^5*z^3 + 17108144*t^5*z^2 - 2844400*t^5*z + 159904*t^5 - 1744*t^4*z^13 + 61968*t^4*z^12 - 965648*t^4*z^11 + 8656704*t^4*z^10 - 49222576*t^4*z^9 + 184669856*t^4*z^8 - 461653616*t^4*z^7 + 762161216*t^4*z^6 - 814385456*t^4*z^5 + 549814656*t^4*z^4 - 225589392*t^4*z^3 + 52222560*t^4*z^2 - 5892960*t^4*z + 242736*t^4 - 1552*t^3*z^15 + 63328*t^3*z^14 - 1152384*t^3*z^13 + 12317056*t^3*z^12 - 85718848*t^3*z^11 + 407004784*t^3*z^10 - 1344190080*t^3*z^9 + 3095596320*t^3*z^8 - 4926849504*t^3*z^7 + 5333474528*t^3*z^6 - 3851715360*t^3*z^5 + 1804412576*t^3*z^4 - 523055936*t^3*z^3 + 86408240*t^3*z^2 - 7055520*t^3*z + 215968*t^3 - 848*t^2*z^17 + 39040*t^2*z^16 - 812080*t^2*z^15 + 10080272*t^2*z^14 - 83067504*t^2*z^13 + 478383536*t^2*z^12 - 1974523488*t^2*z^11 + 5898627200*t^2*z^10 - 12745660256*t^2*z^9 + 19760479760*t^2*z^8 - 21700724064*t^2*z^7 + 16613390720*t^2*z^6 - 8675398272*t^2*z^5 + 2987842192*t^2*z^4 - 642644128*t^2*z^3 + 78887872*t^2*z^2 - 4713840*t^2*z + 85632*t^2 - 256*t*z^19 + 13120*t*z^18 - 307008*t*z^17 + 4340592*t*z^16 - 41352688*t*z^15 + 280326592*t*z^14 - 1392124816*t*z^13 + 5139167184*t*z^12 - 14174072400*t*z^11 + 29152407152*t*z^10 - 44405017760*t*z^9 + 49572846368*t*z^8 - 40029650944*t*z^7 + 22972972784*t*z^6 - 9131790464*t*z^5 + 2415200928*t*z^4 - 398130976*t*z^3 + 36431472*t*z^2 - 1406400*t*z - 1472*t - 32*z^21 + 1808*z^20 - 47040*z^19 + 746864*z^18 - 8084608*z^17 + 63141216*z^16 - 367290896*z^15 + 1619980240*z^14 - 5466142112*z^13 + 14146194736*z^12 - 28018633600*z^11 + 42230290192*z^10 - 48033935792*z^9 + 40792265536*z^8 - 25502538240*z^7 + 11502426320*z^6 - 3628430672*z^5 + 760741088*z^4 - 96570736*z^3 + 5970048*z^2 - 46048*z - 6144)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_16 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 16) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_16 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*z^6 - 60*z^5 + 328*z^4 - 780*z^3 + 760*z^2 - 300*z + 36:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4*z^3 + 36*z^2 - 92*z + 44)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_17 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 17) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_17 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 30*z^5 + 164*z^4 - 390*z^3 + 376*z^2 - 130*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^3 + 18*z^2 - 46*z + 22)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_18 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 18) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_18 z t hf hn0 hn1 hn2 hn3
  · have hr : (16*t*z^19 - 720*t*z^18 + 14576*t*z^17 - 175040*t*z^16 + 1383776*t*z^15 - 7552160*t*z^14 + 29002336*t*z^13 - 78318080*t*z^12 + 145822896*t*z^11 - 178812400*t*z^10 + 130372368*t*z^9 - 39887360*t*z^8 - 10937312*t*z^7 + 10403680*t*z^6 - 456672*t*z^5 - 953280*t*z^4 + 34128*t*z^3 + 45360*t*z^2 + 3888*t*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t*z^16 + 624*t*z^15 - 10752*t*z^14 + 107392*t*z^13 - 685040*t*z^12 + 2894208*t*z^11 - 8104496*t*z^10 + 14535024*t*z^9 - 15196064*t*z^8 + 6856400*t*z^7 + 1281376*t*z^6 - 1902448*t*z^5 - 27856*t*z^4 + 222800*t*z^3 + 30304*t*z^2 - 6752*t*z - 3360*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_19 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 19) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_19 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^4 + 20*t*z^3 - 62*t*z^2 + 60*t*z - 22*t + 4*z^6 - 60*z^5 + 330*z^4 - 800*z^3 + 822*z^2 - 360*z + 56:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t*z - 8*t - 4*z^3 + 36*z^2 - 94*z + 52)*hf
  · have hr : (16*t^8 + 16*t^7*z^4 - 160*t^7*z^3 + 432*t^7*z^2 - 288*t^7*z - 48*t^7 + 16*t^6*z^6 - 320*t^6*z^5 + 2096*t^6*z^4 - 5120*t^6*z^3 + 3728*t^6*z^2 - 160*t^6*z - 192*t^6 + 16*t^5*z^10 - 384*t^5*z^9 + 3808*t^5*z^8 - 20192*t^5*z^7 + 62048*t^5*z^6 - 111808*t^5*z^5 + 110448*t^5*z^4 - 43008*t^5*z^3 - 5696*t^5*z^2 + 4416*t^5*z + 576*t^5 - 48*t^4*z^11 + 1152*t^4*z^10 - 11504*t^4*z^9 + 62176*t^4*z^8 - 198352*t^4*z^7 + 380208*t^4*z^6 - 413680*t^4*z^5 + 199200*t^4*z^4 - 848*t^4*z^3 - 20448*t^4*z^2 + 432*t^4*z + 432*t^4 + 16*t^3*z^15 - 544*t^3*z^14 + 8000*t^3*z^13 - 66224*t^3*z^12 + 335344*t^3*z^11 - 1048528*t^3*z^10 + 1892240*t^3*z^9 - 1422416*t^3*z^8 - 993328*t^3*z^7 + 2697472*t^3*z^6 - 1612688*t^3*z^5 + 3184*t^3*z^4 + 233376*t^3*z^3 - 9648*t^3*z^2 - 14256*t^3*z - 1296*t^3 - 32*t^2*z^16 + 1104*t^2*z^15 - 16560*t^2*z^14 + 141088*t^2*z^13 - 747312*t^2*z^12 + 2524400*t^2*z^11 - 5327152*t^2*z^10 + 6423856*t^2*z^9 - 3129440*t^2*z^8 - 1334224*t^2*z^7 + 1966352*t^2*z^6 - 307312*t^2*z^5 - 245136*t^2*z^4 + 31392*t^2*z^3 + 16848*t^2*z^2 + 1296*t^2*z + 16*t*z^19 - 720*t*z^18 + 14592*t*z^17 - 175616*t*z^16 + 1392896*t*z^15 - 7635552*t*z^14 + 29488240*t*z^13 - 80194320*t*z^12 + 150652640*t*z^11 - 186907888*t*z^10 + 138637984*t*z^9 - 44181152*t*z^8 - 10634192*t*z^7 + 11041920*t*z^6 - 605664*t*z^5 - 991728*t*z^4 + 41472*t*z^3 + 46656*t*z^2 + 3888*t*z + 16*z^17 - 560*z^16 + 8560*z^15 - 74704*z^14 + 408064*z^13 - 1436832*z^12 + 3230656*z^11 - 4413184*z^10 + 3238464*z^9 - 816432*z^8 - 327360*z^7 + 176976*z^6 + 15696*z^5 - 10368*z^4 - 1296*z^3:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7*z + 64*t^7 - 16*t^6*z^3 + 224*t^6*z^2 - 672*t^6*z - 48*t^6 - 16*t^5*z^7 + 288*t^5*z^6 - 2000*t^5*z^5 + 6736*t^5*z^4 - 11344*t^5*z^3 + 8064*t^5*z^2 + 1392*t^5*z - 304*t^5 + 48*t^4*z^8 - 864*t^4*z^7 + 6080*t^4*z^6 - 21328*t^4*z^5 + 39120*t^4*z^4 - 32768*t^4*z^3 + 144*t^4*z^2 + 4624*t^4*z - 4896*t^4 - 16*t^3*z^12 + 448*t^3*z^11 - 5232*t^3*z^10 + 32576*t^3*z^9 - 113280*t^3*z^8 + 200736*t^3*z^7 - 88848*t^3*z^6 - 227632*t^3*z^5 + 272512*t^3*z^4 - 13088*t^3*z^3 - 56032*t^3*z^2 - 1424*t^3*z + 25152*t^3 + 32*t^2*z^13 - 912*t^2*z^12 + 10928*t^2*z^11 - 70928*t^2*z^10 + 266192*t^2*z^9 - 561680*t^2*z^8 + 555184*t^2*z^7 - 18160*t^2*z^6 - 317120*t^2*z^5 + 77488*t^2*z^4 + 66016*t^2*z^3 - 1152*t^2*z^2 - 14368*t^2*z - 45824*t^2 - 16*t*z^16 + 624*t*z^15 - 10768*t*z^14 + 107872*t*z^13 - 691200*t*z^12 + 2938224*t*z^11 - 8295024*t*z^10 + 15041856*t*z^9 - 15988160*t*z^8 + 7474624*t*z^7 + 1192416*t*z^6 - 2025632*t*z^5 - 7056*t*z^4 + 236320*t*z^3 + 33232*t*z^2 + 2464*t*z + 43472*t - 16*z^14 + 464*z^13 - 5696*z^12 + 38192*z^11 - 149968*z^10 + 340368*z^9 - 400416*z^8 + 158880*z^7 + 57264*z^6 - 34800*z^5 - 8880*z^4 + 1008*z^3 - 48*z^2 - 3840*z - 20496)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_20 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 20) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_20 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 30*z^5 + 164*z^4 - 390*z^3 + 376*z^2 - 130*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^3 + 18*z^2 - 46*z + 22)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_21 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 21) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_21 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 30*z^5 + 160*z^4 - 350*z^3 + 258*z^2 - 40*z - 12:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^3 + 18*z^2 - 42*z + 6)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_22 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 22) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_22 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 30*z^5 + 164*z^4 - 396*z^3 + 414*z^2 - 178*z + 24:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^3 + 18*z^2 - 46*z + 28)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_23 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 23) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_23 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t*z^2 + 30*t*z - 18*t + 2*z^6 - 30*z^5 + 164*z^4 - 390*z^3 + 382*z^2 - 160*z + 24:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^3 + 18*z^2 - 46*z + 22)*hf
  · have hr : (16*t^8 + 80*t^7*z^4 - 864*t^7*z^3 + 2608*t^7*z^2 - 1504*t^7*z + 16*t^7 + 144*t^6*z^8 - 3120*t^6*z^7 + 26368*t^6*z^6 - 108128*t^6*z^5 + 215984*t^6*z^4 - 184224*t^6*z^3 + 58176*t^6*z^2 - 2896*t^6*z + 208*t^6 + 112*t^5*z^12 - 3648*t^5*z^11 + 50752*t^5*z^10 - 392048*t^5*z^9 + 1829296*t^5*z^8 - 5255600*t^5*z^7 + 9109680*t^5*z^6 - 9076192*t^5*z^5 + 4942272*t^5*z^4 - 1349968*t^5*z^3 + 170128*t^5*z^2 - 16752*t^5*z + 256*t^5 + 32*t^4*z^16 - 1392*t^4*z^15 + 27024*t^4*z^14 - 308208*t^4*z^13 + 2287328*t^4*z^12 - 11561520*t^4*z^11 + 40515488*t^4*z^10 - 98483552*t^4*z^9 + 164228272*t^4*z^8 - 184804560*t^4*z^7 + 138350960*t^4*z^6 - 68022672*t^4*z^5 + 21707040*t^4*z^4 - 4448016*t^4*z^3 + 554400*t^4*z^2 - 30880*t^4*z + 976*t^4 + 32*t^3*z^18 - 1488*t^3*z^17 + 31248*t^3*z^16 - 391536*t^3*z^15 + 3258528*t^3*z^14 - 18981040*t^3*z^13 + 79495488*t^3*z^12 - 242363376*t^3*z^11 + 539576928*t^3*z^10 - 874580368*t^3*z^9 + 1024844464*t^3*z^8 - 859433360*t^3*z^7 + 508465968*t^3*z^6 - 208031648*t^3*z^5 + 57290896*t^3*z^4 - 10226528*t^3*z^3 + 1098192*t^3*z^2 - 57472*t^3*z + 1744*t^3 + 32*t^2*z^19 - 1456*t^2*z^18 + 29648*t^2*z^17 - 355280*t^2*z^16 + 2766896*t^2*z^15 - 14544064*t^2*z^14 + 51447856*t^2*z^13 - 115043024*t^2*z^12 + 120536960*t^2*z^11 + 124678144*t^2*z^10 - 688606864*t^2*z^9 + 1229438176*t^2*z^8 - 1278976032*t^2*z^7 + 847512944*t^2*z^6 - 361615664*t^2*z^5 + 96911344*t^2*z^4 - 15611168*t^2*z^3 + 1508864*t^2*z^2 - 97872*t^2*z + 592*t^2 + 32*t*z^19 - 1504*t*z^18 + 31872*t*z^17 - 401680*t*z^16 + 3342480*t*z^15 - 19265664*t*z^14 + 78400368*t*z^13 - 224780832*t*z^12 + 442068336*t*z^11 - 551641552*t*z^10 + 320621360*t*z^9 + 183800656*t*z^8 - 553506720*t*z^7 + 533687552*t*z^6 - 291783600*t*z^5 + 95639744*t*z^4 - 17703456*t*z^3 + 1510064*t*z^2 - 31696*t*z + 2464*t - 16*z^18 + 704*z^17 - 13904*z^16 + 162544*z^15 - 1248624*z^14 + 6613104*z^13 - 24632368*z^12 + 64517504*z^11 - 116266544*z^10 + 135353008*z^9 - 81541632*z^8 - 14818384*z^7 + 74725680*z^6 - 67849568*z^5 + 32757856*z^4 - 8904640*z^3 + 1178400*z^2 - 25312*z - 6272:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7*z + 384*t^7 - 144*t^6*z^5 + 2256*t^6*z^4 - 12112*t^6*z^3 + 24032*t^6*z^2 - 8976*t^6*z - 1904*t^6 - 112*t^5*z^9 + 2976*t^5*z^8 - 32336*t^5*z^7 + 183040*t^5*z^6 - 566400*t^5*z^5 + 909664*t^5*z^4 - 636656*t^5*z^3 + 141536*t^5*z^2 - 112*t^5*z + 4960*t^5 - 32*t^4*z^13 + 1200*t^4*z^12 - 19664*t^4*z^11 + 184192*t^4*z^10 - 1082656*t^4*z^9 + 4124960*t^4*z^8 - 10168256*t^4*z^7 + 15766560*t^4*z^6 - 14662672*t^4*z^5 + 7827472*t^4*z^4 - 2306208*t^4*z^3 + 385392*t^4*z^2 - 36176*t^4*z - 2208*t^4 - 32*t^3*z^15 + 1296*t^3*z^14 - 23312*t^3*z^13 + 245152*t^3*z^12 - 1669760*t^3*z^11 + 7713408*t^3*z^10 - 24621088*t^3*z^9 + 54400048*t^3*z^8 - 82357792*t^3*z^7 + 83812288*t^3*z^6 - 55781728*t^3*z^5 + 23323760*t^3*z^4 - 5802480*t^3*z^3 + 816240*t^3*z^2 - 57296*t^3*z - 928*t^3 - 32*t^2*z^16 + 1264*t^2*z^15 - 21904*t^2*z^14 + 217504*t^2*z^13 - 1351088*t^2*z^12 + 5328112*t^2*z^11 - 12506240*t^2*z^10 + 12013936*t^2*z^9 + 19405968*t^2*z^8 - 80818256*t^2*z^7 + 118681424*t^2*z^6 - 93852384*t^2*z^5 + 41636352*t^2*z^4 - 9751488*t^2*z^3 + 1072592*t^2*z^2 - 82000*t^2*z + 4720*t^2 - 32*t*z^16 + 1312*t*z^15 - 23840*t*z^14 + 252048*t*z^13 - 1709680*t*z^12 + 7723504*t*z^11 - 23258896*t*z^10 + 44900256*t*z^9 - 48648816*t*z^8 + 11988480*t*z^7 + 39453856*t*z^6 - 55668736*t*z^5 + 34213504*t*z^4 - 10608992*t*z^3 + 1393392*t*z^2 - 20928*t*z + 1936*t + 16*z^15 - 608*z^14 + 10176*z^13 - 98432*z^12 + 606544*z^11 - 2471504*z^10 + 6672192*z^9 - 11520288*z^8 + 11312352*z^7 - 3205264*z^6 - 5772000*z^5 + 7525056*z^4 - 3920608*z^3 + 928640*z^2 - 57920*z - 6688)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_24 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 24) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_24 z t hf hn0 hn1 hn2 hn3
  · have hr : (16*t*z^19 - 720*t*z^18 + 14576*t*z^17 - 175040*t*z^16 + 1383776*t*z^15 - 7552160*t*z^14 + 29002336*t*z^13 - 78318080*t*z^12 + 145822896*t*z^11 - 178812400*t*z^10 + 130372368*t*z^9 - 39887360*t*z^8 - 10937312*t*z^7 + 10403680*t*z^6 - 456672*t*z^5 - 953280*t*z^4 + 34128*t*z^3 + 45360*t*z^2 + 3888*t*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t*z^16 + 624*t*z^15 - 10752*t*z^14 + 107392*t*z^13 - 685040*t*z^12 + 2894208*t*z^11 - 8104496*t*z^10 + 14535024*t*z^9 - 15196064*t*z^8 + 6856400*t*z^7 + 1281376*t*z^6 - 1902448*t*z^5 - 27856*t*z^4 + 222800*t*z^3 + 30304*t*z^2 - 6752*t*z - 3360*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_25 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 25) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_25 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 30*z^5 + 164*z^4 - 396*z^3 + 414*z^2 - 178*z + 24:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^3 + 18*z^2 - 46*z + 28)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_26 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 26) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_26 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*z^6 - 64*z^5 + 374*z^4 - 958*z^3 + 1032*z^2 - 478*z + 78:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4*z^3 + 40*z^2 - 114*z + 70)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_27 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 27) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_27 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^4 + 22*t*z^3 - 74*t*z^2 + 72*t*z - 24*t + 4*z^6 - 62*z^5 + 352*z^4 - 884*z^3 + 958*z^2 - 454*z + 78:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t*z - 10*t - 4*z^3 + 38*z^2 - 104*z + 66)*hf
  · have hr : (16*t^8 + 16*t^7*z^4 - 96*t^7*z^3 + 48*t^7*z^2 + 96*t^7*z - 112*t^7 + 48*t^6*z^7 - 656*t^6*z^6 + 2992*t^6*z^5 - 4928*t^6*z^4 + 1456*t^6*z^3 + 2400*t^6*z^2 - 1376*t^6*z + 112*t^6 + 64*t^5*z^10 - 1328*t^5*z^9 + 10816*t^5*z^8 - 43760*t^5*z^7 + 92384*t^5*z^6 - 99136*t^5*z^5 + 44736*t^5*z^4 + 9936*t^5*z^3 - 18464*t^5*z^2 + 4368*t^5*z + 608*t^5 + 48*t^4*z^13 - 1344*t^4*z^12 + 15872*t^4*z^11 - 103152*t^4*z^10 + 405184*t^4*z^9 - 999744*t^4*z^8 + 1562064*t^4*z^7 - 1484672*t^4*z^6 + 705552*t^4*z^5 - 1888*t^4*z^4 - 142960*t^4*z^3 + 44752*t^4*z^2 + 240*t^4*z - 1232*t^4 + 16*t^3*z^16 - 544*t^3*z^15 + 8016*t^3*z^14 - 67216*t^3*z^13 + 355120*t^3*z^12 - 1243792*t^3*z^11 + 2992128*t^3*z^10 - 5140304*t^3*z^9 + 6583120*t^3*z^8 - 6323216*t^3*z^7 + 4093024*t^3*z^6 - 1174096*t^3*z^5 - 370064*t^3*z^4 + 338800*t^3*z^3 - 37824*t^3*z^2 - 12832*t^3*z + 368*t^3 + 16*t^2*z^18 - 656*t^2*z^17 + 11856*t^2*z^16 - 124080*t^2*z^15 + 830160*t^2*z^14 - 3694208*t^2*z^13 + 10993808*t^2*z^12 - 21258816*t^2*z^11 + 24227632*t^2*z^10 - 10340336*t^2*z^9 - 10067952*t^2*z^8 + 16307792*t^2*z^7 - 7826608*t^2*z^6 + 69456*t^2*z^5 + 1173728*t^2*z^4 - 286432*t^2*z^3 - 28064*t^2*z^2 + 11280*t^2*z + 592*t^2 - 80*t*z^18 + 3216*t*z^17 - 57168*t*z^16 + 590768*t*z^15 - 3923712*t*z^14 + 17475680*t*z^13 - 52812192*t*z^12 + 106944640*t*z^11 - 138966464*t*z^10 + 103538640*t*z^9 - 27108320*t*z^8 - 17032272*t*z^7 + 13275248*t*z^6 - 679568*t*z^5 - 1550480*t*z^4 + 234144*t*z^3 + 69280*t*z^2 - 6768*t*z - 1120*t + 64*z^18 - 2416*z^17 + 39920*z^16 - 378384*z^15 + 2264880*z^14 - 8877872*z^13 + 22848672*z^12 - 37547840*z^11 + 36408176*z^10 - 15714864*z^9 - 4144768*z^8 + 7609392*z^7 - 2343072*z^6 - 506608*z^5 + 369328*z^4 - 10528*z^3 - 17280*z^2 + 640*z + 256:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7*z - 48*t^6*z^4 + 368*t^6*z^3 - 544*t^6*z^2 - 224*t^6*z + 288*t^6 - 64*t^5*z^7 + 944*t^5*z^6 - 4832*t^5*z^5 + 9984*t^5*z^4 - 7376*t^5*z^3 + 128*t^5*z^2 + 2896*t^5*z - 576*t^5 - 48*t^4*z^10 + 1056*t^4*z^9 - 9296*t^4*z^8 + 42048*t^4*z^7 - 105360*t^4*z^6 + 148048*t^4*z^5 - 104928*t^4*z^4 + 9504*t^4*z^3 + 24160*t^4*z^2 - 5600*t^4*z - 1936*t^4 - 16*t^3*z^13 + 448*t^3*z^12 - 5248*t^3*z^11 + 33472*t^3*z^10 - 127600*t^3*z^9 + 305584*t^3*z^8 - 487152*t^3*z^7 + 561872*t^3*z^6 - 470544*t^3*z^5 + 203440*t^3*z^4 + 42208*t^3*z^3 - 60400*t^3*z^2 + 64*t^3*z + 5792*t^3 - 16*t^2*z^15 + 560*t^2*z^14 - 8416*t^2*z^13 + 70768*t^2*z^12 - 362912*t^2*z^11 + 1154480*t^2*z^10 - 2181600*t^2*z^9 + 2033904*t^2*z^8 + 38272*t^2*z^7 - 1781152*t^2*z^6 + 1223584*t^2*z^5 - 22256*t^2*z^4 - 206000*t^2*z^3 + 29408*t^2*z^2 + 10464*t^2*z - 3824*t^2 + 80*t*z^15 - 2736*t*z^14 + 40352*t*z^13 - 334896*t*z^12 + 1709840*t*z^11 - 5501808*t*z^10 + 10917248*t*z^9 - 12222272*t*z^8 + 5544784*t*z^7 + 1758672*t*z^6 - 2285840*t*z^5 + 68656*t*z^4 + 324560*t*z^3 - 2192*t*z^2 - 16816*t*z + 480*t - 64*z^15 + 2032*z^14 - 27408*z^13 + 203712*z^12 - 903536*z^11 + 2410688*z^10 - 3663152*z^9 + 2611952*z^8 - 10016*z^7 - 1068144*z^6 + 397936*z^5 + 108928*z^4 - 61184*z^3 - 7200*z^2 + 2320*z - 736)*hf
  · have hr : (16*t^8 + 16*t^7*z^4 - 160*t^7*z^3 + 432*t^7*z^2 - 160*t^7*z - 176*t^7 + 16*t^6*z^6 - 224*t^6*z^5 + 1040*t^6*z^4 - 1568*t^6*z^3 - 272*t^6*z^2 + 512*t^6*z + 544*t^6 + 16*t^5*z^10 - 384*t^5*z^9 + 3808*t^5*z^8 - 20096*t^5*z^7 + 60368*t^5*z^6 - 101248*t^5*z^5 + 82224*t^5*z^4 - 13024*t^5*z^3 - 15104*t^5*z^2 + 3552*t^5*z + 112*t^5 + 16*t^4*z^11 - 448*t^4*z^10 + 5264*t^4*z^9 - 33680*t^4*z^8 + 127568*t^4*z^7 - 292016*t^4*z^6 + 395088*t^4*z^5 - 281568*t^4*z^4 + 42704*t^4*z^3 + 52304*t^4*z^2 - 13840*t^4*z - 2672*t^4 + 16*t^3*z^15 - 544*t^3*z^14 + 8000*t^3*z^13 - 66256*t^3*z^12 + 336048*t^3*z^11 - 1054832*t^3*z^10 + 1922128*t^3*z^9 - 1504544*t^3*z^8 - 863568*t^3*z^7 + 2624016*t^3*z^6 - 1743984*t^3*z^5 + 220624*t^3*z^4 + 188288*t^3*z^3 - 70016*t^3*z^2 + 2672*t^3*z + 2656*t^3 - 16*t^2*z^15 + 528*t^2*z^14 - 7456*t^2*z^13 + 58192*t^2*z^12 - 267792*t^2*z^11 + 692160*t^2*z^10 - 671088*t^2*z^9 - 1287472*t^2*z^8 + 4724912*t^2*z^7 - 5539600*t^2*z^6 + 2395504*t^2*z^5 + 308992*t^2*z^4 - 459104*t^2*z^3 + 29312*t^2*z^2 + 21360*t^2*z + 736*t^2 + 16*t*z^19 - 720*t*z^18 + 14576*t*z^17 - 175040*t*z^16 + 1383760*t*z^15 - 7551584*t*z^14 + 28993248*t*z^13 - 78235696*t*z^12 + 145350272*t*z^11 - 177030512*t*z^10 + 125929024*t*z^9 - 32683104*t*z^8 - 18206224*t*z^7 + 14476960*t*z^6 - 1088496*t*z^5 - 1524336*t*z^4 + 292304*t*z^3 + 61696*t*z^2 - 11200*t*z - 1472*t + 16*z^15 - 560*z^14 + 8544*z^13 - 74320*z^12 + 404352*z^11 - 1418784*z^10 + 3187424*z^9 - 4382368*z^8 + 3300096*z^7 - 926064*z^6 - 313312*z^5 + 239728*z^4 - 15312*z^3 - 12992*z^2 + 992*z + 256:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7*z + 64*t^7 - 16*t^6*z^3 + 128*t^6*z^2 - 192*t^6*z - 240*t^6 - 16*t^5*z^7 + 288*t^5*z^6 - 2000*t^5*z^5 + 6640*t^5*z^4 - 10240*t^5*z^3 + 4608*t^5*z^2 + 3264*t^5*z - 672*t^5 - 16*t^4*z^8 + 352*t^4*z^7 - 3072*t^4*z^6 + 13472*t^4*z^5 - 31024*t^4*z^4 + 35440*t^4*z^3 - 13856*t^4*z^2 - 9792*t^4*z + 3264*t^4 - 16*t^3*z^12 + 448*t^3*z^11 - 5232*t^3*z^10 + 32608*t^3*z^9 - 113792*t^3*z^8 + 203808*t^3*z^7 - 97712*t^3*z^6 - 214560*t^3*z^5 + 268576*t^3*z^4 - 37472*t^3*z^3 - 38288*t^3*z^2 + 5584*t^3*z - 816*t^3 + 16*t^2*z^12 - 432*t^2*z^11 + 4784*t^2*z^10 - 27312*t^2*z^9 + 79568*t^2*z^8 - 73408*t^2*z^7 - 194512*t^2*z^6 + 567008*t^2*z^5 - 423712*t^2*z^4 - 32224*t^2*z^3 + 96720*t^2*z^2 + 8736*t^2*z - 4304*t^2 - 16*t*z^16 + 624*t*z^15 - 10752*t*z^14 + 107392*t*z^13 - 685024*t*z^12 + 2893728*t*z^11 - 8098368*t*z^10 + 14491824*t*z^9 - 15013760*t*z^8 + 6390464*t*z^7 + 1974384*t*z^6 - 2436672*t*z^5 + 104736*t*z^4 + 309200*t*z^3 - 16656*t*z^2 - 16864*t*z - 1008*t - 16*z^12 + 464*z^11 - 5680*z^10 + 37904*z^9 - 148064*z^8 + 335200*z^7 - 398000*z^6 + 170304*z^5 + 46928*z^4 - 41888*z^3 - 2352*z^2 + 2528*z + 352)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_28 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 28) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_28 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^4 + 20*t*z^3 - 62*t*z^2 + 60*t*z - 22*t + 4*z^6 - 60*z^5 + 330*z^4 - 800*z^3 + 822*z^2 - 360*z + 56:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t*z - 8*t - 4*z^3 + 36*z^2 - 94*z + 52)*hf
  · have hr : (16*t^8 + 16*t^7*z^4 - 224*t^7*z^3 + 816*t^7*z^2 - 544*t^7*z - 112*t^7 - 48*t^6*z^7 + 880*t^6*z^6 - 5840*t^6*z^5 + 16832*t^6*z^4 - 19216*t^6*z^3 + 5024*t^6*z^2 + 2304*t^6*z + 112*t^6 + 64*t^5*z^10 - 1552*t^5*z^9 + 15280*t^5*z^8 - 78272*t^5*z^7 + 221600*t^5*z^6 - 337888*t^5*z^5 + 241824*t^5*z^4 - 37072*t^5*z^3 - 26096*t^5*z^2 + 1728*t^5*z + 608*t^5 - 48*t^4*z^13 + 1472*t^4*z^12 - 19360*t^4*z^11 + 142560*t^4*z^10 - 643216*t^4*z^9 + 1826816*t^4*z^8 - 3219248*t^4*z^7 + 3292480*t^4*z^6 - 1577296*t^4*z^5 - 27440*t^4*z^4 + 242688*t^4*z^3 - 5936*t^4*z^2 - 13520*t^4*z - 1232*t^4 + 16*t^3*z^16 - 576*t^3*z^15 + 9120*t^3*z^14 - 83488*t^3*z^13 + 488832*t^3*z^12 - 1914320*t^3*z^11 + 5102752*t^3*z^10 - 9257808*t^3*z^9 + 11200768*t^3*z^8 - 8382608*t^3*z^7 + 2796144*t^3*z^6 + 640528*t^3*z^5 - 603824*t^3*z^4 - 44752*t^3*z^3 + 41824*t^3*z^2 + 7728*t^3*z + 368*t^3 - 16*t^2*z^18 + 656*t^2*z^17 - 11968*t^2*z^16 + 127792*t^2*z^15 - 883200*t^2*z^14 + 4121568*t^2*z^13 - 13128096*t^2*z^12 + 28116848*t^2*z^11 - 38576992*t^2*z^10 + 30029472*t^2*z^9 - 8204304*t^2*z^8 - 3994160*t^2*z^7 + 1970720*t^2*z^6 + 771360*t^2*z^5 - 240864*t^2*z^4 - 113936*t^2*z^3 + 7216*t^2*z^2 + 6480*t^2*z + 592*t^2 + 16*t*z^19 - 720*t*z^18 + 14576*t*z^17 - 175120*t*z^16 + 1386512*t*z^15 - 7593360*t*z^14 + 29360912*t*z^13 - 80307840*t*z^12 + 153143952*t*z^11 - 196790608*t*z^10 + 159199408*t*z^9 - 68168144*t*z^8 + 3044144*t*z^7 + 10248208*t*z^6 - 3232896*t*z^5 - 429312*t*z^4 + 292896*t*z^3 + 13216*t*z^2 - 11248*t*z - 1120*t + 16*z^18 - 624*z^17 + 10864*z^16 - 111152*z^15 + 740080*z^14 - 3353552*z^13 + 10500944*z^12 - 22584128*z^11 + 32426640*z^10 - 29145648*z^9 + 13846128*z^8 - 877456*z^7 - 2205040*z^6 + 706256*z^5 + 110480*z^4 - 64576*z^3 - 4192*z^2 + 2400*z + 256:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7*z + 128*t^7 + 48*t^6*z^4 - 592*t^6*z^3 + 2048*t^6*z^2 - 1536*t^6*z - 832*t^6 - 64*t^5*z^7 + 1168*t^5*z^6 - 7952*t^5*z^5 + 24656*t^5*z^4 - 32736*t^5*z^3 + 10240*t^5*z^2 + 7952*t^5*z + 848*t^5 + 48*t^4*z^10 - 1184*t^4*z^9 + 12016*t^4*z^8 - 64496*t^4*z^7 + 194976*t^4*z^6 - 322464*t^4*z^5 + 245088*t^4*z^4 - 14656*t^4*z^3 - 58544*t^4*z^2 - 5456*t^4*z + 2640*t^4 - 16*t^3*z^13 + 480*t^3*z^12 - 6160*t^3*z^11 + 44112*t^3*z^10 - 192880*t^3*z^9 + 530320*t^3*z^8 - 912320*t^3*z^7 + 939408*t^3*z^6 - 472400*t^3*z^5 - 61152*t^3*z^4 + 138352*t^3*z^3 + 22944*t^3*z^2 - 11424*t^3*z - 160*t^3 + 16*t^2*z^15 - 560*t^2*z^14 + 8528*t^2*z^13 - 73808*t^2*z^12 + 397152*t^2*z^11 - 1361088*t^2*z^10 + 2902000*t^2*z^9 - 3502256*t^2*z^8 + 1692368*t^2*z^7 + 538016*t^2*z^6 - 531696*t^2*z^5 - 193728*t^2*z^4 + 63408*t^2*z^3 + 46032*t^2*z^2 + 6288*t^2*z - 15088*t^2 - 16*t*z^16 + 624*t*z^15 - 10752*t*z^14 + 107472*t*z^13 - 687296*t*z^12 + 2921472*t*z^11 - 8288128*t*z^10 + 15284416*t*z^9 - 17075344*t*z^8 + 9628336*t*z^7 - 768256*t*z^6 - 1658416*t*z^5 + 474976*t*z^4 + 125472*t*z^3 - 47568*t*z^2 - 8480*t*z + 19536*t - 16*z^15 + 528*z^14 - 7616*z^13 + 62800*z^12 - 324672*z^11 + 1083904*z^10 - 2311360*z^9 + 2971776*z^8 - 1955280*z^7 + 243728*z^6 + 364416*z^5 - 109968*z^4 - 33120*z^3 + 9280*z^2 + 832*z - 9952)*hf
  · have hr : (16*t^8 + 16*t^7*z^4 - 160*t^7*z^3 + 432*t^7*z^2 - 288*t^7*z - 48*t^7 + 16*t^6*z^6 - 320*t^6*z^5 + 2096*t^6*z^4 - 5120*t^6*z^3 + 3728*t^6*z^2 - 160*t^6*z - 192*t^6 + 16*t^5*z^10 - 384*t^5*z^9 + 3808*t^5*z^8 - 20192*t^5*z^7 + 62048*t^5*z^6 - 111808*t^5*z^5 + 110448*t^5*z^4 - 43008*t^5*z^3 - 5696*t^5*z^2 + 4416*t^5*z + 576*t^5 - 48*t^4*z^11 + 1152*t^4*z^10 - 11504*t^4*z^9 + 62176*t^4*z^8 - 198352*t^4*z^7 + 380208*t^4*z^6 - 413680*t^4*z^5 + 199200*t^4*z^4 - 848*t^4*z^3 - 20448*t^4*z^2 + 432*t^4*z + 432*t^4 + 16*t^3*z^15 - 544*t^3*z^14 + 8000*t^3*z^13 - 66224*t^3*z^12 + 335344*t^3*z^11 - 1048528*t^3*z^10 + 1892240*t^3*z^9 - 1422416*t^3*z^8 - 993328*t^3*z^7 + 2697472*t^3*z^6 - 1612688*t^3*z^5 + 3184*t^3*z^4 + 233376*t^3*z^3 - 9648*t^3*z^2 - 14256*t^3*z - 1296*t^3 - 32*t^2*z^16 + 1104*t^2*z^15 - 16560*t^2*z^14 + 141088*t^2*z^13 - 747312*t^2*z^12 + 2524400*t^2*z^11 - 5327152*t^2*z^10 + 6423856*t^2*z^9 - 3129440*t^2*z^8 - 1334224*t^2*z^7 + 1966352*t^2*z^6 - 307312*t^2*z^5 - 245136*t^2*z^4 + 31392*t^2*z^3 + 16848*t^2*z^2 + 1296*t^2*z + 16*t*z^19 - 720*t*z^18 + 14592*t*z^17 - 175616*t*z^16 + 1392896*t*z^15 - 7635552*t*z^14 + 29488240*t*z^13 - 80194320*t*z^12 + 150652640*t*z^11 - 186907888*t*z^10 + 138637984*t*z^9 - 44181152*t*z^8 - 10634192*t*z^7 + 11041920*t*z^6 - 605664*t*z^5 - 991728*t*z^4 + 41472*t*z^3 + 46656*t*z^2 + 3888*t*z + 16*z^17 - 560*z^16 + 8560*z^15 - 74704*z^14 + 408064*z^13 - 1436832*z^12 + 3230656*z^11 - 4413184*z^10 + 3238464*z^9 - 816432*z^8 - 327360*z^7 + 176976*z^6 + 15696*z^5 - 10368*z^4 - 1296*z^3:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7*z + 64*t^7 - 16*t^6*z^3 + 224*t^6*z^2 - 672*t^6*z - 48*t^6 - 16*t^5*z^7 + 288*t^5*z^6 - 2000*t^5*z^5 + 6736*t^5*z^4 - 11344*t^5*z^3 + 8064*t^5*z^2 + 1392*t^5*z - 304*t^5 + 48*t^4*z^8 - 864*t^4*z^7 + 6080*t^4*z^6 - 21328*t^4*z^5 + 39120*t^4*z^4 - 32768*t^4*z^3 + 144*t^4*z^2 + 4624*t^4*z - 4896*t^4 - 16*t^3*z^12 + 448*t^3*z^11 - 5232*t^3*z^10 + 32576*t^3*z^9 - 113280*t^3*z^8 + 200736*t^3*z^7 - 88848*t^3*z^6 - 227632*t^3*z^5 + 272512*t^3*z^4 - 13088*t^3*z^3 - 56032*t^3*z^2 - 1424*t^3*z + 25152*t^3 + 32*t^2*z^13 - 912*t^2*z^12 + 10928*t^2*z^11 - 70928*t^2*z^10 + 266192*t^2*z^9 - 561680*t^2*z^8 + 555184*t^2*z^7 - 18160*t^2*z^6 - 317120*t^2*z^5 + 77488*t^2*z^4 + 66016*t^2*z^3 - 1152*t^2*z^2 - 14368*t^2*z - 45824*t^2 - 16*t*z^16 + 624*t*z^15 - 10768*t*z^14 + 107872*t*z^13 - 691200*t*z^12 + 2938224*t*z^11 - 8295024*t*z^10 + 15041856*t*z^9 - 15988160*t*z^8 + 7474624*t*z^7 + 1192416*t*z^6 - 2025632*t*z^5 - 7056*t*z^4 + 236320*t*z^3 + 33232*t*z^2 + 2464*t*z + 43472*t - 16*z^14 + 464*z^13 - 5696*z^12 + 38192*z^11 - 149968*z^10 + 340368*z^9 - 400416*z^8 + 158880*z^7 + 57264*z^6 - 34800*z^5 - 8880*z^4 + 1008*z^3 - 48*z^2 - 3840*z - 20496)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_29 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 29) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_29 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t*z^2 + 30*t*z - 18*t + 2*z^6 - 30*z^5 + 164*z^4 - 390*z^3 + 382*z^2 - 160*z + 24:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^3 + 18*z^2 - 46*z + 22)*hf
  · have hr : (16*t^8 + 80*t^7*z^4 - 864*t^7*z^3 + 2608*t^7*z^2 - 1504*t^7*z + 16*t^7 + 144*t^6*z^8 - 3120*t^6*z^7 + 26368*t^6*z^6 - 108128*t^6*z^5 + 215984*t^6*z^4 - 184224*t^6*z^3 + 58176*t^6*z^2 - 2896*t^6*z + 208*t^6 + 112*t^5*z^12 - 3648*t^5*z^11 + 50752*t^5*z^10 - 392048*t^5*z^9 + 1829296*t^5*z^8 - 5255600*t^5*z^7 + 9109680*t^5*z^6 - 9076192*t^5*z^5 + 4942272*t^5*z^4 - 1349968*t^5*z^3 + 170128*t^5*z^2 - 16752*t^5*z + 256*t^5 + 32*t^4*z^16 - 1392*t^4*z^15 + 27024*t^4*z^14 - 308208*t^4*z^13 + 2287328*t^4*z^12 - 11561520*t^4*z^11 + 40515488*t^4*z^10 - 98483552*t^4*z^9 + 164228272*t^4*z^8 - 184804560*t^4*z^7 + 138350960*t^4*z^6 - 68022672*t^4*z^5 + 21707040*t^4*z^4 - 4448016*t^4*z^3 + 554400*t^4*z^2 - 30880*t^4*z + 976*t^4 + 32*t^3*z^18 - 1488*t^3*z^17 + 31248*t^3*z^16 - 391536*t^3*z^15 + 3258528*t^3*z^14 - 18981040*t^3*z^13 + 79495488*t^3*z^12 - 242363376*t^3*z^11 + 539576928*t^3*z^10 - 874580368*t^3*z^9 + 1024844464*t^3*z^8 - 859433360*t^3*z^7 + 508465968*t^3*z^6 - 208031648*t^3*z^5 + 57290896*t^3*z^4 - 10226528*t^3*z^3 + 1098192*t^3*z^2 - 57472*t^3*z + 1744*t^3 + 32*t^2*z^19 - 1456*t^2*z^18 + 29648*t^2*z^17 - 355280*t^2*z^16 + 2766896*t^2*z^15 - 14544064*t^2*z^14 + 51447856*t^2*z^13 - 115043024*t^2*z^12 + 120536960*t^2*z^11 + 124678144*t^2*z^10 - 688606864*t^2*z^9 + 1229438176*t^2*z^8 - 1278976032*t^2*z^7 + 847512944*t^2*z^6 - 361615664*t^2*z^5 + 96911344*t^2*z^4 - 15611168*t^2*z^3 + 1508864*t^2*z^2 - 97872*t^2*z + 592*t^2 + 32*t*z^19 - 1504*t*z^18 + 31872*t*z^17 - 401680*t*z^16 + 3342480*t*z^15 - 19265664*t*z^14 + 78400368*t*z^13 - 224780832*t*z^12 + 442068336*t*z^11 - 551641552*t*z^10 + 320621360*t*z^9 + 183800656*t*z^8 - 553506720*t*z^7 + 533687552*t*z^6 - 291783600*t*z^5 + 95639744*t*z^4 - 17703456*t*z^3 + 1510064*t*z^2 - 31696*t*z + 2464*t - 16*z^18 + 704*z^17 - 13904*z^16 + 162544*z^15 - 1248624*z^14 + 6613104*z^13 - 24632368*z^12 + 64517504*z^11 - 116266544*z^10 + 135353008*z^9 - 81541632*z^8 - 14818384*z^7 + 74725680*z^6 - 67849568*z^5 + 32757856*z^4 - 8904640*z^3 + 1178400*z^2 - 25312*z - 6272:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7*z + 384*t^7 - 144*t^6*z^5 + 2256*t^6*z^4 - 12112*t^6*z^3 + 24032*t^6*z^2 - 8976*t^6*z - 1904*t^6 - 112*t^5*z^9 + 2976*t^5*z^8 - 32336*t^5*z^7 + 183040*t^5*z^6 - 566400*t^5*z^5 + 909664*t^5*z^4 - 636656*t^5*z^3 + 141536*t^5*z^2 - 112*t^5*z + 4960*t^5 - 32*t^4*z^13 + 1200*t^4*z^12 - 19664*t^4*z^11 + 184192*t^4*z^10 - 1082656*t^4*z^9 + 4124960*t^4*z^8 - 10168256*t^4*z^7 + 15766560*t^4*z^6 - 14662672*t^4*z^5 + 7827472*t^4*z^4 - 2306208*t^4*z^3 + 385392*t^4*z^2 - 36176*t^4*z - 2208*t^4 - 32*t^3*z^15 + 1296*t^3*z^14 - 23312*t^3*z^13 + 245152*t^3*z^12 - 1669760*t^3*z^11 + 7713408*t^3*z^10 - 24621088*t^3*z^9 + 54400048*t^3*z^8 - 82357792*t^3*z^7 + 83812288*t^3*z^6 - 55781728*t^3*z^5 + 23323760*t^3*z^4 - 5802480*t^3*z^3 + 816240*t^3*z^2 - 57296*t^3*z - 928*t^3 - 32*t^2*z^16 + 1264*t^2*z^15 - 21904*t^2*z^14 + 217504*t^2*z^13 - 1351088*t^2*z^12 + 5328112*t^2*z^11 - 12506240*t^2*z^10 + 12013936*t^2*z^9 + 19405968*t^2*z^8 - 80818256*t^2*z^7 + 118681424*t^2*z^6 - 93852384*t^2*z^5 + 41636352*t^2*z^4 - 9751488*t^2*z^3 + 1072592*t^2*z^2 - 82000*t^2*z + 4720*t^2 - 32*t*z^16 + 1312*t*z^15 - 23840*t*z^14 + 252048*t*z^13 - 1709680*t*z^12 + 7723504*t*z^11 - 23258896*t*z^10 + 44900256*t*z^9 - 48648816*t*z^8 + 11988480*t*z^7 + 39453856*t*z^6 - 55668736*t*z^5 + 34213504*t*z^4 - 10608992*t*z^3 + 1393392*t*z^2 - 20928*t*z + 1936*t + 16*z^15 - 608*z^14 + 10176*z^13 - 98432*z^12 + 606544*z^11 - 2471504*z^10 + 6672192*z^9 - 11520288*z^8 + 11312352*z^7 - 3205264*z^6 - 5772000*z^5 + 7525056*z^4 - 3920608*z^3 + 928640*z^2 - 57920*z - 6688)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_30 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 30) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_30 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^4 + 22*t*z^3 - 74*t*z^2 + 72*t*z - 24*t + 4*z^6 - 62*z^5 + 352*z^4 - 884*z^3 + 958*z^2 - 454*z + 78:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t*z - 10*t - 4*z^3 + 38*z^2 - 104*z + 66)*hf
  · have hr : (16*t^8 + 16*t^7*z^4 - 160*t^7*z^3 + 432*t^7*z^2 - 160*t^7*z - 176*t^7 + 16*t^6*z^6 - 224*t^6*z^5 + 1040*t^6*z^4 - 1568*t^6*z^3 - 272*t^6*z^2 + 512*t^6*z + 544*t^6 + 16*t^5*z^10 - 384*t^5*z^9 + 3808*t^5*z^8 - 20096*t^5*z^7 + 60368*t^5*z^6 - 101248*t^5*z^5 + 82224*t^5*z^4 - 13024*t^5*z^3 - 15104*t^5*z^2 + 3552*t^5*z + 112*t^5 + 16*t^4*z^11 - 448*t^4*z^10 + 5264*t^4*z^9 - 33680*t^4*z^8 + 127568*t^4*z^7 - 292016*t^4*z^6 + 395088*t^4*z^5 - 281568*t^4*z^4 + 42704*t^4*z^3 + 52304*t^4*z^2 - 13840*t^4*z - 2672*t^4 + 16*t^3*z^15 - 544*t^3*z^14 + 8000*t^3*z^13 - 66256*t^3*z^12 + 336048*t^3*z^11 - 1054832*t^3*z^10 + 1922128*t^3*z^9 - 1504544*t^3*z^8 - 863568*t^3*z^7 + 2624016*t^3*z^6 - 1743984*t^3*z^5 + 220624*t^3*z^4 + 188288*t^3*z^3 - 70016*t^3*z^2 + 2672*t^3*z + 2656*t^3 - 16*t^2*z^15 + 528*t^2*z^14 - 7456*t^2*z^13 + 58192*t^2*z^12 - 267792*t^2*z^11 + 692160*t^2*z^10 - 671088*t^2*z^9 - 1287472*t^2*z^8 + 4724912*t^2*z^7 - 5539600*t^2*z^6 + 2395504*t^2*z^5 + 308992*t^2*z^4 - 459104*t^2*z^3 + 29312*t^2*z^2 + 21360*t^2*z + 736*t^2 + 16*t*z^19 - 720*t*z^18 + 14576*t*z^17 - 175040*t*z^16 + 1383760*t*z^15 - 7551584*t*z^14 + 28993248*t*z^13 - 78235696*t*z^12 + 145350272*t*z^11 - 177030512*t*z^10 + 125929024*t*z^9 - 32683104*t*z^8 - 18206224*t*z^7 + 14476960*t*z^6 - 1088496*t*z^5 - 1524336*t*z^4 + 292304*t*z^3 + 61696*t*z^2 - 11200*t*z - 1472*t + 16*z^15 - 560*z^14 + 8544*z^13 - 74320*z^12 + 404352*z^11 - 1418784*z^10 + 3187424*z^9 - 4382368*z^8 + 3300096*z^7 - 926064*z^6 - 313312*z^5 + 239728*z^4 - 15312*z^3 - 12992*z^2 + 992*z + 256:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7*z + 64*t^7 - 16*t^6*z^3 + 128*t^6*z^2 - 192*t^6*z - 240*t^6 - 16*t^5*z^7 + 288*t^5*z^6 - 2000*t^5*z^5 + 6640*t^5*z^4 - 10240*t^5*z^3 + 4608*t^5*z^2 + 3264*t^5*z - 672*t^5 - 16*t^4*z^8 + 352*t^4*z^7 - 3072*t^4*z^6 + 13472*t^4*z^5 - 31024*t^4*z^4 + 35440*t^4*z^3 - 13856*t^4*z^2 - 9792*t^4*z + 3264*t^4 - 16*t^3*z^12 + 448*t^3*z^11 - 5232*t^3*z^10 + 32608*t^3*z^9 - 113792*t^3*z^8 + 203808*t^3*z^7 - 97712*t^3*z^6 - 214560*t^3*z^5 + 268576*t^3*z^4 - 37472*t^3*z^3 - 38288*t^3*z^2 + 5584*t^3*z - 816*t^3 + 16*t^2*z^12 - 432*t^2*z^11 + 4784*t^2*z^10 - 27312*t^2*z^9 + 79568*t^2*z^8 - 73408*t^2*z^7 - 194512*t^2*z^6 + 567008*t^2*z^5 - 423712*t^2*z^4 - 32224*t^2*z^3 + 96720*t^2*z^2 + 8736*t^2*z - 4304*t^2 - 16*t*z^16 + 624*t*z^15 - 10752*t*z^14 + 107392*t*z^13 - 685024*t*z^12 + 2893728*t*z^11 - 8098368*t*z^10 + 14491824*t*z^9 - 15013760*t*z^8 + 6390464*t*z^7 + 1974384*t*z^6 - 2436672*t*z^5 + 104736*t*z^4 + 309200*t*z^3 - 16656*t*z^2 - 16864*t*z - 1008*t - 16*z^12 + 464*z^11 - 5680*z^10 + 37904*z^9 - 148064*z^8 + 335200*z^7 - 398000*z^6 + 170304*z^5 + 46928*z^4 - 41888*z^3 - 2352*z^2 + 2528*z + 352)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_31 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 31) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_31 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z^2 - 10*t^2*z + 6*t^2 - 4*t*z^4 + 40*t*z^3 - 128*t*z^2 + 140*t*z - 48*t + 4*z^6 - 60*z^5 + 332*z^4 - 820*z^3 + 886*z^2 - 430*z + 78:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4*t*z - 16*t - 4*z^3 + 36*z^2 - 96*z + 60)*hf
  · have hr : (16*t^8*z^8 - 320*t^8*z^7 + 2592*t^8*z^6 - 10880*t^8*z^5 + 25264*t^8*z^4 - 32640*t^8*z^3 + 23328*t^8*z^2 - 8640*t^8*z + 1296*t^8 + 16*t^7*z^10 - 464*t^7*z^9 + 5392*t^7*z^8 - 32608*t^7*z^7 + 110224*t^7*z^6 - 205616*t^7*z^5 + 190768*t^7*z^4 - 55392*t^7*z^3 - 37584*t^7*z^2 + 31536*t^7*z - 6480*t^7 + 16*t^6*z^12 - 512*t^6*z^11 + 7088*t^6*z^10 - 54816*t^6*z^9 + 256480*t^6*z^8 - 737920*t^6*z^7 + 1275312*t^6*z^6 - 1251936*t^6*z^5 + 649248*t^6*z^4 - 167744*t^6*z^3 + 49392*t^6*z^2 - 31968*t^6*z + 8208*t^6 + 16*t^5*z^14 - 592*t^5*z^13 + 9536*t^5*z^12 - 87808*t^5*z^11 + 509008*t^5*z^10 - 1924496*t^5*z^9 + 4747648*t^5*z^8 - 7409920*t^5*z^7 + 6767792*t^5*z^6 - 2847216*t^5*z^5 - 365856*t^5*z^4 + 878880*t^5*z^3 - 301536*t^5*z^2 + 18144*t^5*z + 5184*t^5 - 16*t^4*z^15 + 560*t^4*z^14 - 8400*t^4*z^13 + 70432*t^4*z^12 - 358688*t^4*z^11 + 1112528*t^4*z^10 - 1892288*t^4*z^9 + 787760*t^4*z^8 + 3265088*t^4*z^7 - 6623248*t^4*z^6 + 5017824*t^4*z^5 - 929520*t^4*z^4 - 851568*t^4*z^3 + 445632*t^4*z^2 - 20592*t^4*z - 15984*t^4 + 16*t^3*z^17 - 640*t^3*z^16 + 11328*t^3*z^15 - 116592*t^3*z^14 + 770112*t^3*z^13 - 3392128*t^3*z^12 + 9992496*t^3*z^11 - 19041072*t^3*z^10 + 21125440*t^3*z^9 - 8469600*t^3*z^8 - 8286112*t^3*z^7 + 12126480*t^3*z^6 - 5049472*t^3*z^5 - 346896*t^3*z^4 + 892480*t^3*z^3 - 204144*t^3*z^2 - 13536*t^3*z + 7344*t^3 - 16*t^2*z^18 + 640*t^2*z^17 - 11296*t^2*z^16 + 115520*t^2*z^15 - 755056*t^2*z^14 + 3278432*t^2*z^13 - 9513456*t^2*z^12 + 18114288*t^2*z^11 - 21902304*t^2*z^10 + 17290352*t^2*z^9 - 13314912*t^2*z^8 + 14320048*t^2*z^7 - 11122704*t^2*z^6 + 3007120*t^2*z^5 + 1174912*t^2*z^4 - 721904*t^2*z^3 + 208*t^2*z^2 + 32368*t^2*z + 1488*t^2 + 16*t*z^19 - 720*t*z^18 + 14560*t*z^17 - 174560*t*z^16 + 1377680*t*z^15 - 7510192*t*z^14 + 28838656*t*z^13 - 77997888*t*z^12 + 145761744*t*z^11 - 179695360*t*z^10 + 131106608*t*z^9 - 37085424*t*z^8 - 17615776*t*z^7 + 15962576*t*z^6 - 1826224*t*z^5 - 1569664*t*z^4 + 351200*t*z^3 + 68192*t*z^2 - 13328*t*z - 1824*t + 16*z^18 - 608*z^17 + 10288*z^16 - 101936*z^15 + 653904*z^14 - 2832816*z^13 + 8378800*z^12 - 16678528*z^11 + 21314512*z^10 - 15469680*z^9 + 3589184*z^8 + 2989872*z^7 - 2174032*z^6 + 130624*z^5 + 239456*z^4 - 37504*z^3 - 11616*z^2 + 1344*z + 256:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^5 + 224*t^8*z^4 - 1168*t^8*z^3 + 2736*t^8*z^2 - 2784*t^8*z + 1088*t^8 - 16*t^7*z^7 + 368*t^7*z^6 - 3104*t^7*z^5 + 12128*t^7*z^4 - 21568*t^7*z^3 + 12464*t^7*z^2 + 3984*t^7*z - 4592*t^7 - 16*t^6*z^9 + 416*t^6*z^8 - 4512*t^6*z^7 + 25648*t^6*z^6 - 79616*t^6*z^5 + 127472*t^6*z^4 - 86752*t^6*z^3 + 14448*t^6*z^2 - 1328*t^6*z + 784*t^6 - 16*t^5*z^11 + 496*t^5*z^10 - 6480*t^5*z^9 + 46432*t^5*z^8 - 197520*t^5*z^7 + 500736*t^5*z^6 - 709200*t^5*z^5 + 453520*t^5*z^4 + 64*t^5*z^3 - 129200*t^5*z^2 + 43856*t^5*z + 30320*t^5 + 16*t^4*z^12 - 464*t^4*z^11 + 5536*t^4*z^10 - 34880*t^4*z^9 + 121264*t^4*z^8 - 205008*t^4*z^7 + 21040*t^4*z^6 + 484784*t^4*z^5 - 666592*t^4*z^4 + 220816*t^4*z^3 + 124816*t^4*z^2 - 92256*t^4*z - 105232*t^4 - 16*t^3*z^14 + 544*t^3*z^13 - 7984*t^3*z^12 + 65952*t^3*z^11 - 333936*t^3*z^10 + 1050768*t^3*z^9 - 1952256*t^3*z^8 + 1739760*t^3*z^7 + 125168*t^3*z^6 - 1430448*t^3*z^5 + 817344*t^3*z^4 + 54992*t^3*z^3 - 137744*t^3*z^2 + 62816*t^3*z + 228128*t^3 + 16*t^2*z^15 - 544*t^2*z^14 + 7952*t^2*z^13 - 65072*t^2*z^12 + 324320*t^2*z^11 - 999200*t^2*z^10 + 1831584*t^2*z^9 - 1804464*t^2*z^8 + 918400*t^2*z^7 - 926048*t^2*z^6 + 1362160*t^2*z^5 - 598448*t^2*z^4 - 204832*t^2*z^3 + 118288*t^2*z^2 - 39472*t^2*z - 311200*t^2 - 16*t*z^16 + 624*t*z^15 - 10736*t*z^14 + 107008*t*z^13 - 681328*t*z^12 + 2876448*t*z^11 - 8066320*t*z^10 + 14536400*t*z^9 - 15335296*t*z^8 + 6935264*t*z^7 + 1717856*t*z^6 - 2619056*t*z^5 + 247424*t*z^4 + 335104*t*z^3 - 19328*t*z^2 + 25600*t*z + 234144*t - 16*z^15 + 512*z^14 - 7136*z^13 + 56544*z^12 - 278448*z^11 + 872272*z^10 - 1696384*z^9 + 1860416*z^8 - 797824*z^7 - 315728*z^6 + 365984*z^5 - 13152*z^4 - 50528*z^3 - 2048*z^2 - 12256*z - 76320)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_32 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 32) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_32 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^5 - 18*z^4 + 44*z^3 - 14*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 6*z + 2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_33 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 33) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_33 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*z^4 - 36*z^3 + 94*z^2 - 58*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(12 - 4*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_34 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 34) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_34 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^5 - 20*z^4 + 56*z^3 - 28*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 8*z + 2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_35 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 35) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_35 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^3 + 10*t*z^2 - 6*t*z - 4*t + 2*z^5 - 18*z^4 + 46*z^3 - 24*z^2 + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 2*z^2 + 6*z)*hf
  · have hr : (16*t^8 + 80*t^7*z^4 - 864*t^7*z^3 + 2736*t^7*z^2 - 2400*t^7*z + 528*t^7 + 144*t^6*z^8 - 3120*t^6*z^7 + 26912*t^6*z^6 - 117824*t^6*z^5 + 277648*t^6*z^4 - 349184*t^6*z^3 + 227744*t^6*z^2 - 70576*t^6*z + 8016*t^6 + 112*t^5*z^12 - 3648*t^5*z^11 + 51568*t^5*z^10 - 415472*t^5*z^9 + 2108128*t^5*z^8 - 7032512*t^5*z^7 + 15647120*t^5*z^6 - 23110048*t^5*z^5 + 22205040*t^5*z^4 - 13428528*t^5*z^3 + 4836448*t^5*z^2 - 932160*t^5*z + 73152*t^5 + 32*t^4*z^16 - 1392*t^4*z^15 + 27536*t^4*z^14 - 328496*t^4*z^13 + 2641040*t^4*z^12 - 15128912*t^4*z^11 + 63543792*t^4*z^10 - 197997936*t^4*z^9 + 457417424*t^4*z^8 - 775872944*t^4*z^7 + 951032320*t^4*z^6 - 826058864*t^4*z^5 + 496097040*t^4*z^4 - 198893696*t^4*z^3 + 50260896*t^4*z^2 - 7175520*t^4*z + 438480*t^4 + 144*t^3*z^18 - 7152*t^3*z^17 + 161696*t^3*z^16 - 2203456*t^3*z^15 + 20203520*t^3*z^14 - 131802976*t^3*z^13 + 631110064*t^3*z^12 - 2256713264*t^3*z^11 + 6077413840*t^3*z^10 - 12353934000*t^3*z^9 + 18907722736*t^3*z^8 - 21647916304*t^3*z^7 + 18352804016*t^3*z^6 - 11350666304*t^3*z^5 + 5008955824*t^3*z^4 - 1523644752*t^3*z^3 + 301504752*t^3*z^2 - 34752240*t^3*z + 1763856*t^3 + 224*t^2*z^20 - 12560*t^2*z^19 + 323088*t^2*z^18 - 5052320*t^2*z^17 + 53659984*t^2*z^16 - 409716992*t^2*z^15 + 2322789008*t^2*z^14 - 9962799152*t^2*z^13 + 32668246896*t^2*z^12 - 82294617296*t^2*z^11 + 159447212992*t^2*z^10 - 237264324096*t^2*z^9 + 270207610176*t^2*z^8 - 234159447696*t^2*z^7 + 153031888400*t^2*z^6 - 74384750992*t^2*z^5 + 26316945168*t^2*z^4 - 6547244832*t^2*z^3 + 1080403920*t^2*z^2 - 105744528*t^2*z + 4630608*t^2 + 144*t*z^22 - 9024*t*z^21 + 261408*t*z^20 - 4642944*t*z^19 + 56553616*t*z^18 - 500681728*t*z^17 + 3332336096*t*z^16 - 17016843856*t*z^15 + 67490222880*t*z^14 - 209293812304*t*z^13 + 509008474016*t*z^12 - 971261035216*t*z^11 + 1452178884512*t*z^10 - 1696750811536*t*z^9 + 1542819952848*t*z^8 - 1084808877248*t*z^7 + 584165784336*t*z^6 - 237398880816*t*z^5 + 71184471120*t*z^4 - 15198503040*t*z^3 + 2176568496*t*z^2 - 186620112*t*z + 7208352*t + 32*z^24 - 2224*z^23 + 71920*z^22 - 1436608*z^21 + 19845728*z^20 - 201173328*z^19 + 1549744720*z^18 - 9273046864*z^17 + 43695251088*z^16 - 163510431968*z^15 + 488190560080*z^14 - 1165354415936*z^13 + 2224558062432*z^12 - 3392129317744*z^11 + 4122954029488*z^10 - 3981108538176*z^9 + 3038741516304*z^8 - 1819910037936*z^7 + 845818563168*z^6 - 300094018416*z^5 + 79307167392*z^4 - 15028913664*z^3 + 1918168128*z^2 - 146686464*z + 5038848:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7*z + 384*t^7 - 144*t^6*z^5 + 2256*t^6*z^4 - 12656*t^6*z^3 + 30464*t^6*z^2 - 29328*t^6*z + 8240*t^6 - 112*t^5*z^9 + 2976*t^5*z^8 - 33152*t^5*z^7 + 201568*t^5*z^6 - 729984*t^5*z^5 + 1611616*t^5*z^4 - 2125936*t^5*z^3 + 1566368*t^5*z^2 - 565536*t^5*z + 77536*t^5 - 32*t^4*z^13 + 1200*t^4*z^12 - 20176*t^4*z^11 + 201408*t^4*z^10 - 1330512*t^4*z^9 + 6118624*t^4*z^8 - 19978080*t^4*z^7 + 46205824*t^4*z^6 - 74173456*t^4*z^5 + 79825008*t^4*z^4 - 55009168*t^4*z^3 + 22705360*t^4*z^2 - 4994032*t^4*z + 393536*t^4 - 144*t^3*z^15 + 6288*t^3*z^14 - 123248*t^3*z^13 + 1432384*t^3*z^12 - 10986688*t^3*z^11 + 58597680*t^3*z^10 - 223158160*t^3*z^9 + 613789216*t^3*z^8 - 1220290064*t^3*z^7 + 1740089376*t^3*z^6 - 1751946944*t^3*z^5 + 1215497696*t^3*z^4 - 559993744*t^3*z^3 + 161268416*t^3*z^2 - 25878912*t^3*z + 2035456*t^3 - 224*t^2*z^17 + 11216*t^2*z^16 - 254672*t^2*z^15 + 3467984*t^2*z^14 - 31567504*t^2*z^13 + 202717376*t^2*z^12 - 945179248*t^2*z^11 + 3246569280*t^2*z^10 - 8260217600*t^2*z^9 + 15555286048*t^2*z^8 - 21567839424*t^2*z^7 + 21820639712*t^2*z^6 - 15889288736*t^2*z^5 + 8152677296*t^2*z^4 - 2848741232*t^2*z^3 + 639628384*t^2*z^2 - 82791408*t^2*z + 3613232*t^2 - 144*t*z^19 + 8160*t*z^18 - 211728*t*z^17 + 3331632*t*z^16 - 35497024*t*z^15 + 270829696*t*z^14 - 1526541168*t*z^13 + 6467951344*t*z^12 - 20778979280*t*z^11 + 50753638736*t*z^10 - 94123793856*t*z^9 + 131971099120*t*z^8 - 138979681776*t*z^7 + 108893431424*t*z^6 - 62589856304*t*z^5 + 25822900528*t*z^4 - 7385668224*t*z^3 + 1380512528*t*z^2 - 150154304*t*z + 9346352*t - 32*z^21 + 2032*z^20 - 59568*z^19 + 1069008*z^18 - 13131808*z^17 + 116977872*z^16 - 781149440*z^15 + 3988129056*z^14 - 15743751680*z^13 + 48326127168*z^12 - 115526909616*z^11 + 214818570720*z^10 - 309685962864*z^9 + 344393777344*z^8 - 293342980384*z^7 + 189395806288*z^6 - 91257999312*z^5 + 32040030240*z^4 - 7892578880*z^3 + 1280394624*z^2 - 121875008*z + 3111616)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_36 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 36) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_36 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*z^4 - 36*z^3 + 94*z^2 - 58*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(12 - 4*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_37 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 37) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_37 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^6 - 32*z^5 + 186*z^4 - 466*z^3 + 468*z^2 - 190*z + 24:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^3 + 20*z^2 - 56*z + 28)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_38 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (_hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 38) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : ((0:ℝ):ℝ)=0 := by
  apply cell_10_38 z t hf hn0 hn1 hn2 hn3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_39 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 39) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_39 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^4 - 22*t*z^3 + 66*t*z^2 - 36*t*z + 2*z^4 - 14*z^3 + 28*z^2 - 22*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t*z + 10*t - 2*z + 2)*hf
  · have hr : (16*t^8 + 144*t^7*z^4 - 1504*t^7*z^3 + 4528*t^7*z^2 - 3360*t^7*z + 656*t^7 + 480*t^6*z^8 - 10032*t^6*z^7 + 82800*t^6*z^6 - 341008*t^6*z^5 + 731520*t^6*z^4 - 796880*t^6*z^3 + 447424*t^6*z^2 - 123008*t^6*z + 12976*t^6 + 704*t^5*z^12 - 22080*t^5*z^11 + 298432*t^5*z^10 - 2274144*t^5*z^9 + 10743472*t^5*z^8 - 32669360*t^5*z^7 + 64642080*t^5*z^6 - 83142016*t^5*z^5 + 69246816*t^5*z^4 - 36739776*t^5*z^3 + 11884912*t^5*z^2 - 2118480*t^5*z + 158432*t^5 + 384*t^4*z^16 - 16064*t^4*z^15 + 302688*t^4*z^14 - 3398064*t^4*z^13 + 25340800*t^4*z^12 - 132542192*t^4*z^11 + 500511776*t^4*z^10 - 1383985952*t^4*z^9 + 2812696000*t^4*z^8 - 4183176880*t^4*z^7 + 4506375296*t^4*z^6 - 3467082048*t^4*z^5 + 1868196752*t^4*z^4 - 683584944*t^4*z^3 + 160879440*t^4*z^2 - 21863856*t^4*z + 1299184*t^4 + 1600*t^3*z^18 - 77504*t^3*z^17 + 1703568*t^3*z^16 - 22477552*t^3*z^15 + 198509488*t^3*z^14 - 1239178288*t^3*z^13 + 5632310704*t^3*z^12 - 18939796432*t^3*z^11 + 47483992368*t^3*z^10 - 88996742192*t^3*z^9 + 124677100192*t^3*z^8 - 130277188784*t^3*z^7 + 101033423392*t^3*z^6 - 57577608176*t^3*z^5 + 23677804448*t^3*z^4 - 6806798240*t^3*z^3 + 1292966576*t^3*z^2 - 145342720*t^3*z + 7303280*t^3 + 2432*t^2*z^20 - 134048*t^2*z^19 + 3384592*t^2*z^18 - 51857424*t^2*z^17 + 538452688*t^2*z^16 - 4008495472*t^2*z^15 + 22083745408*t^2*z^14 - 91683614800*t^2*z^13 + 289665205952*t^2*z^12 - 699582713680*t^2*z^11 + 1293190389936*t^2*z^10 - 1828698817392*t^2*z^9 + 1975067909120*t^2*z^8 - 1624040958048*t^2*z^7 + 1010433497536*t^2*z^6 - 470379168224*t^2*z^5 + 160711204928*t^2*z^4 - 39006207232*t^2*z^3 + 6352160320*t^2*z^2 - 621137328*t^2*z + 27519568*t^2 + 1600*t*z^22 - 98976*t*z^21 + 2828192*t*z^20 - 49509232*t*z^19 + 593808688*t*z^18 - 5170925968*t*z^17 + 33808790464*t*z^16 - 169359912912*t*z^15 + 657855058608*t*z^14 - 1994672582592*t*z^13 + 4735473316592*t*z^12 - 8809306298800*t*z^11 + 12833586471584*t*z^10 - 14618606011296*t*z^9 + 12983922924304*t*z^8 - 8948356143360*t*z^7 + 4746412223968*t*z^6 - 1911997036672*t*z^5 + 572610152192*t*z^4 - 123176404048*t*z^3 + 17948682656*t*z^2 - 1583427312*t*z + 63750176*t + 384*z^24 - 26368*z^23 + 842272*z^22 - 16614784*z^21 + 226602688*z^20 - 2267218912*z^19 + 17234173872*z^18 - 101729746352*z^17 + 472782988976*z^16 - 1744713391184*z^15 + 5137449148912*z^14 - 12099294797728*z^13 + 22806880961792*z^12 - 34394746977504*z^11 + 41446789489408*z^10 - 39816940152736*z^9 + 30377594304256*z^8 - 18291240103424*z^7 + 8607868528896*z^6 - 3118845591888*z^5 + 850236856848*z^4 - 168197772400*z^3 + 22729836352*z^2 - 1871925440*z + 70685440:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-144*t^7*z + 640*t^7 - 480*t^6*z^5 + 7152*t^6*z^4 - 37488*t^6*z^3 + 79840*t^6*z^2 - 57888*t^6*z + 12864*t^6 - 704*t^5*z^9 + 17856*t^5*z^8 - 187776*t^5*z^7 + 1057504*t^5*z^6 - 3441712*t^5*z^5 + 6543792*t^5*z^4 - 7113264*t^5*z^3 + 4301760*t^5*z^2 - 1326144*t^5*z + 160848*t^5 - 384*t^4*z^13 + 13760*t^4*z^12 - 218208*t^4*z^11 + 2019632*t^4*z^10 - 12118208*t^4*z^9 + 49516576*t^4*z^8 - 140801648*t^4*z^7 + 279474976*t^4*z^6 - 382321328*t^4*z^5 + 351072384*t^4*z^4 - 208859376*t^4*z^3 + 76242544*t^4*z^2 - 15372224*t^4*z + 1279504*t^4 - 1600*t^3*z^15 + 67904*t^3*z^14 - 1288144*t^3*z^13 + 14407568*t^3*z^12 - 105555456*t^3*z^11 + 532519568*t^3*z^10 - 1895008448*t^3*z^9 + 4801592448*t^3*z^8 - 8666875872*t^3*z^7 + 11092516272*t^3*z^6 - 9986030752*t^3*z^5 + 6231547040*t^3*z^4 - 2621471120*t^3*z^3 + 705015504*t^3*z^2 - 108808784*t^3*z + 7396896*t^3 - 2432*t^2*z^17 + 119456*t^2*z^16 - 2655696*t^2*z^15 + 35323536*t^2*z^14 - 313113536*t^2*z^13 + 1950540880*t^2*z^12 - 8779608912*t^2*z^11 + 28940143392*t^2*z^10 - 70175760160*t^2*z^9 + 125047826848*t^2*z^8 - 163084484656*t^2*z^7 + 154777015056*t^2*z^6 - 105935568656*t^2*z^5 + 51457986176*t^2*z^4 - 17230722144*t^2*z^3 + 3769335824*t^2*z^2 - 483593088*t^2*z + 27247440*t^2 - 1600*t*z^19 + 89376*t*z^18 - 2283936*t*z^17 + 35357136*t*z^16 - 370156816*t*z^15 + 2770915456*t*z^14 - 15297156512*t*z^13 + 63352239744*t*z^12 - 198484922128*t*z^11 + 471704694592*t*z^10 - 849468298656*t*z^9 + 1155488111776*t*z^8 - 1181611613056*t*z^7 + 902027475424*t*z^6 - 508211894704*t*z^5 + 207335784960*t*z^4 - 59310565264*t*z^3 + 11242825584*t*z^2 - 1264587408*t*z + 64186416*t - 384*z^21 + 24064*z^20 - 695968*z^19 + 12318272*z^18 - 149189152*z^17 + 1309796672*z^16 - 8617129808*z^15 + 43328794992*z^14 - 168414773312*z^13 + 508963646544*z^12 - 1198264608096*z^11 + 2196474143120*z^10 - 3127749416048*z^9 + 3447615157520*z^8 - 2925877320928*z^7 + 1895851023520*z^6 - 925486400976*z^5 + 333189259040*z^4 - 85449946256*z^3 + 14713218176*z^2 - 1518557472*z + 70390432)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_40 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 40) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_40 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^5 - 20*z^4 + 56*z^3 - 28*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 8*z + 2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_41 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (_hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 41) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : ((0:ℝ):ℝ)=0 := by
  apply cell_10_41 z t hf hn0 hn1 hn2 hn3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_42 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 42) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_42 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^5 - 20*z^4 + 54*z^3 - 18*z^2 - 16*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 8*z + 4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_43 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 43) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_43 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 + 6*t*z - 6*t + 2*z^5 - 20*z^4 + 56*z^3 - 26*z^2 - 10*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 8*z + 2)*hf
  · have hr : (16*t^8 + 80*t^7*z^4 - 864*t^7*z^3 + 2736*t^7*z^2 - 2272*t^7*z + 400*t^7 + 144*t^6*z^8 - 3120*t^6*z^7 + 26912*t^6*z^6 - 117280*t^6*z^5 + 271216*t^6*z^4 - 324576*t^6*z^3 + 192832*t^6*z^2 - 51088*t^6*z + 4720*t^6 + 112*t^5*z^12 - 3648*t^5*z^11 + 51568*t^5*z^10 - 414656*t^5*z^9 + 2089600*t^5*z^8 - 6861632*t^5*z^7 + 14822288*t^5*z^6 - 20860288*t^5*z^5 + 18669264*t^5*z^4 - 10231072*t^5*z^3 + 3231520*t^5*z^2 - 528096*t^5*z + 34240*t^5 + 32*t^4*z^16 - 1392*t^4*z^15 + 27536*t^4*z^14 - 327984*t^4*z^13 + 2623824*t^4*z^12 - 14875552*t^4*z^11 + 61396432*t^4*z^10 - 186383920*t^4*z^9 + 415407728*t^4*z^8 - 672159504*t^4*z^7 + 775531648*t^4*z^6 - 624017344*t^4*z^5 + 340663696*t^4*z^4 - 121512192*t^4*z^3 + 26710880*t^4*z^2 - 3249472*t^4*z + 166384*t^4 + 144*t^3*z^18 - 7040*t^3*z^17 + 156704*t^3*z^16 - 2101808*t^3*z^15 + 18949328*t^3*z^14 - 121321216*t^3*z^13 + 568340288*t^3*z^12 - 1979155024*t^3*z^11 + 5158123536*t^3*z^10 - 10065331696*t^3*z^9 + 14642879488*t^3*z^8 - 15754071440*t^3*z^7 + 12389725184*t^3*z^6 - 7007386352*t^3*z^5 + 2784335280*t^3*z^4 - 750298304*t^3*z^3 + 129425584*t^3*z^2 - 12814672*t^3*z + 552016*t^3 + 224*t^2*z^20 - 12192*t^2*z^19 + 304544*t^2*z^18 - 4625248*t^2*z^17 + 47704016*t^2*z^16 - 353523040*t^2*z^15 + 1943124400*t^2*z^14 - 8065550816*t^2*z^13 + 25522635568*t^2*z^12 - 61798998112*t^2*z^11 + 114469558464*t^2*z^10 - 161720140288*t^2*z^9 + 173395387488*t^2*z^8 - 140092250704*t^2*z^7 + 84426026624*t^2*z^6 - 37391274464*t^2*z^5 + 11902039792*t^2*z^4 - 2629960064*t^2*z^3 + 380622896*t^2*z^2 - 32279856*t^2*z + 1210768*t^2 + 144*t*z^22 - 8656*t*z^21 + 240640*t*z^20 - 4103424*t*z^19 + 47999168*t*z^18 - 408123536*t*z^17 + 2608316848*t*z^16 - 12783389120*t*z^15 + 48611061072*t*z^14 - 144306811952*t*z^13 + 335174318032*t*z^12 - 608810594496*t*z^11 + 862801918720*t*z^10 - 950466321264*t*z^9 + 809628146368*t*z^8 - 529363211200*t*z^7 + 262854512176*t*z^6 - 97582296752*t*z^5 + 26456275936*t*z^4 - 5050806624*t*z^3 + 639083440*t*z^2 - 47791792*t*z + 1586272*t + 32*z^24 - 2112*z^23 + 64896*z^22 - 1232384*z^21 + 16192624*z^20 - 156180848*z^19 + 1145083488*z^18 - 6521697168*z^17 + 29246953616*z^16 - 104117410000*z^15 + 295504525264*z^14 - 669731336208*z^13 + 1211704935520*z^12 - 1747133084960*z^11 + 2002114850544*z^10 - 1816246239120*z^9 + 1297046582672*z^8 - 723313856960*z^7 + 311291083488*z^6 - 101606144688*z^5 + 24505377552*z^4 - 4194279040*z^3 + 476694112*z^2 - 31804480*z + 924160:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7*z + 384*t^7 - 144*t^6*z^5 + 2256*t^6*z^4 - 12656*t^6*z^3 + 29920*t^6*z^2 - 26160*t^6*z + 5360*t^6 - 112*t^5*z^9 + 2976*t^5*z^8 - 33152*t^5*z^7 + 200752*t^5*z^6 - 716352*t^5*z^5 + 1526608*t^5*z^4 - 1880128*t^5*z^3 + 1230128*t^5*z^2 - 361248*t^5*z + 32816*t^5 - 32*t^4*z^13 + 1200*t^4*z^12 - 20176*t^4*z^11 + 200896*t^4*z^10 - 1316368*t^4*z^9 + 5952688*t^4*z^8 - 18897568*t^4*z^7 + 41918704*t^4*z^6 - 63454976*t^4*z^5 + 62938560*t^4*z^4 - 38706704*t^4*z^3 + 13629344*t^4*z^2 - 2415552*t^4*z + 165456*t^4 - 144*t^3*z^15 + 6176*t^3*z^14 - 118928*t^3*z^13 + 1357216*t^3*z^12 - 10205216*t^3*z^11 + 53184912*t^3*z^10 - 196847520*t^3*z^9 + 521940128*t^3*z^8 - 989060256*t^3*z^7 + 1324422000*t^3*z^6 - 1229106080*t^3*z^5 + 768264704*t^3*z^4 - 310184560*t^3*z^3 + 75849392*t^3*z^2 - 10051424*t^3*z + 558240*t^3 - 224*t^2*z^17 + 10848*t^2*z^16 - 238336*t^2*z^15 + 3140768*t^2*z^14 - 27656880*t^2*z^13 + 171639584*t^2*z^12 - 771861728*t^2*z^11 + 2548525648*t^2*z^10 - 6200533456*t^2*z^9 + 11081307408*t^2*z^8 - 14430521088*t^2*z^7 + 13529943264*t^2*z^6 - 8981815056*t^2*z^5 + 4121122960*t^2*z^4 - 1260270320*t^2*z^3 + 242222688*t^2*z^2 - 26229104*t^2*z + 1201680*t^2 - 144*t*z^19 + 7792*t*z^18 - 193168*t*z^17 + 2905312*t*z^16 - 29593664*t*z^15 + 215841824*t*z^14 - 1162392272*t*z^13 + 4700232704*t*z^12 - 14381861664*t*z^11 + 33352086176*t*z^10 - 58452259952*t*z^9 + 76954742240*t*z^8 - 75460079344*t*z^7 + 54479874048*t*z^6 - 28493763120*t*z^5 + 10541182896*t*z^4 - 2658725152*t*z^3 + 430268240*t*z^2 - 39857840*t*z + 1593232*t - 32*z^21 + 1920*z^20 - 53216*z^19 + 903456*z^18 - 10503888*z^17 + 88587024*z^16 - 560138448*z^15 + 2707427472*z^14 - 10113109520*z^13 + 29341477072*z^12 - 66182687760*z^11 + 115814714768*z^10 - 156561731040*z^9 + 162506437120*z^8 - 128452857856*z^7 + 76435175344*z^6 - 33664804208*z^5 + 10696297136*z^4 - 2354104288*z^3 + 335229072*z^2 - 27184544*z + 922128)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_44 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 44) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_44 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^3 + 10*t*z^2 - 6*t*z - 4*t + 2*z^5 - 18*z^4 + 46*z^3 - 24*z^2 + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 2*z^2 + 6*z)*hf
  · have hr : (16*t^8 + 80*t^7*z^4 - 928*t^7*z^3 + 3120*t^7*z^2 - 2656*t^7*z + 464*t^7 + 144*t^6*z^8 - 3360*t^6*z^7 + 31040*t^6*z^6 - 143696*t^6*z^5 + 348448*t^6*z^4 - 428560*t^6*z^3 + 257840*t^6*z^2 - 68688*t^6*z + 6592*t^6 + 112*t^5*z^12 - 3936*t^5*z^11 + 59776*t^5*z^10 - 513504*t^5*z^9 + 2744272*t^5*z^8 - 9466112*t^5*z^7 + 21233648*t^5*z^6 - 30659296*t^5*z^5 + 27907200*t^5*z^4 - 15507040*t^5*z^3 + 4993744*t^5*z^2 - 848160*t^5*z + 58496*t^5 + 32*t^4*z^16 - 1504*t^4*z^15 + 32000*t^4*z^14 - 407632*t^4*z^13 + 3463888*t^4*z^12 - 20701056*t^4*z^11 + 89342384*t^4*z^10 - 281396400*t^4*z^9 + 646201008*t^4*z^8 - 1071489904*t^4*z^7 + 1262619760*t^4*z^6 - 1036925264*t^4*z^5 + 579481248*t^4*z^4 - 213236320*t^4*z^3 + 49011808*t^4*z^2 - 6345680*t^4*z + 352432*t^4 + 144*t^3*z^18 - 7520*t^3*z^17 + 178480*t^3*z^16 - 2547024*t^3*z^15 + 24369520*t^3*z^14 - 165071232*t^3*z^13 + 815184384*t^3*z^12 - 2980138960*t^3*z^11 + 8116650304*t^3*z^10 - 16475513168*t^3*z^9 + 24832992096*t^3*z^8 - 27613474160*t^3*z^7 + 22444334560*t^3*z^6 - 13161105040*t^3*z^5 + 5459576144*t^3*z^4 - 1552772224*t^3*z^3 + 286753648*t^3*z^2 - 30879120*t^3*z + 1469168*t^3 + 224*t^2*z^20 - 12928*t^2*z^19 + 342096*t^2*z^18 - 5497904*t^2*z^17 + 59928336*t^2*z^16 - 468684752*t^2*z^15 + 2714152544*t^2*z^14 - 11847850976*t^2*z^13 + 39349729920*t^2*z^12 - 99802182864*t^2*z^11 + 193298063760*t^2*z^10 - 285237019760*t^2*z^9 + 319475977360*t^2*z^8 - 270144810432*t^2*z^7 + 171092373680*t^2*z^6 - 80166151840*t^2*z^5 + 27249491616*t^2*z^4 - 6506363648*t^2*z^3 + 1031764048*t^2*z^2 - 97382880*t^2*z + 4134400*t^2 + 144*t*z^22 - 9136*t*z^21 + 267904*t*z^20 - 4815392*t*z^19 + 59328160*t*z^18 - 530879920*t*z^17 + 3567383760*t*z^16 - 18365804256*t*z^15 + 73293758992*t*z^14 - 228151812240*t*z^13 + 555343760496*t*z^12 - 1057044480256*t*z^11 + 1570975803168*t*z^10 - 1818445022864*t*z^9 + 1633444272736*t*z^8 - 1132412475392*t*z^7 + 600756548560*t*z^6 - 240637007184*t*z^5 + 71250158944*t*z^4 - 15069146816*t*z^3 + 2147269072*t*z^2 - 184280368*t*z + 7181888*t + 32*z^24 - 2224*z^23 + 71920*z^22 - 1436496*z^21 + 19839232*z^20 - 201000512*z^19 + 1546951168*z^18 - 9242402720*z^17 + 43453918288*z^16 - 162102160128*z^15 + 481991489968*z^14 - 1144578016784*z^13 + 2171356395760*z^12 - 3288109309008*z^11 + 3968241216800*z^10 - 3807236555520*z^9 + 2892734140144*z^8 - 1730057468400*z^7 + 806758605024*z^6 - 289045610944*z^5 + 77769155632*z^4 - 15153523024*z^3 + 2011919840*z^2 - 162176448*z + 5958400:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7*z + 448*t^7 - 144*t^6*z^5 + 2496*t^6*z^4 - 15344*t^6*z^3 + 39008*t^6*z^2 - 35184*t^6*z + 7072*t^6 - 112*t^5*z^9 + 3264*t^5*z^8 - 39632*t^5*z^7 + 259280*t^5*z^6 - 987168*t^5*z^5 + 2207072*t^5*z^4 - 2796096*t^5*z^3 + 1860192*t^5*z^2 - 558496*t^5*z + 59008*t^5 - 32*t^4*z^13 + 1312*t^4*z^12 - 23968*t^4*z^11 + 257232*t^4*z^10 - 1799344*t^4*z^9 + 8594864*t^4*z^8 - 28519248*t^4*z^7 + 65507248*t^4*z^6 - 101966416*t^4*z^5 + 103635920*t^4*z^4 - 65464912*t^4*z^3 + 23989776*t^4*z^2 - 4582112*t^4*z + 329856*t^4 - 144*t^3*z^15 + 6656*t^3*z^14 - 137824*t^3*z^13 + 1686656*t^3*z^12 - 13553808*t^3*z^11 + 75177280*t^3*z^10 - 294665008*t^3*z^9 + 822708704*t^3*z^8 - 1631895760*t^3*z^7 + 2275930080*t^3*z^6 - 2195224112*t^3*z^5 + 1430583328*t^3*z^4 - 608783952*t^3*z^3 + 160260576*t^3*z^2 - 23509600*t^3*z + 1627792*t^3 - 224*t^2*z^17 + 11584*t^2*z^16 - 271472*t^2*z^15 + 3810928*t^2*z^14 - 35693824*t^2*z^13 + 235195696*t^2*z^12 - 1120698320*t^2*z^11 + 3911988752*t^2*z^10 - 10039110112*t^2*z^9 + 18886880112*t^2*z^8 - 25869243776*t^2*z^7 + 25548046432*t^2*z^6 - 17954599776*t^2*z^5 + 8807735840*t^2*z^4 - 2924913328*t^2*z^3 + 623392896*t^2*z^2 - 76831760*t^2*z + 3495280*t^2 - 144*t*z^19 + 8272*t*z^18 - 217552*t*z^17 + 3468576*t*z^16 - 37420672*t*z^15 + 288795456*t*z^14 - 1644039088*t*z^13 + 7020171776*t*z^12 - 22663737440*t*z^11 + 55424489632*t*z^10 - 102457963728*t*z^9 + 142510512288*t*z^8 - 148198421168*t*z^7 + 114243970688*t*z^6 - 64477830480*t*z^5 + 26127217904*t*z^4 - 7360118048*t*z^3 + 1362378896*t*z^2 - 148077424*t*z + 8669744*t - 32*z^21 + 2032*z^20 - 59568*z^19 + 1068896*z^18 - 13125984*z^17 + 116840560*z^16 - 779208992*z^15 + 3969819984*z^14 - 15622112864*z^13 + 47741174032*z^12 - 113464061472*z^11 + 209465664928*z^10 - 299500924800*z^9 + 330311374096*z^8 - 279402683296*z^7 + 179762660464*z^6 - 86833386784*z^5 + 30841162080*z^4 - 7782038160*z^3 + 1314184800*z^2 - 132693952*z + 4397152)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_45 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 45) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_45 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^4 - 22*t*z^3 + 66*t*z^2 - 36*t*z + 2*z^4 - 14*z^3 + 28*z^2 - 22*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t*z + 10*t - 2*z + 2)*hf
  · have hr : (16*t^8 + 144*t^7*z^4 - 1568*t^7*z^3 + 4912*t^7*z^2 - 3616*t^7*z + 592*t^7 + 480*t^6*z^8 - 10464*t^6*z^7 + 90000*t^6*z^6 - 384480*t^6*z^5 + 844240*t^6*z^4 - 911200*t^6*z^3 + 483984*t^6*z^2 - 119584*t^6*z + 11296*t^6 + 704*t^5*z^12 - 23040*t^5*z^11 + 324688*t^5*z^10 - 2573440*t^5*z^9 + 12580144*t^5*z^8 - 39214112*t^5*z^7 + 78307680*t^5*z^6 - 99404896*t^5*z^5 + 79779888*t^5*z^4 - 39944512*t^5*z^3 + 12023056*t^5*z^2 - 1983936*t^5*z + 136768*t^5 + 384*t^4*z^16 - 16768*t^4*z^15 + 329472*t^4*z^14 - 3847744*t^4*z^13 + 29723104*t^4*z^12 - 159985168*t^4*z^11 + 616080080*t^4*z^10 - 1717385104*t^4*z^9 + 3473347616*t^4*z^8 - 5075444816*t^4*z^7 + 5313734576*t^4*z^6 - 3938959216*t^4*z^5 + 2031037744*t^4*z^4 - 707322704*t^4*z^3 + 157813920*t^4*z^2 - 20297680*t^4*z + 1144624*t^4 + 1600*t^3*z^18 - 78976*t^3*z^17 + 1769472*t^3*z^16 - 23797744*t^3*z^15 + 214115776*t^3*z^14 - 1360101376*t^3*z^13 + 6277655520*t^3*z^12 - 21368084016*t^3*z^11 + 53979326368*t^3*z^10 - 101329581072*t^3*z^9 + 141171650832*t^3*z^8 - 145616687568*t^3*z^7 + 110718177168*t^3*z^6 - 61518064368*t^3*z^5 + 24571757472*t^3*z^4 - 6848531616*t^3*z^3 + 1261273296*t^3*z^2 - 137610352*t^3*z + 6715312*t^3 + 2432*t^2*z^20 - 134048*t^2*z^19 + 3387296*t^2*z^18 - 51978336*t^2*z^17 + 540881568*t^2*z^16 - 4037432208*t^2*z^15 + 22311147424*t^2*z^14 - 92924660000*t^2*z^13 + 294492770176*t^2*z^12 - 713126562320*t^2*z^11 + 1320682230224*t^2*z^10 - 1868983098992*t^2*z^9 + 2017393739664*t^2*z^8 - 1655465818064*t^2*z^7 + 1026405703808*t^2*z^6 - 475533325040*t^2*z^5 + 161533128496*t^2*z^4 - 38959580480*t^2*z^3 + 6306820016*t^2*z^2 - 614037840*t^2*z + 27185056*t^2 + 1600*t*z^22 - 97504*t*z^21 + 2747488*t*z^20 - 47479552*t*z^19 + 562784736*t*z^18 - 4848988144*t*z^17 + 31408735712*t*z^16 - 156088844272*t*z^15 + 602422026448*t*z^14 - 1818045784624*t*z^13 + 4304423039024*t*z^12 - 8003594868032*t*z^11 + 11683716121648*t*z^10 - 13373504382560*t*z^9 + 11972148228480*t*z^8 - 8343290758592*t*z^7 + 4489892816912*t*z^6 - 1841123876624*t*z^5 + 563071789008*t*z^4 - 124042766192*t*z^3 + 18551606480*t*z^2 - 1681997872*t*z + 69604288*t + 384*z^24 - 25664*z^23 + 798784*z^22 - 15371680*z^21 + 204789856*z^20 - 2004384288*z^19 + 14928849472*z^18 - 86503515056*z^17 + 395477441888*z^16 - 1439243163808*z^15 + 4191485097520*z^14 - 9796383585472*z^13 + 18398024020448*z^12 - 27769156407552*z^11 + 33662288854400*z^10 - 32716303854208*z^9 + 25409332478240*z^8 - 15680610446880*z^7 + 7618513276816*z^6 - 2872372113648*z^5 + 821718530496*z^4 - 172128317984*z^3 + 24867718464*z^2 - 2211726400*z + 91157248:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-144*t^7*z + 704*t^7 - 480*t^6*z^5 + 7584*t^6*z^4 - 42096*t^6*z^3 + 93504*t^6*z^2 - 65152*t^6*z + 10672*t^6 - 704*t^5*z^9 + 18816*t^5*z^8 - 208272*t^5*z^7 + 1229024*t^5*z^6 - 4145824*t^5*z^5 + 7985776*t^5*z^4 - 8434880*t^5*z^3 + 4720912*t^5*z^2 - 1294240*t^5*z + 139632*t^5 - 384*t^4*z^13 + 14464*t^4*z^12 - 240768*t^4*z^11 + 2330432*t^4*z^10 - 14522208*t^4*z^9 + 60958992*t^4*z^8 - 175384656*t^4*z^7 + 345760000*t^4*z^6 - 460905344*t^4*z^5 + 405828096*t^4*z^4 - 228479280*t^4*z^3 + 78037712*t^4*z^2 - 14586976*t^4*z + 1133008*t^4 - 1600*t^3*z^15 + 69376*t^3*z^14 - 1345216*t^3*z^13 + 15377968*t^3*z^12 - 115052512*t^3*z^11 + 591551248*t^3*z^10 - 2137707504*t^3*z^9 + 5469030240*t^3*z^8 - 9885056160*t^3*z^7 + 12536385408*t^3*z^6 - 11059027344*t^3*z^5 + 6695540304*t^3*z^4 - 2713413216*t^3*z^3 + 700856208*t^3*z^2 - 104013840*t^3*z + 6754320*t^3 - 2432*t^2*z^17 + 119456*t^2*z^16 - 2658400*t^2*z^15 + 35428224*t^2*z^14 - 314900768*t^2*z^13 + 1968228080*t^2*z^12 - 8891846880*t^2*z^11 + 29417537552*t^2*z^10 - 71560082384*t^2*z^9 + 127786533376*t^2*z^8 - 166745080496*t^2*z^7 + 158019866752*t^2*z^6 - 107762603296*t^2*z^5 + 52045784032*t^2*z^4 - 17298116384*t^2*z^3 + 3753103280*t^2*z^2 - 478142864*t^2*z + 27090512*t^2 - 1600*t*z^19 + 87904*t*z^18 - 2212064*t*z^17 + 33766048*t*z^16 - 349040224*t*z^15 + 2583704496*t*z^14 - 14127541568*t*z^13 + 58056032160*t*z^12 - 180864421152*t*z^11 + 428451555344*t*z^10 - 771335569040*t*z^9 + 1052459255920*t*z^8 - 1083831185584*t*z^7 + 836885420416*t*z^6 - 479220522144*t*z^5 + 199709338064*t*z^4 - 58648757392*t*z^3 + 11464119808*t*z^2 - 1333945136*t*z + 69738944*t - 384*z^21 + 23360*z^20 - 656704*z^19 + 11314272*z^18 - 133597344*z^17 + 1145572160*z^16 - 7376115520*z^15 + 36385363792*z^14 - 139139109376*z^13 + 415105573072*z^12 - 968770748416*z^11 + 1769092120240*z^10 - 2524511983856*z^9 + 2807853154800*z^8 - 2423517886080*z^7 + 1611418779872*z^6 - 815377213808*z^5 + 307735378592*z^4 - 83796156352*z^3 + 15541068768*z^2 - 1755957536*z + 91072576)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_46 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 46) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_46 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 + 6*t*z - 6*t + 2*z^5 - 20*z^4 + 56*z^3 - 26*z^2 - 10*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z^2 + 8*z + 2)*hf
  · have hr : (16*t^8 + 80*t^7*z^4 - 864*t^7*z^3 + 2736*t^7*z^2 - 2272*t^7*z + 400*t^7 + 144*t^6*z^8 - 3120*t^6*z^7 + 26912*t^6*z^6 - 117280*t^6*z^5 + 271216*t^6*z^4 - 324576*t^6*z^3 + 192832*t^6*z^2 - 51088*t^6*z + 4720*t^6 + 112*t^5*z^12 - 3648*t^5*z^11 + 51568*t^5*z^10 - 414656*t^5*z^9 + 2089600*t^5*z^8 - 6861632*t^5*z^7 + 14822288*t^5*z^6 - 20860288*t^5*z^5 + 18669264*t^5*z^4 - 10231072*t^5*z^3 + 3231520*t^5*z^2 - 528096*t^5*z + 34240*t^5 + 32*t^4*z^16 - 1392*t^4*z^15 + 27536*t^4*z^14 - 327984*t^4*z^13 + 2623824*t^4*z^12 - 14875552*t^4*z^11 + 61396432*t^4*z^10 - 186383920*t^4*z^9 + 415407728*t^4*z^8 - 672159504*t^4*z^7 + 775531648*t^4*z^6 - 624017344*t^4*z^5 + 340663696*t^4*z^4 - 121512192*t^4*z^3 + 26710880*t^4*z^2 - 3249472*t^4*z + 166384*t^4 + 144*t^3*z^18 - 7040*t^3*z^17 + 156704*t^3*z^16 - 2101808*t^3*z^15 + 18949328*t^3*z^14 - 121321216*t^3*z^13 + 568340288*t^3*z^12 - 1979155024*t^3*z^11 + 5158123536*t^3*z^10 - 10065331696*t^3*z^9 + 14642879488*t^3*z^8 - 15754071440*t^3*z^7 + 12389725184*t^3*z^6 - 7007386352*t^3*z^5 + 2784335280*t^3*z^4 - 750298304*t^3*z^3 + 129425584*t^3*z^2 - 12814672*t^3*z + 552016*t^3 + 224*t^2*z^20 - 12192*t^2*z^19 + 304544*t^2*z^18 - 4625248*t^2*z^17 + 47704016*t^2*z^16 - 353523040*t^2*z^15 + 1943124400*t^2*z^14 - 8065550816*t^2*z^13 + 25522635568*t^2*z^12 - 61798998112*t^2*z^11 + 114469558464*t^2*z^10 - 161720140288*t^2*z^9 + 173395387488*t^2*z^8 - 140092250704*t^2*z^7 + 84426026624*t^2*z^6 - 37391274464*t^2*z^5 + 11902039792*t^2*z^4 - 2629960064*t^2*z^3 + 380622896*t^2*z^2 - 32279856*t^2*z + 1210768*t^2 + 144*t*z^22 - 8656*t*z^21 + 240640*t*z^20 - 4103424*t*z^19 + 47999168*t*z^18 - 408123536*t*z^17 + 2608316848*t*z^16 - 12783389120*t*z^15 + 48611061072*t*z^14 - 144306811952*t*z^13 + 335174318032*t*z^12 - 608810594496*t*z^11 + 862801918720*t*z^10 - 950466321264*t*z^9 + 809628146368*t*z^8 - 529363211200*t*z^7 + 262854512176*t*z^6 - 97582296752*t*z^5 + 26456275936*t*z^4 - 5050806624*t*z^3 + 639083440*t*z^2 - 47791792*t*z + 1586272*t + 32*z^24 - 2112*z^23 + 64896*z^22 - 1232384*z^21 + 16192624*z^20 - 156180848*z^19 + 1145083488*z^18 - 6521697168*z^17 + 29246953616*z^16 - 104117410000*z^15 + 295504525264*z^14 - 669731336208*z^13 + 1211704935520*z^12 - 1747133084960*z^11 + 2002114850544*z^10 - 1816246239120*z^9 + 1297046582672*z^8 - 723313856960*z^7 + 311291083488*z^6 - 101606144688*z^5 + 24505377552*z^4 - 4194279040*z^3 + 476694112*z^2 - 31804480*z + 924160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7*z + 384*t^7 - 144*t^6*z^5 + 2256*t^6*z^4 - 12656*t^6*z^3 + 29920*t^6*z^2 - 26160*t^6*z + 5360*t^6 - 112*t^5*z^9 + 2976*t^5*z^8 - 33152*t^5*z^7 + 200752*t^5*z^6 - 716352*t^5*z^5 + 1526608*t^5*z^4 - 1880128*t^5*z^3 + 1230128*t^5*z^2 - 361248*t^5*z + 32816*t^5 - 32*t^4*z^13 + 1200*t^4*z^12 - 20176*t^4*z^11 + 200896*t^4*z^10 - 1316368*t^4*z^9 + 5952688*t^4*z^8 - 18897568*t^4*z^7 + 41918704*t^4*z^6 - 63454976*t^4*z^5 + 62938560*t^4*z^4 - 38706704*t^4*z^3 + 13629344*t^4*z^2 - 2415552*t^4*z + 165456*t^4 - 144*t^3*z^15 + 6176*t^3*z^14 - 118928*t^3*z^13 + 1357216*t^3*z^12 - 10205216*t^3*z^11 + 53184912*t^3*z^10 - 196847520*t^3*z^9 + 521940128*t^3*z^8 - 989060256*t^3*z^7 + 1324422000*t^3*z^6 - 1229106080*t^3*z^5 + 768264704*t^3*z^4 - 310184560*t^3*z^3 + 75849392*t^3*z^2 - 10051424*t^3*z + 558240*t^3 - 224*t^2*z^17 + 10848*t^2*z^16 - 238336*t^2*z^15 + 3140768*t^2*z^14 - 27656880*t^2*z^13 + 171639584*t^2*z^12 - 771861728*t^2*z^11 + 2548525648*t^2*z^10 - 6200533456*t^2*z^9 + 11081307408*t^2*z^8 - 14430521088*t^2*z^7 + 13529943264*t^2*z^6 - 8981815056*t^2*z^5 + 4121122960*t^2*z^4 - 1260270320*t^2*z^3 + 242222688*t^2*z^2 - 26229104*t^2*z + 1201680*t^2 - 144*t*z^19 + 7792*t*z^18 - 193168*t*z^17 + 2905312*t*z^16 - 29593664*t*z^15 + 215841824*t*z^14 - 1162392272*t*z^13 + 4700232704*t*z^12 - 14381861664*t*z^11 + 33352086176*t*z^10 - 58452259952*t*z^9 + 76954742240*t*z^8 - 75460079344*t*z^7 + 54479874048*t*z^6 - 28493763120*t*z^5 + 10541182896*t*z^4 - 2658725152*t*z^3 + 430268240*t*z^2 - 39857840*t*z + 1593232*t - 32*z^21 + 1920*z^20 - 53216*z^19 + 903456*z^18 - 10503888*z^17 + 88587024*z^16 - 560138448*z^15 + 2707427472*z^14 - 10113109520*z^13 + 29341477072*z^12 - 66182687760*z^11 + 115814714768*z^10 - 156561731040*z^9 + 162506437120*z^8 - 128452857856*z^7 + 76435175344*z^6 - 33664804208*z^5 + 10696297136*z^4 - 2354104288*z^3 + 335229072*z^2 - 27184544*z + 922128)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_47 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 47) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_47 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z^2 - 10*t^2*z + 6*t^2 - 4*t*z^3 + 16*t*z^2 + 8*t*z - 12*t + 2*z^5 - 18*z^4 + 48*z^3 - 32*z^2 - 4*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4*t - 2*z^2 + 6*z - 2)*hf
  · have hr : (16*t^8*z^8 - 320*t^8*z^7 + 2592*t^8*z^6 - 10880*t^8*z^5 + 25264*t^8*z^4 - 32640*t^8*z^3 + 23328*t^8*z^2 - 8640*t^8*z + 1296*t^8 + 144*t^7*z^10 - 3792*t^7*z^9 + 41872*t^7*z^8 - 251744*t^7*z^7 + 896784*t^7*z^6 - 1940528*t^7*z^5 + 2550448*t^7*z^4 - 2027616*t^7*z^3 + 947376*t^7*z^2 - 238032*t^7*z + 24624*t^7 + 560*t^6*z^12 - 18272*t^6*z^11 + 256944*t^6*z^10 - 2037504*t^6*z^9 + 10017952*t^6*z^8 - 31701216*t^6*z^7 + 65231216*t^6*z^6 - 87138048*t^6*z^5 + 75298656*t^6*z^4 - 41464928*t^6*z^3 + 13952880*t^6*z^2 - 2595456*t^6*z + 202608*t^6 + 1248*t^5*z^14 - 48464*t^5*z^13 + 828272*t^5*z^12 - 8190512*t^5*z^11 + 51850560*t^5*z^10 - 219803552*t^5*z^9 + 635602096*t^5*z^8 - 1259098864*t^5*z^7 + 1705198784*t^5*z^6 - 1573607328*t^5*z^5 + 980539536*t^5*z^4 - 403167408*t^5*z^3 + 104096448*t^5*z^2 - 15180048*t^5*z + 946080*t^5 + 1744*t^4*z^16 - 78416*t^4*z^15 + 1576896*t^4*z^14 - 18706080*t^4*z^13 + 145422640*t^4*z^12 - 778844624*t^4*z^11 + 2944050240*t^4*z^10 - 7931853200*t^4*z^9 + 15255600448*t^4*z^8 - 20902619792*t^4*z^7 + 20339501728*t^4*z^6 - 13966599888*t^4*z^5 + 6672802992*t^4*z^4 - 2156243136*t^4*z^3 + 446482176*t^4*z^2 - 53120304*t^4*z + 2744496*t^4 + 1552*t^3*z^18 - 79232*t^3*z^17 + 1832080*t^3*z^16 - 25366000*t^3*z^15 + 234274592*t^3*z^14 - 1522414576*t^3*z^13 + 7159665952*t^3*z^12 - 24711702736*t^3*z^11 + 62938693456*t^3*z^10 - 118325796096*t^3*z^9 + 163870126368*t^3*z^8 - 166688500320*t^3*z^7 + 123922677184*t^3*z^6 - 66689555056*t^3*z^5 + 25517576160*t^3*z^4 - 6724719824*t^3*z^3 + 1153118208*t^3*z^2 - 115123824*t^3*z + 5048784*t^3 + 848*t^2*z^20 - 48448*t^2*z^19 + 1266528*t^2*z^18 - 20061312*t^2*z^17 + 214920224*t^2*z^16 - 1646539568*t^2*z^15 + 9304008672*t^2*z^14 - 39447336896*t^2*z^13 + 126575063696*t^2*z^12 - 308315250896*t^2*z^11 + 569943867040*t^2*z^10 - 798005107920*t^2*z^9 + 843936242320*t^2*z^8 - 671325095312*t^2*z^7 + 398806730880*t^2*z^6 - 174747887536*t^2*z^5 + 55316695360*t^2*z^4 - 12221425856*t^2*z^3 + 1776036160*t^2*z^2 - 151510640*t^2*z + 5703888*t^2 + 256*t*z^22 - 16192*t*z^21 + 472544*t*z^20 - 8436272*t*z^19 + 102998896*t*z^18 - 910848112*t*z^17 + 6029678416*t*z^16 - 30466067968*t*z^15 + 118799423232*t*z^14 - 359479719056*t*z^13 + 845596367456*t*z^12 - 1545361933664*t*z^11 + 2190132016720*t*z^10 - 2400752544816*t*z^9 + 2027941590816*t*z^8 - 1312454998480*t*z^7 + 644747335280*t*z^6 - 236884936368*t*z^5 + 63592791040*t*z^4 - 12018951152*t*z^3 + 1502484416*t*z^2 - 110422928*t*z + 3565920*t + 32*z^24 - 2224*z^23 + 71808*z^22 - 1429440*z^21 + 19633968*z^20 - 197344112*z^19 + 1502354592*z^18 - 8847799408*z^17 + 40834976432*z^16 - 148801145712*z^15 + 429684518384*z^14 - 984274933792*z^13 + 1787391185984*z^12 - 2568780875376*z^11 + 2914710401088*z^10 - 2602438874336*z^9 + 1819487105872*z^8 - 988646921712*z^7 + 412748171824*z^6 - 130125927632*z^5 + 30177839856*z^4 - 4942946000*z^3 + 534832128*z^2 - 33784128*z + 924160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^5 + 224*t^8*z^4 - 1168*t^8*z^3 + 2736*t^8*z^2 - 2784*t^8*z + 1088*t^8 - 144*t^7*z^7 + 2928*t^7*z^6 - 23584*t^7*z^5 + 95456*t^7*z^4 - 203200*t^7*z^3 + 220464*t^7*z^2 - 116208*t^7*z + 24848*t^7 - 560*t^6*z^9 + 14912*t^6*z^8 - 164672*t^6*z^7 + 974352*t^6*z^6 - 3333568*t^6*z^5 + 6663376*t^6*z^4 - 7608768*t^6*z^3 + 4834992*t^6*z^2 - 1581488*t^6*z + 192272*t^6 - 1248*t^5*z^11 + 40976*t^5*z^10 - 576176*t^5*z^9 + 4527328*t^5*z^8 - 21764736*t^5*z^7 + 66002320*t^5*z^6 - 126237168*t^5*z^5 + 149899520*t^5*z^4 - 108613504*t^5*z^3 + 46191536*t^5*z^2 - 10423280*t^5*z + 1056544*t^5 - 1744*t^4*z^13 + 67952*t^4*z^12 - 1160464*t^4*z^11 + 11401792*t^4*z^10 - 71141616*t^4*z^9 + 293825504*t^4*z^8 - 813987344*t^4*z^7 + 1507660000*t^4*z^6 - 1845878224*t^4*z^5 + 1475063104*t^4*z^4 - 752071984*t^4*z^3 + 232974240*t^4*z^2 - 39534528*t^4*z + 2092784*t^4 - 1552*t^3*z^15 + 69920*t^3*z^14 - 1404800*t^3*z^13 + 16586048*t^3*z^12 - 127664384*t^3*z^11 + 672093232*t^3*z^10 - 2472198592*t^3*z^9 + 6390380640*t^3*z^8 - 11563323424*t^3*z^7 + 14521753760*t^3*z^6 - 12532606048*t^3*z^5 + 7320771808*t^3*z^4 - 2813262336*t^3*z^3 + 673515952*t^3*z^2 - 89396960*t^3*z + 7495968*t^3 - 848*t^2*z^17 + 43360*t^2*z^16 - 1002128*t^2*z^15 + 13830896*t^2*z^14 - 126880848*t^2*z^13 + 815097872*t^2*z^12 - 3765186304*t^2*z^11 + 12653848864*t^2*z^10 - 31010941120*t^2*z^9 + 55215173552*t^2*z^8 - 70944271264*t^2*z^7 + 65252671456*t^2*z^6 - 42483683712*t^2*z^5 + 19215364496*t^2*z^4 - 5843453888*t^2*z^3 + 1126658016*t^2*z^2 - 124113328*t^2*z + 1920*t^2 - 256*t*z^19 + 14656*t*z^18 - 383328*t*z^17 + 6062768*t*z^16 - 64690992*t*z^15 + 492004992*t*z^14 - 2748130736*t*z^13 + 11452567600*t*z^12 - 35851358960*t*z^11 + 84360596560*t*z^10 - 148723425696*t*z^9 + 195367037728*t*z^8 - 189952065312*t*z^7 + 135481538608*t*z^6 - 69924994880*t*z^5 + 25545270848*t*z^4 - 6369197184*t*z^3 + 1018404144*t*z^2 - 91109408*t*z + 11076800*t - 32*z^21 + 2032*z^20 - 59456*z^19 + 1062512*z^18 - 12959584*z^17 + 114214592*z^16 - 751206608*z^15 + 3756527216*z^14 - 14425565504*z^13 + 42713910000*z^12 - 97516703648*z^11 + 171179596400*z^10 - 230016179344*z^9 + 235269113664*z^8 - 181835225984*z^7 + 105065770768*z^6 - 44647237680*z^5 + 13599415808*z^4 - 2849717808*z^3 + 383304064*z^2 - 30010624*z - 3355872)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_48 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 48) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_48 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z^2 - 10*t^2*z + 6*t^2 + 2*t*z^4 - 20*t*z^3 + 54*t*z^2 - 20*t*z - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t*z + 8*t)*hf
  · have hr : (16*t^8*z^8 - 320*t^8*z^7 + 2592*t^8*z^6 - 10880*t^8*z^5 + 25264*t^8*z^4 - 32640*t^8*z^3 + 23328*t^8*z^2 - 8640*t^8*z + 1296*t^8 - 112*t^7*z^10 + 2864*t^7*z^9 - 31088*t^7*z^8 + 186528*t^7*z^7 - 676336*t^7*z^6 + 1529296*t^7*z^5 - 2168912*t^7*z^4 + 1916832*t^7*z^3 - 1022544*t^7*z^2 + 301104*t^7*z - 37584*t^7 + 368*t^6*z^12 - 11424*t^6*z^11 + 155056*t^6*z^10 - 1208128*t^6*z^9 + 5970720*t^6*z^8 - 19556384*t^6*z^7 + 43221232*t^6*z^6 - 64711104*t^6*z^5 + 65281248*t^6*z^4 - 43542560*t^6*z^3 + 18369648*t^6*z^2 - 4435776*t^6*z + 466992*t^6 - 736*t^5*z^14 + 26832*t^5*z^13 - 436432*t^5*z^12 + 4177200*t^5*z^11 - 26140576*t^5*z^10 + 112493824*t^5*z^9 - 341402096*t^5*z^8 + 738915632*t^5*z^7 - 1143418912*t^5*z^6 + 1259675712*t^5*z^5 - 975651792*t^5*z^4 + 517583856*t^5*z^3 - 178719264*t^5*z^2 + 36141552*t^5*z - 3245184*t^5 + 976*t^4*z^16 - 40816*t^4*z^15 + 772864*t^4*z^14 - 8763520*t^4*z^13 + 66335184*t^4*z^12 - 353912432*t^4*z^11 + 1370749216*t^4*z^10 - 3915711536*t^4*z^9 + 8310844512*t^4*z^8 - 13125346032*t^4*z^7 + 15372217536*t^4*z^6 - 13231939824*t^4*z^5 + 8229005328*t^4*z^4 - 3586683840*t^4*z^3 + 1037020128*t^4*z^2 - 178334640*t^4*z + 13786416*t^4 - 880*t^3*z^18 + 41472*t^3*z^17 - 894896*t^3*z^16 + 11714608*t^3*z^15 - 103926368*t^3*z^14 + 661341968*t^3*z^13 - 3117847232*t^3*z^12 + 11097150192*t^3*z^11 - 30136721392*t^3*z^10 + 62759560704*t^3*z^9 - 100306935968*t^3*z^8 + 122699731552*t^3*z^7 - 114099085888*t^3*z^6 + 79689083984*t^3*z^5 - 40970298528*t^3*z^4 + 14998414864*t^3*z^3 - 3690780864*t^3*z^2 + 546097104*t^3*z - 36643536*t^3 + 528*t^2*z^20 - 27648*t^2*z^19 + 668704*t^2*z^18 - 9910112*t^2*z^17 + 100676896*t^2*z^16 - 743302704*t^2*z^15 + 4126896064*t^2*z^14 - 17595474048*t^2*z^13 + 58354228240*t^2*z^12 - 151654522768*t^2*z^11 + 309935881760*t^2*z^10 - 498321233168*t^2*z^9 + 628859338256*t^2*z^8 - 619582446416*t^2*z^7 + 472303073280*t^2*z^6 - 274616324880*t^2*z^5 + 119120473792*t^2*z^4 - 37213633664*t^2*z^3 + 7890086944*t^2*z^2 - 1013922608*t^2*z + 59477520*t^2 - 192*t*z^22 + 11040*t*z^21 - 295296*t*z^20 + 4878672*t*z^19 - 55755856*t*z^18 + 467863280*t*z^17 - 2986769552*t*z^16 + 14834464832*t*z^15 - 58155582784*t*z^14 + 181598592624*t*z^13 - 454091254464*t*z^12 + 911474012640*t*z^11 - 1468770779216*t*z^10 + 1896155796304*t*z^9 - 1952637424896*t*z^8 + 1592696139600*t*z^7 - 1018072529008*t*z^6 + 501994414768*t*z^5 - 186480189120*t*z^4 + 50314746864*t*z^3 - 9280342144*t*z^2 + 1043876560*t*z - 53880288*t + 32*z^24 - 2000*z^23 + 58496*z^22 - 1063872*z^21 + 13485424*z^20 - 126573872*z^19 + 912392640*z^18 - 5171185072*z^17 + 23406984656*z^16 - 85495601136*z^15 + 253665396304*z^14 - 613699349952*z^13 + 1212595333280*z^12 - 1956186436784*z^11 + 2571310193216*z^10 - 2743467629056*z^9 + 2362258366768*z^8 - 1627871653104*z^7 + 887282648240*z^6 - 376149307056*z^5 + 121022358736*z^4 - 28466804400*z^3 + 4603930368*z^2 - 456392928*z + 20852608:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^5 + 224*t^8*z^4 - 1168*t^8*z^3 + 2736*t^8*z^2 - 2784*t^8*z + 1088*t^8 + 112*t^7*z^7 - 2192*t^7*z^6 + 17376*t^7*z^5 - 71200*t^7*z^4 + 160064*t^7*z^3 - 195536*t^7*z^2 + 124176*t^7*z - 34032*t^7 - 368*t^6*z^9 + 9216*t^6*z^8 - 97920*t^6*z^7 + 574160*t^6*z^6 - 2026944*t^6*z^5 + 4426000*t^6*z^4 - 5956352*t^6*z^3 + 4816048*t^6*z^2 - 2177200*t^6*z + 442768*t^6 + 736*t^5*z^11 - 22416*t^5*z^10 + 298256*t^5*z^9 - 2274848*t^5*z^8 + 10977792*t^5*z^7 - 34954576*t^5*z^6 + 74510832*t^5*z^5 - 106099968*t^5*z^4 + 99310368*t^5*z^3 - 58802832*t^5*z^2 + 20182992*t^5*z - 3161376*t^5 - 976*t^4*z^13 + 34960*t^4*z^12 - 558224*t^4*z^11 + 5238400*t^4*z^10 - 32078704*t^4*z^9 + 134689984*t^4*z^8 - 396977392*t^4*z^7 + 828318560*t^4*z^6 - 1221356208*t^4*z^5 + 1258638592*t^4*z^4 - 885286384*t^4*z^3 + 405672352*t^4*z^2 - 109900704*t^4*z + 13631472*t^4 + 880*t^3*z^15 - 36192*t^3*z^14 + 673344*t^3*z^13 - 7492704*t^3*z^12 + 55567232*t^3*z^11 - 289801712*t^3*z^10 + 1093708096*t^3*z^9 - 3030325824*t^3*z^8 + 6196424256*t^3*z^7 - 9335677952*t^3*z^6 + 10280421152*t^3*z^5 - 8142390624*t^3*z^4 + 4506958432*t^3*z^3 - 1654959120*t^3*z^2 + 363361024*t^3*z - 36494688*t^3 - 528*t^2*z^17 + 24480*t^2*z^16 - 519184*t^2*z^15 + 6672080*t^2*z^14 - 58024016*t^2*z^13 + 361279024*t^2*z^12 - 1662429760*t^2*z^11 + 5756476352*t^2*z^10 - 15141942304*t^2*z^9 + 30358057424*t^2*z^8 - 46321349344*t^2*z^7 + 53460907680*t^2*z^6 - 46129088032*t^2*z^5 + 29182030480*t^2*z^4 - 13104542560*t^2*z^3 + 3949829088*t^2*z^2 - 716755984*t^2*z + 59409760*t^2 + 192*t*z^19 - 9888*t*z^18 + 235008*t*z^17 - 3418992*t*z^16 + 34056976*t*z^15 - 246191456*t*z^14 + 1335916944*t*z^13 - 5553948912*t*z^12 + 17906113136*t*z^11 - 45056252304*t*z^10 + 88669226048*t*z^9 - 136271281696*t*z^8 + 162740706496*t*z^7 - 149685922800*t*z^6 + 104547073920*t*z^5 - 54243375584*t*z^4 + 20190983104*t*z^3 - 5084564304*t*z^2 + 774512192*t*z - 53869088*t - 32*z^21 + 1808*z^20 - 47488*z^19 + 769872*z^18 - 8626944*z^17 + 70915360*z^16 - 442995888*z^15 + 2150006000*z^14 - 8221053856*z^13 + 24976252112*z^12 - 60552608352*z^11 + 117281385424*z^10 - 181167726864*z^9 + 222220540128*z^8 - 214866932704*z^7 + 161995605328*z^6 - 93729531152*z^5 + 40649506848*z^4 - 12742346064*z^3 + 2718165280*z^2 - 352129888*z + 20852608)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_49 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 49) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_49 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z^2 - 10*t^2*z + 6*t^2 - 6*t*z^2 + 30*t*z - 18*t + 2*z^4 - 20*z^3 + 58*z^2 - 40*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8*z^8 - 320*t^8*z^7 + 2592*t^8*z^6 - 10880*t^8*z^5 + 25264*t^8*z^4 - 32640*t^8*z^3 + 23328*t^8*z^2 - 8640*t^8*z + 1296*t^8 - 176*t^7*z^10 + 4464*t^7*z^9 - 47984*t^7*z^8 + 284448*t^7*z^7 - 1015728*t^7*z^6 + 2252176*t^7*z^5 - 3117136*t^7*z^4 + 2679072*t^7*z^3 - 1387152*t^7*z^2 + 396144*t^7*z - 47952*t^7 + 864*t^6*z^12 - 26496*t^6*z^11 + 354640*t^6*z^10 - 2718544*t^6*z^9 + 13177552*t^6*z^8 - 42165408*t^6*z^7 + 90603152*t^6*z^6 - 131223536*t^6*z^5 + 127521200*t^6*z^4 - 81687072*t^6*z^3 + 33029424*t^6*z^2 - 7633872*t^6*z + 768528*t^6 - 2480*t^5*z^14 + 89072*t^5*z^13 - 1425232*t^5*z^12 + 13394656*t^5*z^11 - 82115424*t^5*z^10 + 345175888*t^5*z^9 - 1019672048*t^5*z^8 + 2139669920*t^5*z^7 - 3197013280*t^5*z^6 + 3388463728*t^5*z^5 - 2517530288*t^5*z^4 + 1278323328*t^5*z^3 - 421800048*t^5*z^2 + 81411264*t^5*z - 6969888*t^5 + 4560*t^4*z^16 - 187488*t^4*z^15 + 3486528*t^4*z^14 - 38773312*t^4*z^13 + 287381328*t^4*z^12 - 1498400848*t^4*z^11 + 5658704848*t^4*z^10 - 15720581728*t^4*z^9 + 32358093888*t^4*z^8 - 49420547056*t^4*z^7 + 55831487504*t^4*z^6 - 46257213536*t^4*z^5 + 27643017552*t^4*z^4 - 11562986160*t^4*z^3 + 3205677168*t^4*z^2 - 528291072*t^4*z + 39124944*t^4 - 5504*t^3*z^18 + 254640*t^3*z^17 - 5390208*t^3*z^16 + 69160288*t^3*z^15 - 600796192*t^3*z^14 + 3739474992*t^3*z^13 - 17221191824*t^3*z^12 + 59788248384*t^3*z^11 - 158129248016*t^3*z^10 + 320180558560*t^3*z^9 - 496759998496*t^3*z^8 + 589016369296*t^3*z^7 - 530285408544*t^3*z^6 + 358243625776*t^3*z^5 - 178053476688*t^3*z^4 + 62996862816*t^3*z^3 - 14983538976*t^3*z^2 + 2143695456*t^3*z - 139194288*t^3 + 4256*t^2*z^20 - 218576*t^2*z^19 + 5183264*t^2*z^18 - 75287968*t^2*z^17 + 749353888*t^2*z^16 - 5418128080*t^2*z^15 + 29446377136*t^2*z^14 - 122832614976*t^2*z^13 + 398337464336*t^2*z^12 - 1011692103776*t^2*z^11 + 2019403720528*t^2*z^10 - 3169393678240*t^2*z^9 + 3902387210176*t^2*z^8 - 3750126111808*t^2*z^7 + 2787971266272*t^2*z^6 - 1581162036000*t^2*z^5 + 669278157552*t^2*z^4 - 204182887536*t^2*z^3 + 42323011920*t^2*z^2 - 5325125328*t^2*z + 306448272*t^2 - 1920*t*z^22 + 108256*t*z^21 - 2839472*t*z^20 + 46004848*t*z^19 - 515645568*t*z^18 + 4244132848*t*z^17 - 26579467312*t*z^16 + 129530664784*t*z^15 - 498364609056*t*z^14 + 1527707751664*t*z^13 - 3751271005760*t*z^12 + 7396765028784*t*z^11 - 11713585706832*t*z^10 + 14867943504720*t*z^9 - 15061896431360*t*z^8 + 12093908197456*t*z^7 - 7616559847424*t*z^6 + 3704212036896*t*z^5 - 1359063097056*t*z^4 + 362785576032*t*z^3 - 66339268272*t*z^2 + 7416534960*t*z - 381622752*t + 384*z^24 - 23552*z^23 + 676192*z^22 - 12076096*z^21 + 150370320*z^20 - 1387047152*z^19 + 9830902320*z^18 - 54816416208*z^17 + 244261248368*z^16 - 878947318048*z^15 + 2571351462256*z^14 - 6139969378368*z^13 + 11987566528128*z^12 - 19133431168864*z^11 + 24919191609536*z^10 - 26385426240448*z^9 + 22584591952160*z^8 - 15498921899568*z^7 + 8428623417216*z^6 - 3572224622640*z^5 + 1151534691648*z^4 - 272048435136*z^3 + 44315214048*z^2 - 4439201760*z + 205752960:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^5 + 224*t^8*z^4 - 1168*t^8*z^3 + 2736*t^8*z^2 - 2784*t^8*z + 1088*t^8 + 176*t^7*z^7 - 3408*t^7*z^6 + 26656*t^7*z^5 - 107296*t^7*z^4 + 235264*t^7*z^3 - 277456*t^7*z^2 + 168784*t^7*z - 43824*t^7 - 864*t^6*z^9 + 21312*t^6*z^8 - 222448*t^6*z^7 + 1276432*t^6*z^6 - 4385408*t^6*z^5 + 9248352*t^6*z^4 - 11909568*t^6*z^3 + 9138960*t^6*z^2 - 3891248*t^6*z + 735216*t^6 + 2480*t^5*z^11 - 74192*t^5*z^10 + 967680*t^5*z^9 - 7215136*t^5*z^8 + 33912016*t^5*z^7 - 104660432*t^5*z^6 + 214934240*t^5*z^5 - 292850304*t^5*z^4 + 260579824*t^5*z^3 - 145799024*t^5*z^2 + 46986720*t^5*z - 6828064*t^5 - 4560*t^4*z^13 + 160128*t^4*z^12 - 2502960*t^4*z^11 + 22950352*t^4*z^10 - 137004288*t^4*z^9 + 559120400*t^4*z^8 - 1596010656*t^4*z^7 + 3211911504*t^4*z^6 - 4547451184*t^4*z^5 + 4480271776*t^4*z^4 - 3000689424*t^4*z^3 + 1304266928*t^4*z^2 - 333697088*t^4*z + 38779568*t^4 + 5504*t^3*z^15 - 221616*t^3*z^14 + 4032992*t^3*z^13 - 43848752*t^3*z^12 + 317317104*t^3*z^11 - 1612295616*t^3*z^10 + 5916983856*t^3*z^9 - 15907550064*t^3*z^8 + 31486732736*t^3*z^7 - 45805427968*t^3*z^6 + 48586216944*t^3*z^5 - 36985195056*t^3*z^4 + 19637725520*t^3*z^3 - 6905080432*t^3*z^2 + 1449171440*t^3*z - 138706496*t^3 - 4256*t^2*z^17 + 193040*t^2*z^16 - 4003744*t^2*z^15 + 50296048*t^2*z^14 - 427365840*t^2*z^13 + 2598449056*t^2*z^12 - 11668557552*t^2*z^11 + 39401658544*t^2*z^10 - 100986276256*t^2*z^9 + 197097595968*t^2*z^8 - 292485104896*t^2*z^7 + 328008792768*t^2*z^6 - 274811333120*t^2*z^5 + 168729044352*t^2*z^4 - 73531541792*t^2*z^3 + 21516230368*t^2*z^2 - 3794022032*t^2*z + 306061712*t^2 + 1920*t*z^19 - 96736*t*z^18 + 2249456*t*z^17 - 32022512*t*z^16 + 312166480*t*z^15 - 2208771952*t*z^14 + 11733980688*t*z^13 - 47770754416*t*z^12 + 150861407168*t*z^11 - 371951555888*t*z^10 + 717483880176*t*z^9 - 1081242561120*t*z^8 + 1266759383344*t*z^7 - 1143690518880*t*z^6 + 784713840240*t*z^5 - 400413178272*t*z^4 + 146821057712*t*z^3 - 36505959024*t*z^2 + 5508876080*t*z - 381466720*t - 384*z^21 + 21248*z^20 - 546784*z^19 + 8688768*z^18 - 95482544*z^17 + 770161264*z^16 - 4723833248*z^15 + 22527127856*z^14 - 84709153728*z^13 + 253332923152*z^12 - 605281026848*z^11 + 1156909447792*z^10 - 1766371783984*z^9 + 2145372199152*z^8 - 2058190046912*z^7 + 1543053179232*z^6 - 889950443056*z^5 + 385763298160*z^4 - 121238233744*z^3 + 26028286320*z^2 - 3410506848*z + 205728704)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_50 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 50) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_50 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z^2 - 10*t^2*z + 6*t^2 + 2*t*z^4 - 22*t*z^3 + 66*t*z^2 - 36*t*z + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t*z + 10*t)*hf
  · have hr : (16*t^8*z^8 - 320*t^8*z^7 + 2592*t^8*z^6 - 10880*t^8*z^5 + 25264*t^8*z^4 - 32640*t^8*z^3 + 23328*t^8*z^2 - 8640*t^8*z + 1296*t^8 - 112*t^7*z^10 + 2800*t^7*z^9 - 29744*t^7*z^8 + 174880*t^7*z^7 - 622448*t^7*z^6 + 1384720*t^7*z^5 - 1937296*t^7*z^4 + 1692960*t^7*z^3 - 894672*t^7*z^2 + 261360*t^7*z - 32400*t^7 + 368*t^6*z^12 - 11024*t^6*z^11 + 144560*t^6*z^10 - 1089824*t^6*z^9 + 5221136*t^6*z^8 - 16616048*t^6*z^7 + 35778512*t^6*z^6 - 52339616*t^6*z^5 + 51716144*t^6*z^4 - 33846672*t^6*z^3 + 14027472*t^6*z^2 - 3329856*t^6*z + 344736*t^6 - 736*t^5*z^14 + 25680*t^5*z^13 - 400240*t^5*z^12 + 3676016*t^5*z^11 - 22113104*t^5*z^10 + 91664896*t^5*z^9 - 268605344*t^5*z^8 + 562775792*t^5*z^7 - 845116048*t^5*z^6 + 905337664*t^5*z^5 - 682725344*t^5*z^4 + 352817328*t^5*z^3 - 118644912*t^5*z^2 + 23343984*t^5*z - 2036016*t^5 + 976*t^4*z^16 - 38848*t^4*z^15 + 700928*t^4*z^14 - 7583408*t^4*z^13 + 54856896*t^4*z^12 - 280208368*t^4*z^11 + 1041222880*t^4*z^10 - 2860061344*t^4*z^9 + 5850250960*t^4*z^8 - 8922468848*t^4*z^7 + 10106470048*t^4*z^6 - 8419502240*t^4*z^5 + 5066889024*t^4*z^4 - 2134768176*t^4*z^3 + 595423008*t^4*z^2 - 98473968*t^4*z + 7290000*t^4 - 880*t^3*z^18 + 39328*t^3*z^17 - 805600*t^3*z^16 + 10023056*t^3*z^15 - 84630992*t^3*z^14 + 513395040*t^3*z^13 - 2311398672*t^3*z^12 + 7871612592*t^3*z^11 - 20494863152*t^3*z^10 + 40996791216*t^3*z^9 - 63039197360*t^3*z^8 + 74264180976*t^3*z^7 - 66525053760*t^3*z^6 + 44728051792*t^3*z^5 - 22100142096*t^3*z^4 + 7753562208*t^3*z^3 - 1821207456*t^3*z^2 + 255826512*t^3*z - 16181856*t^3 + 528*t^2*z^20 - 26160*t^2*z^19 + 599216*t^2*z^18 - 8418992*t^2*z^17 + 81182016*t^2*z^16 - 569669728*t^2*z^15 + 3010567456*t^2*z^14 - 12237295328*t^2*z^13 + 38756124720*t^2*z^12 - 96344094672*t^2*z^11 + 188624272720*t^2*z^10 - 290872698000*t^2*z^9 + 352284365568*t^2*z^8 - 333073871136*t^2*z^7 + 243399124128*t^2*z^6 - 135386072544*t^2*z^5 + 55996208208*t^2*z^4 - 16603434864*t^2*z^3 + 3320863920*t^2*z^2 - 399441456*t^2*z + 21718368*t^2 - 192*t*z^22 + 10432*t*z^21 - 263872*t*z^20 + 4126272*t*z^19 - 44678528*t*z^18 + 355600192*t*z^17 - 2155819456*t*z^16 + 10181886080*t*z^15 - 38010465856*t*z^14 + 113187003840*t*z^13 - 270261741760*t*z^12 + 518610800320*t*z^11 - 799558896256*t*z^10 + 987827344576*t*z^9 - 973062891584*t*z^8 + 758197265536*t*z^7 - 461872576448*t*z^6 + 216262201920*t*z^5 - 75911830848*t*z^4 + 19229313600*t*z^3 - 3302767872*t*z^2 + 342470592*t*z - 16096320*t + 32*z^24 - 1888*z^23 + 52160*z^22 - 896704*z^21 + 10752960*z^20 - 95569024*z^19 + 653014816*z^18 - 3512437664*z^17 + 15107501792*z^16 - 52504374304*z^15 + 148418382336*z^14 - 342512422656*z^13 + 646158638528*z^12 - 995774692096*z^11 + 1250249979616*z^10 - 1273100635232*z^9 + 1044338317088*z^8 - 683698609632*z^7 + 352631235456*z^6 - 140725406592*z^5 + 42341460480*z^4 - 9237934656*z^3 + 1371989664*z^2 - 123381792*z + 5038848:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^5 + 224*t^8*z^4 - 1168*t^8*z^3 + 2736*t^8*z^2 - 2784*t^8*z + 1088*t^8 + 112*t^7*z^7 - 2128*t^7*z^6 + 16416*t^7*z^5 - 65632*t^7*z^4 + 144448*t^7*z^3 - 173456*t^7*z^2 + 108688*t^7*z - 29104*t^7 - 368*t^6*z^9 + 8816*t^6*z^8 - 89824*t^6*z^7 + 506432*t^6*z^6 - 1724608*t^6*z^5 + 3646416*t^6*z^4 - 4770544*t^6*z^3 + 3759664*t^6*z^2 - 1659024*t^6*z + 323664*t^6 + 736*t^5*z^11 - 21264*t^5*z^10 + 268976*t^5*z^9 - 1955104*t^5*z^8 + 9016336*t^5*z^7 - 27522384*t^5*z^6 + 56434256*t^5*z^5 - 77542000*t^5*z^4 + 70170384*t^5*z^3 - 40171104*t^5*z^2 + 13304800*t^5*z - 1962624*t^5 - 976*t^4*z^13 + 32992*t^4*z^12 - 498096*t^4*z^11 + 4428896*t^4*z^10 - 25760048*t^4*z^9 + 103005504*t^4*z^8 - 289960720*t^4*z^7 + 579509456*t^4*z^6 - 820385120*t^4*z^5 + 812650128*t^4*z^4 - 549134224*t^4*z^3 + 241061136*t^4*z^2 - 62200960*t^4*z + 7122512*t^4 + 880*t^3*z^15 - 34048*t^3*z^14 + 596912*t^3*z^13 - 6270464*t^3*z^12 + 43989600*t^3*z^11 - 217508208*t^3*z^10 + 780130960*t^3*z^9 - 2059296192*t^3*z^8 + 4020922992*t^3*z^7 - 5794641344*t^3*z^6 + 6107438144*t^3*z^5 - 4625422400*t^3*z^4 + 2440687296*t^3*z^3 - 849377872*t^3*z^2 + 175015984*t^3*z - 15889648*t^3 - 528*t^2*z^17 + 22992*t^2*z^16 - 458624*t^2*z^15 + 5551760*t^2*z^14 - 45555344*t^2*z^13 + 268120240*t^2*z^12 - 1168517536*t^2*z^11 + 3840033568*t^2*z^10 - 9605215392*t^2*z^9 + 18344116944*t^2*z^8 - 26693460528*t^2*z^7 + 29386134720*t^2*z^6 - 24156137664*t^2*z^5 + 14512911024*t^2*z^4 - 6154834944*t^2*z^3 + 1736370096*t^2*z^2 - 290901888*t^2*z + 21338112*t^2 + 192*t*z^19 - 9280*t*z^18 + 207232*t*z^17 - 2836288*t*z^16 + 26615360*t*z^15 - 181519360*t*z^14 + 930790208*t*z^13 - 3662932672*t*z^12 + 11197399424*t*z^11 - 26757153728*t*z^10 + 50068889600*t*z^9 - 73214294656*t*z^8 + 83171526592*t*z^7 - 72657822144*t*z^6 + 48044031104*t*z^5 - 23472441600*t*z^4 + 8159949184*t*z^3 - 1896267712*t*z^2 + 262037056*t*z - 15803520*t - 32*z^21 + 1696*z^20 - 41824*z^19 + 637248*z^18 - 6718656*z^17 + 52029024*z^16 - 306610144*z^15 + 1405913024*z^14 - 5086943904*z^13 + 14646535616*z^12 - 33698536096*z^11 + 62001584096*z^10 - 91009917856*z^9 + 106008728384*z^8 - 97146435936*z^7 + 69168459840*z^6 - 37586649984*z^5 + 15189974592*z^4 - 4389678144*z^3 + 850814784*z^2 - 98206464*z + 4943808)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_51 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 51) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_51 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^4 - 20*t*z^3 + 56*t*z^2 - 30*t*z - 4*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t*z + 8*t)*hf
  · have hr : (16*t^8 - 48*t^7*z^4 + 544*t^7*z^3 - 1872*t^7*z^2 + 1824*t^7*z - 624*t^7 + 48*t^6*z^8 - 1104*t^6*z^7 + 10304*t^6*z^6 - 49728*t^6*z^5 + 131664*t^6*z^4 - 191360*t^6*z^3 + 153536*t^6*z^2 - 63376*t^6*z + 10608*t^6 - 16*t^5*z^12 + 576*t^5*z^11 - 9200*t^5*z^10 + 85328*t^5*z^9 - 505568*t^5*z^8 + 1987744*t^5*z^7 - 5238832*t^5*z^6 + 9204128*t^5*z^5 - 10632048*t^5*z^4 + 7912272*t^5*z^3 - 3639968*t^5*z^2 + 938400*t^5*z - 103104*t^5 - 16*t^4*z^15 + 784*t^4*z^14 - 16976*t^4*z^13 + 215088*t^4*z^12 - 1776688*t^4*z^11 + 10082064*t^4*z^10 - 40350928*t^4*z^9 + 115248528*t^4*z^8 - 235655280*t^4*z^7 + 344360000*t^4*z^6 - 357557712*t^4*z^5 + 260254992*t^4*z^4 - 129167936*t^4*z^3 + 41446368*t^4*z^2 - 7712064*t^4*z + 627696*t^4 - 16*t^3*z^18 + 848*t^3*z^17 - 20672*t^3*z^16 + 306592*t^3*z^15 - 3085120*t^3*z^14 + 22251136*t^3*z^13 - 118558160*t^3*z^12 + 474494224*t^3*z^11 - 1438124592*t^3*z^10 + 3309149968*t^3*z^9 - 5772371536*t^3*z^8 + 7598664048*t^3*z^7 - 7490721264*t^3*z^6 + 5462447296*t^3*z^5 - 2888416112*t^3*z^4 + 1071125520*t^3*z^3 - 262763280*t^3*z^2 + 38075184*t^3*z - 2450736*t^3 + 64*t^2*z^20 - 3504*t^2*z^19 + 88432*t^2*z^18 - 1363936*t^2*z^17 + 14373552*t^2*z^16 - 109643968*t^2*z^15 + 625980400*t^2*z^14 - 2729317808*t^2*z^13 + 9198711504*t^2*z^12 - 24129264528*t^2*z^11 + 49415866592*t^2*z^10 - 79035045216*t^2*z^9 + 98487173408*t^2*z^8 - 95102613968*t^2*z^7 + 70497605264*t^2*z^6 - 39522314512*t^2*z^5 + 16373601168*t^2*z^4 - 4832972928*t^2*z^3 + 956109744*t^2*z^2 - 112952880*t^2*z + 5983632*t^2 - 80*t*z^22 + 4672*t*z^21 - 126592*t*z^20 + 2112288*t*z^19 - 24295472*t*z^18 + 204354464*t*z^17 - 1301624736*t*z^16 + 6416313520*t*z^15 - 24817572320*t*z^14 + 75959805104*t*z^13 - 184854444032*t*z^12 + 358418020336*t*z^11 - 553638000224*t*z^10 + 679918053776*t*z^9 - 661107889936*t*z^8 + 505441308544*t*z^7 - 300602854608*t*z^6 + 136832905584*t*z^5 - 46516613328*t*z^4 + 11369432160*t*z^3 - 1876749264*t*z^2 + 186184656*t*z - 8328096*t + 32*z^24 - 2000*z^23 + 58384*z^22 - 1057504*z^21 + 13317184*z^20 - 123831632*z^19 + 881511664*z^18 - 4916181808*z^17 + 21807269936*z^16 - 77699741344*z^15 + 223728231600*z^14 - 522296347552*z^13 + 989580434560*z^12 - 1520381017296*z^11 + 1889333523312*z^10 - 1890829821120*z^9 + 1514427071280*z^8 - 962167718928*z^7 + 478942291872*z^6 - 183542225040*z^5 + 52790509728*z^4 - 10964172960*z^3 + 1544010336*z^2 - 131150016*z + 5038848:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7*z - 256*t^7 - 48*t^6*z^5 + 816*t^6*z^4 - 5168*t^6*z^3 + 14592*t^6*z^2 - 17456*t^6*z + 8496*t^6 + 16*t^5*z^9 - 480*t^5*z^8 + 6240*t^5*z^7 - 45472*t^5*z^6 + 201056*t^5*z^5 - 547808*t^5*z^4 + 901232*t^5*z^3 - 856640*t^5*z^2 + 438240*t^5*z - 98400*t^5 + 16*t^4*z^12 - 688*t^4*z^11 + 12768*t^4*z^10 - 135024*t^4*z^9 + 902016*t^4*z^8 - 3982080*t^4*z^7 + 11813344*t^4*z^6 - 23556048*t^4*z^5 + 31270192*t^4*z^4 - 27145264*t^4*z^3 + 14779120*t^4*z^2 - 4583760*t^4*z + 624512*t^4 + 16*t^3*z^15 - 752*t^3*z^14 + 16080*t^3*z^13 - 206336*t^3*z^12 + 1765952*t^3*z^11 - 10607664*t^3*z^10 + 45876080*t^3*z^9 - 144433472*t^3*z^8 + 331535696*t^3*z^7 - 551892352*t^3*z^6 + 658905472*t^3*z^5 - 554233760*t^3*z^4 + 318898992*t^3*z^3 - 118979072*t^3*z^2 + 25812960*t^3*z - 2453408*t^3 - 64*t^2*z^17 + 3120*t^2*z^16 - 69392*t^2*z^15 + 931920*t^2*z^14 - 8431952*t^2*z^13 + 54323264*t^2*z^12 - 256949136*t^2*z^11 + 907574720*t^2*z^10 - 2414194240*t^2*z^9 + 4849276352*t^2*z^8 - 7341662560*t^2*z^7 + 8324493856*t^2*z^6 - 6982621120*t^2*z^5 + 4242755408*t^2*z^4 - 1803473360*t^2*z^3 + 505076192*t^2*z^2 - 83021808*t^2*z + 5987760*t^2 + 80*t*z^19 - 4192*t*z^18 + 101040*t*z^17 - 1485008*t*z^16 + 14876032*t*z^15 - 107572192*t*z^14 + 580326416*t*z^13 - 2381618032*t*z^12 + 7518659856*t*z^11 - 18359429392*t*z^10 + 34722950368*t*z^9 - 50764511312*t*z^8 + 57076751120*t*z^7 - 48912040128*t*z^6 + 31487382256*t*z^5 - 14880063248*t*z^4 + 4973523712*t*z^3 - 1104064816*t*z^2 + 144542624*t*z - 8328624*t - 32*z^21 + 1808*z^20 - 47376*z^19 + 764176*z^18 - 8493440*z^17 + 69002736*z^16 - 424263872*z^15 + 2017091456*z^14 - 7514399104*z^13 + 22103625568*z^12 - 51517391216*z^11 + 95159473312*z^10 - 138933013040*z^9 + 159468181280*z^8 - 142699897120*z^7 + 98356518960*z^6 - 51320290640*z^5 + 19763483168*z^4 - 5403420704*z^3 + 983994336*z^2 - 105957024*z + 5038432)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_52 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 52) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_52 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z^2 - 10*t^2*z + 6*t^2 - 6*t*z^2 + 30*t*z - 18*t + 2*z^4 - 20*z^3 + 58*z^2 - 40*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(8 - 2*z)*hf
  · have hr : (16*t^8*z^8 - 320*t^8*z^7 + 2592*t^8*z^6 - 10880*t^8*z^5 + 25264*t^8*z^4 - 32640*t^8*z^3 + 23328*t^8*z^2 - 8640*t^8*z + 1296*t^8 - 176*t^7*z^10 + 4464*t^7*z^9 - 47984*t^7*z^8 + 284448*t^7*z^7 - 1015728*t^7*z^6 + 2252176*t^7*z^5 - 3117136*t^7*z^4 + 2679072*t^7*z^3 - 1387152*t^7*z^2 + 396144*t^7*z - 47952*t^7 + 864*t^6*z^12 - 26560*t^6*z^11 + 356304*t^6*z^10 - 2736784*t^6*z^9 + 13286992*t^6*z^8 - 42556384*t^6*z^7 + 91453968*t^6*z^6 - 132341680*t^6*z^5 + 128381744*t^6*z^4 - 82037984*t^6*z^3 + 33076656*t^6*z^2 - 7621776*t^6*z + 765072*t^6 - 2480*t^5*z^14 + 89600*t^5*z^13 - 1441792*t^5*z^12 + 13620544*t^5*z^11 - 83871600*t^5*z^10 + 353750320*t^5*z^9 - 1047028928*t^5*z^8 + 2197392800*t^5*z^7 - 3277200784*t^5*z^6 + 3460466320*t^5*z^5 - 2557327904*t^5*z^4 + 1290051360*t^5*z^3 - 422546976*t^5*z^2 + 80922672*t^5*z - 6873984*t^5 + 4560*t^4*z^16 - 189360*t^4*z^15 + 3555216*t^4*z^14 - 39893248*t^4*z^13 + 298070016*t^4*z^12 - 1564636720*t^4*z^11 + 5938352320*t^4*z^10 - 16542918496*t^4*z^9 + 34054251984*t^4*z^8 - 51867107728*t^4*z^7 + 58268868128*t^4*z^6 - 47886803456*t^4*z^5 + 28326427872*t^4*z^4 - 11709515232*t^4*z^3 + 3204357648*t^4*z^2 - 520860960*t^4*z + 38034576*t^4 - 5504*t^3*z^18 + 258304*t^3*z^17 - 5544064*t^3*z^16 + 72076464*t^3*z^15 - 633764736*t^3*z^14 + 3987035808*t^3*z^13 - 18522957840*t^3*z^12 + 64716230208*t^3*z^11 - 171741827376*t^3*z^10 + 347737986784*t^3*z^9 - 537548338816*t^3*z^8 + 632762077904*t^3*z^7 - 563645000896*t^3*z^6 + 375645762016*t^3*z^5 - 183732880176*t^3*z^4 + 63846903056*t^3*z^3 - 14892700512*t^3*z^2 + 2087385264*t^3*z - 132694416*t^3 + 4256*t^2*z^20 - 222752*t^2*z^19 + 5380624*t^2*z^18 - 79548640*t^2*z^17 + 804989792*t^2*z^16 - 5908665168*t^2*z^15 + 32534377920*t^2*z^14 - 137150561856*t^2*z^13 + 448092379664*t^2*z^12 - 1142413378560*t^2*z^11 + 2279779178416*t^2*z^10 - 3561778250496*t^2*z^9 + 4346726410432*t^2*z^8 - 4123188419312*t^2*z^7 + 3014489636400*t^2*z^6 - 1675848497728*t^2*z^5 + 693458467152*t^2*z^4 - 206365125648*t^2*z^3 + 41653916224*t^2*z^2 - 5097090128*t^2*z + 285024720*t^2 - 1920*t*z^22 + 110880*t*z^21 - 2977216*t*z^20 + 49339008*t*z^19 - 564992480*t*z^18 + 4743478224*t*z^17 - 30239684192*t*z^16 + 149624588336*t*z^15 - 582647505456*t*z^14 + 1800966327552*t*z^13 - 4440142244320*t*z^12 + 8749343933312*t*z^11 - 13778196847712*t*z^10 + 17304612683600*t*z^9 - 17263107306112*t*z^8 + 13589762779024*t*z^7 - 8357906976192*t*z^6 + 3955970527984*t*z^5 - 1408592664224*t*z^4 + 364076600384*t*z^3 - 64348879888*t*z^2 + 6944317904*t*z - 344608032*t + 384*z^24 - 24256*z^23 + 716800*z^22 - 13164512*z^21 + 168364384*z^20 - 1592467808*z^19 + 11548952400*z^18 - 65717596912*z^17 + 297888838288*z^16 - 1086282311056*z^15 + 3206433609840*z^14 - 7687447440400*z^13 + 14989865323376*z^12 - 23762834534496*z^11 + 30566459033872*z^10 - 31791993149552*z^9 + 26594723397488*z^8 - 17754734993520*z^7 + 9355166601392*z^6 - 3828599548880*z^5 + 1188449340272*z^4 - 269778426944*z^3 + 42156211904*z^2 - 4046294944*z + 179560576:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^5 + 224*t^8*z^4 - 1168*t^8*z^3 + 2736*t^8*z^2 - 2784*t^8*z + 1088*t^8 + 176*t^7*z^7 - 3408*t^7*z^6 + 26656*t^7*z^5 - 107296*t^7*z^4 + 235264*t^7*z^3 - 277456*t^7*z^2 + 168784*t^7*z - 43824*t^7 - 864*t^6*z^9 + 21376*t^6*z^8 - 223728*t^6*z^7 + 1286672*t^6*z^6 - 4426944*t^6*z^5 + 9337632*t^6*z^4 - 12006784*t^6*z^3 + 9185872*t^6*z^2 - 3894960*t^6*z + 732080*t^6 + 2480*t^5*z^11 - 74720*t^5*z^10 + 981072*t^5*z^9 - 7358032*t^5*z^8 + 34743328*t^5*z^7 - 107519120*t^5*z^6 + 220839536*t^5*z^5 - 300016656*t^5*z^4 + 265384048*t^5*z^3 - 147239216*t^5*z^2 + 46955712*t^5*z - 6736960*t^5 - 4560*t^4*z^13 + 162000*t^4*z^12 - 2560416*t^4*z^11 + 23716192*t^4*z^10 - 142808784*t^4*z^9 + 586642640*t^4*z^8 - 1680736368*t^4*z^7 + 3382478304*t^4*z^6 - 4769057680*t^4*z^5 + 4659633760*t^4*z^4 - 3083298864*t^4*z^3 + 1319783792*t^4*z^2 - 331597040*t^4*z + 37715168*t^4 + 5504*t^3*z^15 - 225280*t^3*z^14 + 4164864*t^3*z^13 - 45955376*t^3*z^12 + 336982880*t^3*z^11 - 1731196784*t^3*z^10 + 6404907360*t^3*z^9 - 17293819248*t^3*z^8 + 34223178304*t^3*z^7 - 49524913360*t^3*z^6 + 51989147888*t^3*z^5 - 38979445472*t^3*z^4 + 20297675264*t^3*z^3 - 6973335184*t^3*z^2 + 1425047280*t^3*z - 132268192*t^3 - 4256*t^2*z^17 + 197216*t^2*z^16 - 4176048*t^2*z^15 + 53502016*t^2*z^14 - 462900240*t^2*z^13 + 2859577600*t^2*z^12 - 13008909104*t^2*z^11 + 44336318992*t^2*z^10 - 114170342592*t^2*z^9 + 222700818944*t^2*z^8 - 328386232800*t^2*z^7 + 363786416384*t^2*z^6 - 299375929184*t^2*z^5 + 179614529488*t^2*z^4 - 76136397168*t^2*z^3 + 21581538096*t^2*z^2 - 3672723248*t^2*z + 284698512*t^2 + 1920*t*z^19 - 99360*t*z^18 + 2371456*t*z^17 - 34611552*t*z^16 + 345366528*t*z^15 - 2495849840*t*z^14 + 13503140960*t*z^13 - 55781126848*t*z^12 + 177949189728*t*z^11 - 440862413984*t*z^10 + 849440684928*t*z^9 - 1270438564096*t*z^8 + 1467499624512*t*z^7 - 1297981431120*t*z^6 + 867282032736*t*z^5 - 428663802496*t*z^4 + 151532566416*t*z^3 - 36174084272*t*z^2 + 5221524016*t*z - 344468512*t - 384*z^21 + 21952*z^20 - 583168*z^19 + 9555360*z^18 - 108094432*z^17 + 895541248*z^16 - 5625677392*z^15 + 27377731888*z^14 - 104598518752*z^13 + 316176861712*z^12 - 759002113920*z^11 + 1447951929568*z^10 - 2190966314656*z^9 + 2618274884800*z^8 - 2454026222224*z^7 + 1785495077552*z^6 - 993346936256*z^5 + 413151766000*z^4 - 124026246560*z^3 + 25336303264*z^2 - 3148521888*z + 179532736)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_53 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 53) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_53 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z^2 - 10*t^2*z + 6*t^2 - 2*t*z^4 + 20*t*z^3 - 66*t*z^2 + 80*t*z - 30*t + 2*z^6 - 30*z^5 + 164*z^4 - 390*z^3 + 382*z^2 - 160*z + 24:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t*z - 8*t - 2*z^3 + 18*z^2 - 46*z + 22)*hf
  · have hr : (16*t^8*z^8 - 320*t^8*z^7 + 2592*t^8*z^6 - 10880*t^8*z^5 + 25264*t^8*z^4 - 32640*t^8*z^3 + 23328*t^8*z^2 - 8640*t^8*z + 1296*t^8 - 240*t^7*z^10 + 6064*t^7*z^9 - 64880*t^7*z^8 + 382368*t^7*z^7 - 1355120*t^7*z^6 + 2975056*t^7*z^5 - 4065360*t^7*z^4 + 3441312*t^7*z^3 - 1751760*t^7*z^2 + 491184*t^7*z - 58320*t^7 + 1616*t^6*z^12 - 49312*t^6*z^11 + 655856*t^6*z^10 - 4986400*t^6*z^9 + 23911296*t^6*z^8 - 75434848*t^6*z^7 + 159143344*t^6*z^6 - 225289952*t^6*z^5 + 213205632*t^6*z^4 - 132661856*t^6*z^3 + 52020720*t^6*z^2 - 11649312*t^6*z + 1135728*t^6 - 6384*t^5*z^14 + 228208*t^5*z^13 - 3628192*t^5*z^12 + 33804704*t^5*z^11 - 204848624*t^5*z^10 + 847949200*t^5*z^9 - 2455185728*t^5*z^8 + 5022730016*t^5*z^7 - 7277112784*t^5*z^6 + 7445283824*t^5*z^5 - 5322734176*t^5*z^4 + 2595670656*t^5*z^3 - 821801376*t^5*z^2 + 152164224*t^5*z - 12501216*t^5 + 16192*t^4*z^16 - 663280*t^4*z^15 + 12265808*t^4*z^14 - 135322064*t^4*z^13 + 991945088*t^4*z^12 - 5095258560*t^4*z^11 + 18866987568*t^4*z^10 - 51107520576*t^4*z^9 + 101950293744*t^4*z^8 - 150005567776*t^4*z^7 + 162428856144*t^4*z^6 - 128505344992*t^4*z^5 + 73158968912*t^4*z^4 - 29121049200*t^4*z^3 + 7681530048*t^4*z^2 - 1205162352*t^4*z + 85066416*t^4 - 27008*t^3*z^18 + 1246800*t^3*z^17 - 26283584*t^3*z^16 + 335017984*t^3*z^15 - 2882167248*t^3*z^14 + 17697476256*t^3*z^13 - 80028637536*t^3*z^12 + 271326632112*t^3*z^11 - 696451904304*t^3*z^10 + 1359647353536*t^3*z^9 - 2021006296096*t^3*z^8 + 2283192696352*t^3*z^7 - 1950217396656*t^3*z^6 + 1246509669440*t^3*z^5 - 585304616400*t^3*z^4 + 195584231040*t^3*z^3 - 43962516432*t^3*z^2 + 5952037248*t^3*z - 366419376*t^3 + 28928*t^2*z^20 - 1485376*t^2*z^19 + 35146768*t^2*z^18 - 508121568*t^2*z^17 + 5018137408*t^2*z^16 - 35865272064*t^2*z^15 + 191800849008*t^2*z^14 - 783075014528*t^2*z^13 + 2470361880048*t^2*z^12 - 6062802343728*t^2*z^11 + 11613328754784*t^2*z^10 - 17375050816816*t^2*z^9 + 20274775481344*t^2*z^8 - 18379671512848*t^2*z^7 + 12848443164912*t^2*z^6 - 6839471931120*t^2*z^5 + 2715813548512*t^2*z^4 - 777656324368*t^2*z^3 + 151504262032*t^2*z^2 - 17953947824*t^2*z + 975664848*t^2 - 18176*t*z^22 + 1027136*t*z^21 - 26946208*t*z^20 + 435552304*t*z^19 - 4855236880*t*z^18 + 39594524800*t*z^17 - 244586547136*t*z^16 + 1169557104208*t*z^15 - 4388874852816*t*z^14 + 13034952632992*t*z^13 - 30790606992896*t*z^12 + 57984182876336*t*z^11 - 87093886907488*t*z^10 + 104214972068208*t*z^9 - 99038334770032*t*z^8 + 74336073067552*t*z^7 - 43670115090608*t*z^6 + 19796000846672*t*z^5 - 6772542491072*t*z^4 + 1688090236064*t*z^3 - 288868152544*t*z^2 + 30306434544*t*z - 1468250784*t + 5120*z^24 - 315648*z^23 + 9089536*z^22 - 162384384*z^21 + 2016206304*z^20 - 18473866304*z^19 + 129477641360*z^18 - 710185034208*z^17 + 3094420491152*z^16 - 10815745039280*z^15 + 30513042302288*z^14 - 69733148073968*z^13 + 129322517812688*z^12 - 194673995843488*z^11 + 237621507237680*z^10 - 234600911914128*z^9 + 186540201251008*z^8 - 118650189704624*z^7 + 59751380979728*z^6 - 23459348014880*z^5 + 7015618850720*z^4 - 1541179271136*z^3 + 234144640576*z^2 - 21953104992*z + 956091136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^5 + 224*t^8*z^4 - 1168*t^8*z^3 + 2736*t^8*z^2 - 2784*t^8*z + 1088*t^8 + 240*t^7*z^7 - 4624*t^7*z^6 + 35936*t^7*z^5 - 143392*t^7*z^4 + 310464*t^7*z^3 - 359376*t^7*z^2 + 213392*t^7*z - 53616*t^7 - 1616*t^6*z^9 + 39616*t^6*z^8 - 410080*t^6*z^7 + 2326224*t^6*z^6 - 7863936*t^6*z^5 + 16210032*t^6*z^4 - 20237248*t^6*z^3 + 14952368*t^6*z^2 - 6095152*t^6*z + 1091856*t^6 + 6384*t^5*z^11 - 189904*t^5*z^10 + 2456848*t^5*z^9 - 18107712*t^5*z^8 + 83728208*t^5*z^7 - 252584544*t^5*z^6 + 502929712*t^5*z^5 - 658500816*t^5*z^4 + 558874784*t^5*z^3 - 296601328*t^5*z^2 + 90251472*t^5*z - 12280400*t^5 - 16192*t^4*z^13 + 566128*t^4*z^12 - 8788080*t^4*z^11 + 79746752*t^4*z^10 - 468958048*t^4*z^9 + 1873988432*t^4*z^8 - 5198519984*t^4*z^7 + 10077500464*t^4*z^6 - 13618702608*t^4*z^5 + 12707329824*t^4*z^4 - 8013863696*t^4*z^3 + 3266811088*t^4*z^2 - 781454080*t^4*z + 84405584*t^4 + 27008*t^3*z^15 - 1084752*t^3*z^14 + 19640032*t^3*z^13 - 211727024*t^3*z^12 + 1512520192*t^3*z^11 - 7544079952*t^3*z^10 + 26989829840*t^3*z^9 - 70154733120*t^3*z^8 + 133030276432*t^3*z^7 - 183702199504*t^3*z^6 + 183486983792*t^3*z^5 - 130729519648*t^3*z^4 + 64703160304*t^3*z^3 - 21156125584*t^3*z^2 + 4122541728*t^3*z - 365192448*t^3 - 28928*t^2*z^17 + 1311808*t^2*z^16 - 27131280*t^2*z^15 + 338745920*t^2*z^14 - 2848693680*t^2*z^13 + 17052249104*t^2*z^12 - 74905140064*t^2*z^11 + 245534234944*t^2*z^10 - 605578520960*t^2*z^9 + 1126754903184*t^2*z^8 - 1579372495936*t^2*z^7 + 1659462804320*t^2*z^6 - 1294381272560*t^2*z^5 + 736697359952*t^2*z^4 - 296889838080*t^2*z^3 + 80264830320*t^2*z^2 - 13078016240*t^2*z + 974237248*t^2 + 18176*t*z^19 - 918080*t*z^18 + 21346848*t*z^17 - 302862640*t*z^16 + 2930408720*t*z^15 - 20476412432*t*z^14 + 106773166304*t*z^13 - 423605635504*t*z^12 + 1292898795840*t*z^11 - 3052758514128*t*z^10 + 5585956293424*t*z^9 - 7911753749312*t*z^8 + 8640824430368*t*z^7 - 7225300446016*t*z^6 + 4570656192784*t*z^5 - 2144809250400*t*z^4 + 722678178272*t*z^3 - 165229332256*t*z^2 + 22966355776*t*z - 1467261856*t - 5120*z^21 + 284928*z^20 - 7354368*z^19 + 116828416*z^18 - 1278179040*z^17 + 10213295616*z^16 - 61690144048*z^15 + 287699512800*z^14 - 1049559398496*z^13 + 3018200940256*z^12 - 6868340155472*z^11 + 12382543041360*z^10 - 17667357846912*z^9 + 19888793399744*z^8 - 17569414563296*z^7 + 12073099688720*z^6 - 6365736902464*z^5 + 2520855282944*z^4 - 724465081024*z^3 + 142544211552*z^2 - 17172893344*z + 955772288)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_54 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 54) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_54 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z^2 - 10*t^2*z + 6*t^2 - 2*t*z^3 + 6*t*z^2 + 14*t*z - 12*t + 2*z^5 - 20*z^4 + 56*z^3 - 26*z^2 - 10*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 2*z^2 + 8*z + 2)*hf
  · have hr : (16*t^8*z^8 - 320*t^8*z^7 + 2592*t^8*z^6 - 10880*t^8*z^5 + 25264*t^8*z^4 - 32640*t^8*z^3 + 23328*t^8*z^2 - 8640*t^8*z + 1296*t^8 - 176*t^7*z^10 + 4400*t^7*z^9 - 46640*t^7*z^8 + 272800*t^7*z^7 - 961840*t^7*z^6 + 2107600*t^7*z^5 - 2885520*t^7*z^4 + 2455200*t^7*z^3 - 1259280*t^7*z^2 + 356400*t^7*z - 42768*t^7 + 864*t^6*z^12 - 25904*t^6*z^11 + 339152*t^6*z^10 - 2544624*t^6*z^9 + 12080832*t^6*z^8 - 37889968*t^6*z^7 + 79867888*t^6*z^6 - 113562256*t^6*z^5 + 108399744*t^6*z^4 - 68222672*t^6*z^3 + 27102096*t^6*z^2 - 6152976*t^6*z + 608256*t^6 - 2480*t^5*z^14 + 86672*t^5*z^13 - 1350160*t^5*z^12 + 12360192*t^5*z^11 - 73849840*t^5*z^10 + 302714224*t^5*z^9 - 872454272*t^5*z^8 + 1786905728*t^5*z^7 - 2606618224*t^5*z^6 + 2697136016*t^5*z^5 - 1955692768*t^5*z^4 + 968559648*t^5*z^3 - 311436576*t^5*z^2 + 58510080*t^5*z - 4869072*t^5 + 4560*t^4*z^16 - 181952*t^4*z^15 + 3285232*t^4*z^14 - 35489024*t^4*z^13 + 255618496*t^4*z^12 - 1295667984*t^4*z^11 + 4758106672*t^4*z^10 - 12855707952*t^4*z^9 + 25733187376*t^4*z^8 - 38208782416*t^4*z^7 + 41938476624*t^4*z^6 - 33727949392*t^4*z^5 + 19540782944*t^4*z^4 - 7912520112*t^4*z^3 + 2119658496*t^4*z^2 - 336815568*t^4*z + 23991120*t^4 - 5504*t^3*z^18 + 246800*t^3*z^17 - 5065568*t^3*z^16 + 63045024*t^3*z^15 - 531413424*t^3*z^14 + 3210168752*t^3*z^13 - 14349544000*t^3*z^12 + 48352693152*t^3*z^11 - 124086558480*t^3*z^10 + 243656465456*t^3*z^9 - 366296047664*t^3*z^8 + 420349236800*t^3*z^7 - 365719328416*t^3*z^6 + 238340466128*t^3*z^5 - 114037234512*t^3*z^4 + 38748490800*t^3*z^3 - 8826911712*t^3*z^2 + 1205789328*t^3*z - 74491488*t^3 + 4256*t^2*z^20 - 211776*t^2*z^19 + 4867616*t^2*z^18 - 68551264*t^2*z^17 + 661691984*t^2*z^16 - 4640352640*t^2*z^15 + 24460037024*t^2*z^14 - 98940246624*t^2*z^13 + 310997069968*t^2*z^12 - 765057881664*t^2*z^11 + 1477654927200*t^2*z^10 - 2241055061536*t^2*z^9 + 2662033132400*t^2*z^8 - 2463074043600*t^2*z^7 + 1759044760560*t^2*z^6 - 955873946912*t^2*z^5 + 386557618384*t^2*z^4 - 112310434912*t^2*z^3 + 22091728720*t^2*z^2 - 2627400272*t^2*z + 142298400*t^2 - 1920*t*z^22 + 104928*t*z^21 - 2668448*t*z^20 + 41929248*t*z^19 - 455854496*t*z^18 + 3639498320*t*z^17 - 22106800832*t*z^16 + 104459195600*t*z^15 - 389479257088*t*z^14 + 1156094841824*t*z^13 - 2745805971600*t*z^12 + 5229395186512*t*z^11 - 7984540766896*t*z^10 + 9750940553216*t*z^9 - 9481002790448*t*z^8 + 7286679173152*t*z^7 - 4379168932016*t*z^6 + 2025606346784*t*z^5 - 704296006256*t*z^4 + 177467931888*t*z^3 - 30503653552*t*z^2 + 3190801728*t*z - 152861184*t + 384*z^24 - 22848*z^23 + 636544*z^22 - 11033312*z^21 + 133352704*z^20 - 1193924384*z^19 + 8211917632*z^18 - 44418907072*z^17 + 191895238272*z^16 - 668900723312*z^15 + 1893482431888*z^14 - 4368576018304*z^13 + 8226239747152*z^12 - 12636477341632*z^11 + 15799328748416*z^10 - 16013874095456*z^9 + 13079324749088*z^8 - 8534890799744*z^7 + 4396843440048*z^6 - 1758195348256*z^5 + 532479128528*z^4 - 117657378480*z^3 + 17840828480*z^2 - 1655314080*z + 70685440:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^5 + 224*t^8*z^4 - 1168*t^8*z^3 + 2736*t^8*z^2 - 2784*t^8*z + 1088*t^8 + 176*t^7*z^7 - 3344*t^7*z^6 + 25696*t^7*z^5 - 101728*t^7*z^4 + 219648*t^7*z^3 - 255376*t^7*z^2 + 153296*t^7*z - 38896*t^7 - 864*t^6*z^9 + 20720*t^6*z^8 - 210512*t^6*z^7 + 1177088*t^6*z^6 - 3945024*t^6*z^5 + 8123872*t^6*z^4 - 10222448*t^6*z^3 + 7663184*t^6*z^2 - 3184528*t^6*z + 577136*t^6 + 2480*t^5*z^11 - 71792*t^5*z^10 + 907008*t^5*z^9 - 6556704*t^5*z^8 + 29902784*t^5*z^7 - 89606992*t^5*z^6 + 178741696*t^5*z^5 - 236517808*t^5*z^4 + 204195904*t^5*z^3 - 110629856*t^5*z^2 + 34416304*t^5*z - 4716640*t^5 - 4560*t^4*z^13 + 154592*t^4*z^12 - 2334880*t^4*z^11 + 20702224*t^4*z^10 - 119576160*t^4*z^9 + 472365024*t^4*z^8 - 1305333504*t^4*z^7 + 2542305648*t^4*z^6 - 3480320944*t^4*z^5 + 3309995008*t^4*z^4 - 2134596208*t^4*z^3 + 890076160*t^4*z^2 - 217349936*t^4*z + 23443488*t^4 + 5504*t^3*z^15 - 213776*t^3*z^14 + 3755392*t^3*z^13 - 39438288*t^3*z^12 + 275792960*t^3*z^11 - 1354464160*t^3*z^10 + 4804355952*t^3*z^9 - 12478443680*t^3*z^8 + 23839652480*t^3*z^7 - 33421976224*t^3*z^6 + 34087484240*t^3*z^5 - 24874797760*t^3*z^4 + 12611144432*t^3*z^3 - 4212126496*t^3*z^2 + 833955616*t^3*z - 72980192*t^3 - 4256*t^2*z^17 + 186240*t^2*z^16 - 3728896*t^2*z^15 + 45242432*t^2*z^14 - 371406672*t^2*z^13 + 2181971552*t^2*z^12 - 9465931920*t^2*z^11 + 30863390672*t^2*z^10 - 76305094784*t^2*z^9 + 143444427680*t^2*z^8 - 204599496528*t^2*z^7 + 219930849184*t^2*z^6 - 176006126976*t^2*z^5 + 102783539296*t^2*z^4 - 42382040720*t^2*z^3 + 11657879136*t^2*z^2 - 1916600672*t^2*z + 139394480*t^2 + 1920*t*z^19 - 93408*t*z^18 + 2098400*t*z^17 - 28869888*t*z^16 + 272049760*t*z^15 - 1860751920*t*z^14 + 9553170624*t*z^13 - 37564362496*t*z^12 + 114466477072*t*z^11 - 271920996288*t*z^10 + 504383246016*t*z^9 - 729024251904*t*z^8 + 816558029104*t*z^7 - 702087873056*t*z^6 + 456661154688*t*z^5 - 219714850640*t*z^4 + 75486181680*t*z^3 - 17453848816*t*z^2 + 2427154320*t*z - 149580208*t - 384*z^21 + 20544*z^20 - 511360*z^19 + 7862048*z^18 - 83603072*z^17 + 652484352*z^16 - 3871134112*z^15 + 17846077568*z^14 - 64810617952*z^13 + 186935493648*z^12 - 429970302672*z^11 + 789266116080*z^10 - 1153856043664*z^9 + 1337040196576*z^8 - 1218541234560*z^7 + 863569661552*z^6 - 468160410400*z^5 + 189538795024*z^4 - 55238956352*z^3 + 10907224624*z^2 - 1302204000*z + 69075008)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_55 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 55) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_55 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^4 - 20*t*z^3 + 52*t*z^2 - 10*t*z - 12*t + 2*z^2 - 10*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t*z + 8*t)*hf
  · have hr : (16*t^8 - 48*t^7*z^4 + 544*t^7*z^3 - 2000*t^7*z^2 + 2464*t^7*z - 880*t^7 + 48*t^6*z^8 - 1104*t^6*z^7 + 10656*t^6*z^6 - 55456*t^6*z^5 + 166192*t^6*z^4 - 284384*t^6*z^3 + 262560*t^6*z^2 - 119792*t^6*z + 21040*t^6 - 16*t^5*z^12 + 576*t^5*z^11 - 9536*t^5*z^10 + 94640*t^5*z^9 - 615632*t^5*z^8 + 2708944*t^5*z^7 - 8094192*t^5*z^6 + 16214624*t^5*z^5 - 21275904*t^5*z^4 + 17742160*t^5*z^3 - 8957744*t^5*z^2 + 2477520*t^5*z - 286240*t^5 - 16*t^4*z^15 + 912*t^4*z^14 - 22032*t^4*z^13 + 305568*t^4*z^12 - 2743536*t^4*z^11 + 16924160*t^4*z^10 - 73967776*t^4*z^9 + 232256528*t^4*z^8 - 525357776*t^4*z^7 + 851380304*t^4*z^6 - 976751440*t^4*z^5 + 778599200*t^4*z^4 - 418408624*t^4*z^3 + 143681664*t^4*z^2 - 28322560*t^4*z + 2426224*t^4 - 32*t^3*z^18 + 1680*t^3*z^17 - 41328*t^3*z^16 + 629232*t^3*z^15 - 6597952*t^3*z^14 + 50210448*t^3*z^13 - 285100768*t^3*z^12 + 1225137040*t^3*z^11 - 4007511584*t^3*z^10 + 9980057840*t^3*z^9 - 18848741968*t^3*z^8 + 26812870000*t^3*z^7 - 28452560528*t^3*z^6 + 22217254912*t^3*z^5 - 12505907568*t^3*z^4 + 4909386816*t^3*z^3 - 1269487824*t^3*z^2 + 193525568*t^3*z - 13123984*t^3 + 224*t^2*z^20 - 12288*t^2*z^19 + 312496*t^2*z^18 - 4886000*t^2*z^17 + 52524208*t^2*z^16 - 411321136*t^2*z^15 + 2426041152*t^2*z^14 - 10993468688*t^2*z^13 + 38713261808*t^2*z^12 - 106550127136*t^2*z^11 + 229561520032*t^2*z^10 - 386554663248*t^2*z^9 + 506619063264*t^2*z^8 - 513332632992*t^2*z^7 + 398164492368*t^2*z^6 - 232976479824*t^2*z^5 + 100575913808*t^2*z^4 - 30928809728*t^2*z^3 + 6385705888*t^2*z^2 - 790657776*t^2*z + 44223568*t^2 - 512*t*z^22 + 30112*t*z^21 - 822976*t*z^20 + 13872576*t*z^19 - 161440960*t*z^18 + 1375907840*t*z^17 - 8891965552*t*z^16 + 44528317104*t*z^15 - 175148431936*t*z^14 + 545625538128*t*z^13 - 1352294531328*t*z^12 + 2671316671472*t*z^11 - 4204636455408*t*z^10 + 5261878560432*t*z^9 - 5213797171376*t*z^8 + 4063137763424*t*z^7 - 2465085297600*t*z^6 + 1146586754128*t*z^5 - 399488348352*t*z^4 + 100549406368*t*z^3 - 17211204304*t*z^2 + 1787632048*t*z - 84783328*t + 384*z^24 - 24256*z^23 + 715392*z^22 - 13083744*z^21 + 166214176*z^20 - 1557211840*z^19 + 11150463536*z^18 - 62424432544*z^17 + 277288087056*z^16 - 986612125968*z^15 + 2828419258128*z^14 - 6554366700400*z^13 + 12293455194704*z^12 - 18658727730688*z^11 + 22881219906384*z^10 - 22602842712048*z^9 + 17899609834208*z^8 - 11281205893584*z^7 + 5597716437872*z^6 - 2152255131072*z^5 + 626137505536*z^4 - 132847937728*z^3 + 19342072992*z^2 - 1723391936*z + 70685440:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7*z - 256*t^7 - 48*t^6*z^5 + 816*t^6*z^4 - 5520*t^6*z^3 + 18208*t^6*z^2 - 28528*t^6*z + 16656*t^6 + 16*t^5*z^9 - 480*t^5*z^8 + 6576*t^5*z^7 - 52768*t^5*z^6 + 265664*t^5*z^5 - 844544*t^5*z^4 + 1645840*t^5*z^3 - 1851200*t^5*z^2 + 1094960*t^5*z - 270560*t^5 + 16*t^4*z^12 - 816*t^4*z^11 + 17056*t^4*z^10 - 199136*t^4*z^9 + 1462624*t^4*z^8 - 7135680*t^4*z^7 + 23641440*t^4*z^6 - 53266864*t^4*z^5 + 80413712*t^4*z^4 - 78922272*t^4*z^3 + 47882384*t^4*z^2 - 16279824*t^4*z + 2395488*t^4 + 32*t^3*z^15 - 1488*t^3*z^14 + 32240*t^3*z^13 - 428320*t^3*z^12 + 3865344*t^3*z^11 - 24844544*t^3*z^10 + 116278464*t^3*z^9 - 399378192*t^3*z^8 + 1005005568*t^3*z^7 - 1836855008*t^3*z^6 + 2403205888*t^3*z^5 - 2204354064*t^3*z^4 + 1373551696*t^3*z^3 - 550968528*t^3*z^2 + 127983856*t^3*z - 13089344*t^3 - 224*t^2*z^17 + 10944*t^2*z^16 - 245712*t^2*z^15 + 3356784*t^2*z^14 - 31144000*t^2*z^13 + 207427504*t^2*z^12 - 1022399344*t^2*z^11 + 3790791104*t^2*z^10 - 10649090960*t^2*z^9 + 22679226512*t^2*z^8 - 36449915056*t^2*z^7 + 43809949392*t^2*z^6 - 38830565120*t^2*z^5 + 24849580256*t^2*z^4 - 11104235840*t^2*z^3 + 3272598384*t^2*z^2 - 569564048*t^2*z + 44197680*t^2 + 512*t*z^19 - 27040*t*z^18 + 658176*t*z^17 - 9787808*t*z^16 + 99396192*t*z^15 - 729933472*t*z^14 + 4005595952*t*z^13 - 16745677840*t*z^12 + 53916451664*t*z^11 - 134392842992*t*z^10 + 259609537216*t*z^9 - 387778781552*t*z^8 + 445523237024*t*z^7 - 390235693312*t*z^6 + 256988044832*t*z^5 - 124507790848*t*z^4 + 42862635040*t*z^3 - 9883944816*t*z^2 + 1363713408*t*z - 84766800*t - 384*z^21 + 21952*z^20 - 581760*z^19 + 9483040*z^18 - 106385184*z^17 + 870903776*z^16 - 5383631920*z^15 + 25661736960*z^14 - 95528601920*z^13 + 279748197728*z^12 - 646625325200*z^11 + 1180345158640*z^10 - 1698509419136*z^9 + 1919320097472*z^8 - 1692407067232*z^7 + 1153290402160*z^6 - 598511987616*z^5 + 231274889856*z^4 - 64216758496*z^3 + 12068143200*z^2 - 1369964000*z + 70679232)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_56 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 56) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_56 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z^2 - 10*t^2*z + 6*t^2 + 2*t*z^4 - 22*t*z^3 + 66*t*z^2 - 36*t*z + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t*z + 10*t)*hf
  · have hr : (16*t^8*z^8 - 320*t^8*z^7 + 2592*t^8*z^6 - 10880*t^8*z^5 + 25264*t^8*z^4 - 32640*t^8*z^3 + 23328*t^8*z^2 - 8640*t^8*z + 1296*t^8 - 112*t^7*z^10 + 2800*t^7*z^9 - 29744*t^7*z^8 + 174880*t^7*z^7 - 622448*t^7*z^6 + 1384720*t^7*z^5 - 1937296*t^7*z^4 + 1692960*t^7*z^3 - 894672*t^7*z^2 + 261360*t^7*z - 32400*t^7 + 368*t^6*z^12 - 11024*t^6*z^11 + 144496*t^6*z^10 - 1088416*t^6*z^9 + 5208400*t^6*z^8 - 16554864*t^6*z^7 + 35609488*t^6*z^6 - 52065312*t^6*z^5 + 51456752*t^6*z^4 - 33713552*t^6*z^3 + 14000400*t^6*z^2 - 3333312*t^6*z + 346464*t^6 - 736*t^5*z^14 + 25680*t^5*z^13 - 399904*t^5*z^12 + 3666944*t^5*z^11 - 22008080*t^5*z^10 + 90982960*t^5*z^9 - 265873088*t^5*z^8 + 555751616*t^5*z^7 - 833384560*t^5*z^6 + 892686544*t^5*z^5 - 674225216*t^5*z^4 + 349628832*t^5*z^3 - 118237104*t^5*z^2 + 23454144*t^5*z - 2068416*t^5 + 976*t^4*z^16 - 38848*t^4*z^15 + 700112*t^4*z^14 - 7557344*t^4*z^13 + 54490464*t^4*z^12 - 277223680*t^4*z^11 + 1025608192*t^4*z^10 - 2805014416*t^4*z^9 + 5716527664*t^4*z^8 - 8696967968*t^4*z^7 + 9843779008*t^4*z^6 - 8212621424*t^4*z^5 + 4962619392*t^4*z^4 - 2105900064*t^4*z^3 + 593768400*t^4*z^2 - 99705456*t^4*z + 7534512*t^4 - 880*t^3*z^18 + 39328*t^3*z^17 - 804448*t^3*z^16 + 9980592*t^3*z^15 - 83929472*t^3*z^14 + 506534064*t^3*z^13 - 2267175104*t^3*z^12 + 7673553936*t^3*z^11 - 19861119888*t^3*z^10 + 39527782352*t^3*z^9 - 60561588720*t^3*z^8 + 71235751664*t^3*z^7 - 63881149952*t^3*z^6 + 43132601712*t^3*z^5 - 21482104752*t^3*z^4 + 7630403744*t^3*z^3 - 1824056112*t^3*z^2 + 262412928*t^3*z - 17130096*t^3 + 528*t^2*z^20 - 26160*t^2*z^19 + 598224*t^2*z^18 - 8377584*t^2*z^17 + 80397040*t^2*z^16 - 560722928*t^2*z^15 + 2942138256*t^2*z^14 - 11865910432*t^2*z^13 + 37280458320*t^2*z^12 - 91974884848*t^2*z^11 + 178897471376*t^2*z^10 - 274550240848*t^2*z^9 + 331709010624*t^2*z^8 - 313798417088*t^2*z^7 + 230269817952*t^2*z^6 - 129160699520*t^2*z^5 + 54135747936*t^2*z^4 - 16359811104*t^2*z^3 + 3357407104*t^2*z^2 - 417660368*t^2*z + 23707488*t^2 - 192*t*z^22 + 10432*t*z^21 - 263376*t*z^20 + 4103168*t*z^19 - 44184848*t*z^18 + 349184608*t*z^17 - 2099127536*t*z^16 + 9820981872*t*z^15 - 36298963600*t*z^14 + 107017808752*t*z^13 - 253157911936*t*z^12 + 481916340832*t*z^11 - 738554655232*t*z^10 + 909475910144*t*z^9 - 895963317264*t*z^8 + 700984916480*t*z^7 - 430766802544*t*z^6 + 204552646144*t*z^5 - 73261336592*t*z^4 + 19066772112*t*z^3 - 3391349584*t*z^2 + 367466576*t*z - 18234048*t + 32*z^24 - 1888*z^23 + 52048*z^22 - 890960*z^21 + 10616752*z^20 - 93586816*z^19 + 633196160*z^18 - 3367993392*z^17 + 14312696384*z^16 - 49129309632*z^15 + 137204299680*z^14 - 313116451968*z^13 + 585120338720*z^12 - 895337060800*z^11 + 1119680694096*z^10 - 1139937854352*z^9 + 939103315376*z^8 - 620578696640*z^7 + 324930120640*z^6 - 132474371504*z^5 + 41007119520*z^4 - 9276027616*z^3 + 1440599808*z^2 - 136760512*z + 5958400:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^5 + 224*t^8*z^4 - 1168*t^8*z^3 + 2736*t^8*z^2 - 2784*t^8*z + 1088*t^8 + 112*t^7*z^7 - 2128*t^7*z^6 + 16416*t^7*z^5 - 65632*t^7*z^4 + 144448*t^7*z^3 - 173456*t^7*z^2 + 108688*t^7*z - 29104*t^7 - 368*t^6*z^9 + 8816*t^6*z^8 - 89760*t^6*z^7 + 505408*t^6*z^6 - 1718336*t^6*z^5 + 3628048*t^6*z^4 - 4744112*t^6*z^3 + 3742064*t^6*z^2 - 1655760*t^6*z + 324560*t^6 + 736*t^5*z^11 - 21264*t^5*z^10 + 268640*t^5*z^9 - 1948048*t^5*z^8 + 8955328*t^5*z^7 - 27242112*t^5*z^6 + 55695728*t^5*z^5 - 76411360*t^5*z^4 + 69195648*t^5*z^3 - 39760128*t^5*z^2 + 13274848*t^5*z - 1983456*t^5 - 976*t^4*z^13 + 32992*t^4*z^12 - 497280*t^4*z^11 + 4407728*t^4*z^10 - 25524704*t^4*z^9 + 101539536*t^4*z^8 - 284339728*t^4*z^7 + 565753664*t^4*z^6 - 798767504*t^4*z^5 + 791254896*t^4*z^4 - 536658448*t^4*z^3 + 237628752*t^4*z^2 - 62299744*t^4*z + 7299392*t^4 + 880*t^3*z^15 - 34048*t^3*z^14 + 595760*t^3*z^13 - 6234912*t^3*z^12 + 43507152*t^3*z^11 - 213720832*t^3*z^10 + 761079440*t^3*z^9 - 1994965984*t^3*z^8 + 3872205952*t^3*z^7 - 5558637280*t^3*z^6 + 5853769296*t^3*z^5 - 4447743536*t^3*z^4 + 2367204976*t^3*z^3 - 836884880*t^3*z^2 + 177027056*t^3*z - 16612032*t^3 - 528*t^2*z^17 + 22992*t^2*z^16 - 457632*t^2*z^15 + 5516304*t^2*z^14 - 44988064*t^2*z^13 + 262755392*t^2*z^12 - 1135149280*t^2*z^11 + 3696249728*t^2*z^10 - 9164458160*t^2*z^9 + 17371737968*t^2*z^8 - 25148503040*t^2*z^7 + 27636074608*t^2*z^6 - 22778309808*t^2*z^5 + 13799682160*t^2*z^4 - 5944101344*t^2*z^3 + 1719370848*t^2*z^2 - 299333968*t^2*z + 22851712*t^2 + 192*t*z^19 - 9280*t*z^18 + 206736*t*z^17 - 2816160*t*z^16 + 26244928*t*z^15 - 177427504*t*z^14 + 900521712*t*z^13 - 3504469152*t*z^12 + 10592112624*t*z^11 - 25042265536*t*z^10 + 46439286448*t*z^9 - 67477181840*t*z^8 + 76452866416*t*z^7 - 66933516000*t*z^6 + 44620707344*t*z^5 - 22140226000*t*z^4 + 7888393824*t*z^3 - 1900445856*t*z^2 + 276466336*t*z - 17350992*t - 32*z^21 + 1696*z^20 - 41712*z^19 + 632176*z^18 - 6613440*z^17 + 50703584*z^16 - 295275280*z^15 + 1336210352*z^14 - 4768354288*z^13 + 13542856864*z^12 - 30769176704*z^11 + 56018753136*z^10 - 81619079520*z^9 + 94759641296*z^8 - 87008695584*z^7 + 62468394848*z^6 - 34489827072*z^5 + 14289064384*z^4 - 4278204128*z^3 + 869997744*z^2 - 107048032*z + 5546576)*hf
  · have hr : (16*t^8*z^8 - 320*t^8*z^7 + 2592*t^8*z^6 - 10880*t^8*z^5 + 25264*t^8*z^4 - 32640*t^8*z^3 + 23328*t^8*z^2 - 8640*t^8*z + 1296*t^8 - 112*t^7*z^10 + 2800*t^7*z^9 - 29744*t^7*z^8 + 174880*t^7*z^7 - 622448*t^7*z^6 + 1384720*t^7*z^5 - 1937296*t^7*z^4 + 1692960*t^7*z^3 - 894672*t^7*z^2 + 261360*t^7*z - 32400*t^7 + 368*t^6*z^12 - 11024*t^6*z^11 + 144560*t^6*z^10 - 1089824*t^6*z^9 + 5221136*t^6*z^8 - 16616048*t^6*z^7 + 35778512*t^6*z^6 - 52339616*t^6*z^5 + 51716144*t^6*z^4 - 33846672*t^6*z^3 + 14027472*t^6*z^2 - 3329856*t^6*z + 344736*t^6 - 736*t^5*z^14 + 25680*t^5*z^13 - 400240*t^5*z^12 + 3676016*t^5*z^11 - 22113104*t^5*z^10 + 91664896*t^5*z^9 - 268605344*t^5*z^8 + 562775792*t^5*z^7 - 845116048*t^5*z^6 + 905337664*t^5*z^5 - 682725344*t^5*z^4 + 352817328*t^5*z^3 - 118644912*t^5*z^2 + 23343984*t^5*z - 2036016*t^5 + 976*t^4*z^16 - 38848*t^4*z^15 + 700928*t^4*z^14 - 7583408*t^4*z^13 + 54856896*t^4*z^12 - 280208368*t^4*z^11 + 1041222880*t^4*z^10 - 2860061344*t^4*z^9 + 5850250960*t^4*z^8 - 8922468848*t^4*z^7 + 10106470048*t^4*z^6 - 8419502240*t^4*z^5 + 5066889024*t^4*z^4 - 2134768176*t^4*z^3 + 595423008*t^4*z^2 - 98473968*t^4*z + 7290000*t^4 - 880*t^3*z^18 + 39328*t^3*z^17 - 805600*t^3*z^16 + 10023056*t^3*z^15 - 84630992*t^3*z^14 + 513395040*t^3*z^13 - 2311398672*t^3*z^12 + 7871612592*t^3*z^11 - 20494863152*t^3*z^10 + 40996791216*t^3*z^9 - 63039197360*t^3*z^8 + 74264180976*t^3*z^7 - 66525053760*t^3*z^6 + 44728051792*t^3*z^5 - 22100142096*t^3*z^4 + 7753562208*t^3*z^3 - 1821207456*t^3*z^2 + 255826512*t^3*z - 16181856*t^3 + 528*t^2*z^20 - 26160*t^2*z^19 + 599216*t^2*z^18 - 8418992*t^2*z^17 + 81182016*t^2*z^16 - 569669728*t^2*z^15 + 3010567456*t^2*z^14 - 12237295328*t^2*z^13 + 38756124720*t^2*z^12 - 96344094672*t^2*z^11 + 188624272720*t^2*z^10 - 290872698000*t^2*z^9 + 352284365568*t^2*z^8 - 333073871136*t^2*z^7 + 243399124128*t^2*z^6 - 135386072544*t^2*z^5 + 55996208208*t^2*z^4 - 16603434864*t^2*z^3 + 3320863920*t^2*z^2 - 399441456*t^2*z + 21718368*t^2 - 192*t*z^22 + 10432*t*z^21 - 263872*t*z^20 + 4126272*t*z^19 - 44678528*t*z^18 + 355600192*t*z^17 - 2155819456*t*z^16 + 10181886080*t*z^15 - 38010465856*t*z^14 + 113187003840*t*z^13 - 270261741760*t*z^12 + 518610800320*t*z^11 - 799558896256*t*z^10 + 987827344576*t*z^9 - 973062891584*t*z^8 + 758197265536*t*z^7 - 461872576448*t*z^6 + 216262201920*t*z^5 - 75911830848*t*z^4 + 19229313600*t*z^3 - 3302767872*t*z^2 + 342470592*t*z - 16096320*t + 32*z^24 - 1888*z^23 + 52160*z^22 - 896704*z^21 + 10752960*z^20 - 95569024*z^19 + 653014816*z^18 - 3512437664*z^17 + 15107501792*z^16 - 52504374304*z^15 + 148418382336*z^14 - 342512422656*z^13 + 646158638528*z^12 - 995774692096*z^11 + 1250249979616*z^10 - 1273100635232*z^9 + 1044338317088*z^8 - 683698609632*z^7 + 352631235456*z^6 - 140725406592*z^5 + 42341460480*z^4 - 9237934656*z^3 + 1371989664*z^2 - 123381792*z + 5038848:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^5 + 224*t^8*z^4 - 1168*t^8*z^3 + 2736*t^8*z^2 - 2784*t^8*z + 1088*t^8 + 112*t^7*z^7 - 2128*t^7*z^6 + 16416*t^7*z^5 - 65632*t^7*z^4 + 144448*t^7*z^3 - 173456*t^7*z^2 + 108688*t^7*z - 29104*t^7 - 368*t^6*z^9 + 8816*t^6*z^8 - 89824*t^6*z^7 + 506432*t^6*z^6 - 1724608*t^6*z^5 + 3646416*t^6*z^4 - 4770544*t^6*z^3 + 3759664*t^6*z^2 - 1659024*t^6*z + 323664*t^6 + 736*t^5*z^11 - 21264*t^5*z^10 + 268976*t^5*z^9 - 1955104*t^5*z^8 + 9016336*t^5*z^7 - 27522384*t^5*z^6 + 56434256*t^5*z^5 - 77542000*t^5*z^4 + 70170384*t^5*z^3 - 40171104*t^5*z^2 + 13304800*t^5*z - 1962624*t^5 - 976*t^4*z^13 + 32992*t^4*z^12 - 498096*t^4*z^11 + 4428896*t^4*z^10 - 25760048*t^4*z^9 + 103005504*t^4*z^8 - 289960720*t^4*z^7 + 579509456*t^4*z^6 - 820385120*t^4*z^5 + 812650128*t^4*z^4 - 549134224*t^4*z^3 + 241061136*t^4*z^2 - 62200960*t^4*z + 7122512*t^4 + 880*t^3*z^15 - 34048*t^3*z^14 + 596912*t^3*z^13 - 6270464*t^3*z^12 + 43989600*t^3*z^11 - 217508208*t^3*z^10 + 780130960*t^3*z^9 - 2059296192*t^3*z^8 + 4020922992*t^3*z^7 - 5794641344*t^3*z^6 + 6107438144*t^3*z^5 - 4625422400*t^3*z^4 + 2440687296*t^3*z^3 - 849377872*t^3*z^2 + 175015984*t^3*z - 15889648*t^3 - 528*t^2*z^17 + 22992*t^2*z^16 - 458624*t^2*z^15 + 5551760*t^2*z^14 - 45555344*t^2*z^13 + 268120240*t^2*z^12 - 1168517536*t^2*z^11 + 3840033568*t^2*z^10 - 9605215392*t^2*z^9 + 18344116944*t^2*z^8 - 26693460528*t^2*z^7 + 29386134720*t^2*z^6 - 24156137664*t^2*z^5 + 14512911024*t^2*z^4 - 6154834944*t^2*z^3 + 1736370096*t^2*z^2 - 290901888*t^2*z + 21338112*t^2 + 192*t*z^19 - 9280*t*z^18 + 207232*t*z^17 - 2836288*t*z^16 + 26615360*t*z^15 - 181519360*t*z^14 + 930790208*t*z^13 - 3662932672*t*z^12 + 11197399424*t*z^11 - 26757153728*t*z^10 + 50068889600*t*z^9 - 73214294656*t*z^8 + 83171526592*t*z^7 - 72657822144*t*z^6 + 48044031104*t*z^5 - 23472441600*t*z^4 + 8159949184*t*z^3 - 1896267712*t*z^2 + 262037056*t*z - 15803520*t - 32*z^21 + 1696*z^20 - 41824*z^19 + 637248*z^18 - 6718656*z^17 + 52029024*z^16 - 306610144*z^15 + 1405913024*z^14 - 5086943904*z^13 + 14646535616*z^12 - 33698536096*z^11 + 62001584096*z^10 - 91009917856*z^9 + 106008728384*z^8 - 97146435936*z^7 + 69168459840*z^6 - 37586649984*z^5 + 15189974592*z^4 - 4389678144*z^3 + 850814784*z^2 - 98206464*z + 4943808)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_57 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 57) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_57 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z^2 - 10*t^2*z + 6*t^2 - 2*t*z^3 + 6*t*z^2 + 14*t*z - 12*t + 2*z^5 - 20*z^4 + 56*z^3 - 26*z^2 - 10*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 2*z^2 + 8*z + 2)*hf
  · have hr : (16*t^8*z^8 - 320*t^8*z^7 + 2592*t^8*z^6 - 10880*t^8*z^5 + 25264*t^8*z^4 - 32640*t^8*z^3 + 23328*t^8*z^2 - 8640*t^8*z + 1296*t^8 - 176*t^7*z^10 + 4400*t^7*z^9 - 46640*t^7*z^8 + 272800*t^7*z^7 - 961840*t^7*z^6 + 2107600*t^7*z^5 - 2885520*t^7*z^4 + 2455200*t^7*z^3 - 1259280*t^7*z^2 + 356400*t^7*z - 42768*t^7 + 864*t^6*z^12 - 25840*t^6*z^11 + 337424*t^6*z^10 - 2524976*t^6*z^9 + 11958656*t^6*z^8 - 37437808*t^6*z^7 + 78848048*t^6*z^6 - 112169808*t^6*z^5 + 107279808*t^6*z^4 - 67738640*t^6*z^3 + 27027792*t^6*z^2 - 6168528*t^6*z + 613440*t^6 - 2480*t^5*z^14 + 86144*t^5*z^13 - 1333264*t^5*z^12 + 12125232*t^5*z^11 - 71988640*t^5*z^10 + 293457856*t^5*z^9 - 842365136*t^5*z^8 + 1722158672*t^5*z^7 - 2514699232*t^5*z^6 + 2612482304*t^5*z^5 - 1907395024*t^5*z^4 + 953643120*t^5*z^3 - 310281840*t^5*z^2 + 59108832*t^5*z - 4997376*t^5 + 4560*t^4*z^16 - 180080*t^4*z^15 + 3216112*t^4*z^14 - 34355696*t^4*z^13 + 244745584*t^4*z^12 - 1227945024*t^4*z^11 + 4470609952*t^4*z^10 - 12004825056*t^4*z^9 + 23963787136*t^4*z^8 - 35629194400*t^4*z^7 + 39332359968*t^4*z^6 - 31953275008*t^4*z^5 + 18777608912*t^4*z^4 - 7741719984*t^4*z^3 + 2119088400*t^4*z^2 - 345223152*t^4*z + 25294896*t^4 - 5504*t^3*z^18 + 243136*t^3*z^17 - 4912464*t^3*z^16 + 60158992*t^3*z^15 - 498975520*t^3*z^14 + 2968012704*t^3*z^13 - 13083080624*t^3*z^12 + 43579548192*t^3*z^11 - 110938165968*t^3*z^10 + 217049149872*t^3*z^9 - 326810002928*t^3*z^8 + 377739439680*t^3*z^7 - 332897819872*t^3*z^6 + 220965663776*t^3*z^5 - 108241502496*t^3*z^4 + 37839954624*t^3*z^3 - 8910152496*t^3*z^2 + 1263903264*t^3*z - 81454896*t^3 + 4256*t^2*z^20 - 207600*t^2*z^19 + 4673056*t^2*z^18 - 64413008*t^2*z^17 + 608469104*t^2*z^16 - 4178161536*t^2*z^15 + 21593081168*t^2*z^14 - 85829241296*t^2*z^13 + 265988634832*t^2*z^12 - 647973764928*t^2*z^11 + 1246060125760*t^2*z^10 - 1893249703104*t^2*z^9 + 2268033995120*t^2*z^8 - 2130839063488*t^2*z^7 + 1555599072336*t^2*z^6 - 869696083248*t^2*z^5 + 364075219792*t^2*z^4 - 110140635712*t^2*z^3 + 22686042784*t^2*z^2 - 2840953280*t^2*z + 162914304*t^2 - 1920*t*z^22 + 102304*t*z^21 - 2533776*t*z^20 + 38744048*t*z^19 - 409806784*t*z^18 + 3184360416*t*z^17 - 18846777536*t*z^16 + 86954622752*t*z^15 - 317557157264*t*z^14 + 927172902336*t*z^13 - 2177614352528*t*z^12 + 4127135380160*t*z^11 - 6315583914944*t*z^10 + 7788878735104*t*z^9 - 7707939569424*t*z^8 + 6076347486048*t*z^7 - 3774084057296*t*z^6 + 1817281695520*t*z^5 - 662310920928*t*z^4 + 176085090912*t*z^3 - 32136494800*t*z^2 + 3591397200*t*z - 184931136*t + 384*z^24 - 22144*z^23 + 597152*z^22 - 10009760*z^21 + 116954208*z^20 - 1012510368*z^19 + 6740982992*z^18 - 35362313248*z^17 + 148596414448*z^16 - 505855817536*z^15 + 1405660118960*z^14 - 3203400713680*z^13 + 6001204442560*z^12 - 9244346652960*z^11 + 11689069925776*z^10 - 12087157222864*z^9 + 10160250073024*z^8 - 6882294760016*z^7 + 3710854157744*z^6 - 1565306863072*z^5 + 503785786736*z^4 - 119125131056*z^3 + 19458594144*z^2 - 1957190976*z + 91157248:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^5 + 224*t^8*z^4 - 1168*t^8*z^3 + 2736*t^8*z^2 - 2784*t^8*z + 1088*t^8 + 176*t^7*z^7 - 3344*t^7*z^6 + 25696*t^7*z^5 - 101728*t^7*z^4 + 219648*t^7*z^3 - 255376*t^7*z^2 + 153296*t^7*z - 38896*t^7 - 864*t^6*z^9 + 20656*t^6*z^8 - 209168*t^6*z^7 + 1165824*t^6*z^6 - 3897216*t^6*z^5 + 8016224*t^6*z^4 - 10098800*t^6*z^3 + 7598672*t^6*z^2 - 3177552*t^6*z + 581168*t^6 + 2480*t^5*z^11 - 71264*t^5*z^10 + 893280*t^5*z^9 - 6406752*t^5*z^8 + 29010464*t^5*z^7 - 86468032*t^5*z^6 + 172097872*t^5*z^5 - 228220816*t^5*z^4 + 198416944*t^5*z^3 - 108778688*t^5*z^2 + 34417360*t^5*z - 4828576*t^5 - 4560*t^4*z^13 + 152720*t^4*z^12 - 2276992*t^4*z^11 + 19925584*t^4*z^10 - 113654400*t^4*z^9 + 444113712*t^4*z^8 - 1217730096*t^4*z^7 + 2364221520*t^4*z^6 - 3245693824*t^4*z^5 + 3116193760*t^4*z^4 - 2042506768*t^4*z^3 + 871571776*t^4*z^2 - 219450656*t^4*z + 24650400*t^4 + 5504*t^3*z^15 - 210112*t^3*z^14 + 3624272*t^3*z^13 - 37357296*t^3*z^12 + 256500272*t^3*z^11 - 1238600320*t^3*z^10 + 4331620048*t^3*z^9 - 11140326032*t^3*z^8 + 21199509216*t^3*z^7 - 29818844368*t^3*z^6 + 30759064608*t^3*z^5 - 22891320976*t^3*z^4 + 11935726608*t^3*z^3 - 4135634640*t^3*z^2 + 857740640*t^3*z - 79610976*t^3 - 4256*t^2*z^17 + 182064*t^2*z^16 - 3559392*t^2*z^15 + 42142080*t^2*z^14 - 337637600*t^2*z^13 + 1938066144*t^2*z^12 - 8234354224*t^2*z^11 + 26395147632*t^2*z^10 - 64507911776*t^2*z^9 + 120716201888*t^2*z^8 - 172828207920*t^2*z^7 + 188191534368*t^2*z^6 - 154027547424*t^2*z^5 + 92887899184*t^2*z^4 - 39942405744*t^2*z^3 + 11574605440*t^2*z^2 - 2027659248*t^2*z + 159247280*t^2 + 1920*t*z^19 - 90784*t*z^18 + 1979472*t*z^17 - 26411376*t*z^16 + 241350384*t*z^15 - 1602221760*t*z^14 + 8000283680*t*z^13 - 30700461488*t*z^12 + 91750748176*t*z^11 - 215165822160*t*z^10 + 397165217200*t*z^9 - 576564217984*t*z^8 + 655206698880*t*z^7 - 577652234704*t*z^6 + 389428448816*t*z^5 - 196308920752*t*z^4 + 71436054000*t*z^3 - 17692318944*t*z^2 + 2667816512*t*z - 180543120*t - 384*z^21 + 19840*z^20 - 476192*z^19 + 7053024*z^18 - 72235264*z^17 + 543357472*z^16 - 3112608816*z^15 + 13897637728*z^14 - 49104186528*z^13 + 138629900912*z^12 - 314462143120*z^11 + 574374163872*z^10 - 844018842816*z^9 + 993900633584*z^8 - 931197746320*z^7 + 686448734208*z^6 - 391668302592*z^5 + 168843527104*z^4 - 53002747952*z^3 + 11404437248*z^2 - 1501896384*z + 88818560)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_58 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 58) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_58 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2*z^2 - 10*t^2*z + 6*t^2 + 2*t*z^4 - 24*t*z^3 + 78*t*z^2 - 52*t*z + 6*t + 2*z^4 - 14*z^3 + 28*z^2 - 22*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t*z + 12*t - 2*z + 2)*hf
  · have hr : (16*t^8*z^8 - 320*t^8*z^7 + 2592*t^8*z^6 - 10880*t^8*z^5 + 25264*t^8*z^4 - 32640*t^8*z^3 + 23328*t^8*z^2 - 8640*t^8*z + 1296*t^8 - 112*t^7*z^10 + 2736*t^7*z^9 - 28400*t^7*z^8 + 163232*t^7*z^7 - 568560*t^7*z^6 + 1240144*t^7*z^5 - 1705680*t^7*z^4 + 1469088*t^7*z^3 - 766800*t^7*z^2 + 221616*t^7*z - 27216*t^7 + 368*t^6*z^12 - 10624*t^6*z^11 + 134256*t^6*z^10 - 975744*t^6*z^9 + 4510656*t^6*z^8 - 13874496*t^6*z^7 + 28945904*t^6*z^6 - 41147648*t^6*z^5 + 39615552*t^6*z^4 - 25315328*t^6*z^3 + 10258416*t^6*z^2 - 2382912*t^6*z + 241488*t^6 - 736*t^5*z^14 + 24528*t^5*z^13 - 365104*t^5*z^12 + 3203344*t^5*z^11 - 18420384*t^5*z^10 + 73082080*t^5*z^9 - 205347824*t^5*z^8 + 413548304*t^5*z^7 - 598507360*t^5*z^6 + 619362656*t^5*z^5 - 451939792*t^5*z^4 + 226163472*t^5*z^3 - 73636128*t^5*z^2 + 14011920*t^5*z - 1179360*t^5 + 976*t^4*z^16 - 36880*t^4*z^15 + 631584*t^4*z^14 - 6486144*t^4*z^13 + 44555696*t^4*z^12 - 216314256*t^4*z^11 + 765045440*t^4*z^10 - 2003950128*t^4*z^9 + 3917784032*t^4*z^8 - 5724158416*t^4*z^7 + 6223384800*t^4*z^6 - 4982283184*t^4*z^5 + 2881941584*t^4*z^4 - 1165986048*t^4*z^3 + 311610912*t^4*z^2 - 49197744*t^4*z + 3457296*t^4 - 880*t^3*z^18 + 37184*t^3*z^17 - 719920*t^3*z^16 + 8464944*t^3*z^15 - 67559232*t^3*z^14 + 387584048*t^3*z^13 - 1651799776*t^3*z^12 + 5332317808*t^3*z^11 - 13183790960*t^3*z^10 + 25093831424*t^3*z^9 - 36788885344*t^3*z^8 + 41388209824*t^3*z^7 - 35437199360*t^3*z^6 + 22770525200*t^3*z^5 - 10737498912*t^3*z^4 + 3584887440*t^3*z^3 - 797586336*t^3*z^2 + 105392880*t^3*z - 6209136*t^3 + 528*t^2*z^20 - 24672*t^2*z^19 + 532736*t^2*z^18 - 7053664*t^2*z^17 + 64090912*t^2*z^16 - 423851824*t^2*z^15 + 2112054592*t^2*z^14 - 8101679136*t^2*z^13 + 24243053936*t^2*z^12 - 57028312752*t^2*z^11 + 105833979744*t^2*z^10 - 154962658992*t^2*z^9 + 178448641520*t^2*z^8 - 160537073008*t^2*z^7 + 111599701056*t^2*z^6 - 58960521200*t^2*z^5 + 23090219392*t^2*z^4 - 6449620192*t^2*z^3 + 1206049216*t^2*z^2 - 134169872*t^2*z + 6645648*t^2 - 192*t*z^22 + 9824*t*z^21 - 233856*t*z^20 + 3439632*t*z^19 - 35017712*t*z^18 + 262008464*t*z^17 - 1493399184*t*z^16 + 6634111328*t*z^15 - 23311755328*t*z^14 + 65411269968*t*z^13 - 147368802816*t*z^12 + 267219220544*t*z^11 - 389851467568*t*z^10 + 456291034896*t*z^9 - 426044660512*t*z^8 + 314564847216*t*z^7 - 181300663568*t*z^6 + 80067516208*t*z^5 - 26372804448*t*z^4 + 6220636624*t*z^3 - 983949280*t*z^2 + 92511888*t*z - 3857760*t + 32*z^24 - 1776*z^23 + 46112*z^22 - 744384*z^21 + 8376208*z^20 - 69822704*z^19 + 447368896*z^18 - 2256609680*z^17 + 9106341840*z^16 - 29717410096*z^15 + 78972730064*z^14 - 171577531776*z^13 + 305198565440*z^12 - 444097317808*z^11 + 527033045376*z^10 - 507447041568*z^9 + 393378975088*z^8 - 242943899344*z^7 + 117818228368*z^6 - 43983230384*z^5 + 12287009520*z^4 - 2462595152*z^3 + 330955552*z^2 - 26360448*z + 924160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^5 + 224*t^8*z^4 - 1168*t^8*z^3 + 2736*t^8*z^2 - 2784*t^8*z + 1088*t^8 + 112*t^7*z^7 - 2064*t^7*z^6 + 15456*t^7*z^5 - 60064*t^7*z^4 + 128832*t^7*z^3 - 151376*t^7*z^2 + 93200*t^7*z - 24176*t^7 - 368*t^6*z^9 + 8416*t^6*z^8 - 81920*t^6*z^7 + 441776*t^6*z^6 - 1441984*t^6*z^5 + 2931792*t^6*z^4 - 3703456*t^6*z^3 + 2825968*t^6*z^2 - 1210672*t^6*z + 218000*t^6 + 736*t^5*z^11 - 20112*t^5*z^10 + 240752*t^5*z^9 - 1657536*t^5*z^8 + 7251296*t^5*z^7 - 21045872*t^5*z^6 + 41158576*t^5*z^5 - 54116192*t^5*z^4 + 46971456*t^5*z^3 - 25794384*t^5*z^2 + 8200016*t^5*z - 1020000*t^5 - 976*t^4*z^13 + 31024*t^4*z^12 - 440560*t^4*z^11 + 3686688*t^4*z^10 - 20201744*t^4*z^9 + 76229792*t^4*z^8 - 202971280*t^4*z^7 + 384771744*t^4*z^6 - 518067376*t^4*z^5 + 488924160*t^4*z^4 - 314731216*t^4*z^3 + 131207712*t^4*z^2 - 32115072*t^4*z + 2525840*t^4 + 880*t^3*z^15 - 31904*t^3*z^14 + 524096*t^3*z^13 - 5159968*t^3*z^12 + 33947040*t^3*z^11 - 157577872*t^3*z^10 + 531437376*t^3*z^9 - 1321857152*t^3*z^8 + 2437883296*t^3*z^7 - 3325808512*t^3*z^6 + 3322760640*t^3*z^5 - 2384720128*t^3*z^4 + 1189266880*t^3*z^3 - 388562640*t^3*z^2 + 75068544*t^3*z - 2396096*t^3 - 528*t^2*z^17 + 21504*t^2*z^16 - 401072*t^2*z^15 + 4539184*t^2*z^14 - 34828944*t^2*z^13 + 191781168*t^2*z^12 - 782683680*t^2*z^11 + 2411842272*t^2*z^10 - 5666800736*t^2*z^9 + 10185613296*t^2*z^8 - 13974454016*t^2*z^7 + 14521067680*t^2*z^6 - 11264352064*t^2*z^5 + 6371168208*t^2*z^4 - 2529863808*t^2*z^3 + 661145248*t^2*z^2 - 102860656*t^2*z - 3133792*t^2 + 192*t*z^19 - 8672*t*z^18 + 180864*t*z^17 - 2310896*t*z^16 + 20239344*t*z^15 - 128837056*t*z^14 + 616869232*t*z^13 - 2268471312*t*z^12 + 6487744240*t*z^11 - 14525578736*t*z^10 + 25508137888*t*z^9 - 35054755296*t*z^8 + 37456667616*t*z^7 - 30769114832*t*z^6 + 19091878144*t*z^5 - 8711336576*t*z^4 + 2804138560*t*z^3 - 594123824*t*z^2 + 76032128*t*z + 10313824*t - 32*z^21 + 1584*z^20 - 36448*z^19 + 517744*z^18 - 5085920*z^17 + 36682016*z^16 - 201329456*z^15 + 860136944*z^14 - 2902190880*z^13 + 7802250640*z^12 - 16788134880*z^11 + 28935278416*z^10 - 39843969904*z^9 + 43568971424*z^8 - 37464088896*z^7 + 24973681168*z^6 - 12647472176*z^5 + 4726571552*z^4 - 1247757008*z^3 + 216358400*z^2 - 23502528*z - 7969024)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_59 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 59) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_59 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^4 - 20*t*z^3 + 56*t*z^2 - 34*t*z - 2*z^3 + 14*z^2 - 16*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t*z + 8*t + 2)*hf
  · have hr : (16*t^8 - 48*t^7*z^4 + 544*t^7*z^3 - 1872*t^7*z^2 + 1696*t^7*z - 496*t^7 + 48*t^6*z^8 - 1104*t^6*z^7 + 10304*t^6*z^6 - 49376*t^6*z^5 + 127344*t^6*z^4 - 173856*t^6*z^3 + 127520*t^6*z^2 - 47024*t^6*z + 6736*t^6 - 16*t^5*z^12 + 576*t^5*z^11 - 9200*t^5*z^10 + 84992*t^5*z^9 - 497600*t^5*z^8 + 1909984*t^5*z^7 - 4837936*t^5*z^6 + 8029760*t^5*z^5 - 8634384*t^5*z^4 + 5895904*t^5*z^3 - 2447840*t^5*z^2 + 558144*t^5*z - 52672*t^5 - 16*t^4*z^15 + 784*t^4*z^14 - 16848*t^4*z^13 + 210544*t^4*z^12 - 1705088*t^4*z^11 + 9424944*t^4*z^10 - 36472144*t^4*z^9 + 99869424*t^4*z^8 - 193944400*t^4*z^7 + 266526912*t^4*z^6 - 257683552*t^4*z^5 + 172872336*t^4*z^4 - 78187840*t^4*z^3 + 22545184*t^4*z^2 - 3702112*t^4*z + 259792*t^4 - 16*t^3*z^18 + 832*t^3*z^17 - 19904*t^3*z^16 + 289328*t^3*z^15 - 2845808*t^3*z^14 + 19983968*t^3*z^13 - 103156224*t^3*z^12 + 397671920*t^3*z^11 - 1153761328*t^3*z^10 + 2525348240*t^3*z^9 - 4164857280*t^3*z^8 + 5153131440*t^3*z^7 - 4745553632*t^3*z^6 + 3210247952*t^3*z^5 - 1561420208*t^3*z^4 + 527040736*t^3*z^3 - 116128592*t^3*z^2 + 14858384*t^3*z - 826480*t^3 + 64*t^2*z^20 - 3392*t^2*z^19 + 82784*t^2*z^18 - 1232960*t^2*z^17 + 12523664*t^2*z^16 - 91873440*t^2*z^15 + 503130992*t^2*z^14 - 2098217216*t^2*z^13 + 6743523536*t^2*z^12 - 16816194880*t^2*z^11 + 32639167296*t^2*z^10 - 49322605792*t^2*z^9 + 57884135456*t^2*z^8 - 52448524720*t^2*z^7 + 36316614112*t^2*z^6 - 18905469984*t^2*z^5 + 7215615536*t^2*z^4 - 1941710048*t^2*z^3 + 345449296*t^2*z^2 - 36060048*t^2*z + 1650256*t^2 - 80*t*z^22 + 4464*t*z^21 - 115392*t*z^20 + 1833888*t*z^19 - 20058432*t*z^18 + 160191600*t*z^17 - 967439280*t*z^16 + 4516563840*t*z^15 - 16531207056*t*z^14 + 47856305008*t*z^13 - 110131656976*t*z^12 + 201919955488*t*z^11 - 294884239968*t*z^10 + 342177282480*t*z^9 - 313922558624*t*z^8 + 225879713568*t*z^7 - 125930714928*t*z^6 + 53425624048*t*z^5 - 16790876672*t*z^4 + 3752296960*t*z^3 - 557887184*t*z^2 + 48857776*t*z - 1878112*t + 32*z^24 - 1888*z^23 + 51936*z^22 - 884992*z^21 + 10469232*z^20 - 91340304*z^19 + 609584320*z^18 - 3186106512*z^17 + 13248097936*z^16 - 44284088656*z^15 + 119795165328*z^14 - 263243606160*z^13 + 470520880064*z^12 - 683495346656*z^11 + 804555553104*z^10 - 763543157552*z^9 + 579847161840*z^8 - 348706327008*z^7 + 163695325344*z^6 - 58801148368*z^5 + 15709681104*z^4 - 2992149728*z^3 + 379605056*z^2 - 28340096*z + 924160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7*z - 256*t^7 - 48*t^6*z^5 + 816*t^6*z^4 - 5168*t^6*z^3 + 14240*t^6*z^2 - 15248*t^6*z + 6000*t^6 + 16*t^5*z^9 - 480*t^5*z^8 + 6240*t^5*z^7 - 45136*t^5*z^6 + 195104*t^5*z^5 - 507440*t^5*z^4 + 772640*t^5*z^3 - 661616*t^5*z^2 + 294048*t^5*z - 50896*t^5 + 16*t^4*z^12 - 688*t^4*z^11 + 12640*t^4*z^10 - 131248*t^4*z^9 + 853712*t^4*z^8 - 3633792*t^4*z^7 + 10269584*t^4*z^6 - 19229248*t^4*z^5 + 23587200*t^4*z^4 - 18587888*t^4*z^3 + 8990976*t^4*z^2 - 2399840*t^4*z + 246032*t^4 + 16*t^3*z^15 - 736*t^3*z^14 + 15408*t^3*z^13 - 193184*t^3*z^12 + 1608928*t^3*z^11 - 9349072*t^3*z^10 + 38823968*t^3*z^9 - 116373824*t^3*z^8 + 252049472*t^3*z^7 - 392358320*t^3*z^6 + 434086176*t^3*z^5 - 334773312*t^3*z^4 + 174124560*t^3*z^3 - 57547856*t^3*z^2 + 10736960*t^3*z - 755136*t^3 - 64*t^2*z^17 + 3008*t^2*z^16 - 64416*t^2*z^15 + 831360*t^2*z^14 - 7210416*t^2*z^13 + 44389728*t^2*z^12 - 199909184*t^2*z^11 + 669603056*t^2*z^10 - 1681969552*t^2*z^9 + 3176453104*t^2*z^8 - 4500997856*t^2*z^7 + 4752383584*t^2*z^6 - 3688391568*t^2*z^5 + 2055259536*t^2*z^4 - 790715472*t^2*z^3 + 196487904*t^2*z^2 - 27851216*t^2*z + 1447760*t^2 + 80*t*z^19 - 3984*t*z^18 + 91088*t*z^17 - 1267360*t*z^16 + 11994848*t*z^15 - 81794624*t*z^14 + 415429936*t*z^13 - 1603016256*t*z^12 + 4754165216*t*z^11 - 10900802496*t*z^10 + 19352999664*t*z^9 - 26543779808*t*z^8 + 27955760304*t*z^7 - 22370821952*t*z^6 + 13375045584*t*z^5 - 5819570000*t*z^4 + 1767245056*t*z^3 - 349258128*t*z^2 + 39532624*t*z - 1565520*t - 32*z^21 + 1696*z^20 - 41600*z^19 + 626880*z^18 - 6498256*z^17 + 49174768*z^16 - 281417552*z^15 + 1245229104*z^14 - 4320460784*z^13 + 11853760880*z^12 - 25825067024*z^11 + 44703938832*z^10 - 61318151072*z^9 + 66241679040*z^8 - 55810784672*z^7 + 36151903248*z^6 - 17640139952*z^5 + 6295186384*z^4 - 1571604032*z^3 + 255452304*z^2 - 23760736*z + 719760)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_60 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 60) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_60 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^4 - 20*t*z^3 + 56*t*z^2 - 30*t*z - 4*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t*z + 8*t)*hf
  · have hr : (16*t^8 - 48*t^7*z^4 + 544*t^7*z^3 - 1872*t^7*z^2 + 1824*t^7*z - 624*t^7 + 48*t^6*z^8 - 1104*t^6*z^7 + 10304*t^6*z^6 - 49728*t^6*z^5 + 131664*t^6*z^4 - 191360*t^6*z^3 + 153536*t^6*z^2 - 63376*t^6*z + 10608*t^6 - 16*t^5*z^12 + 576*t^5*z^11 - 9200*t^5*z^10 + 85328*t^5*z^9 - 505568*t^5*z^8 + 1987744*t^5*z^7 - 5238832*t^5*z^6 + 9204128*t^5*z^5 - 10632048*t^5*z^4 + 7912272*t^5*z^3 - 3639968*t^5*z^2 + 938400*t^5*z - 103104*t^5 - 16*t^4*z^15 + 784*t^4*z^14 - 16976*t^4*z^13 + 215088*t^4*z^12 - 1776688*t^4*z^11 + 10082064*t^4*z^10 - 40350928*t^4*z^9 + 115248528*t^4*z^8 - 235655280*t^4*z^7 + 344360000*t^4*z^6 - 357557712*t^4*z^5 + 260254992*t^4*z^4 - 129167936*t^4*z^3 + 41446368*t^4*z^2 - 7712064*t^4*z + 627696*t^4 - 16*t^3*z^18 + 848*t^3*z^17 - 20672*t^3*z^16 + 306592*t^3*z^15 - 3085120*t^3*z^14 + 22251136*t^3*z^13 - 118558160*t^3*z^12 + 474494224*t^3*z^11 - 1438124592*t^3*z^10 + 3309149968*t^3*z^9 - 5772371536*t^3*z^8 + 7598664048*t^3*z^7 - 7490721264*t^3*z^6 + 5462447296*t^3*z^5 - 2888416112*t^3*z^4 + 1071125520*t^3*z^3 - 262763280*t^3*z^2 + 38075184*t^3*z - 2450736*t^3 + 64*t^2*z^20 - 3504*t^2*z^19 + 88432*t^2*z^18 - 1363936*t^2*z^17 + 14373552*t^2*z^16 - 109643968*t^2*z^15 + 625980400*t^2*z^14 - 2729317808*t^2*z^13 + 9198711504*t^2*z^12 - 24129264528*t^2*z^11 + 49415866592*t^2*z^10 - 79035045216*t^2*z^9 + 98487173408*t^2*z^8 - 95102613968*t^2*z^7 + 70497605264*t^2*z^6 - 39522314512*t^2*z^5 + 16373601168*t^2*z^4 - 4832972928*t^2*z^3 + 956109744*t^2*z^2 - 112952880*t^2*z + 5983632*t^2 - 80*t*z^22 + 4672*t*z^21 - 126592*t*z^20 + 2112288*t*z^19 - 24295472*t*z^18 + 204354464*t*z^17 - 1301624736*t*z^16 + 6416313520*t*z^15 - 24817572320*t*z^14 + 75959805104*t*z^13 - 184854444032*t*z^12 + 358418020336*t*z^11 - 553638000224*t*z^10 + 679918053776*t*z^9 - 661107889936*t*z^8 + 505441308544*t*z^7 - 300602854608*t*z^6 + 136832905584*t*z^5 - 46516613328*t*z^4 + 11369432160*t*z^3 - 1876749264*t*z^2 + 186184656*t*z - 8328096*t + 32*z^24 - 2000*z^23 + 58384*z^22 - 1057504*z^21 + 13317184*z^20 - 123831632*z^19 + 881511664*z^18 - 4916181808*z^17 + 21807269936*z^16 - 77699741344*z^15 + 223728231600*z^14 - 522296347552*z^13 + 989580434560*z^12 - 1520381017296*z^11 + 1889333523312*z^10 - 1890829821120*z^9 + 1514427071280*z^8 - 962167718928*z^7 + 478942291872*z^6 - 183542225040*z^5 + 52790509728*z^4 - 10964172960*z^3 + 1544010336*z^2 - 131150016*z + 5038848:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7*z - 256*t^7 - 48*t^6*z^5 + 816*t^6*z^4 - 5168*t^6*z^3 + 14592*t^6*z^2 - 17456*t^6*z + 8496*t^6 + 16*t^5*z^9 - 480*t^5*z^8 + 6240*t^5*z^7 - 45472*t^5*z^6 + 201056*t^5*z^5 - 547808*t^5*z^4 + 901232*t^5*z^3 - 856640*t^5*z^2 + 438240*t^5*z - 98400*t^5 + 16*t^4*z^12 - 688*t^4*z^11 + 12768*t^4*z^10 - 135024*t^4*z^9 + 902016*t^4*z^8 - 3982080*t^4*z^7 + 11813344*t^4*z^6 - 23556048*t^4*z^5 + 31270192*t^4*z^4 - 27145264*t^4*z^3 + 14779120*t^4*z^2 - 4583760*t^4*z + 624512*t^4 + 16*t^3*z^15 - 752*t^3*z^14 + 16080*t^3*z^13 - 206336*t^3*z^12 + 1765952*t^3*z^11 - 10607664*t^3*z^10 + 45876080*t^3*z^9 - 144433472*t^3*z^8 + 331535696*t^3*z^7 - 551892352*t^3*z^6 + 658905472*t^3*z^5 - 554233760*t^3*z^4 + 318898992*t^3*z^3 - 118979072*t^3*z^2 + 25812960*t^3*z - 2453408*t^3 - 64*t^2*z^17 + 3120*t^2*z^16 - 69392*t^2*z^15 + 931920*t^2*z^14 - 8431952*t^2*z^13 + 54323264*t^2*z^12 - 256949136*t^2*z^11 + 907574720*t^2*z^10 - 2414194240*t^2*z^9 + 4849276352*t^2*z^8 - 7341662560*t^2*z^7 + 8324493856*t^2*z^6 - 6982621120*t^2*z^5 + 4242755408*t^2*z^4 - 1803473360*t^2*z^3 + 505076192*t^2*z^2 - 83021808*t^2*z + 5987760*t^2 + 80*t*z^19 - 4192*t*z^18 + 101040*t*z^17 - 1485008*t*z^16 + 14876032*t*z^15 - 107572192*t*z^14 + 580326416*t*z^13 - 2381618032*t*z^12 + 7518659856*t*z^11 - 18359429392*t*z^10 + 34722950368*t*z^9 - 50764511312*t*z^8 + 57076751120*t*z^7 - 48912040128*t*z^6 + 31487382256*t*z^5 - 14880063248*t*z^4 + 4973523712*t*z^3 - 1104064816*t*z^2 + 144542624*t*z - 8328624*t - 32*z^21 + 1808*z^20 - 47376*z^19 + 764176*z^18 - 8493440*z^17 + 69002736*z^16 - 424263872*z^15 + 2017091456*z^14 - 7514399104*z^13 + 22103625568*z^12 - 51517391216*z^11 + 95159473312*z^10 - 138933013040*z^9 + 159468181280*z^8 - 142699897120*z^7 + 98356518960*z^6 - 51320290640*z^5 + 19763483168*z^4 - 5403420704*z^3 + 983994336*z^2 - 105957024*z + 5038432)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_61 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 61) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_61 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^4 - 20*t*z^3 + 52*t*z^2 - 10*t*z - 12*t + 2*z^2 - 10*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t*z + 8*t)*hf
  · have hr : (16*t^8 - 48*t^7*z^4 + 544*t^7*z^3 - 2000*t^7*z^2 + 2464*t^7*z - 880*t^7 + 48*t^6*z^8 - 1104*t^6*z^7 + 10656*t^6*z^6 - 55456*t^6*z^5 + 166192*t^6*z^4 - 284384*t^6*z^3 + 262560*t^6*z^2 - 119792*t^6*z + 21040*t^6 - 16*t^5*z^12 + 576*t^5*z^11 - 9536*t^5*z^10 + 94640*t^5*z^9 - 615632*t^5*z^8 + 2708944*t^5*z^7 - 8094192*t^5*z^6 + 16214624*t^5*z^5 - 21275904*t^5*z^4 + 17742160*t^5*z^3 - 8957744*t^5*z^2 + 2477520*t^5*z - 286240*t^5 - 16*t^4*z^15 + 912*t^4*z^14 - 22032*t^4*z^13 + 305568*t^4*z^12 - 2743536*t^4*z^11 + 16924160*t^4*z^10 - 73967776*t^4*z^9 + 232256528*t^4*z^8 - 525357776*t^4*z^7 + 851380304*t^4*z^6 - 976751440*t^4*z^5 + 778599200*t^4*z^4 - 418408624*t^4*z^3 + 143681664*t^4*z^2 - 28322560*t^4*z + 2426224*t^4 - 32*t^3*z^18 + 1680*t^3*z^17 - 41328*t^3*z^16 + 629232*t^3*z^15 - 6597952*t^3*z^14 + 50210448*t^3*z^13 - 285100768*t^3*z^12 + 1225137040*t^3*z^11 - 4007511584*t^3*z^10 + 9980057840*t^3*z^9 - 18848741968*t^3*z^8 + 26812870000*t^3*z^7 - 28452560528*t^3*z^6 + 22217254912*t^3*z^5 - 12505907568*t^3*z^4 + 4909386816*t^3*z^3 - 1269487824*t^3*z^2 + 193525568*t^3*z - 13123984*t^3 + 224*t^2*z^20 - 12288*t^2*z^19 + 312496*t^2*z^18 - 4886000*t^2*z^17 + 52524208*t^2*z^16 - 411321136*t^2*z^15 + 2426041152*t^2*z^14 - 10993468688*t^2*z^13 + 38713261808*t^2*z^12 - 106550127136*t^2*z^11 + 229561520032*t^2*z^10 - 386554663248*t^2*z^9 + 506619063264*t^2*z^8 - 513332632992*t^2*z^7 + 398164492368*t^2*z^6 - 232976479824*t^2*z^5 + 100575913808*t^2*z^4 - 30928809728*t^2*z^3 + 6385705888*t^2*z^2 - 790657776*t^2*z + 44223568*t^2 - 512*t*z^22 + 30112*t*z^21 - 822976*t*z^20 + 13872576*t*z^19 - 161440960*t*z^18 + 1375907840*t*z^17 - 8891965552*t*z^16 + 44528317104*t*z^15 - 175148431936*t*z^14 + 545625538128*t*z^13 - 1352294531328*t*z^12 + 2671316671472*t*z^11 - 4204636455408*t*z^10 + 5261878560432*t*z^9 - 5213797171376*t*z^8 + 4063137763424*t*z^7 - 2465085297600*t*z^6 + 1146586754128*t*z^5 - 399488348352*t*z^4 + 100549406368*t*z^3 - 17211204304*t*z^2 + 1787632048*t*z - 84783328*t + 384*z^24 - 24256*z^23 + 715392*z^22 - 13083744*z^21 + 166214176*z^20 - 1557211840*z^19 + 11150463536*z^18 - 62424432544*z^17 + 277288087056*z^16 - 986612125968*z^15 + 2828419258128*z^14 - 6554366700400*z^13 + 12293455194704*z^12 - 18658727730688*z^11 + 22881219906384*z^10 - 22602842712048*z^9 + 17899609834208*z^8 - 11281205893584*z^7 + 5597716437872*z^6 - 2152255131072*z^5 + 626137505536*z^4 - 132847937728*z^3 + 19342072992*z^2 - 1723391936*z + 70685440:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7*z - 256*t^7 - 48*t^6*z^5 + 816*t^6*z^4 - 5520*t^6*z^3 + 18208*t^6*z^2 - 28528*t^6*z + 16656*t^6 + 16*t^5*z^9 - 480*t^5*z^8 + 6576*t^5*z^7 - 52768*t^5*z^6 + 265664*t^5*z^5 - 844544*t^5*z^4 + 1645840*t^5*z^3 - 1851200*t^5*z^2 + 1094960*t^5*z - 270560*t^5 + 16*t^4*z^12 - 816*t^4*z^11 + 17056*t^4*z^10 - 199136*t^4*z^9 + 1462624*t^4*z^8 - 7135680*t^4*z^7 + 23641440*t^4*z^6 - 53266864*t^4*z^5 + 80413712*t^4*z^4 - 78922272*t^4*z^3 + 47882384*t^4*z^2 - 16279824*t^4*z + 2395488*t^4 + 32*t^3*z^15 - 1488*t^3*z^14 + 32240*t^3*z^13 - 428320*t^3*z^12 + 3865344*t^3*z^11 - 24844544*t^3*z^10 + 116278464*t^3*z^9 - 399378192*t^3*z^8 + 1005005568*t^3*z^7 - 1836855008*t^3*z^6 + 2403205888*t^3*z^5 - 2204354064*t^3*z^4 + 1373551696*t^3*z^3 - 550968528*t^3*z^2 + 127983856*t^3*z - 13089344*t^3 - 224*t^2*z^17 + 10944*t^2*z^16 - 245712*t^2*z^15 + 3356784*t^2*z^14 - 31144000*t^2*z^13 + 207427504*t^2*z^12 - 1022399344*t^2*z^11 + 3790791104*t^2*z^10 - 10649090960*t^2*z^9 + 22679226512*t^2*z^8 - 36449915056*t^2*z^7 + 43809949392*t^2*z^6 - 38830565120*t^2*z^5 + 24849580256*t^2*z^4 - 11104235840*t^2*z^3 + 3272598384*t^2*z^2 - 569564048*t^2*z + 44197680*t^2 + 512*t*z^19 - 27040*t*z^18 + 658176*t*z^17 - 9787808*t*z^16 + 99396192*t*z^15 - 729933472*t*z^14 + 4005595952*t*z^13 - 16745677840*t*z^12 + 53916451664*t*z^11 - 134392842992*t*z^10 + 259609537216*t*z^9 - 387778781552*t*z^8 + 445523237024*t*z^7 - 390235693312*t*z^6 + 256988044832*t*z^5 - 124507790848*t*z^4 + 42862635040*t*z^3 - 9883944816*t*z^2 + 1363713408*t*z - 84766800*t - 384*z^21 + 21952*z^20 - 581760*z^19 + 9483040*z^18 - 106385184*z^17 + 870903776*z^16 - 5383631920*z^15 + 25661736960*z^14 - 95528601920*z^13 + 279748197728*z^12 - 646625325200*z^11 + 1180345158640*z^10 - 1698509419136*z^9 + 1919320097472*z^8 - 1692407067232*z^7 + 1153290402160*z^6 - 598511987616*z^5 + 231274889856*z^4 - 64216758496*z^3 + 12068143200*z^2 - 1369964000*z + 70679232)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_62 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 62) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : False := by
  apply cell_10_62 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^4 - 20*t*z^3 + 56*t*z^2 - 34*t*z - 2*z^3 + 14*z^2 - 16*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t*z + 8*t + 2)*hf
  · have hr : (16*t^8 - 48*t^7*z^4 + 544*t^7*z^3 - 1872*t^7*z^2 + 1696*t^7*z - 496*t^7 + 48*t^6*z^8 - 1104*t^6*z^7 + 10304*t^6*z^6 - 49376*t^6*z^5 + 127344*t^6*z^4 - 173856*t^6*z^3 + 127520*t^6*z^2 - 47024*t^6*z + 6736*t^6 - 16*t^5*z^12 + 576*t^5*z^11 - 9200*t^5*z^10 + 84992*t^5*z^9 - 497600*t^5*z^8 + 1909984*t^5*z^7 - 4837936*t^5*z^6 + 8029760*t^5*z^5 - 8634384*t^5*z^4 + 5895904*t^5*z^3 - 2447840*t^5*z^2 + 558144*t^5*z - 52672*t^5 - 16*t^4*z^15 + 784*t^4*z^14 - 16848*t^4*z^13 + 210544*t^4*z^12 - 1705088*t^4*z^11 + 9424944*t^4*z^10 - 36472144*t^4*z^9 + 99869424*t^4*z^8 - 193944400*t^4*z^7 + 266526912*t^4*z^6 - 257683552*t^4*z^5 + 172872336*t^4*z^4 - 78187840*t^4*z^3 + 22545184*t^4*z^2 - 3702112*t^4*z + 259792*t^4 - 16*t^3*z^18 + 832*t^3*z^17 - 19904*t^3*z^16 + 289328*t^3*z^15 - 2845808*t^3*z^14 + 19983968*t^3*z^13 - 103156224*t^3*z^12 + 397671920*t^3*z^11 - 1153761328*t^3*z^10 + 2525348240*t^3*z^9 - 4164857280*t^3*z^8 + 5153131440*t^3*z^7 - 4745553632*t^3*z^6 + 3210247952*t^3*z^5 - 1561420208*t^3*z^4 + 527040736*t^3*z^3 - 116128592*t^3*z^2 + 14858384*t^3*z - 826480*t^3 + 64*t^2*z^20 - 3392*t^2*z^19 + 82784*t^2*z^18 - 1232960*t^2*z^17 + 12523664*t^2*z^16 - 91873440*t^2*z^15 + 503130992*t^2*z^14 - 2098217216*t^2*z^13 + 6743523536*t^2*z^12 - 16816194880*t^2*z^11 + 32639167296*t^2*z^10 - 49322605792*t^2*z^9 + 57884135456*t^2*z^8 - 52448524720*t^2*z^7 + 36316614112*t^2*z^6 - 18905469984*t^2*z^5 + 7215615536*t^2*z^4 - 1941710048*t^2*z^3 + 345449296*t^2*z^2 - 36060048*t^2*z + 1650256*t^2 - 80*t*z^22 + 4464*t*z^21 - 115392*t*z^20 + 1833888*t*z^19 - 20058432*t*z^18 + 160191600*t*z^17 - 967439280*t*z^16 + 4516563840*t*z^15 - 16531207056*t*z^14 + 47856305008*t*z^13 - 110131656976*t*z^12 + 201919955488*t*z^11 - 294884239968*t*z^10 + 342177282480*t*z^9 - 313922558624*t*z^8 + 225879713568*t*z^7 - 125930714928*t*z^6 + 53425624048*t*z^5 - 16790876672*t*z^4 + 3752296960*t*z^3 - 557887184*t*z^2 + 48857776*t*z - 1878112*t + 32*z^24 - 1888*z^23 + 51936*z^22 - 884992*z^21 + 10469232*z^20 - 91340304*z^19 + 609584320*z^18 - 3186106512*z^17 + 13248097936*z^16 - 44284088656*z^15 + 119795165328*z^14 - 263243606160*z^13 + 470520880064*z^12 - 683495346656*z^11 + 804555553104*z^10 - 763543157552*z^9 + 579847161840*z^8 - 348706327008*z^7 + 163695325344*z^6 - 58801148368*z^5 + 15709681104*z^4 - 2992149728*z^3 + 379605056*z^2 - 28340096*z + 924160:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7*z - 256*t^7 - 48*t^6*z^5 + 816*t^6*z^4 - 5168*t^6*z^3 + 14240*t^6*z^2 - 15248*t^6*z + 6000*t^6 + 16*t^5*z^9 - 480*t^5*z^8 + 6240*t^5*z^7 - 45136*t^5*z^6 + 195104*t^5*z^5 - 507440*t^5*z^4 + 772640*t^5*z^3 - 661616*t^5*z^2 + 294048*t^5*z - 50896*t^5 + 16*t^4*z^12 - 688*t^4*z^11 + 12640*t^4*z^10 - 131248*t^4*z^9 + 853712*t^4*z^8 - 3633792*t^4*z^7 + 10269584*t^4*z^6 - 19229248*t^4*z^5 + 23587200*t^4*z^4 - 18587888*t^4*z^3 + 8990976*t^4*z^2 - 2399840*t^4*z + 246032*t^4 + 16*t^3*z^15 - 736*t^3*z^14 + 15408*t^3*z^13 - 193184*t^3*z^12 + 1608928*t^3*z^11 - 9349072*t^3*z^10 + 38823968*t^3*z^9 - 116373824*t^3*z^8 + 252049472*t^3*z^7 - 392358320*t^3*z^6 + 434086176*t^3*z^5 - 334773312*t^3*z^4 + 174124560*t^3*z^3 - 57547856*t^3*z^2 + 10736960*t^3*z - 755136*t^3 - 64*t^2*z^17 + 3008*t^2*z^16 - 64416*t^2*z^15 + 831360*t^2*z^14 - 7210416*t^2*z^13 + 44389728*t^2*z^12 - 199909184*t^2*z^11 + 669603056*t^2*z^10 - 1681969552*t^2*z^9 + 3176453104*t^2*z^8 - 4500997856*t^2*z^7 + 4752383584*t^2*z^6 - 3688391568*t^2*z^5 + 2055259536*t^2*z^4 - 790715472*t^2*z^3 + 196487904*t^2*z^2 - 27851216*t^2*z + 1447760*t^2 + 80*t*z^19 - 3984*t*z^18 + 91088*t*z^17 - 1267360*t*z^16 + 11994848*t*z^15 - 81794624*t*z^14 + 415429936*t*z^13 - 1603016256*t*z^12 + 4754165216*t*z^11 - 10900802496*t*z^10 + 19352999664*t*z^9 - 26543779808*t*z^8 + 27955760304*t*z^7 - 22370821952*t*z^6 + 13375045584*t*z^5 - 5819570000*t*z^4 + 1767245056*t*z^3 - 349258128*t*z^2 + 39532624*t*z - 1565520*t - 32*z^21 + 1696*z^20 - 41600*z^19 + 626880*z^18 - 6498256*z^17 + 49174768*z^16 - 281417552*z^15 + 1245229104*z^14 - 4320460784*z^13 + 11853760880*z^12 - 25825067024*z^11 + 44703938832*z^10 - 61318151072*z^9 + 66241679040*z^8 - 55810784672*z^7 + 36151903248*z^6 - 17640139952*z^5 + 6295186384*z^4 - 1571604032*z^3 + 255452304*z^2 - 23760736*z + 719760)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_10_63 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t 63) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : (t - z^2/7 + 4*z/7 - 4/7:ℝ)=0 := by
  apply cell_10_63 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t*z^4 - 20*t*z^3 + 54*t*z^2 - 20*t*z - 6*t + 2*z^2 - 10*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t*z + 8*t)*hf


private def limit10 (z t : ℝ) : Fin 64→Prop := ![False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,(((0:ℝ):ℝ)=0),False,False,(((0:ℝ):ℝ)=0),False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,((t - z^2/7 + 4*z/7 - 4/7:ℝ)=0)]

private def hue10 : Fin 64→Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma exclude_field_10 (z t : ℝ) (hf : z^3 - 6*z^2 + 5*z - 1=0) (hn0 : t-(1)≠0) (hn1 : t-(z^2 - 5*z + 3)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (g : Fin 5→Fin 64) (hinj : Function.Injective g)
    (hc : ∀ i, cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t (g i)) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t)
    (he : ∀ i j : Fin 5, i≠j → edge4 (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t (g i)) (profile4 (z^2 - 5*z + 3) (z) t (g j)) (z^2 - 5*z + 3) (z) t=0) : False := by
  have row (k : Fin 64) (hh : cell (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t k) ((z^2 - 5*z + 3),(1),(z)) ((z^2 - 5*z + 3),(z),(1)) (z^2 - 5*z + 3) (z) t) : limit10 z t k := by
    fin_cases k
    · exact row_10_0 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_1 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_2 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_3 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_4 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_5 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_6 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_7 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_8 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_9 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_10 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_11 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_12 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_13 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_14 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_15 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_16 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_17 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_18 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_19 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_20 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_21 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_22 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_23 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_24 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_25 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_26 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_27 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_28 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_29 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_30 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_31 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_32 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_33 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_34 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_35 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_36 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_37 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_38 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_39 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_40 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_41 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_42 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_43 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_44 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_45 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_46 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_47 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_48 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_49 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_50 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_51 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_52 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_53 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_54 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_55 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_56 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_57 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_58 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_59 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_60 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_61 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_62 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_10_63 z t hf hn0 hn1 hn2 hn3 hh
  have allowed (k : Fin 64) (hh : limit10 z t k) : k∈([38,41,63]:List (Fin 64)) := by
    fin_cases k <;> first | decide | exact False.elim hh
  have cert : ∀ i j : Fin 64, i∈([38,41,63]:List (Fin 64)) → j∈([38,41,63]:List (Fin 64)) → i<j → hue10 i=hue10 j → (i,j)∈([]:List (Fin 64×Fin 64)) := by decide
  have bad (i j : Fin 64) (hi : limit10 z t i) (hj : limit10 z t j) (hlt : i<j) (hc : hue10 i=hue10 j) (hb : edge4 (1) (1) (z^2 - 5*z + 3) (profile4 (z^2 - 5*z + 3) (z) t i) (profile4 (z^2 - 5*z + 3) (z) t j) (z^2 - 5*z + 3) (z) t=0) : False := by
    have h := cert i j (allowed i hi) (allowed j hj) hlt hc
    simpa using h
  have hi : Function.Injective (fun i : Fin 5 => hue10 (g i)) := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne (show g i≠g j from fun e => hne (hinj e)) with hl|hl
    · exact bad _ _ (row _ (hc i)) (row _ (hc j)) hl h (he i j hne)
    · exact bad _ _ (row _ (hc j)) (row _ (hc i)) hl h.symm (he j i (Ne.symm hne))
  have hh := Fintype.card_le_of_injective _ hi
  norm_num at hh

private lemma no_0011102202 (x y t : ℝ) (H : admissible ![0,0,1,1,1,0,2,2,0,2] x y) (E : hasExtension ![0,0,1,1,1,0,2,2,0,2] x y t)
    (t1 : t-1≠0) (tx : t-x≠0) (ty : t-y≠0) (t0 : t≠0) : False := by
  obtain ⟨h0,h1⟩ := shape_0011102202 x y H
  by_cases G0 : y - 2=0
  · have ex : x=1/2 := by linear_combination (1)*h0 + (-937*y^4/164738 + 11476*y^3/82369 - 95517*y^2/82369 + 581801*y/164738 - 264437/164738)*G0
    have ey : y=2 := by linear_combination (1)*G0
    apply H.2.1 0 3 4 (by decide) (by decide)
    change area (x) (x) (y)=0
    simp only [ex,ey,area]
    ring
  by_cases G1 : y - 9=0
  · have ex : x=4 := by linear_combination (1)*h0 + (-937*y^4/164738 + 16393*y^3/164738 - 89401*y^2/164738 + 79630*y/82369 + 5301/164738)*G1
    have ey : y=9 := by linear_combination (1)*G1
    apply H.2.1 0 1 2 (by decide) (by decide)
    change area (1) (1) (x)=0
    simp only [ex,ey,area]
    ring
  by_cases G2 : y^3 - 6*y^2 + 5*y - 1=0
  · have ex : x=y^2 - 5*y + 3 := by linear_combination (1)*h0 + (-937*y^2/164738 + 9602*y/82369 - 117029/164738)*G2
    obtain ⟨u,hu,hc,he⟩ := E
    change ∀ i, cell (1) (1) (x) (profile4 x y t (u i)) ((x),(1),(y)) ((x),(y),(1)) x y t at hc
    change ∀ i j, i≠j → edge4 (1) (1) (x) (profile4 x y t (u i)) (profile4 x y t (u j)) x y t=0 at he
    simp only [ex] at hc he tx ty
    apply exclude_field_10 y t (by linear_combination (1)*G2) t1 tx ty (by simpa using t0) u hu hc he
  apply (mul_ne_zero (mul_ne_zero G0 (pow_ne_zero 2 G1)) G2)
  linear_combination (1)*h1

private lemma no_0011012212 (x y t : ℝ) (H : admissible ![0,0,1,1,0,1,2,2,1,2] x y) (E : hasExtension ![0,0,1,1,0,1,2,2,1,2] x y t)
    (t1 : t-1≠0) (tx : t-x≠0) (ty : t-y≠0) (t0 : t≠0) : False := by
  obtain ⟨h0,h1⟩ := shape_0011012212 x y H
  by_cases G0 : 4*y^2 - 8*y + 1=0
  · have ex : x=1/2 := by linear_combination (1)*h0
    obtain ⟨u,hu,hc,he⟩ := E
    change ∀ i, cell (1) (1) (1) (profile4 x y t (u i)) ((x),(x),(y)) ((x),(y),(x)) x y t at hc
    change ∀ i j, i≠j → edge4 (1) (1) (1) (profile4 x y t (u i)) (profile4 x y t (u j)) x y t=0 at he
    simp only [ex] at hc he tx ty
    apply exclude_field_8 y t (by linear_combination (1)*G0) t1 tx ty (by simpa using t0) u hu hc he
  apply G0
  linear_combination (4)*h1

end Erdos1082Ten

open Erdos1082Ten EuclideanGeometry

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H2_R1.H2 := by
  intro A hn hA hd M hm B hBA hB hf hthree p r c hc hh
  obtain ⟨x,y,t,H,E,t1,tx,ty,t0⟩ := given_extension A B M hm hBA hA hB hd hthree hn hf p r c hc
  change colorCode c∈([3233,3074]:List ℕ) at hh
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with eq|eq
  · have cc : c=![0,0,1,1,1,0,2,2,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact no_0011102202 x y t H E t1 tx ty t0
  · have cc : c=![0,0,1,1,0,1,2,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact no_0011012212 x y t H E t1 tx ty t0
