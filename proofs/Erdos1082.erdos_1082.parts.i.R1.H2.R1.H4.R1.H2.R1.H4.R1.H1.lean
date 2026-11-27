import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H4_R1

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
private lemma base_0000112212 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : x^3 - x^2*y - 4*x^2 + x*y^2 + 4*x*y - 2*y^2=0) (g2 : 2*x^2*y - 8*x*y + 2*y^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -y^2 + 4*y≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -y^2 + 4*y≠0) (_n11 : 4*x*y - y^2≠0) (n12 : 4*x*y - y^2≠0) (_n13 : -x^2 + 4*x*y≠0) (_n14 : -x^2 + 4*x*y≠0) : (x + y - (5:ℝ)=0) ∧ (y^2 - 5*y + (5:ℝ)=0) := by
  have h2 : y≠0 := by
    intro he
    apply n12
    linear_combination (4*x - y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g2
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^2 - 4*x + y=0 := by linear_combination (1)*h4
  have h7 : x*y + y^3 - 4*y^2=0 := by linear_combination (3 - x)*g1 + (x^2 - x*y - 3*x + y^2 + 2*y)*h4
  have h8 : y^4 - 5*y^3 + 5*y^2=0 := by linear_combination (-x*y + x + 3*y - 4)*g1 + (x^2*y - x^2 - x*y^2 - 2*x*y + 4*x + y^3 + y^2 - 3*y)*h4
  have h9 : x^2 - 4*x + y=0 := by linear_combination (1)*h6
  have h11 : ((y))*(x + y^2 - 4*y)=0 := by linear_combination (1)*h7
  have h10 := (mul_eq_zero.mp h11).resolve_left h2
  have h13 : ((y) * (y))*(y^2 - 5*y + 5)=0 := by linear_combination (1)*h8
  have h12 := (mul_eq_zero.mp h13).resolve_left (mul_ne_zero h2 h2)
  have h14 : x + y - (5:ℝ)=0 := by linear_combination (1)*h10 + (-1)*h12
  have h15 : y^2 - 5*y + (5:ℝ)=0 := by linear_combination (1)*h12
  have h16 : x + y - (5:ℝ)=0 := by linear_combination (1)*h14
  have h17 : y^2 - 5*y + (5:ℝ)=0 := by linear_combination (1)*h15
  exact ⟨h16, h17⟩



private lemma shape_0000112212 (x y : ℝ) (ha : admissible ![0,0,0,0,1,1,2,2,1,2] x y) : (x + y - 5=0) ∧ (y^2 - 5*y + 5=0) := by
  apply base_0000112212 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y 1 y x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 y x 1 y x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
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

private lemma base_0001010112 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : -x^2 - 2*x + 3*y - (1:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : -x^2 + 4*x≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : 4*x*y - y^2≠0) : (x - y/(2:ℝ)=0) ∧ (y^2 - 8*y + (4:ℝ)=0) := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 + 2*x - 3*y + (1:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : 2*x - y=0 := by linear_combination (1/3)*h2 + (-1/3)*h3
  have h5 : y^2 - 8*y + (4:ℝ)=0 := by linear_combination (-2*x/3 - y/3 + 8/3)*h2 + (2*x/3 + y/3 + 4/3)*h3
  have h6 : x - y/(2:ℝ)=0 := by linear_combination (1/2)*h4
  have h7 : y^2 - 8*y + (4:ℝ)=0 := by linear_combination (1)*h5
  exact ⟨h6, h7⟩



private lemma base_0001010220 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : -x^2 - 2*x*y + 2*x + 2*y^2 - 4*y + (2:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -y^2 + 4*y≠0) (_n13 : -x^2 + 4*x≠0) (_n14 : 4*y - (1:ℝ)≠0) : (x - (2:ℝ)=0) ∧ (y^2 - 4*y + (1:ℝ)=0) := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 + 2*x*y - 2*x - 2*y^2 + 4*y - (2:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x + y^3 - 6*y^2 + 9*y - (4:ℝ)=0 := by linear_combination (4/3 - x/3)*h2 + (x/3 + y - 4/3)*h3
  have h5 : y^4 - 6*y^3 + 10*y^2 - 6*y + (1:ℝ)=0 := by linear_combination (-x*y/3 + 4*y/3 - 1/3)*h2 + (x*y/3 + y^2 - 4*y/3 + 1/3)*h3
  have h6 : x + y^3 - 6*y^2 + 9*y - (4:ℝ)=0 := by linear_combination (1)*h4
  have h8 : y - (1:ℝ)≠0 := by
    intro he
    apply n3
    linear_combination (1)*he
  have h9 : ((y - 1) * (y - 1))*(y^2 - 4*y + 1)=0 := by linear_combination (1)*h5
  have h7 := (mul_eq_zero.mp h9).resolve_left (mul_ne_zero h8 h8)
  have h10 : x - (2:ℝ)=0 := by linear_combination (1)*h6 + (2 - y)*h7
  exact ⟨h10, h7⟩



private lemma shape_0001010112 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,0,1,1,2] x y) : (x - y/2=0) ∧ (y^2 - 8*y + 4=0) := by
  apply base_0001010112 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x x 1 x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x 1 x x 1 x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001010220 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,0,2,2,0] x y) : (x - 2=0) ∧ (y^2 - 4*y + 1=0) := by
  apply base_0001010220 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x 1 y 1=0 := ha.2.2.2.1
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
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
  · have hn : area x 1 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring

private lemma cell_2_0 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (10 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/2 - z/5)*h0 + (-4/5)*hf
  norm_num at hh

private lemma cell_2_1 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 2)*h0 + (1)*hf
  norm_num at hh

private lemma cell_2_2 (z t : ℝ) (_hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/2)*h0
  norm_num at hh

private lemma cell_2_3 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z - 14) - 6*z + 22:ℝ)=0) (h1 : (16*t^8 + t^7*(-16*z - 448) + t^6*(176*z + 5728) + t^5*(960*z - 44176) + t^4*(220880 - 22320*z) + t^3*(124720*z - 705536) + t^2*(1356128 - 313184*z) + t*(373344*z - 1416848) - 173280*z + 617856:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(11*z/750 - 4/75) + t^6*(193/150 - 53*z/150) + t^5*(883*z/250 - 322/25) + t^4*(10343/150 - 2833*z/150) + t^3*(2883*z/50 - 31597/150) + t^2*(8941/25 - 12236*z/125) + t*(1202*z/15 - 1464/5) - 4803*z/250 + 351/5)*h0 + (t*(1/150 - 11*z/6000) + z/1500 - 1/400)*h1 + (-22*t^8/375 + 141*t^7/125 - 2828*t^6/375 + 6527*t^5/375 + 1117*t^4/75 - 43343*t^3/375 + 54622*t^2/375 - 5919*t/125 + 31/125)*hf
  norm_num at hh

private lemma cell_2_4 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 2)*h0 + (1)*hf
  norm_num at hh

private lemma cell_2_5 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (30 - 10*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/5 - z/10)*h0 + (-1)*hf
  norm_num at hh

private lemma cell_2_6 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h1 : (t*(6000*z - 8000):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (11/2000 - 3*z/2000)*h1 + (9*t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_2_7 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 2*t*z:ℝ)=0) (h1 : (16*t^8 - 144*t^7*z + t^6*(2624*z - 2720) + t^5*(25040 - 19360*z) + t^4*(72320*z - 99200) + t^3*(196400 - 141200*z) + t^2*(136800*z - 190000) + t*(72000 - 52000*z):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(3*z/250 - 11/250) + t^5*(12/25 - 16*z/125) + t^4*(53*z/125 - 43/25) + t^3*(81/50 - 9*z/50) + t^2*(5/2 - 34*z/25) + t*(9*z/5 - 19/5) - z/2 + 1/2)*h0 + (11/2000 - 3*z/2000)*h1 + (-24*t^7/125 + 92*t^6/25 - 3524*t^5/125 + 2703*t^4/25 - 5363*t^3/25 + 1044*t^2/5 - 79*t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_2_8 (z t : ℝ) (_hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/2)*h0
  norm_num at hh

private lemma cell_2_9 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h2 : (t*(6000*z - 8000):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (11/2000 - 3*z/2000)*h2 + (9*t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_2_10 (z t : ℝ) (_hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) : ((0:ℝ):ℝ)=0 := by
  rfl

private lemma cell_2_11 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 10*t + 10:ℝ)=0) (h2 : (16*t^8 + t^7*(112*z - 640) + t^6*(9440 - 2336*z) + t^5*(19600*z - 70800) + t^4*(303200 - 85920*z) + t^3*(216000*z - 775600) + t^2*(1186000 - 324000*z) + t*(280000*z - 1012000) - 100000*z + 360000:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(z/125 - 7/250) + t^5*(7/10 - 49*z/250) + t^4*(487*z/250 - 176/25) + t^3*(181/5 - 499*z/50) + t^2*(688*z/25 - 498/5) + t*(1383/10 - 383*z/10) + 209*z/10 - 76)*h0 + (7/2000 - z/1000)*h2 + (14*t^7/125 - 292*t^6/125 + 98*t^5/5 - 2148*t^4/25 + 216*t^3 - 324*t^2 + 280*t - 100)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_2_12 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(2*z - 14) - 6*z + 22:ℝ)=0) (h1 : (16*t^8 + t^7*(176*z - 768) + t^6*(11568 - 3088*z) + t^5*(24912*z - 90576) + t^4*(422080 - 116800*z) + t^3*(335440*z - 1210736) + t^2*(2092448 - 579856*z) + t*(552528*z - 1993888) - 222912*z + 803456:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(2*z/125 - 3/50) + t^6*(47/25 - 129*z/250) + t^5*(167*z/25 - 121/5) + t^4*(4183/25 - 1156*z/25) + t^3*(371*z/2 - 16777/25) + t^2*(38992/25 - 107789*z/250) + t*(67182*z/125 - 48604/25) - 13857*z/50 + 25058/25)*h0 + (t*(3/400 - z/500) + 3*z/400 - 11/400)*h1 + (8*t^8/25 - 796*t^7/125 + 7066*t^6/125 - 7197*t^5/25 + 22461*t^4/25 - 8501*t^3/5 + 224016*t^2/125 - 101346*t/125 + 9)*hf
  norm_num at hh

private lemma cell_2_13 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 2*t*z:ℝ)=0) (h2 : (16*t^8 - 144*t^7*z + t^6*(2624*z - 2720) + t^5*(25040 - 19360*z) + t^4*(72320*z - 99200) + t^3*(196400 - 141200*z) + t^2*(136800*z - 190000) + t*(72000 - 52000*z):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(3*z/250 - 11/250) + t^5*(12/25 - 16*z/125) + t^4*(53*z/125 - 43/25) + t^3*(81/50 - 9*z/50) + t^2*(5/2 - 34*z/25) + t*(9*z/5 - 19/5) - z/2 + 1/2)*h0 + (11/2000 - 3*z/2000)*h2 + (-24*t^7/125 + 92*t^6/25 - 3524*t^5/125 + 2703*t^4/25 - 5363*t^3/25 + 1044*t^2/5 - 79*t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_2_14 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 10*t + 10:ℝ)=0) (h1 : (16*t^8 + t^7*(112*z - 640) + t^6*(9440 - 2336*z) + t^5*(19600*z - 70800) + t^4*(303200 - 85920*z) + t^3*(216000*z - 775600) + t^2*(1186000 - 324000*z) + t*(280000*z - 1012000) - 100000*z + 360000:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(z/125 - 7/250) + t^5*(7/10 - 49*z/250) + t^4*(487*z/250 - 176/25) + t^3*(181/5 - 499*z/50) + t^2*(688*z/25 - 498/5) + t*(1383/10 - 383*z/10) + 209*z/10 - 76)*h0 + (7/2000 - z/1000)*h1 + (14*t^7/125 - 292*t^6/125 + 98*t^5/5 - 2148*t^4/25 + 216*t^3 - 324*t^2 + 280*t - 100)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_2_15 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(10 - 2*z) + t*(8*z - 40) - 10*z + 40:ℝ)=0) (h1 : (t^8*(4400 - 1200*z) + t^7*(24400*z - 89600) + t^6*(786400 - 214000*z) + t^5*(1057200*z - 3883600) + t^4*(11798000 - 3216800*z) + t^3*(6170800*z - 22568000) + t^2*(26536000 - 7284000*z) + t*(4834000*z - 17530000) - 1380000*z + 4980000:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(4*z/5 - 29/10) + t^5*(95/2 - 131*z/10) + t^4*(439*z/5 - 1592/5) + t^3*(2233/2 - 3079*z/10) + t^2*(5953*z/10 - 2158) + t*(4359/2 - 3008*z/5) + 1243*z/5 - 1799/2)*h0 + (3/400 - z/500)*h1 + (-4*t^8/5 + 81*t^7/5 - 698*t^6/5 + 3326*t^5/5 - 9509*t^4/5 + 3297*t^3 - 3305*t^2 + 8316*t/5 - 274)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_2_16 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (140 - 40*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3/20 - z/10)*h0 + (-4)*hf
  norm_num at hh

private lemma cell_2_17 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (52 - 16*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7/44 - z/11)*h0 + (-16/11)*hf
  norm_num at hh

private lemma cell_2_18 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (122 - 34*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (12/19 - 17*z/38)*h0 + (-289/19)*hf
  norm_num at hh

private lemma cell_2_19 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(10*z - 44) - 50*z + 182:ℝ)=0) (h1 : (16*t^8 + t^7*(240*z - 1408) + t^6*(47168 - 11008*z) + t^5*(221408*z - 852896) + t^4*(9423840 - 2548320*z) + t^3*(18192000*z - 66266976) + t^2*(292060048 - 80578880*z) + t*(204597168*z - 740519328) - 228924608*z + 828297536:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(159/104500 - 39*z/104500) + t^6*(629*z/26125 - 9727/104500) + t^5*(127669/52250 - 68139*z/104500) + t^4*(508091*z/52250 - 374123/10450) + t^3*(6627297/20900 - 2271487*z/26125) + t^2*(48982301*z/104500 - 88903697/52250) + t*(536154387/104500 - 148004099*z/104500) + 8814933*z/4750 - 15953672/2375)*h0 + (t*(39*z/836000 - 159/836000) - 151*z/418000 + 1183/836000)*h1 + (-39*t^8/5225 + 17807*t^7/52250 - 343863*t^6/52250 + 3606221*t^5/52250 - 86433*t^4/209 + 13544963*t^3/10450 - 55053937*t^2/52250 - 249969827*t/52250 + 23966417/2375)*hf
  norm_num at hh

private lemma cell_2_20 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (52 - 16*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7/44 - z/11)*h0 + (-16/11)*hf
  norm_num at hh

private lemma cell_2_21 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/10 - 1/2)*h0 + (1/5)*hf
  norm_num at hh

private lemma cell_2_22 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (40 - 12*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/4 - 3*z/20)*h0 + (-9/5)*hf
  norm_num at hh

private lemma cell_2_23 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(6*z - 30) - 22*z + 80:ℝ)=0) (h1 : (16*t^8 + t^7*(112*z - 960) + t^6*(23680 - 4400*z) + t^5*(72400*z - 318320) + t^4*(2577680 - 649360*z) + t^3*(3446320*z - 12985600) + t^2*(40032000 - 10891440*z) + t*(19100800*z - 69462800) - 14396800*z + 52148800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(367*z/167750 - 1327/167750) + t^6*(2061/6100 - 2851*z/30500) + t^5*(568781*z/335500 - 411089/67100) + t^4*(410551/6710 - 1136111*z/67100) + t^3*(6751031*z/67100 - 2439911/6710) + t^2*(863025/671 - 11936673*z/33550) + t*(46520237*z/67100 - 8410718/3355) - 350243*z/610 + 253329/122)*h0 + (t*(1327/1342000 - 367*z/1342000) + 479*z/536800 - 1721/536800)*h1 + (1468*t^8/83875 - 58229*t^7/83875 + 1928661*t^6/167750 - 1575319*t^5/15250 + 18309887*t^4/33550 - 28610894*t^3/16775 + 49572404*t^2/16775 - 76618043*t/33550 + 65547/305)*hf
  norm_num at hh

private lemma cell_2_24 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (122 - 34*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (12/19 - 17*z/38)*h0 + (-289/19)*hf
  norm_num at hh

private lemma cell_2_25 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (40 - 12*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/4 - 3*z/20)*h0 + (-9/5)*hf
  norm_num at hh

private lemma cell_2_26 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (110 - 32*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (5/38 - 8*z/95)*h0 + (-256/95)*hf
  norm_num at hh

private lemma cell_2_27 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(8*z - 40) - 42*z + 160:ℝ)=0) (h1 : (16*t^8 + t^7*(176*z - 1280) + t^6*(41200 - 8400*z) + t^5*(173040*z - 725120) + t^4*(7794080 - 2004800*z) + t^3*(14164880*z - 53044400) + t^2*(224921200 - 61190640*z) + t*(149814000*z - 545777600) - 160349600*z + 581780800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(7/4750 - 13*z/19000) + t^6*(557*z/19000 - 67/950) + t^5*(1433/950 - 1324*z/2375) + t^4*(4749*z/760 - 71507/3800) + t^3*(14017/95 - 171587*z/3800) + t^2*(99519*z/475 - 274057/380) + t*(1531849/760 - 1081577*z/1900) + 65297*z/95 - 937211/380)*h0 + (t*(13*z/152000 - 7/38000) - 9*z/38000 + 23/30400)*h1 + (-91*t^8/9500 + 236*t^7/475 - 10543*t^6/950 + 330227*t^5/2375 - 100948*t^4/95 + 476487*t^3/95 - 5301751*t^2/380 + 9399839*t/475 - 865392/95)*hf
  norm_num at hh

private lemma cell_2_28 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(10*z - 44) - 50*z + 182:ℝ)=0) (h1 : (16*t^8 + t^7*(432*z - 1728) + t^6*(55888 - 15232*z) + t^5*(272240*z - 987136) + t^4*(10792240 - 2981920*z) + t^3*(20776960*z - 75173776) + t^2*(326052368 - 90119952*z) + t*(222545072*z - 805164048) - 239529600*z + 866614176:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(3*z/500 - 11/500) + t^6*(174/125 - 48*z/125) + t^5*(258*z/25 - 747/20) + t^4*(55393/100 - 76547*z/500) + t^3*(169577*z/125 - 490833/100) + t^2*(12994701/500 - 718329*z/100) + t*(42087*z/2 - 9517004/125) - 6576331*z/250 + 2379334/25)*h0 + (t*(11/4000 - 3*z/4000) + 11*z/2000 - 1/50)*h1 + (33*t^8/125 - 483*t^7/50 + 41389*t^6/250 - 84341*t^5/50 + 538121*t^4/50 - 5274943*t^3/125 + 2324226*t^2/25 - 11052107*t/125 + 10733/5)*hf
  norm_num at hh

private lemma cell_2_29 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(6*z - 30) - 22*z + 80:ℝ)=0) (h1 : (16*t^8 + t^7*(304*z - 1280) + t^6*(31760 - 8560*z) + t^5*(115600*z - 419920) + t^4*(3383680 - 934880*z) + t^3*(4744400*z - 17162800) + t^2*(53603200 - 14817840*z) + t*(26065200*z - 94295200) - 19779200*z + 71556800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(7*z/1000 - 13/500) + t^6*(243/200 - 167*z/500) + t^5*(1631*z/250 - 2363/100) + t^4*(1999/8 - 1381*z/20) + t^3*(10742*z/25 - 12437/8) + t^2*(56961/10 - 157439*z/100) + t*(629633*z/200 - 455597/40) - 13263*z/5 + 95969/10)*h0 + (t*(13/4000 - 7*z/8000) + 23*z/8000 - 17/1600)*h1 + (28*t^8/125 - 3103*t^7/500 + 19817*t^6/250 - 296271*t^5/500 + 54839*t^4/20 - 385323*t^3/50 + 1188277*t^2/100 - 353451*t/50 - 1492)*hf
  norm_num at hh

private lemma cell_2_30 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(8*z - 40) - 42*z + 160:ℝ)=0) (h1 : (16*t^8 + t^7*(368*z - 1600) + t^6*(51520 - 13840*z) + t^5*(243600*z - 883120) + t^4*(9278480 - 2566320*z) + t^3*(17125360*z - 61947200) + t^2*(257208800 - 71089040*z) + t*(167822400*z - 607190000) - 172411200*z + 623788800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(z/100 - 9/250) + t^6*(54/25 - 299*z/500) + t^5*(7637*z/500 - 1381/25) + t^4*(19506/25 - 10783*z/50) + t^3*(9083*z/5 - 131453/20) + t^2*(330203/10 - 456327*z/50) + t*(2531939*z/100 - 1832123/20) - 299211*z/10 + 1082557/10)*h0 + (t*(9/2000 - z/800) + z/125 - 23/800)*h1 + (19*t^8/50 - 376*t^7/25 + 33489*t^6/125 - 348739*t^5/125 + 917337*t^4/50 - 3827733*t^3/50 + 4815513*t^2/25 - 12765501*t/50 + 613017/5)*hf
  norm_num at hh

private lemma cell_2_31 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(10 - 2*z) + t*(24*z - 100) - 62*z + 230:ℝ)=0) (h1 : (t^8*(4400 - 1200*z) + t^7*(50000*z - 182400) + t^6*(3288000 - 904400*z) + t^5*(9281600*z - 33670800) + t^4*(214287600 - 59146400*z) + t^3*(239764400*z - 868039200) + t^2*(2185963200 - 604019600*z) + t*(864818000*z - 3129243600) - 538894400*z + 1949780800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(163*z/100 - 59/10) + t^6*(4193/20 - 5793*z/100) + t^5*(87647*z/100 - 15858/5) + t^4*(529627/20 - 182966*z/25) + t^3*(3642999*z/100 - 659053/5) + t^2*(7823417/20 - 10811481*z/100) + t*(17715521*z/100 - 6409589/10) - 6183071*z/50 + 2237062/5)*h0 + (t*(31/2000 - 17*z/4000) + 59*z/4000 - 107/2000)*h1 + (-46*t^9/25 + 3761*t^8/50 - 33422*t^7/25 + 338062*t^6/25 - 2135683*t^5/25 + 8677576*t^4/25 - 22397074*t^3/25 + 2765199*t^2/2 - 5474348*t/5 + 7042109/25)*hf
  norm_num at hh

private lemma cell_2_32 (z t : ℝ) (_hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (10:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/10)*h0
  norm_num at hh

private lemma cell_2_33 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*z - 8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 3/4)*h0 + (-1)*hf
  norm_num at hh

private lemma cell_2_34 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (12 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/2 - z/4)*h0 + (-1)*hf
  norm_num at hh

private lemma cell_2_35 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 14*t + 22:ℝ)=0) (h1 : (16*t^8 + t^7*(-80*z - 448) + t^6*(2752*z + 4688) + t^5*(-40592*z - 17376) + t^4*(332640*z - 63760) + t^3*(896624 - 1633440*z) + t^2*(4796400*z - 3716912) + t*(7200752 - 7774832*z) + 5349152*z - 5515584:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(3*z/500 - 11/500) + t^6*(82/125 - 89*z/500) + t^5*(1119*z/500 - 1038/125) + t^4*(5787/100 - 1932*z/125) + t^3*(7903*z/125 - 1198/5) + t^2*(147033/250 - 76361*z/500) + t*(50203*z/250 - 98707/125) - 13778*z/125 + 111181/250)*h0 + (t*(11/4000 - 3*z/4000) + 3*z/2000 - 11/2000)*h1 + (-3*t^8/50 + 273*t^7/125 - 8643*t^6/250 + 38796*t^5/125 - 43101*t^4/25 + 302373*t^3/50 - 3256431*t^2/250 + 1959264*t/125 - 1002966/125)*hf
  norm_num at hh

private lemma cell_2_36 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*z - 8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 3/4)*h0 + (-1)*hf
  norm_num at hh

private lemma cell_2_37 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (10 - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/10)*h0 + (1/5)*hf
  norm_num at hh

private lemma cell_2_38 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/10 - 1/2)*h0 + (1/5)*hf
  norm_num at hh

private lemma cell_2_39 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 4*t*z + 8*z - 10:ℝ)=0) (h1 : (16*t^8 - 208*t^7*z + t^6*(5840*z - 6000) + t^5*(92880 - 72720*z) + t^4*(518240*z - 701120) + t^3*(3115600 - 2265680*z) + t^2*(6022160*z - 8315200) + t*(12339200 - 8929200*z) + 5652000*z - 7811200:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(9*z/1000 - 33/1000) + t^6*(11/20 - 147*z/1000) + t^5*(223*z/250 - 177/50) + t^4*(53/5 - 17*z/8) + t^3*(-229*z/200 - 117/10) + t^2*(1739*z/100 - 63/5) + t*(1879/40 - 1839*z/50) + 137*z/5 - 153/4)*h0 + (t*(33/8000 - 9*z/8000) + 3*z/1600 - 11/1600)*h1 + (-99*t^8/500 + 63*t^7/10 - 11002*t^6/125 + 351867*t^5/500 - 350817*t^4/100 + 55509*t^3/5 - 1081157*t^2/50 + 2350459*t/100 - 108167/10)*hf
  norm_num at hh

private lemma cell_2_40 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (12 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/2 - z/4)*h0 + (-1)*hf
  norm_num at hh

private lemma cell_2_41 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/10 - 1/2)*h0 + (1/5)*hf
  norm_num at hh

private lemma cell_2_42 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (20 - 12*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/2 - 3*z/20)*h0 + (-9/5)*hf
  norm_num at hh

private lemma cell_2_43 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 10) - 2*z + 20:ℝ)=0) (h1 : (16*t^8 + t^7*(-144*z - 320) + t^6*(5040*z + 320) + t^5*(44880 - 74320*z) + t^4*(595600*z - 539120) + t^3*(2972800 - 2790320*z) + t^2*(7622960*z - 8836000) + t*(13676400 - 11231200*z) + 6883200*z - 8647200:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(151*z/15250 - 1099/30500) + t^6*(3039/3050 - 8321*z/30500) + t^5*(48173*z/15250 - 35373/3050) + t^4*(449461/6100 - 60767*z/3050) + t^3*(450573*z/6100 - 168231/610) + t^2*(740519/1220 - 979731*z/6100) + t*(1152197*z/6100 - 221032/305) - 28049*z/305 + 219343/610)*h0 + (t*(1099/244000 - 151*z/122000) + 503*z/244000 - 73/9760)*h1 + (-1208*t^8/7625 + 45819*t^7/7625 - 147321*t^6/1525 + 13067061*t^5/15250 - 6974627*t^4/1525 + 45791653*t^3/3050 - 3606187*t^2/122 + 97191467*t/3050 - 876782/61)*hf
  norm_num at hh

private lemma cell_2_44 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 14*t + 22:ℝ)=0) (h1 : (16*t^8 + t^7*(112*z - 768) + t^6*(13408 - 2432*z) + t^5*(24160*z - 125216) + t^4*(691040 - 129760*z) + t^3*(382720*z - 2308576) + t^2*(4400208 - 454272*z) + t*(-374768*z - 3939968) + 1586240*z + 57856:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(14353/209000 - 3967*z/209000) + t^6*(343*z/500 - 1241/500) + t^5*(71569/1900 - 19781*z/1900) + t^4*(4488509*z/52250 - 649589/2090) + t^3*(15718787/10450 - 10861303*z/26125) + t^2*(123217249*z/104500 - 222905257/52250) + t*(1371751793/209000 - 379133963*z/209000) + 61042489*z/52250 - 22086734/5225)*h0 + (t*(3967*z/1672000 - 14353/1672000) - 19101*z/1672000 + 6911/167200)*h1 + (-27769*t^8/104500 + 736691*t^7/104500 - 404251*t^6/4750 + 3050744*t^5/5225 - 999199*t^4/418 + 142381746*t^3/26125 - 449396551*t^2/104500 - 840691103*t/104500 + 94683657/5225)*hf
  norm_num at hh

private lemma cell_2_45 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 4*t*z + 8*z - 10:ℝ)=0) (h1 : (16*t^8 + t^7*(-16*z - 320) + t^6*(720*z + 2080) + t^5*(-9840*z - 1520) + t^4*(71920*z - 55120) + t^3*(366400 - 322000*z) + t^2*(933360*z - 1208000) + t*(2246800 - 1658400*z) + 1537600*z - 2115200:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(733*z/9500 - 663/2375) + t^6*(9977/1900 - 3447*z/2375) + t^5*(5547*z/500 - 38131/950) + t^4*(60947/380 - 84229*z/1900) + t^3*(188363*z/1900 - 34073/95) + t^2*(168667/380 - 58284*z/475) + t*(145171*z/1900 - 26243/95) - 1673*z/95 + 12051/190)*h0 + (t*(663/19000 - 733*z/76000) + 141*z/76000 - 51/7600)*h1 + (733*t^8/4750 + 1309*t^7/2375 - 95601*t^6/2375 + 1058844*t^5/2375 - 1181721*t^4/475 + 3949856*t^3/475 - 15617251*t^2/950 + 8181793*t/475 - 257618/95)*hf
  norm_num at hh

private lemma cell_2_46 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 10) - 2*z + 20:ℝ)=0) (h1 : (16*t^8 + t^7*(48*z - 640) + t^6*(10640 - 1360*z) + t^5*(15920*z - 96320) + t^4*(521280 - 100320*z) + t^3*(369360*z - 1734000) + t^2*(3475600 - 797840*z) + t*(939600*z - 3852000) - 466400*z + 1812800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(8/1375 - 9*z/5500) + t^6*(321*z/5500 - 229/1100) + t^5*(859/275 - 4803*z/5500) + t^4*(3899*z/550 - 6989/275) + t^3*(26573/220 - 9249*z/275) + t^2*(102351*z/1100 - 18404/55) + t*(22003/44 - 76393*z/550) + 173*z/2 - 1559/5)*h0 + (t*(9*z/44000 - 1/1375) - 29*z/22000 + 41/8800)*h1 + (-18*t^8/1375 + 1251*t^7/2750 - 18367*t^6/2750 + 148327*t^5/2750 - 143483*t^4/550 + 211449*t^3/275 - 367287*t^2/275 + 338022*t/275 - 2209/5)*hf
  norm_num at hh

private lemma cell_2_47 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(10 - 2*z) + t*(4*z - 40) - 2*z + 40:ℝ)=0) (h1 : (t^8*(4400 - 1200*z) + t^7*(27600*z - 102400) + t^6*(1024000 - 270000*z) + t^5*(1446400*z - 5718800) + t^4*(19343600 - 4505600*z) + t^3*(7762800*z - 39943200) + t^2*(47591200 - 5395600*z) + t*(-2590800*z - 27511600) + 4558400*z + 4100800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(753*z/1900 - 109/76) + t^6*(10839/380 - 14973*z/1900) + t^5*(124907*z/1900 - 90449/380) + t^4*(20490/19 - 282807*z/950) + t^3*(39433*z/50 - 57193/20) + t^2*(841411/190 - 579219*z/475) + t*(1929341*z/1900 - 351269/95) - 17469*z/50 + 12779/10)*h0 + (t*(287/76000 - 79*z/76000) + 3*z/2375 - 349/76000)*h1 + (-216*t^9/475 + 6108*t^8/475 - 144139*t^7/950 + 921919*t^6/950 - 3430371*t^5/950 + 7193087*t^4/950 - 3290984*t^3/475 - 116923*t^2/38 + 2173473*t/190 - 3066951/475)*hf
  norm_num at hh

private lemma cell_2_48 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(10 - 2*z) - 2*t*z:ℝ)=0) (h1 : (t^8*(4400 - 1200*z) + t^7*(16000 - 4400*z) + t^6*(18400 - 5200*z) + t^5*(4400 - 1200*z) + t^4*(1600*z - 5200) + t^3*(400*z - 3200) - 800*t^2 + t*(400*z - 400):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(47/40 - 13*z/40) + t^5*(47/10 - 13*z/10) + t^4*(33/5 - 73*z/40) + t^3*(37/10 - 41*z/40) + t^2*(3/20 - z/20) + t*(11*z/40 - 21/20) + 3*z/20 - 27/40)*h0 + (7*z/8000 - 1/320)*h1 + (2*t^8/5 + 3*t^7/5 - 17*t^6/10 - 93*t^5/20 - 71*t^4/20 + t^3/10 + 17*t^2/20 - t/20)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_2_49 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(10 - 2*z) + t*(6*z - 30) - 6*z + 22:ℝ)=0) (h1 : (t^8*(4400 - 1200*z) + t^7*(8400*z - 30400) + t^6*(90800 - 25280*z) + t^5*(42160*z - 152000) + t^4*(153920 - 42080*z) + t^3*(25280*z - 94160) + t^2*(32720 - 9184*z) + t*(2416*z - 5760) - 480*z + 416:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(415*z/44 - 6007/176) + t^6*(3249/16 - 449*z/8) + t^5*(15563*z/110 - 5630/11) + t^4*(11265/16 - 15569*z/80) + t^3*(3069*z/20 - 44429/80) + t^2*(20659/88 - 14259*z/220) + t*(44987*z/4400 - 3251/88) + 151*z/200 - 123/40)*h0 + (t*(633/7040 - 109*z/4400) + 1823*z/35200 - 265/1408)*h1 + (-239*t^9/22 + 8923*t^8/88 - 169393*t^7/440 + 342671*t^6/440 - 99267*t^5/110 + 258529*t^4/440 - 454801*t^3/2200 + 38179*t^2/440 - 88219*t/1100 + 8082/275)*hf
  norm_num at hh

private lemma cell_2_50 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(10 - 2*z) - 4*t*z + 6*z - 8:ℝ)=0) (h1 : (t^8*(4400 - 1200*z) + t^7*(9600 - 2800*z) + t^6*(1200 - 80*z) + t^5*(2960*z - 7200) + t^4*(3120 - 3440*z) + t^3*(2640 - 2320*z) + t^2*(7456*z - 10320) + t*(3776*z - 5040) - 896*z + 1216:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(81*z/4 - 293/4) + t^6*(171*z/4 - 619/4) + t^5*(171*z/20 - 31) + t^4*(347/4 - 119*z/5) + t^3*(999/20 - 69*z/5) + t^2*(73/4 - 27*z/5) + t*(17/20 - 37*z/100) + 79*z/50 - 11/2)*h0 + (t*(31/160 - 43*z/800) + z/25 - 23/160)*h1 + (-24*t^9 + 64*t^8 + 1743*t^7/10 - 538*t^6/5 - 2387*t^5/5 + 897*t^4/10 + 27701*t^3/50 - 306*t^2/5 - 9533*t/50 + 659/25)*hf
  norm_num at hh

private lemma cell_2_51 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(6 - 4*z) + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(512 - 208*z) + t^6*(80*z + 1168) + t^5*(9104 - 3792*z) + t^4*(480*z + 6080) + t^3*(13264 - 4880*z) + t^2*(8768 - 4592*z) + t*(7440*z - 10688) - 4128*z + 5376:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-t^7*z/1000 + t^6*(7*z/250 - 3/50) + t^5*(-11*z/500 - 21/200) + t^4*(79*z/200 - 201/200) + t^3*(z/5 - 231/200) + t^2*(301*z/1000 - 251/200) + t*(417*z/1000 - 31/50) - 309*z/500 + 7/5)*h0 + (t*z/8000 - z/4000 + 1/1600)*h1 + (11*t^8/500 + t^7/20 + 203*t^6/500 + 143*t^5/250 + 153*t^4/100 + 279*t^3/500 - 41*t^2/100 - 12*t/125 - 129/125)*hf
  norm_num at hh

private lemma cell_2_52 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(10 - 2*z) + t*(6*z - 30) - 6*z + 22:ℝ)=0) (h1 : (t^8*(4400 - 1200*z) + t^7*(8400*z - 30400) + t^6*(79600 - 22080*z) + t^5*(26560*z - 95600) + t^4*(45920 - 12800*z) + t^3*(2640 - 960*z) + t^2*(1616*z - 6560) + t*(1760 - 624*z) + 128*z - 224:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(373/232 - 101*z/232) + t^6*(331*z/116 - 599/58) + t^5*(5329/232 - 927*z/145) + t^4*(6361*z/1160 - 1135/58) + t^3*(2881/1160 - 108*z/145) + t^2*(363/116 - 1157*z/1160) + t*(-363*z/5800 - 237/1160) - 559*z/2900 + 21/58)*h0 + (t*(23*z/46400 - 31/9280) - 21*z/23200 + 73/9280)*h1 + (-8*t^9/29 + 89*t^8/29 - 8103*t^7/580 + 19311*t^6/580 - 24571*t^5/580 + 7037*t^4/290 - 811*t^3/2900 - 2449*t^2/580 + 443*t/2900 - 1509/1450)*hf
  norm_num at hh

private lemma cell_2_53 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(10 - 2*z) + t*(14*z - 60) - 22*z + 80:ℝ)=0) (h1 : (t^8*(4400 - 1200*z) + t^7*(21200*z - 76800) + t^6*(571200 - 158000*z) + t^5*(656000*z - 2372400) + t^4*(6020400 - 1664000*z) + t^3*(2639600*z - 9552000) + t^2*(9247200 - 2555600*z) + t*(1379600*z - 4990800) - 317600*z + 1148800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(157/30 - 109*z/75) + t^6*(1682*z/75 - 811/10) + t^5*(2632/5 - 3636*z/25) + t^4*(76579*z/150 - 27713/15) + t^3*(113257/30 - 78259*z/75) + t^2*(185839*z/150 - 44817/10) + t*(28583/10 - 19753*z/25) + 31273*z/150 - 22639/30)*h0 + (t*(13*z/3000 - 29/2000) - 49*z/3000 + 331/6000)*h1 + (172*t^9/75 - 694*t^8/15 + 29558*t^7/75 - 28091*t^6/15 + 411853*t^5/75 - 772436*t^4/75 + 922991*t^3/75 - 673852*t^2/75 + 90207*t/25 - 15019/25)*hf
  norm_num at hh

private lemma cell_2_54 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(10 - 2*z) + t*(4*z - 30) - 2*z + 20:ℝ)=0) (h1 : (t^8*(4400 - 1200*z) + t^7*(10000*z - 36800) + t^6*(123200 - 33600*z) + t^5*(58800*z - 210400) + t^4*(190400 - 56000*z) + t^3*(21200*z - 76000) + t^2*(6000*z - 2800) + t*(1600*z - 800) - 800*z + 800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(11/8 - 19*z/50) + t^6*(143*z/50 - 207/20) + t^5*(587/20 - 811*z/100) + t^4*(2111*z/200 - 1527/40) + t^3*(429/20 - 1189*z/200) + t^2*(183*z/200 - 67/20) + t*(4*z/25 - 1/2) - 3*z/100 + 1/5)*h0 + (t*(z/1000 - 29/8000) - z/400 + 73/8000)*h1 + (11*t^9/25 - 144*t^8/25 + 1509*t^7/50 - 8353*t^6/100 + 13267*t^5/100 - 2862*t^4/25 + 3177*t^3/100 + 1453*t^2/100 + 131*t/25 - 103/50)*hf
  norm_num at hh

private lemma cell_2_55 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 10*t - 2*z + 10:ℝ)=0) (h1 : (16*t^8 - 80*t^7*z + t^6*(880*z - 1040) + t^5*(5680 - 3920*z) + t^4*(8960*z - 13120) + t^3*(14000 - 10160*z) + t^2*(2160*z - 2400) + t*(7600*z - 10400) - 6400*z + 8800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(137/7250 - 113*z/21750) + t^6*(114*z/3625 - 497/4350) + t^5*(242/2175 - 347*z/10875) + t^4*(1667/4350 - 83*z/870) + t^3*(191*z/2175 - 77/174) + t^2*(482*z/2175 - 539/870) + t*(241/870 - 68*z/725) - 137*z/870 + 57/145)*h0 + (t*(113*z/174000 - 137/58000) - 479*z/174000 + 343/34800)*h1 + (113*t^8/2175 - 8723*t^7/10875 + 18238*t^6/3625 - 60443*t^5/3625 + 22528*t^4/725 - 63502*t^3/2175 + 1054*t^2/725 + 54137*t/2175 - 269/15)*hf
  norm_num at hh

private lemma cell_2_56 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(10 - 2*z) - 4*t*z + 6*z - 8:ℝ)=0) (h1 : (t^8*(4400 - 1200*z) + t^7*(9600 - 2800*z) + t^6*(1520*z - 2000) + t^5*(1200 - 4240*z) + t^4*(21040*z - 30480) + t^3*(61840 - 44560*z) + t^2*(77056*z - 106400) + t*(107280 - 77504*z) + 54432*z - 75264:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(23433*z/3116 - 84781/3116) + t^6*(48337*z/3116 - 43722/779) + t^5*(6907/3116 - 4759*z/7790) + t^4*(39733/779 - 219737*z/15580) + t^3*(62942/3895 - 17321*z/3895) + t^2*(13197*z/15580 - 4977/1558) + t*(613*z/950 - 202/95) + 23433*z/38950 - 3611/1558)*h0 + (t*(8951/124640 - 12371*z/623200) + 4897*z/311600 - 1771/31160)*h1 + (-360*t^9/41 + 18994*t^8/779 + 350098*t^7/3895 - 1805577*t^6/7790 + 3292451*t^5/7790 - 217869*t^4/190 + 44038261*t^3/19475 - 21428717*t^2/7790 + 44735606*t/19475 - 16729893/19475)*hf
  norm_num at hh

private lemma cell_2_57 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(10 - 2*z) + t*(4*z - 30) - 2*z + 20:ℝ)=0) (h1 : (t^8*(4400 - 1200*z) + t^7*(10000*z - 36800) + t^6*(131200 - 35200*z) + t^5*(67200*z - 258400) + t^4*(298400 - 70400*z) + t^3*(28000*z - 188000) + t^2*(25200*z + 29200) + t*(39200 - 38000*z) + 14400*z - 19200:ℝ)=0) (h2 : (t^8*(4400 - 1200*z) + t^7*(10000*z - 36800) + t^6*(123200 - 33600*z) + t^5*(58800*z - 210400) + t^4*(190400 - 56000*z) + t^3*(21200*z - 76000) + t^2*(6000*z - 2800) + t*(1600*z - 800) - 800*z + 800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(7519/16400 - 10391*z/82000) + t^12*(128661*z/82000 - 931/164) + t^11*(102781/3280 - 710199*z/82000) + t^10*(574937*z/20500 - 832057/8200) + t^9*(3498773/16400 - 4835183*z/82000) + t^8*(6891633*z/82000 - 2493417/8200) + t^7*(4873217/16400 - 6734627*z/82000) + t^6*(224397*z/4100 - 811877/4100) + t^5*(1524697/16400 - 263369*z/10250) + t^4*(840653*z/82000 - 304083/8200) + t^3*(41643/3280 - 144491*z/41000) + t^2*(333*z/1000 - 247/200) + t*(11549*z/82000 - 3543/8200) - 289*z/20500 + 297/2050)*h0 + (t^7*(1097*z/3280000 - 3969/3280000) + t^6*(29299/3280000 - 4049*z/1640000) + t^5*(11309*z/1640000 - 81833/3280000) + t^4*(105121/3280000 - 5811*z/656000) + t^3*(3233*z/656000 - 58483/3280000) + t^2*(9127/3280000 - 1261*z/1640000) + t*(59/164000 - 327*z/3280000) + 237*z/3280000 - 431/1640000)*h1 + (11/2000 - 3*z/2000)*h2 + (758*t^15/5125 - 13644*t^14/5125 + 107036*t^13/5125 - 974717*t^12/10250 + 1431134*t^11/5125 - 11245109*t^10/20500 + 14434327*t^9/20500 - 10140789*t^8/20500 - 24777*t^7/500 + 10665731*t^6/20500 - 575738*t^5/1025 + 6013819*t^4/20500 - 77896*t^3/1025 + 74504*t^2/5125 + 35462*t/5125 - 11627/5125)*hf
  norm_num at hh

private lemma cell_2_58 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t^2*(10 - 2*z) - 6*t*z + 8*z - 10:ℝ)=0) (h1 : (t^8*(4400 - 1200*z) + t^7*(3200 - 1200*z) + t^6*(6000*z - 12800) + t^5*(19600 - 15200*z) + t^4*(32800*z - 43600) + t^3*(48000 - 34800*z) + t^2*(9200*z - 12800) + t*(10800*z - 14800) - 6400*z + 8800:ℝ)=0) : False := by
  have hh : ((t-(1)))*(1:ℝ)=0 := by linear_combination (t^6*(521*z/100 - 377/20) + t^5*(89*z/10 - 161/5) + t^4*(87*z/100 - 63/20) + t^3*(43/4 - 297*z/100) + t^2*(9/10 - z/4) + t*(1/10 - 3*z/100) - 9*z/50 + 3/5)*h0 + (199/4000 - 11*z/800)*h1 + (-152*t^8/25 + 814*t^7/25 + 2399*t^6/25 - 7023*t^5/25 + 10643*t^4/25 - 4563*t^3/10 + 3199*t^2/25 + 7383*t/50 - 2164/25)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn0
  norm_num at hv

private lemma cell_2_59 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(10 - 8*z) + 8*z - 10:ℝ)=0) (h1 : (16*t^8 + t^7*(640 - 336*z) + t^6*(3600*z - 4240) + t^5*(48480 - 34000*z) + t^4*(171520*z - 235520) + t^3*(766000 - 554000*z) + t^2*(1078160*z - 1490800) + t*(1588800 - 1150000*z) + 508800*z - 703200:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(83*z/19000 - 599/38000) + t^6*(937*z/19000 - 1367/7600) + t^5*(4413*z/19000 - 1557/1900) + t^4*(637*z/1520 - 6391/3800) + t^3*(1703*z/1900 - 3739/1520) + t^2*(139/152 - 411*z/475) + t*(8487*z/7600 - 827/1520) - 1147*z/760 + 288/95)*h0 + (t*(599/304000 - 83*z/152000) + 9*z/304000 - 1/15200)*h1 + (-1411*t^8/9500 + 44371*t^7/19000 - 326967*t^6/19000 + 1827041*t^5/19000 - 577169*t^4/1900 + 449191*t^3/760 - 2447291*t^2/3800 + 1105307*t/3800 - 284/95)*hf
  norm_num at hh

private lemma cell_2_60 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(6 - 4*z) + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(192 - 16*z) + t^6*(1248 - 304*z) + t^5*(4464 - 1440*z) + t^4*(8080 - 2320*z) + t^3*(9664 - 2480*z) + t^2*(10688 - 4384*z) + t*(1824*z - 1168) - 480*z + 416:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(-4*z/2375 - 13/7600) + t^6*(-217*z/19000 - 99/3800) + t^5*(1783*z/38000 - 123/475) + t^4*(2969*z/7600 - 2037/1900) + t^3*(1929*z/3800 - 3037/1900) + t^2*(8909*z/38000 - 857/760) + t*(42369*z/38000 - 483/304) - 21799*z/19000 + 198/95)*h0 + (t*(z/4750 + 13/60800) - 527*z/304000 + 29/12160)*h1 + (-8*t^8/2375 - 179*t^7/19000 - 687*t^6/19000 - 423*t^5/950 - 5583*t^4/3800 - 46331*t^3/19000 - 881*t^2/250 - 12599*t/9500 - 1581/1900)*hf
  norm_num at hh

private lemma cell_2_61 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 10*t - 2*z + 10:ℝ)=0) (h1 : (16*t^8 + t^7*(112*z - 320) + t^6*(1280 - 400*z) + t^5*(400*z - 2320) + t^4*(3280 - 560*z) + t^3*(1520*z - 4000) + t^2*(4000 - 2640*z) + t*(2400*z - 2800) - 800*z + 800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(3134*z/78375 - 23033/156750) + t^6*(4418/3135 - 61607*z/156750) + t^5*(10916*z/7125 - 5247/950) + t^4*(359369/31350 - 49103*z/15675) + t^3*(111527*z/31350 - 40789/3135) + t^2*(119/19 - 2567*z/1425) + t*(10361/6270 - 1366*z/5225) + 1129*z/2090 - 8159/3135)*h0 + (t*(23033/1254000 - 1567*z/313500) + 3217*z/156750 - 6319/83600)*h1 + (43876*t^8/78375 - 330584*t^7/78375 + 738493*t^6/78375 - 622628*t^5/78375 + 201038*t^4/15675 - 194767*t^3/5225 + 980854*t^2/15675 - 842956*t/15675 + 54859/3135)*hf
  norm_num at hh

private lemma cell_2_62 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(10 - 8*z) + 8*z - 10:ℝ)=0) (h1 : (16*t^8 + t^7*(320 - 144*z) + t^6*(80*z + 320) + t^5*(80*z + 880) + t^4*(6480 - 3600*z) + t^3*(2400 - 720*z) + t^2*(6160*z - 8000) + t*(2400*z - 3600) - 800*z + 800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(283*z/87000 - 339/29000) + t^6*(481*z/21750 - 176/2175) + t^5*(1547*z/21750 - 1481/5800) + t^4*(581*z/4350 - 689/1450) + t^3*(1853*z/17400 - 237/580) + t^2*(31/145 - 387*z/5800) + t*(303/290 - 1613*z/5800) - 39*z/145 + 1801/1740)*h0 + (t*(339/232000 - 283*z/696000) + 331*z/696000 - 19/11600)*h1 + (-283*t^8/8700 + 5479*t^7/21750 + 4204*t^6/10875 - 7267*t^5/7250 + 872*t^4/725 + 2119*t^3/1450 - 31709*t^2/8700 - 3031*t/2175 + 2203/870)*hf
  norm_num at hh

private lemma cell_2_63 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (_hn0 : t-(1)≠0) (_hn1 : t-(5 - z)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*t*z - 2*z + 10:ℝ)=0) (h1 : (t*(2400*z - 7200) - 12000*z + 40800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/10)*h0 + (1/2400 - z/4000)*h1 + (3*t/5 - 3)*hf
  norm_num at hh

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_0 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 0) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_0 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 14*z + 20:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_1 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 1) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_1 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 12*z + 12:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_2 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 2) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_2 z t hf hn0 hn1 hn2 hn3
  · have hr : (6*z^2 - 30*z + 32:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-6)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_3 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 3) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_3 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z - 14*t + 2*z^2 - 16*z + 32:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 + 224*t^7*z - 688*t^7 + 48*t^6*z^4 - 368*t^6*z^3 + 2224*t^6*z^2 - 7184*t^6*z + 12448*t^6 - 16*t^5*z^6 + 48*t^5*z^5 - 432*t^5*z^4 + 4784*t^5*z^3 - 30432*t^5*z^2 + 92640*t^5*z - 123936*t^5 + 112*t^4*z^7 - 1296*t^4*z^6 + 7952*t^4*z^5 - 26896*t^4*z^4 + 27120*t^4*z^3 + 154768*t^4*z^2 - 618160*t^4*z + 743120*t^4 - 16*t^3*z^9 + 144*t^3*z^8 - 1360*t^3*z^7 + 13728*t^3*z^6 - 90784*t^3*z^5 + 344672*t^3*z^4 - 630160*t^3*z^3 - 68512*t^3*z^2 + 2257680*t^3*z - 2742896*t^3 + 48*t^2*z^10 - 800*t^2*z^9 + 6784*t^2*z^8 - 34160*t^2*z^7 + 82128*t^2*z^6 + 90336*t^2*z^5 - 1206816*t^2*z^4 + 3088528*t^2*z^3 - 1937824*t^2*z^2 - 4313824*t^2*z + 6060608*t^2 - 32*t*z^11 + 336*t*z^10 + 480*t*z^9 - 28048*t*z^8 + 214784*t*z^7 - 797984*t*z^6 + 1335536*t*z^5 + 508144*t*z^4 - 5621888*t*z^3 + 6193264*t*z^2 + 3333584*t*z - 7235328*t + 192*z^11 - 3776*z^10 + 30288*z^9 - 117936*z^8 + 159696*z^7 + 414688*z^6 - 1846480*z^5 + 1672144*z^4 + 2721904*z^3 - 5371840*z^2 - 136960*z + 3526656:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 + 128*t^6*z - 1344*t^6 + 16*t^5*z^4 + 32*t^5*z^3 + 512*t^5*z^2 - 2384*t^5*z + 15952*t^5 - 112*t^4*z^5 + 736*t^4*z^4 - 3712*t^4*z^3 + 4656*t^4*z^2 + 14720*t^4*z - 104448*t^4 + 16*t^3*z^7 - 64*t^3*z^6 + 960*t^3*z^5 - 8608*t^3*z^4 + 42944*t^3*z^3 - 86912*t^3*z^2 - 19120*t^3*z + 407472*t^3 - 48*t^2*z^8 + 560*t^2*z^7 - 3744*t^2*z^6 + 12640*t^2*z^5 - 208*t^2*z^4 - 154576*t^2*z^3 + 434976*t^2*z^2 - 140768*t^2*z - 940896*t^2 + 32*t*z^9 - 176*t*z^8 - 1520*t*z^7 + 21328*t*z^6 - 100544*t*z^5 + 188624*t*z^4 + 110304*t*z^3 - 899744*t*z^2 + 571648*t*z + 1163696*t - 192*z^9 + 2816*z^8 - 15248*z^7 + 27616*z^6 + 54624*z^5 - 279648*z^4 + 175120*z^3 + 601696*z^2 - 589024*z - 581760)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_4 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 4) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_4 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 12*z + 12:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_5 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 5) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_5 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*z^3 + 24*z^2 - 90*z + 100:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z - 14)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_6 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 6) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_6 z t hf hn0 hn1 hn2 hn3
  · have hr : (-16*t*z^10 + 464*t*z^9 - 5696*t*z^8 + 38464*t*z^7 - 155616*t*z^6 + 386400*t*z^5 - 584000*t*z^4 + 520000*t*z^3 - 250000*t*z^2 + 50000*t*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(16*t*z^8 - 384*t*z^7 + 3696*t*z^6 - 18064*t*z^5 + 46816*t*z^4 - 62000*t*z^3 + 39920*t*z^2 - 10400*t*z - 1600*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_7 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 7) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_7 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 12*t*z + 10*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 224*t^7*z + 80*t^7 - 96*t^6*z^3 + 1120*t^6*z^2 - 1056*t^6*z + 480*t^6 + 336*t^5*z^4 - 4064*t^5*z^3 + 9072*t^5*z^2 - 8640*t^5*z + 2400*t^5 - 16*t^4*z^6 - 432*t^4*z^5 + 7472*t^4*z^4 - 24224*t^4*z^3 + 28720*t^4*z^2 - 12400*t^4*z + 2000*t^4 - 16*t^3*z^8 + 432*t^3*z^7 - 3600*t^3*z^6 + 10032*t^3*z^5 - 7184*t^3*z^4 - 13360*t^3*z^3 + 36800*t^3*z^2 - 34000*t^3*z + 10000*t^3 + 32*t^2*z^9 - 848*t^2*z^8 + 8176*t^2*z^7 - 35504*t^2*z^6 + 74832*t^2*z^5 - 69840*t^2*z^4 + 7600*t^2*z^3 + 26000*t^2*z^2 - 10000*t^2*z - 32*t*z^10 + 928*t*z^9 - 10736*t*z^8 + 64528*t*z^7 - 226416*t*z^6 + 491600*t*z^5 - 672000*t*z^4 + 562000*t*z^3 - 260000*t*z^2 + 50000*t*z - 32*z^10 + 640*z^9 - 4912*z^8 + 19280*z^7 - 42560*z^6 + 53600*z^5 - 36000*z^4 + 10000*z^3:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 96*t^6*z - 640*t^6 - 336*t^5*z^2 + 2384*t^5*z + 4528*t^5 + 16*t^4*z^4 + 512*t^4*z^3 - 4992*t^4*z^2 - 3296*t^4*z - 20240*t^4 + 16*t^3*z^6 - 352*t^3*z^5 + 1760*t^3*z^4 + 528*t^3*z^3 + 1024*t^3*z^2 + 15840*t^3*z + 37280*t^3 - 32*t^2*z^7 + 688*t^2*z^6 - 4576*t^2*z^5 + 9184*t^2*z^4 - 6032*t^2*z^3 - 6240*t^2*z^2 - 8640*t^2*z - 38000*t^2 + 32*t*z^8 - 768*t*z^7 + 6736*t*z^6 - 27008*t*z^5 + 57696*t*z^4 - 68080*t*z^3 + 43120*t*z^2 - 6000*t*z + 14400*t + 32*z^8 - 480*z^7 + 2352*z^6 - 5120*z^5 + 5200*z^4 - 2000*z^3)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_8 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 8) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_8 z t hf hn0 hn1 hn2 hn3
  · have hr : (6*z^2 - 30*z + 32:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-6)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_9 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 9) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_9 z t hf hn0 hn1 hn2 hn3
  · have hr : (-16*t*z^10 + 464*t*z^9 - 5696*t*z^8 + 38464*t*z^7 - 155616*t*z^6 + 386400*t*z^5 - 584000*t*z^4 + 520000*t*z^3 - 250000*t*z^2 + 50000*t*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(16*t*z^8 - 384*t*z^7 + 3696*t*z^6 - 18064*t*z^5 + 46816*t*z^4 - 62000*t*z^3 + 39920*t*z^2 - 10400*t*z - 1600*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_10 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (_hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 10) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : ((0:ℝ):ℝ)=0 := by
  apply cell_2_10 z t hf hn0 hn1 hn2 hn3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_11 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 11) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_11 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 + 10*t*z - 20*t + 8*z^2 - 40*z + 50:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 8)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 + 32*t^7*z - 560*t^7 + 96*t^6*z^3 - 512*t^6*z^2 - 1696*t^6*z + 9280*t^6 + 336*t^5*z^4 - 3520*t^5*z^3 + 6240*t^5*z^2 + 33600*t^5*z - 94000*t^5 - 16*t^4*z^6 + 976*t^4*z^5 - 12304*t^4*z^4 + 53344*t^4*z^3 - 23280*t^4*z^2 - 366000*t^4*z + 634000*t^4 - 16*t^3*z^8 + 304*t^3*z^7 - 1104*t^3*z^6 - 13264*t^3*z^5 + 128656*t^3*z^4 - 336880*t^3*z^3 - 265200*t^3*z^2 + 2490000*t^3*z - 2920000*t^3 - 32*t^2*z^9 + 784*t^2*z^8 - 6896*t^2*z^7 + 19472*t^2*z^6 + 68880*t^2*z^5 - 541200*t^2*z^4 + 574000*t^2*z^3 + 3470000*t^2*z^2 - 10750000*t^2*z + 9000000*t^2 - 32*t*z^10 + 896*t*z^9 - 10048*t*z^8 + 54656*t*z^7 - 121664*t*z^6 - 88960*t*z^5 + 528000*t*z^4 + 2640000*t*z^3 - 15300000*t*z^2 + 27200000*t*z - 17000000*t - 32*z^10 + 1120*z^9 - 16832*z^8 + 140160*z^7 - 687040*z^6 + 1851200*z^5 - 1440000*z^4 - 6800000*z^3 + 23500000*z^2 - 30500000*z + 15000000:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 - 96*t^6*z + 32*t^6 - 336*t^5*z^2 + 1840*t^5*z + 4640*t^5 + 16*t^4*z^4 - 896*t^4*z^3 + 7744*t^4*z^2 - 10144*t^4*z - 66160*t^4 + 16*t^3*z^6 - 224*t^3*z^5 - 96*t^3*z^4 + 13904*t^3*z^3 - 58656*t^3*z^2 - 25920*t^3*z + 428880*t^3 + 32*t^2*z^7 - 624*t^2*z^6 + 3616*t^2*z^5 + 1728*t^2*z^4 - 78320*t^2*z^3 + 140960*t^2*z^2 + 522400*t^2*z - 1562800*t^2 + 32*t*z^8 - 736*t*z^7 + 6208*t*z^6 - 19936*t*z^5 - 9056*t*z^4 + 143360*t*z^3 + 234080*t*z^2 - 2186400*t*z + 3197600*t + 32*z^8 - 960*z^7 + 11872*z^6 - 76000*z^5 + 247680*z^4 - 232800*z^3 - 962400*z^2 + 3152000*z - 2928000)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_12 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 12) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_12 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z - 14*t + 2*z^2 - 16*z + 32:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 224*t^7*z - 368*t^7 + 144*t^6*z^4 - 704*t^6*z^3 - 832*t^6*z^2 + 4352*t^6*z + 4208*t^6 + 112*t^5*z^6 - 624*t^5*z^5 - 1632*t^5*z^4 + 10912*t^5*z^3 + 6192*t^5*z^2 - 42288*t^5*z - 30016*t^5 + 32*t^4*z^8 - 32*t^4*z^7 - 2544*t^4*z^6 + 10384*t^4*z^5 + 13040*t^4*z^4 - 86208*t^4*z^3 - 48592*t^4*z^2 + 256720*t^4*z + 143920*t^4 + 112*t^3*z^9 - 1264*t^3*z^8 + 2640*t^3*z^7 + 14272*t^3*z^6 - 34160*t^3*z^5 - 180096*t^3*z^4 + 525360*t^3*z^3 + 230528*t^3*z^2 - 995200*t^3*z - 479696*t^3 + 112*t^2*z^10 - 1536*t^2*z^9 + 4768*t^2*z^8 + 23760*t^2*z^7 - 168208*t^2*z^6 + 152592*t^2*z^5 + 938384*t^2*z^4 - 1931664*t^2*z^3 - 698272*t^2*z^2 + 2411184*t^2*z + 1103888*t^2 + 32*t*z^11 - 240*t*z^10 - 4016*t*z^9 + 65792*t*z^8 - 378752*t*z^7 + 980064*t*z^6 - 566688*t*z^5 - 2441408*t*z^4 + 3879904*t*z^3 + 1354000*t*z^2 - 3368752*t*z - 1617088*t + 128*z^11 - 3264*z^10 + 35392*z^9 - 208384*z^8 + 691456*z^7 - 1112448*z^6 - 64896*z^5 + 2962432*z^4 - 2807680*z^3 - 1901504*z^2 + 2342208*z + 1115136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 - 16*t^6*z + 1472*t^6 - 112*t^5*z^4 + 64*t^5*z^3 + 2512*t^5*z^2 + 1328*t^5*z - 12112*t^5 - 32*t^4*z^6 - 128*t^4*z^5 + 2064*t^4*z^4 + 576*t^4*z^3 - 20480*t^4*z^2 - 19072*t^4*z + 55632*t^4 - 112*t^3*z^7 + 704*t^3*z^6 + 1440*t^3*z^5 - 10592*t^3*z^4 - 26000*t^3*z^3 + 103056*t^3*z^2 + 119920*t^3*z - 146208*t^3 - 112*t^2*z^8 + 976*t^2*z^7 + 672*t^2*z^6 - 25280*t^2*z^5 + 38448*t^2*z^4 + 166048*t^2*z^3 - 300384*t^2*z^2 - 400496*t^2*z + 197712*t^2 - 32*t*z^9 + 80*t*z^8 + 4576*t*z^7 - 43312*t*z^6 + 139312*t*z^5 - 66944*t*z^4 - 464592*t*z^3 + 453168*t*z^2 + 708896*t*z - 75360*t - 128*z^9 + 2624*z^8 - 21632*z^7 + 87104*z^6 - 147776*z^5 - 61952*z^4 + 494016*z^3 - 182592*z^2 - 575360*z - 62336)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_13 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 13) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_13 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 12*t*z + 10*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 224*t^7*z + 80*t^7 - 96*t^6*z^3 + 1120*t^6*z^2 - 1056*t^6*z + 480*t^6 + 336*t^5*z^4 - 4064*t^5*z^3 + 9072*t^5*z^2 - 8640*t^5*z + 2400*t^5 - 16*t^4*z^6 - 432*t^4*z^5 + 7472*t^4*z^4 - 24224*t^4*z^3 + 28720*t^4*z^2 - 12400*t^4*z + 2000*t^4 - 16*t^3*z^8 + 432*t^3*z^7 - 3600*t^3*z^6 + 10032*t^3*z^5 - 7184*t^3*z^4 - 13360*t^3*z^3 + 36800*t^3*z^2 - 34000*t^3*z + 10000*t^3 + 32*t^2*z^9 - 848*t^2*z^8 + 8176*t^2*z^7 - 35504*t^2*z^6 + 74832*t^2*z^5 - 69840*t^2*z^4 + 7600*t^2*z^3 + 26000*t^2*z^2 - 10000*t^2*z - 32*t*z^10 + 928*t*z^9 - 10736*t*z^8 + 64528*t*z^7 - 226416*t*z^6 + 491600*t*z^5 - 672000*t*z^4 + 562000*t*z^3 - 260000*t*z^2 + 50000*t*z - 32*z^10 + 640*z^9 - 4912*z^8 + 19280*z^7 - 42560*z^6 + 53600*z^5 - 36000*z^4 + 10000*z^3:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 96*t^6*z - 640*t^6 - 336*t^5*z^2 + 2384*t^5*z + 4528*t^5 + 16*t^4*z^4 + 512*t^4*z^3 - 4992*t^4*z^2 - 3296*t^4*z - 20240*t^4 + 16*t^3*z^6 - 352*t^3*z^5 + 1760*t^3*z^4 + 528*t^3*z^3 + 1024*t^3*z^2 + 15840*t^3*z + 37280*t^3 - 32*t^2*z^7 + 688*t^2*z^6 - 4576*t^2*z^5 + 9184*t^2*z^4 - 6032*t^2*z^3 - 6240*t^2*z^2 - 8640*t^2*z - 38000*t^2 + 32*t*z^8 - 768*t*z^7 + 6736*t*z^6 - 27008*t*z^5 + 57696*t*z^4 - 68080*t*z^3 + 43120*t*z^2 - 6000*t*z + 14400*t + 32*z^8 - 480*z^7 + 2352*z^6 - 5120*z^5 + 5200*z^4 - 2000*z^3)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_14 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 14) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_14 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 + 10*t*z - 20*t + 8*z^2 - 40*z + 50:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t - 8)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 + 32*t^7*z - 560*t^7 + 96*t^6*z^3 - 512*t^6*z^2 - 1696*t^6*z + 9280*t^6 + 336*t^5*z^4 - 3520*t^5*z^3 + 6240*t^5*z^2 + 33600*t^5*z - 94000*t^5 - 16*t^4*z^6 + 976*t^4*z^5 - 12304*t^4*z^4 + 53344*t^4*z^3 - 23280*t^4*z^2 - 366000*t^4*z + 634000*t^4 - 16*t^3*z^8 + 304*t^3*z^7 - 1104*t^3*z^6 - 13264*t^3*z^5 + 128656*t^3*z^4 - 336880*t^3*z^3 - 265200*t^3*z^2 + 2490000*t^3*z - 2920000*t^3 - 32*t^2*z^9 + 784*t^2*z^8 - 6896*t^2*z^7 + 19472*t^2*z^6 + 68880*t^2*z^5 - 541200*t^2*z^4 + 574000*t^2*z^3 + 3470000*t^2*z^2 - 10750000*t^2*z + 9000000*t^2 - 32*t*z^10 + 896*t*z^9 - 10048*t*z^8 + 54656*t*z^7 - 121664*t*z^6 - 88960*t*z^5 + 528000*t*z^4 + 2640000*t*z^3 - 15300000*t*z^2 + 27200000*t*z - 17000000*t - 32*z^10 + 1120*z^9 - 16832*z^8 + 140160*z^7 - 687040*z^6 + 1851200*z^5 - 1440000*z^4 - 6800000*z^3 + 23500000*z^2 - 30500000*z + 15000000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 - 96*t^6*z + 32*t^6 - 336*t^5*z^2 + 1840*t^5*z + 4640*t^5 + 16*t^4*z^4 - 896*t^4*z^3 + 7744*t^4*z^2 - 10144*t^4*z - 66160*t^4 + 16*t^3*z^6 - 224*t^3*z^5 - 96*t^3*z^4 + 13904*t^3*z^3 - 58656*t^3*z^2 - 25920*t^3*z + 428880*t^3 + 32*t^2*z^7 - 624*t^2*z^6 + 3616*t^2*z^5 + 1728*t^2*z^4 - 78320*t^2*z^3 + 140960*t^2*z^2 + 522400*t^2*z - 1562800*t^2 + 32*t*z^8 - 736*t*z^7 + 6208*t*z^6 - 19936*t*z^5 - 9056*t*z^4 + 143360*t*z^3 + 234080*t*z^2 - 2186400*t*z + 3197600*t + 32*z^8 - 960*z^7 + 11872*z^6 - 76000*z^5 + 247680*z^4 - 232800*z^3 - 962400*z^2 + 3152000*z - 2928000)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_15 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 15) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_15 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*t^2*z + 10*t^2 + 8*t*z - 40*t + 2*z^2 - 20*z + 50:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8*z^4 - 320*t^8*z^3 + 2400*t^8*z^2 - 8000*t^8*z + 10000*t^8 - 16*t^7*z^5 + 16*t^7*z^4 + 3680*t^7*z^3 - 37600*t^7*z^2 + 142000*t^7*z - 190000*t^7 - 64*t^6*z^6 + 1488*t^6*z^5 - 11504*t^6*z^4 + 16480*t^6*z^3 + 218400*t^6*z^2 - 1118000*t^6*z + 1610000*t^6 + 48*t^5*z^7 - 12864*t^5*z^5 + 130336*t^5*z^4 - 411920*t^5*z^3 - 441600*t^5*z^2 + 5092000*t^5*z - 7940000*t^5 + 80*t^4*z^8 - 1872*t^4*z^7 + 12064*t^4*z^6 + 32768*t^4*z^5 - 712640*t^4*z^4 + 2807600*t^4*z^3 - 1368000*t^4*z^2 - 14420000*t^4*z + 24850000*t^4 - 32*t^3*z^9 - 336*t^3*z^8 + 14480*t^3*z^7 - 114784*t^3*z^6 + 154032*t^3*z^5 + 2068240*t^3*z^4 - 10089600*t^3*z^3 + 10698000*t^3*z^2 + 25220000*t^3*z - 50350000*t^3 - 32*t^2*z^10 + 464*t^2*z^9 + 2560*t^2*z^8 - 89744*t^2*z^7 + 664512*t^2*z^6 - 1742160*t^2*z^5 - 1945600*t^2*z^4 + 19540000*t^2*z^3 - 27430000*t^2*z^2 - 25250000*t^2*z + 64250000*t^2 + 320*t*z^10 - 5200*t*z^9 + 20320*t*z^8 + 125040*t*z^7 - 1401840*t*z^6 + 4515360*t*z^5 - 2198000*t*z^4 - 18806000*t*z^3 + 33300000*t*z^2 + 11450000*t*z - 47000000*t + 160*z^11 - 3680*z^10 + 34720*z^9 - 161680*z^8 + 291120*z^7 + 551360*z^6 - 3452000*z^5 + 3960000*z^4 + 6530000*z^3 - 16000000*z^2 - 500000*z + 15000000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 + 240*t^8*z - 1120*t^8 + 16*t^7*z^3 + 64*t^7*z^2 - 3440*t^7*z + 20080*t^7 + 64*t^6*z^4 - 1168*t^6*z^3 + 5344*t^6*z^2 + 16080*t^6*z - 164720*t^6 - 48*t^5*z^5 - 240*t^5*z^4 + 11904*t^5*z^3 - 69616*t^5*z^2 + 4320*t^5*z + 811280*t^5 - 80*t^4*z^6 + 1472*t^4*z^5 - 4304*t^4*z^4 - 61648*t^4*z^3 + 425920*t^4*z^2 - 369760*t^4*z - 2610400*t^4 + 32*t^3*z^7 + 496*t^3*z^6 - 12160*t^3*z^5 + 51504*t^3*z^4 + 164288*t^3*z^3 - 1504320*t^3*z^2 + 1746560*t^3*z + 5556400*t^3 + 32*t^2*z^8 - 304*t^2*z^7 - 4240*t^2*z^6 + 70064*t^2*z^5 - 292992*t^2*z^4 - 73120*t^2*z^3 + 3044960*t^2*z^2 - 3949600*t^2*z - 7542800*t^2 - 320*t*z^8 + 3600*t*z^7 - 720*t*z^6 - 146640*t*z^5 + 672240*t*z^4 - 420960*t*z^3 - 3268000*t*z^2 + 4570800*t*z + 5894000*t - 160*z^9 + 2880*z^8 - 19520*z^7 + 49680*z^6 + 54880*z^5 - 525360*z^4 + 550800*z^3 + 1420800*z^2 - 2180000*z - 2004000)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_16 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 16) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_16 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4*z^3 + 52*z^2 - 220*z + 300:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4*z - 32)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_17 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 17) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_17 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*z^3 + 26*z^2 - 106*z + 132:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z - 16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_18 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 18) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_18 z t hf hn0 hn1 hn2 hn3
  · have hr : (-6*z^3 + 76*z^2 - 294*z + 352:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(6*z - 46)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_19 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 19) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_19 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 + 20*t*z - 54*t - 4*z^3 + 54*z^2 - 240*z + 352:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t + 4*z - 34)*hf
  · have hr : (16*t^8 - 112*t^7*z^2 + 800*t^7*z - 1968*t^7 + 288*t^6*z^4 - 4128*t^6*z^3 + 25920*t^6*z^2 - 79648*t^6*z + 102368*t^6 - 320*t^5*z^6 + 6912*t^5*z^5 - 71712*t^5*z^4 + 434624*t^5*z^3 - 1585536*t^5*z^2 + 3254208*t^5*z - 2934176*t^5 + 128*t^4*z^8 - 3712*t^4*z^7 + 57584*t^4*z^6 - 567408*t^4*z^5 + 3697328*t^4*z^4 - 15939616*t^4*z^3 + 43955856*t^4*z^2 - 70605680*t^4*z + 50605520*t^4 - 4176*t^3*z^8 + 120688*t^3*z^7 - 1656192*t^3*z^6 + 13827408*t^3*z^5 - 75666944*t^3*z^4 + 274851856*t^3*z^3 - 642318144*t^3*z^2 + 878737200*t^3*z - 537491696*t^3 - 32*t^2*z^10 + 1024*t^2*z^9 + 35728*t^2*z^8 - 1329648*t^2*z^7 + 18407824*t^2*z^6 - 145804848*t^2*z^5 + 736142768*t^2*z^4 - 2431066832*t^2*z^3 + 5122614608*t^2*z^2 - 6286609680*t^2*z + 3435609088*t^2 + 592*t*z^10 - 18736*t*z^9 - 3328*t*z^8 + 5519424*t*z^7 - 87250528*t*z^6 + 697264096*t*z^5 - 3409455744*t*z^4 + 10680812608*t*z^3 - 21077905264*t*z^2 + 24013931728*t*z - 12102894848*t - 2496*z^10 + 78784*z^9 - 577088*z^8 - 6124352*z^7 + 144532288*z^6 - 1234169280*z^5 + 6043921216*z^4 - 18464728512*z^3 + 35002892672*z^2 - 37916828928*z + 18031005696:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(112*t^7 - 288*t^6*z^2 + 2688*t^6*z - 11040*t^6 + 320*t^5*z^4 - 5312*t^5*z^3 + 43552*t^5*z^2 - 190304*t^5*z + 416256*t^5 - 128*t^4*z^6 + 3072*t^4*z^5 - 41584*t^4*z^4 + 344128*t^4*z^3 - 1768768*t^4*z^2 + 5375136*t^4*z - 8236336*t^4 + 4176*t^3*z^6 - 99808*t^3*z^5 + 1136272*t^3*z^4 - 7647008*t^3*z^3 + 31750544*t^3*z^2 - 77864096*t^3*z + 94244944*t^3 + 32*t^2*z^8 - 864*t^2*z^7 - 40208*t^2*z^6 + 1132928*t^2*z^5 - 12542144*t^2*z^4 + 77429488*t^2*z^3 - 286284608*t^2*z^2 + 612496352*t^2*z - 628709808*t^2 - 592*t*z^8 + 15776*t*z^7 + 85168*t*z^6 - 5172464*t*z^5 + 60962368*t*z^4 - 366589936*t*z^3 + 1271694224*t*z^2 - 2489391808*t*z + 2272475104*t + 2496*z^8 - 66304*z^7 + 233088*z^6 + 7621312*z^5 - 107591168*z^4 + 658106880*z^3 - 2215430976*z^2 + 4097039232*z - 3440541632)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_20 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 20) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_20 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*z^3 + 26*z^2 - 106*z + 132:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z - 16)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_21 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 21) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_21 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*z^3 + 22*z^2 - 72*z + 60:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z - 12)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_22 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 22) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_22 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*z^3 + 34*z^2 - 142*z + 160:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z - 24)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_23 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 23) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_23 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 6*t*z - 30*t - 2*z^3 + 26*z^2 - 112*z + 160:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z - 16)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 + 352*t^7*z - 1200*t^7 + 48*t^6*z^4 - 720*t^6*z^3 + 5744*t^6*z^2 - 22320*t^6*z + 39200*t^6 - 16*t^5*z^6 + 384*t^5*z^5 - 5616*t^5*z^4 + 46336*t^5*z^3 - 226176*t^5*z^2 + 608160*t^5*z - 730400*t^5 - 16*t^4*z^7 + 1136*t^4*z^6 - 20848*t^4*z^5 + 206096*t^4*z^4 - 1228432*t^4*z^3 + 4473424*t^4*z^2 - 9249840*t^4*z + 8507600*t^4 - 64*t^3*z^8 + 2192*t^3*z^7 - 43152*t^3*z^6 + 504208*t^3*z^5 - 3684992*t^3*z^4 + 17204656*t^3*z^3 - 50333920*t^3*z^2 + 84786000*t^3*z - 63494000*t^3 + 16*t^2*z^9 + 880*t^2*z^8 - 35456*t^2*z^7 + 584496*t^2*z^6 - 5583936*t^2*z^5 + 33783264*t^2*z^4 - 132206992*t^2*z^3 + 326746880*t^2*z^2 - 466926400*t^2*z + 296344000*t^2 + 80*t*z^10 - 2592*t*z^9 + 27248*t*z^8 - 20720*t*z^7 - 2235408*t*z^6 + 25233200*t*z^5 - 146107072*t*z^4 + 517013360*t*z^3 - 1132411600*t*z^2 + 1422050000*t*z - 788960000*t - 480*z^10 + 14976*z^9 - 181424*z^8 + 949840*z^7 + 326208*z^6 - 35166496*z^5 + 230484832*z^4 - 793091440*z^3 + 1609956800*z^2 - 1834976000*z + 913920000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 + 480*t^6*z - 3104*t^6 + 16*t^5*z^4 - 304*t^5*z^3 + 4016*t^5*z^2 - 24736*t^5*z + 82416*t^5 + 16*t^4*z^5 - 1056*t^4*z^4 + 15488*t^4*z^3 - 123376*t^4*z^2 + 534112*t^4*z - 1185984*t^4 + 64*t^3*z^6 - 1872*t^3*z^5 + 33472*t^3*z^4 - 327488*t^3*z^3 + 1880192*t^3*z^2 - 6166256*t^3*z + 10101680*t^3 - 16*t^2*z^7 - 960*t^2*z^6 + 30736*t^2*z^5 - 426016*t^2*z^4 + 3300176*t^2*z^3 - 15152304*t^2*z^2 + 39944592*t^2*z - 51262400*t^2 - 80*t*z^8 + 2192*t*z^7 - 15888*t*z^6 - 69680*t*z^5 + 1966448*t*z^4 - 15052560*t*z^3 + 61012032*t*z^2 - 136690400*t*z + 143899440*t + 480*z^8 - 12576*z^7 + 116144*z^6 - 306240*z^5 - 2438128*z^4 + 24507056*z^3 - 95758912*z^2 + 191761600*z - 172354240)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_24 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 24) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_24 z t hf hn0 hn1 hn2 hn3
  · have hr : (-6*z^3 + 76*z^2 - 294*z + 352:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(6*z - 46)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_25 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 25) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_25 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*z^3 + 34*z^2 - 142*z + 160:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z - 24)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_26 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 26) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_26 z t hf hn0 hn1 hn2 hn3
  · have hr : (-10*z^3 + 110*z^2 - 382*z + 410:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(10*z - 60)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_27 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 27) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_27 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z^2 + 28*t*z - 60*t - 6*z^3 + 80*z^2 - 322*z + 410:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4*t + 6*z - 50)*hf
  · have hr : (16*t^8 - 176*t^7*z^2 + 1056*t^7*z - 2160*t^7 + 720*t^6*z^4 - 8640*t^6*z^3 + 45120*t^6*z^2 - 115200*t^6*z + 122800*t^6 - 1296*t^5*z^6 + 23328*t^5*z^5 - 200064*t^5*z^4 + 1001088*t^5*z^3 - 3017616*t^5*z^2 + 5124960*t^5*z - 3826400*t^5 + 864*t^4*z^8 - 20736*t^4*z^7 + 262064*t^4*z^6 - 2104432*t^4*z^5 + 11224240*t^4*z^4 - 39777184*t^4*z^3 + 90467024*t^4*z^2 - 120131440*t^4*z + 71279600*t^4 - 28864*t^3*z^8 + 692816*t^3*z^7 - 7853328*t^3*z^6 + 54059728*t^3*z^5 - 243976336*t^3*z^4 + 731784304*t^3*z^3 - 1414188720*t^3*z^2 + 1601932400*t^3*z - 812022000*t^3 - 96*t^2*z^10 + 2784*t^2*z^9 + 323872*t^2*z^8 - 8364656*t^2*z^7 + 92867408*t^2*z^6 - 602914032*t^2*z^5 + 2511441552*t^2*z^4 - 6862181712*t^2*z^3 + 11981971280*t^2*z^2 - 12196260400*t^2*z + 5531114000*t^2 + 1712*t*z^10 - 49648*t*z^9 - 1345792*t*z^8 + 42832448*t*z^7 - 486239712*t*z^6 + 3093658336*t*z^5 - 12360281664*t*z^4 + 31938163520*t*z^3 - 52198629200*t*z^2 + 49344410000*t*z - 20652520000*t - 7392*z^10 + 214368*z^9 + 1335680*z^8 - 77512000*z^7 + 938101760*z^6 - 5990839168*z^5 + 23467052992*z^4 - 58620687040*z^3 + 91684056800*z^2 - 82278636000*z + 32476920000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(176*t^7 - 720*t^6*z^2 + 5040*t^6*z - 16320*t^6 + 1296*t^5*z^4 - 16848*t^5*z^3 + 109344*t^5*z^2 - 370128*t^5*z + 620256*t^5 - 864*t^4*z^6 + 16416*t^4*z^5 - 175664*t^4*z^4 + 1144032*t^4*z^3 - 4625760*t^4*z^2 + 10928224*t^4*z - 12697104*t^4 + 28864*t^3*z^6 - 548496*t^3*z^5 + 4966528*t^3*z^4 - 26484608*t^3*z^3 + 86720656*t^3*z^2 - 165757984*t^3*z + 151795520*t^3 + 96*t^2*z^8 - 2304*t^2*z^7 - 335872*t^2*z^6 + 6696816*t^2*z^5 - 57703968*t^2*z^4 + 280910112*t^2*z^3 - 818371152*t^2*z^2 + 1365775392*t^2*z - 1061238560*t^2 - 1712*t*z^8 + 41088*t*z^7 + 1559792*t*z^6 - 35238928*t*z^5 + 302246112*t*z^4 - 1406233136*t*z^3 + 3817885424*t*z^2 - 5817570720*t*z + 4021348480*t + 7392*z^8 - 177408*z^7 - 2259680*z^6 + 67100640*z^5 - 591300160*z^4 + 2698835168*z^3 - 7016376352*z^2 + 10044629440*z - 6379027840)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_28 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 28) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_28 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z^2 + 20*t*z - 54*t - 4*z^3 + 54*z^2 - 240*z + 352:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t + 4*z - 34)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 + 352*t^7*z - 1648*t^7 + 336*t^6*z^3 + 2128*t^6*z^2 - 32592*t^6*z + 74928*t^6 + 2928*t^5*z^4 - 2768*t^5*z^3 - 240624*t^5*z^2 + 1311120*t^5*z - 1966656*t^5 - 16*t^4*z^6 + 13824*t^4*z^5 - 80944*t^4*z^4 - 848480*t^4*z^3 + 9194896*t^4*z^2 - 29701600*t^4*z + 32622320*t^4 - 16*t^3*z^8 + 144*t^3*z^7 + 36288*t^3*z^6 - 346368*t^3*z^5 - 1639136*t^3*z^4 + 34971728*t^3*z^3 - 181195264*t^3*z^2 + 408905120*t^3*z - 350332496*t^3 - 112*t^2*z^9 + 1888*t^2*z^8 + 41584*t^2*z^7 - 579104*t^2*z^6 - 2846784*t^2*z^5 + 83810736*t^2*z^4 - 586405904*t^2*z^3 + 1992060800*t^2*z^2 - 3416343472*t^2*z + 2378260368*t^2 - 176*t*z^10 + 3088*t*z^9 + 21952*t*z^8 - 411248*t*z^7 - 5039472*t*z^6 + 126858944*t*z^5 - 1046647968*t*z^4 + 4609061968*t*z^3 - 11645145152*t*z^2 + 16005115472*t*z - 9323817408*t - 1760*z^10 + 58096*z^9 - 572560*z^8 - 1448080*z^7 + 79672960*z^6 - 793122736*z^5 + 4263121584*z^4 - 14012416880*z^3 + 28273003200*z^2 - 32347454400*z + 16139160576:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 - 336*t^6*z - 3808*t^6 - 2928*t^5*z^2 - 11872*t^5*z + 195904*t^5 + 16*t^4*z^4 - 13744*t^4*z^3 + 12144*t^4*z^2 + 977920*t^4*z - 4366016*t^4 + 16*t^3*z^6 - 64*t^3*z^5 - 36688*t^3*z^4 + 163248*t^3*z^3 + 2638816*t^3*z^2 - 22593888*t^3*z + 55031744*t^3 + 112*t^2*z^7 - 1328*t^2*z^6 - 48784*t^2*z^5 + 341824*t^2*z^4 + 4799824*t^2*z^3 - 61520736*t^2*z^2 + 254803104*t^2*z - 410441600*t^2 + 176*t*z^8 - 2208*t*z^7 - 33872*t*z^6 + 252928*t*z^5 + 6473472*t*z^4 - 95756224*t*z^3 + 535499488*t*z^2 - 1452783408*t*z + 1703730672*t + 1760*z^8 - 49296*z^7 + 317280*z^6 + 3280960*z^5 - 64854560*z^4 + 452445136*z^3 - 1676623104*z^2 + 3367075680*z - 3054509280)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_29 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 29) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_29 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 6*t*z - 30*t - 2*z^3 + 26*z^2 - 112*z + 160:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z - 16)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 96*t^7*z - 880*t^7 + 144*t^6*z^4 - 160*t^6*z^3 - 4032*t^6*z^2 + 4000*t^6*z + 22000*t^6 + 112*t^5*z^6 + 192*t^5*z^5 - 7152*t^5*z^4 + 4896*t^5*z^3 + 92064*t^5*z^2 - 71040*t^5*z - 326400*t^5 + 32*t^4*z^8 + 480*t^4*z^7 - 5360*t^4*z^6 - 8848*t^4*z^5 + 145840*t^4*z^4 - 39808*t^4*z^3 - 1224176*t^4*z^2 + 677360*t^4*z + 3143600*t^4 + 224*t^3*z^9 - 816*t^3*z^8 - 16208*t^3*z^7 + 83792*t^3*z^6 + 215152*t^3*z^5 - 1640656*t^3*z^4 - 161840*t^3*z^3 + 10074080*t^3*z^2 - 3474800*t^3*z - 20138000*t^3 + 544*t^2*z^10 - 6016*t^2*z^9 - 1232*t^2*z^8 + 227760*t^2*z^7 - 579760*t^2*z^6 - 2497584*t^2*z^5 + 10476992*t^2*z^4 + 4789168*t^2*z^3 - 50860720*t^2*z^2 + 7323600*t^2*z + 83834000*t^2 + 544*t*z^11 - 8384*t*z^10 + 27328*t*z^9 + 206448*t*z^8 - 1603440*t*z^7 + 1668928*t*z^6 + 13576080*t*z^5 - 34355648*t*z^4 - 31578960*t*z^3 + 146383600*t*z^2 + 7510000*t*z - 207240000*t + 192*z^12 - 3552*z^11 + 17760*z^10 + 66976*z^9 - 1012880*z^8 + 3311536*z^7 + 1504544*z^6 - 30589312*z^5 + 42371392*z^4 + 76665360*z^3 - 189559200*z^2 - 42856000*z + 232320000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 - 560*t^6*z + 1952*t^6 - 112*t^5*z^4 - 752*t^5*z^3 + 3952*t^5*z^2 + 18624*t^5*z - 18704*t^5 - 32*t^4*z^6 - 640*t^4*z^5 + 2320*t^4*z^4 + 23648*t^4*z^3 - 39200*t^4*z^2 - 274432*t^4*z + 48016*t^4 - 224*t^3*z^7 - 304*t^3*z^6 + 15808*t^3*z^5 - 3232*t^3*z^4 - 310352*t^3*z^3 + 105056*t^3*z^2 + 2238880*t^3*z + 595040*t^3 - 544*t^2*z^8 + 3296*t^2*z^7 + 20432*t^2*z^6 - 142080*t^2*z^5 - 232800*t^2*z^4 + 2043984*t^2*z^3 + 906928*t^2*z^2 - 10474448*t^2*z - 6046160*t^2 - 544*t*z^9 + 5664*t*z^8 + 3712*t*z^7 - 216208*t*z^6 + 503840*t*z^5 + 1931312*t*z^4 - 6438720*t*z^3 - 7494512*t*z^2 + 26300000*t*z + 22588960*t - 192*z^10 + 2592*z^9 - 3840*z^8 - 99136*z^7 + 536400*z^6 - 133856*z^5 - 4855824*z^4 + 6979472*z^3 + 16805088*z^2 - 27537280*z - 32152640)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_30 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 30) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_30 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z^2 + 28*t*z - 60*t - 6*z^3 + 80*z^2 - 322*z + 410:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4*t + 6*z - 50)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 + 608*t^7*z - 1840*t^7 + 48*t^6*z^4 - 1424*t^6*z^3 + 14416*t^6*z^2 - 61040*t^6*z + 92800*t^6 - 16*t^5*z^6 + 1056*t^5*z^5 - 21600*t^5*z^4 + 207536*t^5*z^3 - 1040736*t^5*z^2 + 2642160*t^5*z - 2684400*t^5 - 272*t^4*z^7 + 11376*t^4*z^6 - 199408*t^4*z^5 + 1902320*t^4*z^4 - 10683600*t^4*z^3 + 35366224*t^4*z^2 - 63952240*t^4*z + 48755600*t^4 + 32*t^3*z^9 - 2544*t^3*z^8 + 75200*t^3*z^7 - 1183344*t^3*z^6 + 11293232*t^3*z^5 - 68889424*t^3*z^4 + 271043168*t^3*z^3 - 666923920*t^3*z^2 + 934563600*t^3*z - 569576000*t^3 + 192*t^2*z^10 - 11120*t^2*z^9 + 286048*t^2*z^8 - 4294064*t^2*z^7 + 41632176*t^2*z^6 - 272427936*t^2*z^5 + 1219060416*t^2*z^4 - 3685415792*t^2*z^3 + 7207394480*t^2*z^2 - 8236968400*t^2*z + 4178744000*t^2 + 352*t*z^11 - 20256*t*z^10 + 526080*t*z^9 - 8132320*t*z^8 + 83088080*t*z^7 - 588905072*t*z^6 + 2953924256*t*z^5 - 10484059520*t*z^4 + 25799556400*t*z^3 - 41919938000*t*z^2 + 40472960000*t*z - 17589000000*t + 192*z^12 - 12192*z^11 + 345952*z^10 - 5830512*z^9 + 65228400*z^8 - 511544592*z^7 + 2888571712*z^6 - 11848413232*z^5 + 35070129712*z^4 - 73101116240*z^3 + 101907876800*z^2 - 85342156000*z + 32476920000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 + 1184*t^6*z - 8256*t^6 + 16*t^5*z^4 - 976*t^5*z^3 + 16640*t^5*z^2 - 119456*t^5*z + 360256*t^5 + 272*t^4*z^5 - 10016*t^4*z^4 + 147968*t^4*z^3 - 1112400*t^4*z^2 + 4381760*t^4*z - 7895424*t^4 - 32*t^3*z^7 + 2384*t^3*z^6 - 63120*t^3*z^5 + 855824*t^3*z^4 - 6698512*t^3*z^3 + 31117744*t^3*z^2 - 81961888*t^3*z + 101525760*t^3 - 192*t^2*z^8 + 10160*t^2*z^7 - 234288*t^2*z^6 + 3071824*t^2*z^5 - 25101616*t^2*z^4 + 131560736*t^2*z^3 - 435748656*t^2*z^2 + 848868832*t^2*z - 784307040*t^2 - 352*t*z^9 + 18496*t*z^8 - 431840*t*z^7 + 5880640*t*z^6 - 51525680*t*z^5 + 301873472*t*z^4 - 1186928496*t*z^3 + 3040049680*t*z^2 - 4664665520*t*z + 3396362000*t - 192*z^10 + 11232*z^9 - 288832*z^8 + 4330192*z^7 - 42133280*z^6 + 279227232*z^5 - 1281769152*z^4 + 4043431312*z^3 - 8444127392*z^2 + 10663322720*z - 6370626240)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_31 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 31) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_31 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*t^2*z + 10*t^2 - 4*t*z^2 + 44*t*z - 120*t - 4*z^3 + 56*z^2 - 262*z + 410:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4*t + 4*z - 36)*hf
  · have hr : (16*t^8*z^4 - 320*t^8*z^3 + 2400*t^8*z^2 - 8000*t^8*z + 10000*t^8 + 112*t^7*z^5 - 3056*t^7*z^4 + 33120*t^7*z^3 - 178400*t^7*z^2 + 478000*t^7*z - 510000*t^7 + 288*t^6*z^6 - 10896*t^6*z^5 + 163920*t^6*z^4 - 1276000*t^6*z^3 + 5472000*t^6*z^2 - 12330000*t^6*z + 11450000*t^6 + 320*t^5*z^7 - 18208*t^5*z^6 + 384048*t^5*z^5 - 4161632*t^5*z^4 + 25759840*t^5*z^3 - 92512800*t^5*z^2 + 180206000*t^5*z - 147820000*t^5 + 112*t^4*z^8 - 13840*t^4*z^7 + 448288*t^4*z^6 - 6867104*t^4*z^5 + 59352544*t^4*z^4 - 307772880*t^4*z^3 + 954201600*t^4*z^2 - 1637272000*t^4*z + 1200290000*t^4 - 48*t^3*z^9 - 2528*t^3*z^8 + 228432*t^3*z^7 - 5598768*t^3*z^6 + 69358032*t^3*z^5 - 505047648*t^3*z^4 + 2265940160*t^3*z^3 - 6191375200*t^3*z^2 + 9489114000*t^3*z - 6277030000*t^3 - 32*t^2*z^10 + 1856*t^2*z^9 + 10768*t^2*z^8 - 1765120*t^2*z^7 + 37602352*t^2*z^6 - 401295360*t^2*z^5 + 2552003408*t^2*z^4 - 10134991760*t^2*z^3 + 24786315200*t^2*z^2 - 34307574000*t^2*z + 20644330000*t^2 + 592*t*z^10 - 22720*t*z^9 + 110320*t*z^8 + 6001424*t*z^7 - 127816736*t*z^6 + 1237426128*t*z^5 - 7071552064*t*z^4 + 25316868880*t*z^3 - 56122793600*t*z^2 + 70806702000*t*z - 39033640000*t - 2496*z^10 + 81984*z^9 - 667408*z^8 - 6268816*z^7 + 169473440*z^6 - 1568438080*z^5 + 8267811712*z^4 - 27120201040*z^3 + 55108548800*z^2 - 63897516000*z + 32476920000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 + 240*t^8*z - 1120*t^8 - 112*t^7*z^3 + 2496*t^7*z^2 - 20080*t^7*z + 65520*t^7 - 288*t^6*z^4 + 9456*t^6*z^3 - 115200*t^6*z^2 + 652720*t^6*z - 1632400*t^6 - 320*t^5*z^5 + 16608*t^5*z^4 - 299408*t^5*z^3 + 2581552*t^5*z^2 - 11355040*t^5*z + 22829840*t^5 - 112*t^4*z^6 + 13280*t^4*z^5 - 381328*t^4*z^4 + 4894064*t^4*z^3 - 32975584*t^4*z^2 + 118424640*t^4*z - 197200480*t^4 + 48*t^3*z^7 + 2768*t^3*z^6 - 214832*t^3*z^5 + 4510768*t^3*z^4 - 45730032*t^3*z^3 + 253843648*t^3*z^2 - 768071760*t^3*z + 1081798160*t^3 + 32*t^2*z^8 - 1696*t^2*z^7 - 19408*t^2*z^6 + 1676560*t^2*z^5 - 29122512*t^2*z^4 + 247300000*t^2*z^3 - 1169890848*t^2*z^2 + 3049037520*t^2*z - 3691673360*t^2 - 592*t*z^8 + 19760*t*z^7 - 8560*t*z^6 - 6143024*t*z^5 + 97144416*t*z^4 - 720988928*t*z^3 + 2980885344*t*z^2 - 6807497520*t*z + 7180879280*t + 2496*z^8 - 69504*z^7 + 307408*z^6 + 8153376*z^5 - 130243600*z^4 + 876453200*z^3 - 3234327712*z^2 + 6566296480*z - 6105427840)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_32 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 32) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_32 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*z^2 + 10*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_33 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 33) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_33 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*z^3 + 18*z^2 - 46*z + 32:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z - 8)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_34 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 34) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_34 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 12*z^2 + 16*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_35 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 35) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_35 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z - 4*t - 4*z^2 + 20*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*t)*hf
  · have hr : (16*t^8 + 16*t^7*z^2 - 160*t^7*z - 368*t^7 - 48*t^6*z^3 + 16*t^6*z^2 + 3632*t^6*z + 3568*t^6 + 48*t^5*z^4 + 656*t^5*z^3 - 4560*t^5*z^2 - 34512*t^5*z - 18976*t^5 - 16*t^4*z^6 + 256*t^4*z^5 - 2608*t^4*z^4 + 4192*t^4*z^3 + 40656*t^4*z^2 + 186720*t^4*z + 57520*t^4 - 16*t^3*z^8 + 400*t^3*z^7 - 3840*t^3*z^6 + 18272*t^3*z^5 - 37184*t^3*z^4 + 24464*t^3*z^3 - 232704*t^3*z^2 - 595200*t^3*z - 91696*t^3 + 16*t^2*z^9 - 224*t^2*z^8 - 272*t^2*z^7 + 20576*t^2*z^6 - 146112*t^2*z^5 + 443760*t^2*z^4 - 613904*t^2*z^3 + 1126400*t^2*z^2 + 931280*t^2*z + 73488*t^2 + 16*t*z^10 - 592*t*z^9 + 8384*t*z^8 - 58384*t*z^7 + 206512*t*z^6 - 295168*t*z^5 - 188256*t*z^4 + 955056*t*z^3 - 2106720*t*z^2 - 591952*t*z - 26048*t - 32*z^10 + 1168*z^9 - 16976*z^8 + 127152*z^7 - 529216*z^6 + 1209872*z^5 - 1348560*z^4 + 485584*z^3 + 1016896*z^2 + 100192*z + 2496:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^7 + 48*t^6*z + 224*t^6 - 48*t^5*z^2 - 896*t^5*z + 320*t^5 + 16*t^4*z^4 - 176*t^4*z^3 + 1648*t^4*z^2 + 4928*t^4*z - 24256*t^4 + 16*t^3*z^6 - 320*t^3*z^5 + 2160*t^3*z^4 - 5872*t^3*z^3 - 2976*t^3*z^2 - 9984*t^3*z + 197664*t^3 - 16*t^2*z^7 + 144*t^2*z^6 + 1072*t^2*z^5 - 15936*t^2*z^4 + 61072*t^2*z^3 - 58720*t^2*z^2 + 14944*t^2*z - 758080*t^2 - 16*t*z^8 + 512*t*z^7 - 5744*t*z^6 + 27104*t*z^5 - 42272*t*z^4 - 51712*t*z^3 + 141056*t*z^2 + 8784*t*z + 1445360*t + 32*z^8 - 1008*z^7 + 11776*z^6 - 63232*z^5 + 154176*z^4 - 122832*z^3 - 36480*z^2 - 53824*z - 1103616)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_36 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 36) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_36 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*z^3 + 18*z^2 - 46*z + 32:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*z - 8)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_37 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 37) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_37 z t hf hn0 hn1 hn2 hn3
  · have hr : (-6*z^3 + 60*z^2 - 182*z + 160:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(6*z - 30)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_38 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 38) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_38 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 8*z^2 - 2*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_39 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 39) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_39 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 4*t*z^2 - 24*t*z + 20*t - 2*z^3 + 14*z^2 - 22*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4*t + 2*z - 4)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 608*t^7*z + 400*t^7 + 144*t^6*z^4 - 2336*t^6*z^3 + 10880*t^6*z^2 - 12640*t^6*z + 4400*t^6 + 112*t^5*z^6 - 3072*t^5*z^5 + 29040*t^5*z^4 - 114080*t^5*z^3 + 176544*t^5*z^2 - 119040*t^5*z + 29600*t^5 + 32*t^4*z^8 - 1568*t^4*z^7 + 25872*t^4*z^6 - 196112*t^4*z^5 + 737264*t^4*z^4 - 1373952*t^4*z^3 + 1335824*t^4*z^2 - 653840*t^4*z + 127600*t^4 - 224*t^3*z^9 + 7856*t^3*z^8 - 108048*t^3*z^7 + 753232*t^3*z^6 - 2872784*t^3*z^5 + 6150576*t^3*z^4 - 7647984*t^3*z^3 + 5504480*t^3*z^2 - 2134000*t^3*z + 346000*t^3 + 544*t^2*z^10 - 17280*t^2*z^9 + 224560*t^2*z^8 - 1548240*t^2*z^7 + 6183440*t^2*z^6 - 14896560*t^2*z^5 + 22345856*t^2*z^4 - 21071952*t^2*z^3 + 12182480*t^2*z^2 - 3956400*t^2*z + 554000*t^2 - 544*t*z^11 + 16800*t*z^10 - 216800*t*z^9 + 1525520*t*z^8 - 6447344*t*z^7 + 17186112*t*z^6 - 29875440*t*z^5 + 34434208*t*z^4 - 26185040*t*z^3 + 12672400*t*z^2 - 3550000*t*z + 440000*t + 192*z^12 - 5920*z^11 + 77376*z^10 - 562112*z^9 + 2514800*z^8 - 7312016*z^7 + 14312928*z^6 - 19250304*z^5 + 17869312*z^4 - 11277040*z^3 + 4628800*z^2 - 1116000*z + 120000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 + 1616*t^6*z - 2080*t^6 - 112*t^5*z^4 + 2512*t^5*z^3 - 15920*t^5*z^2 + 21920*t^5*z + 12656*t^5 - 32*t^4*z^6 + 1408*t^4*z^5 - 18672*t^4*z^4 + 95712*t^4*z^3 - 165344*t^4*z^2 + 68672*t^4*z - 165744*t^4 + 224*t^3*z^7 - 6736*t^3*z^6 + 73248*t^3*z^5 - 353312*t^3*z^4 + 739984*t^3*z^3 - 684096*t^3*z^2 + 527584*t^3*z + 553920*t^3 - 544*t^2*z^8 + 14560*t^2*z^7 - 149040*t^2*z^6 + 730240*t^2*z^5 - 1787040*t^2*z^4 + 2310160*t^2*z^3 - 1859856*t^2*z^2 + 221872*t^2*z - 1773840*t^2 + 544*t*z^9 - 14080*t*z^8 + 143680*t*z^7 - 736720*t*z^6 + 2045344*t*z^5 - 3275792*t*z^4 + 3269760*t*z^3 - 1706448*t*z^2 + 1304000*t*z + 2379840*t - 192*z^10 + 4960*z^9 - 51616*z^8 + 279232*z^7 - 860560*z^6 + 1613056*z^5 - 1944848*z^4 + 1460784*z^3 - 841152*z^2 - 232640*z - 1586240)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_40 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 40) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_40 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 12*z^2 + 16*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_41 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 41) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_41 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 8*z^2 - 2*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*z - 2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_42 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 42) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_42 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^3 - 12*z^2 + 8*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2 - 2*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_43 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 43) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_43 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 10*t + 2*z^3 - 12*z^2 + 18*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2 - 2*z)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 + 96*t^7*z - 560*t^7 + 48*t^6*z^4 - 16*t^6*z^3 + 656*t^6*z^2 - 1520*t^6*z + 8000*t^6 - 16*t^5*z^6 - 288*t^5*z^5 + 1536*t^5*z^4 - 6960*t^5*z^3 + 9024*t^5*z^2 - 240*t^5*z - 60400*t^5 + 240*t^4*z^7 - 1424*t^4*z^6 + 7952*t^4*z^5 - 31568*t^4*z^4 + 106736*t^4*z^3 - 187376*t^4*z^2 + 132560*t^4*z + 259600*t^4 - 32*t^3*z^9 - 400*t^3*z^8 + 4704*t^3*z^7 - 25200*t^3*z^6 + 65008*t^3*z^5 - 38128*t^3*z^4 - 353536*t^3*z^3 + 1029680*t^3*z^2 - 967600*t^3*z - 632000*t^3 + 192*t^2*z^10 - 1904*t^2*z^9 + 12640*t^2*z^8 - 70448*t^2*z^7 + 319472*t^2*z^6 - 993696*t^2*z^5 + 1834944*t^2*z^4 - 1186672*t^2*z^3 - 1663120*t^2*z^2 + 2759600*t^2*z + 824000*t^2 - 352*t*z^11 + 5056*t*z^10 - 35520*t*z^9 + 149312*t*z^8 - 360720*t*z^7 + 216208*t*z^6 + 1580768*t*z^5 - 5337824*t*z^4 + 6655120*t*z^3 - 1369200*t*z^2 - 3080000*t*z - 520000*t + 192*z^12 - 2656*z^11 + 12736*z^10 + 3280*z^9 - 320272*z^8 + 1651696*z^7 - 4238016*z^6 + 5648784*z^5 - 2309328*z^4 - 2810640*z^3 + 2168800*z^2 + 1124000*z + 120000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 - 224*t^6*z - 1536*t^6 + 16*t^5*z^4 + 368*t^5*z^3 + 224*t^5*z^2 + 6240*t^5*z + 21056*t^5 - 240*t^4*z^5 + 224*t^4*z^4 - 5632*t^4*z^3 + 2288*t^4*z^2 - 67136*t^4*z - 159744*t^4 + 32*t^3*z^7 + 560*t^3*z^6 - 2064*t^3*z^5 + 12080*t^3*z^4 + 5712*t^3*z^3 + 6288*t^3*z^2 + 356416*t^3*z + 720960*t^3 - 192*t^2*z^8 + 944*t^2*z^7 - 6960*t^2*z^6 + 30928*t^2*z^5 - 130032*t^2*z^4 + 188896*t^2*z^3 - 240304*t^2*z^2 - 959328*t^2*z - 1932000*t^2 + 352*t*z^9 - 3296*t*z^8 + 17280*t*z^7 - 46432*t*z^6 + 42160*t*z^5 + 226752*t*z^4 - 657808*t*z^3 + 915024*t*z^2 + 1209040*t*z + 2839280*t - 192*z^10 + 1696*z^9 - 3296*z^8 - 28240*z^7 + 195552*z^6 - 532736*z^5 + 596576*z^4 - 2224*z^3 - 684672*z^2 - 601600*z - 1753440)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_44 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 44) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_44 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z - 4*t - 4*z^2 + 20*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4 - 2*t)*hf
  · have hr : (16*t^8 + 144*t^7*z^2 - 608*t^7*z - 48*t^7 + 480*t^6*z^4 - 4032*t^6*z^3 + 7904*t^6*z^2 + 2688*t^6*z + 128*t^6 + 704*t^5*z^6 - 8832*t^5*z^5 + 34848*t^5*z^4 - 32000*t^5*z^3 - 43008*t^5*z^2 - 9600*t^5*z + 544*t^5 + 384*t^4*z^8 - 6400*t^4*z^7 + 36848*t^4*z^6 - 67312*t^4*z^5 - 78544*t^4*z^4 + 242528*t^4*z^3 + 142096*t^4*z^2 + 22800*t^4*z - 5680*t^4 - 1744*t^3*z^8 + 32432*t^3*z^7 - 217344*t^3*z^6 + 587728*t^3*z^5 - 348992*t^3*z^4 - 484784*t^3*z^3 - 553024*t^3*z^2 + 60720*t^3*z + 7504*t^3 - 96*t^2*z^10 + 2464*t^2*z^9 - 23984*t^2*z^8 + 103216*t^2*z^7 - 154320*t^2*z^6 - 10704*t^2*z^5 - 640560*t^2*z^4 + 2086544*t^2*z^3 + 686192*t^2*z^2 - 218512*t^2*z + 4768*t^2 + 272*t*z^10 - 7440*t*z^9 + 83840*t*z^8 - 499136*t*z^7 + 1701216*t*z^6 - 3585376*t*z^5 + 5594432*t*z^4 - 6149056*t*z^3 + 656912*t*z^2 + 119792*t*z - 12608*t - 192*z^10 + 5568*z^9 - 67328*z^8 + 438784*z^7 - 1673088*z^6 + 3871616*z^5 - 5694464*z^4 + 5196800*z^3 - 1057216*z^2 + 22720*z + 5376:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-144*t^7 - 480*t^6*z^2 + 1632*t^6*z + 2656*t^6 - 704*t^5*z^4 + 5312*t^5*z^3 - 4768*t^5*z^2 - 18400*t^5*z - 25152*t^5 - 384*t^4*z^6 + 4480*t^4*z^5 - 12528*t^4*z^4 - 17728*t^4*z^3 + 52544*t^4*z^2 + 108832*t^4*z + 139344*t^4 + 1744*t^3*z^6 - 23712*t^3*z^5 + 90064*t^3*z^4 - 18848*t^3*z^3 - 195568*t^3*z^2 - 398816*t^3*z - 463216*t^3 + 96*t^2*z^8 - 1984*t^2*z^7 + 13584*t^2*z^6 - 25376*t^2*z^5 - 40480*t^2*z^4 - 64816*t^2*z^3 + 518880*t^2*z^2 + 831936*t^2*z + 879088*t^2 - 272*t*z^8 + 6080*t*z^7 - 52080*t*z^6 + 208336*t*z^5 - 399136*t*z^4 + 548016*t*z^3 - 858672*t*z^2 - 884384*t*z - 785472*t + 192*z^8 - 4608*z^7 + 43328*z^6 - 199104*z^5 + 460928*z^4 - 571456*z^3 + 532544*z^2 + 323200*z + 10496)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_45 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 45) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_45 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 4*t*z^2 - 24*t*z + 20*t - 2*z^3 + 14*z^2 - 22*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4*t + 2*z - 4)*hf
  · have hr : (16*t^8 + 208*t^7*z^2 - 1056*t^7*z + 720*t^7 + 1008*t^6*z^4 - 10224*t^6*z^3 + 32784*t^6*z^2 - 34320*t^6*z + 11200*t^6 + 2160*t^5*z^6 - 32832*t^5*z^5 + 187728*t^5*z^4 - 493056*t^5*z^3 + 591744*t^5*z^2 - 318240*t^5*z + 61600*t^5 + 1728*t^4*z^8 - 34992*t^4*z^7 + 286544*t^4*z^6 - 1198384*t^4*z^5 + 2665168*t^4*z^4 - 3014128*t^4*z^3 + 1578224*t^4*z^2 - 246640*t^4*z - 36400*t^4 - 3136*t^3*z^8 + 79376*t^3*z^7 - 781392*t^3*z^6 + 3881104*t^3*z^5 - 10445248*t^3*z^4 + 15340720*t^3*z^3 - 12239520*t^3*z^2 + 4965200*t^3*z - 798000*t^3 - 192*t^2*z^10 + 5232*t^2*z^9 - 59600*t^2*z^8 + 349312*t^2*z^7 - 981712*t^2*z^6 + 369216*t^2*z^5 + 4977504*t^2*z^4 - 12543792*t^2*z^3 + 13126880*t^2*z^2 - 6486400*t^2*z + 1244000*t^2 + 272*t*z^10 - 8320*t*z^9 + 107696*t*z^8 - 766960*t*z^7 + 3247536*t*z^6 - 8221904*t*z^5 + 12069312*t*z^4 - 9913360*t*z^3 + 4135600*t*z^2 - 610000*t*z - 40000*t - 96*z^10 + 3264*z^9 - 46768*z^8 + 369104*z^7 - 1758400*z^6 + 5206880*z^5 - 9578528*z^4 + 10927760*z^3 - 7547200*z^2 + 2904000*z - 480000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-208*t^7 - 1008*t^6*z^2 + 5184*t^6*z - 1824*t^6 - 2160*t^5*z^4 + 22032*t^5*z^3 - 66768*t^5*z^2 + 49056*t^5*z - 12624*t^5 - 1728*t^4*z^6 + 26352*t^4*z^5 - 146144*t^4*z^4 + 335904*t^4*z^3 - 254928*t^4*z^2 + 59968*t^4*z - 3744*t^4 + 3136*t^3*z^6 - 63696*t^3*z^5 + 447232*t^3*z^4 - 1326464*t^3*z^3 + 1576768*t^3*z^2 - 824560*t^3*z + 232880*t^3 + 192*t^2*z^8 - 4272*t^2*z^7 + 37280*t^2*z^6 - 141552*t^2*z^5 + 87552*t^2*z^4 + 776304*t^2*z^3 - 1533744*t^2*z^2 + 993552*t^2*z - 490400*t^2 - 272*t*z^8 + 6960*t*z^7 - 71536*t*z^6 + 374480*t*z^5 - 1017456*t*z^4 + 1262224*t*z^3 - 670912*t*z^2 + 247680*t*z + 457360*t + 96*z^8 - 2784*z^7 + 32368*z^6 - 193344*z^5 + 629840*z^4 - 1090960*z^3 + 974528*z^2 - 600320*z - 327040)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_46 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 46) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_46 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 10*t + 2*z^3 - 12*z^2 + 18*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2 - 2*z)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 352*t^7*z - 240*t^7 + 144*t^6*z^4 - 1248*t^6*z^3 + 1632*t^6*z^2 + 4640*t^6*z + 2000*t^6 + 112*t^5*z^6 - 1440*t^5*z^5 + 4608*t^5*z^4 + 4352*t^5*z^3 - 19536*t^5*z^2 - 35040*t^5*z - 10400*t^5 + 32*t^4*z^8 - 544*t^4*z^7 + 2576*t^4*z^6 + 1200*t^4*z^5 - 25648*t^4*z^4 - 14080*t^4*z^3 + 115824*t^4*z^2 + 171760*t^4*z + 35600*t^4 - 192*t^3*z^8 + 3280*t^3*z^7 - 18384*t^3*z^6 + 30480*t^3*z^5 + 5104*t^3*z^4 + 182128*t^3*z^3 - 497520*t^3*z^2 - 536400*t^3*z - 86000*t^3 - 32*t^2*z^10 + 832*t^2*z^9 - 8672*t^2*z^8 + 46800*t^2*z^7 - 144560*t^2*z^6 + 272784*t^2*z^5 - 217072*t^2*z^4 - 612752*t^2*z^3 + 1272080*t^2*z^2 + 1071600*t^2*z + 154000*t^2 + 112*t*z^10 - 2896*t*z^9 + 30848*t*z^8 - 174144*t*z^7 + 556064*t*z^6 - 957536*t*z^5 + 494400*t*z^4 + 1336000*t*z^3 - 1930000*t*z^2 - 1250000*t*z - 200000*t - 96*z^10 + 2464*z^9 - 26048*z^8 + 145024*z^7 - 445760*z^6 + 680640*z^5 - 132608*z^4 - 1107840*z^3 + 1008800*z^2 + 804000*z + 120000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 + 528*t^6*z + 1728*t^6 - 112*t^5*z^4 + 880*t^5*z^3 + 352*t^5*z^2 - 6992*t^5*z - 17184*t^5 - 32*t^4*z^6 + 384*t^4*z^5 - 496*t^4*z^4 - 5600*t^4*z^3 + 128*t^4*z^2 + 42720*t^4*z + 97136*t^4 + 192*t^3*z^6 - 2320*t^3*z^5 + 5824*t^3*z^4 + 10240*t^3*z^3 + 16976*t^3*z^2 - 148448*t^3*z - 329600*t^3 + 32*t^2*z^8 - 672*t^2*z^7 + 5152*t^2*z^6 - 17680*t^2*z^5 + 30400*t^2*z^4 - 32384*t^2*z^3 - 96848*t^2*z^2 + 290432*t^2*z + 664320*t^2 - 112*t*z^8 + 2336*t*z^7 - 18608*t*z^6 + 69424*t*z^5 - 115904*t*z^4 + 30896*t*z^3 + 239600*t*z^2 - 292480*t*z - 730400*t + 96*z^8 - 1984*z^7 + 15648*z^6 - 56864*z^5 + 83200*z^4 + 19680*z^3 - 184992*z^2 + 84480*z + 338560)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_47 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 47) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_47 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*t^2*z + 10*t^2 + 4*t*z^2 - 16*t*z - 20*t - 6*z^2 + 28*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(6 - 4*t)*hf
  · have hr : (16*t^8*z^4 - 320*t^8*z^3 + 2400*t^8*z^2 - 8000*t^8*z + 10000*t^8 - 144*t^7*z^5 + 2704*t^7*z^4 - 18080*t^7*z^3 + 45600*t^7*z^2 - 2000*t^7*z - 110000*t^7 + 480*t^6*z^6 - 8240*t^6*z^5 + 45360*t^6*z^4 - 48800*t^6*z^3 - 272000*t^6*z^2 + 450000*t^6*z + 550000*t^6 - 704*t^5*z^7 + 10336*t^5*z^6 - 34320*t^5*z^5 - 126752*t^5*z^4 + 742240*t^5*z^3 + 79200*t^5*z^2 - 2634000*t^5*z - 1620000*t^5 + 368*t^4*z^8 - 2960*t^4*z^7 - 25120*t^4*z^6 + 298368*t^4*z^5 - 531776*t^4*z^4 - 1790480*t^4*z^3 + 2473600*t^4*z^2 + 7788000*t^4*z + 2990000*t^4 + 80*t^3*z^9 - 3744*t^3*z^8 + 48400*t^3*z^7 - 214576*t^3*z^6 + 17488*t^3*z^5 + 1332192*t^3*z^4 + 2255360*t^3*z^3 - 8799200*t^3*z^2 - 13606000*t^3*z - 3430000*t^3 - 96*t^2*z^10 + 2272*t^2*z^9 - 18224*t^2*z^8 + 35872*t^2*z^7 + 195408*t^2*z^6 - 619680*t^2*z^5 - 694992*t^2*z^4 - 2631760*t^2*z^3 + 15675200*t^2*z^2 + 13726000*t^2*z + 2330000*t^2 + 272*t*z^10 - 7328*t*z^9 + 79088*t*z^8 - 427312*t*z^7 + 1192928*t*z^6 - 1839984*t*z^5 + 2515456*t*z^4 + 590480*t*z^3 - 14105600*t*z^2 - 7158000*t*z - 840000*t - 192*z^10 + 5568*z^9 - 66320*z^8 + 415600*z^7 - 1465440*z^6 + 2973632*z^5 - 3675008*z^4 + 1757360*z^3 + 4740800*z^2 + 1444000*z + 120000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 + 240*t^8*z - 1120*t^8 + 144*t^7*z^3 - 1984*t^7*z^2 + 7440*t^7*z + 1520*t^7 - 480*t^6*z^4 + 5840*t^6*z^3 - 13760*t^6*z^2 - 49200*t^6*z + 94800*t^6 + 704*t^5*z^5 - 6816*t^5*z^4 - 3280*t^5*z^3 + 144432*t^5*z^2 - 3680*t^5*z - 819760*t^5 - 368*t^4*z^6 + 1120*t^4*z^5 + 32560*t^4*z^4 - 141168*t^4*z^3 - 336864*t^4*z^2 + 812000*t^4*z + 3270720*t^4 - 80*t^3*z^7 + 3344*t^3*z^6 - 31280*t^3*z^5 + 41456*t^3*z^4 + 346192*t^3*z^3 + 191488*t^3*z^2 - 3028880*t^3*z - 7302640*t^3 + 96*t^2*z^8 - 1792*t^2*z^7 + 8784*t^2*z^6 + 17008*t^2*z^5 - 154288*t^2*z^4 - 236800*t^2*z^3 + 282432*t^2*z^2 + 5227920*t^2*z + 9052240*t^2 - 272*t*z^8 + 5968*t*z^7 - 47888*t*z^6 + 158032*t*z^5 - 163328*t*z^4 + 233184*t*z^3 - 532896*t*z^2 - 4420880*t*z - 5334320*t + 192*z^8 - 4608*z^7 + 42320*z^6 - 180960*z^5 + 349040*z^4 - 323632*z^3 + 311648*z^2 + 1419040*z + 796160)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_48 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 48) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_48 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*t^2*z + 10*t^2 + 2*t*z^2 - 12*t*z + 10*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8*z^4 - 320*t^8*z^3 + 2400*t^8*z^2 - 8000*t^8*z + 10000*t^8 - 16*t^7*z^5 + 400*t^7*z^4 - 4000*t^7*z^3 + 20000*t^7*z^2 - 50000*t^7*z + 50000*t^7 - 64*t^6*z^6 + 1200*t^6*z^5 - 8144*t^6*z^4 + 21280*t^6*z^3 + 2400*t^6*z^2 - 98000*t^6*z + 110000*t^6 + 48*t^5*z^7 - 1152*t^5*z^6 + 11040*t^5*z^5 - 52544*t^5*z^4 + 120880*t^5*z^3 - 81600*t^5*z^2 - 128000*t^5*z + 160000*t^5 + 80*t^4*z^8 - 1296*t^4*z^7 + 6304*t^4*z^6 + 3680*t^4*z^5 - 130208*t^4*z^4 + 432560*t^4*z^3 - 547200*t^4*z^2 + 184000*t^4*z + 70000*t^4 - 32*t^3*z^9 + 624*t^3*z^8 - 3952*t^3*z^7 + 1184*t^3*z^6 + 103632*t^3*z^5 - 548048*t^3*z^4 + 1296960*t^3*z^3 - 1537200*t^3*z^2 + 824000*t^3*z - 130000*t^3 - 32*t^2*z^10 + 272*t^2*z^9 + 2464*t^2*z^8 - 44048*t^2*z^7 + 251904*t^2*z^6 - 728976*t^2*z^5 + 1117568*t^2*z^4 - 786560*t^2*z^3 + 33200*t^2*z^2 + 226000*t^2*z - 70000*t^2 + 128*t*z^10 - 3184*t*z^9 + 33856*t*z^8 - 201552*t*z^7 + 739536*t*z^6 - 1735392*t*z^5 + 2612944*t*z^4 - 2457680*t*z^3 + 1353600*t*z^2 - 382000*t*z + 40000*t + 160*z^11 - 3488*z^10 + 32896*z^9 - 176080*z^8 + 589872*z^7 - 1286464*z^6 + 1841440*z^5 - 1701120*z^4 + 966800*z^3 - 304000*z^2 + 40000*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 + 240*t^8*z - 1120*t^8 + 16*t^7*z^3 - 320*t^7*z^2 + 2320*t^7*z - 6800*t^7 + 64*t^6*z^4 - 880*t^6*z^3 + 3424*t^6*z^2 + 240*t^6*z - 18320*t^6 - 48*t^5*z^5 + 912*t^5*z^4 - 6240*t^5*z^3 + 16784*t^5*z^2 - 5760*t^5*z - 31120*t^5 - 80*t^4*z^6 + 896*t^4*z^5 - 1424*t^4*z^4 - 15280*t^4*z^3 + 60928*t^4*z^2 - 51520*t^4*z - 15040*t^4 + 32*t^3*z^7 - 464*t^3*z^6 + 1472*t^3*z^5 + 8496*t^3*z^4 - 68512*t^3*z^3 + 163008*t^3*z^2 - 139360*t^3*z + 25360*t^3 + 32*t^2*z^8 - 112*t^2*z^7 - 3184*t^2*z^6 + 28688*t^2*z^5 - 92544*t^2*z^4 + 122816*t^2*z^3 - 40768*t^2*z^2 - 31360*t^2*z + 13840*t^2 - 128*t*z^8 + 2544*t*z^7 - 20496*t*z^6 + 86352*t*z^5 - 205296*t*z^4 + 277152*t*z^3 - 200704*t*z^2 + 68400*t*z - 8080*t - 160*z^9 + 2688*z^8 - 18656*z^7 + 69360*z^6 - 149792*z^5 + 190704*z^4 - 138960*z^3 + 52800*z^2 - 8000*z)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_49 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 49) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_49 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*t^2*z + 10*t^2 + 6*t*z - 30*t + 2*z^2 - 16*z + 32:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8*z^4 - 320*t^8*z^3 + 2400*t^8*z^2 - 8000*t^8*z + 10000*t^8 + 48*t^7*z^5 - 1136*t^7*z^4 + 10720*t^7*z^3 - 50400*t^7*z^2 + 118000*t^7*z - 110000*t^7 - 80*t^6*z^6 + 1312*t^6*z^5 - 6000*t^6*z^4 - 10304*t^6*z^3 + 164560*t^6*z^2 - 472800*t^6*z + 438000*t^6 - 272*t^5*z^7 + 6496*t^5*z^6 - 62832*t^5*z^5 + 310144*t^5*z^4 - 791792*t^5*z^3 + 845280*t^5*z^2 + 159600*t^5*z - 696000*t^5 + 176*t^4*z^8 - 2288*t^4*z^7 - 160*t^4*z^6 + 151152*t^4*z^5 - 1048736*t^4*z^4 + 3182320*t^4*z^3 - 4589984*t^4*z^2 + 2493840*t^4*z + 100400*t^4 + 528*t^3*z^9 - 12912*t^3*z^8 + 130720*t^3*z^7 - 698656*t^3*z^6 + 2047936*t^3*z^5 - 2881536*t^3*z^4 + 246112*t^3*z^3 + 4267552*t^3*z^2 - 4115920*t^3*z + 786800*t^3 - 256*t^2*z^10 + 3856*t^2*z^9 - 10736*t^2*z^8 - 142464*t^2*z^7 + 1383232*t^2*z^6 - 5440992*t^2*z^5 + 11363552*t^2*z^4 - 12560640*t^2*z^3 + 6075200*t^2*z^2 - 215984*t^2*z - 340080*t^2 - 352*t*z^11 + 8976*t*z^10 - 97488*t*z^9 + 583488*t*z^8 - 2063296*t*z^7 + 4180768*t*z^6 - 3724064*t*z^5 - 2228096*t*z^4 + 8857504*t*z^3 - 8401584*t*z^2 + 3315056*t*z - 463680*t + 192*z^12 - 4000*z^11 + 33696*z^10 - 137344*z^9 + 187456*z^8 + 702336*z^7 - 4021760*z^6 + 9226688*z^5 - 11984640*z^4 + 9202208*z^3 - 4036512*z^2 + 918720*z - 82944:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 + 240*t^8*z - 1120*t^8 - 48*t^7*z^3 + 896*t^7*z^2 - 6000*t^7*z + 15920*t^7 + 80*t^6*z^4 - 912*t^6*z^3 + 1040*t^6*z^2 + 20064*t^6*z - 69440*t^6 + 272*t^5*z^5 - 5136*t^5*z^4 + 35792*t^5*z^3 - 105504*t^5*z^2 + 85312*t^5*z + 108800*t^5 - 176*t^4*z^6 + 1408*t^4*z^5 + 8080*t^4*z^4 - 117792*t^4*z^3 + 419376*t^4*z^2 - 496480*t^4*z + 10704*t^4 - 528*t^3*z^7 + 10272*t^3*z^6 - 76720*t^3*z^5 + 263696*t^3*z^4 - 345856*t^3*z^3 - 166224*t^3*z^2 + 652048*t^3*z - 176192*t^3 + 256*t^2*z^8 - 2576*t^2*z^7 - 3424*t^2*z^6 + 138224*t^2*z^5 - 674992*t^2*z^4 + 1374912*t^2*z^3 - 1114032*t^2*z^2 + 115920*t^2*z + 74560*t^2 + 352*t*z^9 - 7216*t*z^8 + 59648*t*z^7 - 249168*t*z^6 + 519216*t*z^5 - 338848*t*z^4 - 566256*t*z^3 + 1091056*t*z^2 - 570944*t*z + 91584*t - 192*z^10 + 3040*z^9 - 17536*z^8 + 34464*z^7 + 72544*z^6 - 511936*z^5 + 1099360*z^4 - 1170208*z^3 + 636800*z^2 - 167168*z + 16672)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_50 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 50) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_50 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*t^2*z + 10*t^2 + 4*t*z^2 - 24*t*z + 20*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4*t - 2)*hf
  · have hr : (16*t^8*z^4 - 320*t^8*z^3 + 2400*t^8*z^2 - 8000*t^8*z + 10000*t^8 - 80*t^7*z^5 + 1744*t^7*z^4 - 14880*t^7*z^3 + 61600*t^7*z^2 - 122000*t^7*z + 90000*t^7 + 144*t^6*z^6 - 3504*t^6*z^5 + 34656*t^6*z^4 - 177184*t^6*z^3 + 489360*t^6*z^2 - 682800*t^6*z + 368000*t^6 - 112*t^5*z^7 + 3248*t^5*z^6 - 39168*t^5*z^5 + 252976*t^5*z^4 - 936752*t^5*z^3 + 1964880*t^5*z^2 - 2130400*t^5*z + 914000*t^5 + 16*t^4*z^8 - 928*t^4*z^7 + 17344*t^4*z^6 - 159344*t^4*z^5 + 822784*t^4*z^4 - 2481408*t^4*z^3 + 4283616*t^4*z^2 - 3872560*t^4*z + 1408400*t^4 + 48*t^3*z^9 - 1184*t^3*z^8 + 11280*t^3*z^7 - 46752*t^3*z^6 + 20496*t^3*z^5 + 578736*t^3*z^4 - 2375488*t^3*z^3 + 4251152*t^3*z^2 - 3667920*t^3*z + 1236800*t^3 - 32*t^2*z^10 + 992*t^2*z^9 - 13040*t^2*z^8 + 94304*t^2*z^7 - 405776*t^2*z^6 + 1038624*t^2*z^5 - 1434112*t^2*z^4 + 583888*t^2*z^3 + 1028768*t^2*z^2 - 1423344*t^2*z + 531520*t^2 - 32*t*z^10 + 944*t*z^9 - 11888*t*z^8 + 83312*t*z^7 - 355136*t*z^6 + 945360*t*z^5 - 1550176*t*z^4 + 1469104*t*z^3 - 655088*t*z^2 + 6336*t*z + 67520*t - 16*z^8 + 368*z^7 - 3424*z^6 + 16448*z^5 - 43136*z^4 + 60080*z^3 - 39424*z^2 + 6624*z + 2496:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 + 240*t^8*z - 1120*t^8 + 80*t^7*z^3 - 1344*t^7*z^2 + 7760*t^7*z - 16080*t^7 - 144*t^6*z^4 + 2784*t^6*z^3 - 20016*t^6*z^2 + 63184*t^6*z - 73360*t^6 + 112*t^5*z^5 - 2688*t^5*z^4 + 25168*t^5*z^3 - 113696*t^5*z^2 + 242432*t^5*z - 184240*t^5 - 16*t^4*z^6 + 848*t^4*z^5 - 13024*t^4*z^4 + 89984*t^4*z^3 - 307744*t^4*z^2 + 492768*t^4*z - 281056*t^4 - 48*t^3*z^7 + 944*t^3*z^6 - 6320*t^3*z^5 + 10432*t^3*z^4 + 63264*t^3*z^3 - 314576*t^3*z^2 + 486288*t^3*z - 246832*t^3 + 32*t^2*z^8 - 832*t^2*z^7 + 8720*t^2*z^6 - 46544*t^2*z^5 + 129456*t^2*z^4 - 158624*t^2*z^3 - 6288*t^2*z^2 + 177792*t^2*z - 108368*t^2 + 32*t*z^8 - 784*t*z^7 + 7808*t*z^6 - 40352*t*z^5 + 114336*t*z^4 - 171920*t*z^3 + 118896*t*z^2 - 15024*t*z - 14512*t + 16*z^6 - 288*z^5 + 1904*z^4 - 5488*z^3 + 6176*z^2 - 1760*z - 256)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_51 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 51) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_51 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 14*t*z + 16*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 + 32*t^7*z + 272*t^7 + 48*t^6*z^4 + 64*t^6*z^3 - 1088*t^6*z^2 + 640*t^6*z + 2128*t^6 - 16*t^5*z^6 - 240*t^5*z^5 + 1728*t^5*z^4 - 1120*t^5*z^3 - 6096*t^5*z^2 + 1488*t^5*z + 11424*t^5 + 160*t^4*z^7 - 816*t^4*z^6 - 688*t^4*z^5 + 5552*t^4*z^4 + 11904*t^4*z^3 - 48272*t^4*z^2 + 12560*t^4*z + 37520*t^4 - 16*t^3*z^9 - 144*t^3*z^8 + 2000*t^3*z^7 - 3840*t^3*z^6 - 10864*t^3*z^5 + 19328*t^3*z^4 + 88496*t^3*z^3 - 213952*t^3*z^2 + 72960*t^3*z + 74704*t^3 + 48*t^2*z^10 - 416*t^2*z^9 + 1696*t^2*z^8 - 12464*t^2*z^7 + 83568*t^2*z^6 - 272688*t^2*z^5 + 374160*t^2*z^4 - 22544*t^2*z^3 - 389344*t^2*z^2 + 184208*t^2*z + 82448*t^2 - 32*t*z^11 + 240*t*z^10 + 528*t*z^9 - 8896*t*z^8 + 17024*t*z^7 + 67552*t*z^6 - 329248*t*z^5 + 444928*t*z^4 + 28960*t*z^3 - 524624*t*z^2 + 290960*t*z + 28992*t + 192*z^11 - 3680*z^10 + 29856*z^9 - 131712*z^8 + 332352*z^7 - 435200*z^6 + 110336*z^5 + 445120*z^4 - 515840*z^3 + 125024*z^2 + 45152*z + 2496:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 - 304*t^6*z - 192*t^6 + 16*t^5*z^4 + 320*t^5*z^3 - 208*t^5*z^2 - 1520*t^5*z - 464*t^5 - 160*t^4*z^5 + 16*t^4*z^4 + 1568*t^4*z^3 + 2208*t^4*z^2 - 8704*t^4*z - 6288*t^4 + 16*t^3*z^7 + 224*t^3*z^6 - 960*t^3*z^5 - 2080*t^3*z^4 + 5264*t^3*z^3 + 17392*t^3*z^2 - 27856*t^3*z - 12288*t^3 - 48*t^2*z^8 + 176*t^2*z^7 - 576*t^2*z^6 + 8704*t^2*z^5 - 37168*t^2*z^4 + 43328*t^2*z^3 + 28320*t^2*z^2 - 52496*t^2*z - 14736*t^2 + 32*t*z^9 - 80*t*z^8 - 1088*t*z^7 + 3856*t*z^6 + 7696*t*z^5 - 48352*t*z^4 + 49008*t*z^3 + 41872*t*z^2 - 64640*t*z - 7936*t - 192*z^9 + 2720*z^8 - 15296*z^7 + 41632*z^6 - 47712*z^5 - 11520*z^4 + 70624*z^3 - 34400*z^2 - 9280*z + 576)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_52 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 52) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_52 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*t^2*z + 10*t^2 + 6*t*z - 30*t + 2*z^2 - 16*z + 32:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8*z^4 - 320*t^8*z^3 + 2400*t^8*z^2 - 8000*t^8*z + 10000*t^8 + 48*t^7*z^5 - 1136*t^7*z^4 + 10720*t^7*z^3 - 50400*t^7*z^2 + 118000*t^7*z - 110000*t^7 + 48*t^6*z^6 - 1568*t^6*z^5 + 20112*t^6*z^4 - 131264*t^6*z^3 + 462160*t^6*z^2 - 832800*t^6*z + 598000*t^6 + 16*t^5*z^7 - 1040*t^5*z^6 + 19680*t^5*z^5 - 177440*t^5*z^4 + 875728*t^5*z^3 - 2419920*t^5*z^2 + 3489600*t^5*z - 2016000*t^5 - 16*t^4*z^8 + 112*t^4*z^7 + 5408*t^4*z^6 - 103632*t^4*z^5 + 807328*t^4*z^4 - 3356336*t^4*z^3 + 7760416*t^4*z^2 - 9342960*t^4*z + 4516400*t^4 - 16*t^3*z^9 + 480*t^3*z^8 - 4256*t^3*z^7 - 2848*t^3*z^6 + 293008*t^3*z^5 - 2194416*t^3*z^4 + 7989440*t^3*z^3 - 15890048*t^3*z^2 + 16400480*t^3*z - 6821200*t^3 + 112*t^2*z^9 - 2720*t^2*z^8 + 23200*t^2*z^7 - 55056*t^2*z^6 - 397344*t^2*z^5 + 3454992*t^2*z^4 - 11614048*t^2*z^3 + 20456336*t^2*z^2 - 18517904*t^2*z + 6767120*t^2 + 32*t*z^10 - 1040*t*z^9 + 13280*t*z^8 - 84208*t*z^7 + 245744*t*z^6 + 59808*t*z^5 - 2861696*t*z^4 + 9580304*t*z^3 - 15344048*t*z^2 + 12403536*t*z - 4044480*t - 96*z^10 + 2544*z^9 - 27536*z^8 + 157552*z^7 - 500352*z^6 + 759632*z^5 + 175024*z^4 - 2816368*z^3 + 4864832*z^2 - 3726272*z + 1115136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 + 240*t^8*z - 1120*t^8 - 48*t^7*z^3 + 896*t^7*z^2 - 6000*t^7*z + 15920*t^7 - 48*t^6*z^4 + 1328*t^6*z^3 - 13232*t^6*z^2 + 58464*t^6*z - 103680*t^6 - 16*t^5*z^5 + 960*t^5*z^4 - 14800*t^5*z^3 + 98640*t^5*z^2 - 308528*t^5*z + 384080*t^5 + 16*t^4*z^6 - 32*t^4*z^5 - 5648*t^4*z^4 + 75552*t^4*z^3 - 401328*t^4*z^2 + 971936*t^4*z - 894096*t^4 + 16*t^3*z^7 - 400*t^3*z^6 + 2176*t^3*z^5 + 15728*t^3*z^4 - 225248*t^3*z^3 + 989536*t^3*z^2 - 1915520*t^3*z + 1364768*t^3 - 112*t^2*z^7 + 2160*t^2*z^6 - 11840*t^2*z^5 - 14944*t^2*z^4 + 381824*t^2*z^3 - 1471152*t^2*z^2 + 2349168*t^2*z - 1354736*t^2 - 32*t*z^8 + 880*t*z^7 - 8720*t*z^6 + 36208*t*z^5 - 21104*t*z^4 - 346368*t*z^3 + 1235376*t*z^2 - 1671584*t*z + 809248*t + 96*z^8 - 2064*z^7 + 16736*z^6 - 63552*z^5 + 98912*z^4 + 52688*z^3 - 406144*z^2 + 522208*z - 223072)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_53 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 53) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_53 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*t^2*z + 10*t^2 - 2*t*z^2 + 24*t*z - 70*t - 2*z^3 + 26*z^2 - 112*z + 160:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(2*t + 2*z - 16)*hf
  · have hr : (16*t^8*z^4 - 320*t^8*z^3 + 2400*t^8*z^2 - 8000*t^8*z + 10000*t^8 + 112*t^7*z^5 - 2672*t^7*z^4 + 25440*t^7*z^3 - 120800*t^7*z^2 + 286000*t^7*z - 270000*t^7 + 288*t^6*z^6 - 8496*t^6*z^5 + 102768*t^6*z^4 - 652960*t^6*z^3 + 2299200*t^6*z^2 - 4254000*t^6*z + 3230000*t^6 + 320*t^5*z^7 - 12736*t^5*z^6 + 202032*t^5*z^5 - 1694336*t^5*z^4 + 8209120*t^5*z^3 - 23126400*t^5*z^2 + 35198000*t^5*z - 22360000*t^5 + 112*t^4*z^8 - 8464*t^4*z^7 + 196768*t^4*z^6 - 2256512*t^4*z^5 + 14828416*t^4*z^4 - 58680720*t^4*z^3 + 138398400*t^4*z^2 - 179188000*t^4*z + 97910000*t^4 - 48*t^3*z^9 - 800*t^3*z^8 + 74448*t^3*z^7 - 1420944*t^3*z^6 + 13453584*t^3*z^5 - 74355840*t^3*z^4 + 251297600*t^3*z^3 - 512128000*t^3*z^2 + 578130000*t^3*z - 277450000*t^3 - 32*t^2*z^10 + 1376*t^2*z^9 - 9200*t^2*z^8 - 243424*t^2*z^7 + 5089552*t^2*z^6 - 43776480*t^2*z^5 + 214205168*t^2*z^4 - 639310160*t^2*z^3 + 1153707200*t^2*z^2 - 1157994000*t^2*z + 496330000*t^2 + 304*t*z^10 - 9856*t*z^9 + 95632*t*z^8 + 52112*t*z^7 - 8012768*t*z^6 + 71495568*t*z^5 - 326811232*t*z^4 + 888825040*t*z^3 - 1451760800*t*z^2 + 1317846000*t*z - 511720000*t - 672*z^10 + 19488*z^9 - 200080*z^8 + 670640*z^7 + 3442400*z^6 - 43949248*z^5 + 201483712*z^4 - 516849040*z^3 + 781128800*z^2 - 651816000*z + 232320000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 + 240*t^8*z - 1120*t^8 - 112*t^7*z^3 + 2112*t^7*z^2 - 14320*t^7*z + 38640*t^7 - 288*t^6*z^4 + 7056*t^6*z^3 - 66048*t^6*z^2 + 287440*t^6*z - 531760*t^6 - 320*t^5*z^5 + 11136*t^5*z^4 - 144752*t^5*z^3 + 914896*t^5*z^2 - 2910880*t^5*z + 3997520*t^5 - 112*t^4*z^6 + 7904*t^4*z^5 - 156688*t^4*z^4 + 1433552*t^4*z^3 - 6877216*t^4*z^2 + 17126880*t^4*z - 18377920*t^4 + 48*t^3*z^7 + 1040*t^3*z^6 - 69488*t^3*z^5 + 1068304*t^3*z^4 - 7764624*t^3*z^3 + 30191200*t^3*z^2 - 61518480*t^3*z + 53579600*t^3 + 32*t^2*z^8 - 1216*t^2*z^7 + 2960*t^2*z^6 + 264304*t^2*z^5 - 3782832*t^2*z^4 + 23540800*t^2*z^3 - 77587008*t^2*z^2 + 133671120*t^2*z - 97416560*t^2 - 304*t*z^8 + 8336*t*z^7 - 52432*t*z^6 - 355952*t*z^5 + 6495168*t*z^4 - 37239968*t*z^3 + 108135552*t*z^2 - 161947440*t*z + 101345840*t + 672*z^8 - 16128*z^7 + 116080*z^6 - 9600*z^5 - 4070800*z^4 + 23643248*z^3 - 62913472*z^2 + 84065440*z - 46234240)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_54 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 54) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_54 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*t^2*z + 10*t^2 + 2*t*z^2 - 6*t*z - 20*t + 2*z^3 - 12*z^2 + 18*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t - 2*z + 2)*hf
  · have hr : (16*t^8*z^4 - 320*t^8*z^3 + 2400*t^8*z^2 - 8000*t^8*z + 10000*t^8 - 16*t^7*z^5 + 208*t^7*z^4 - 160*t^7*z^3 - 8800*t^7*z^2 + 46000*t^7*z - 70000*t^7 + 448*t^6*z^4 - 8960*t^6*z^3 + 67200*t^6*z^2 - 224000*t^6*z + 280000*t^6 + 96*t^5*z^6 - 1776*t^5*z^5 + 10384*t^5*z^4 - 3680*t^5*z^3 - 182400*t^5*z^2 + 658000*t^5*z - 710000*t^5 - 16*t^4*z^8 + 432*t^4*z^7 - 5120*t^4*z^6 + 33968*t^4*z^5 - 127424*t^4*z^4 + 206480*t^4*z^3 + 206400*t^4*z^2 - 1238000*t^4*z + 1210000*t^4 + 16*t^3*z^9 - 384*t^3*z^8 + 3440*t^3*z^7 - 11856*t^3*z^6 - 12192*t^3*z^5 + 205600*t^3*z^4 - 474000*t^3*z^3 - 90000*t^3*z^2 + 1550000*t^3*z - 1400000*t^3 - 16*t^2*z^9 + 352*t^2*z^8 - 2496*t^2*z^7 + 736*t^2*z^6 + 78624*t^2*z^5 - 414752*t^2*z^4 + 799040*t^2*z^3 - 152800*t^2*z^2 - 1274000*t^2*z + 1080000*t^2 - 16*t*z^10 + 448*t*z^9 - 5184*t*z^8 + 31408*t*z^7 - 101520*t*z^6 + 138848*t*z^5 + 82208*t*z^4 - 406160*t*z^3 + 51200*t*z^2 + 696000*t*z - 520000*t + 16*z^9 - 464*z^8 + 5680*z^7 - 37952*z^6 + 148944*z^5 - 340688*z^4 + 407760*z^3 - 143200*z^2 - 156000*z + 120000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 + 240*t^8*z - 1120*t^8 + 16*t^7*z^3 - 128*t^7*z^2 - 560*t^7*z + 6640*t^7 - 448*t^6*z^2 + 6720*t^6*z - 31360*t^6 - 96*t^5*z^4 + 1296*t^5*z^3 - 3424*t^5*z^2 - 19920*t^5*z + 99920*t^5 + 16*t^4*z^6 - 352*t^4*z^5 + 3280*t^4*z^4 - 15808*t^4*z^3 + 31984*t^4*z^2 + 32480*t^4*z - 203920*t^4 - 16*t^3*z^7 + 304*t^3*z^6 - 1840*t^3*z^5 + 1136*t^3*z^4 + 27072*t^3*z^3 - 75920*t^3*z^2 - 40960*t^3*z + 264800*t^3 + 16*t^2*z^7 - 272*t^2*z^6 + 1056*t^2*z^5 + 5904*t^2*z^4 - 54384*t^2*z^3 + 113312*t^2*z^2 + 39440*t^2*z - 216560*t^2 + 16*t*z^8 - 368*t*z^7 + 3264*t*z^6 - 13248*t*z^5 + 18960*t*z^4 + 22192*t*z^3 - 66048*t*z^2 - 35040*t*z + 103840*t - 16*z^7 + 384*z^6 - 3680*z^5 + 17632*z^4 - 42384*z^3 + 40608*z^2 + 7200*z - 23840)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_55 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 55) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_55 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z - 2*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 + 160*t^7*z - 240*t^7 + 48*t^6*z^4 - 288*t^6*z^3 + 1088*t^6*z^2 - 2400*t^6*z + 2000*t^6 - 16*t^5*z^6 + 96*t^5*z^5 - 720*t^5*z^4 + 4000*t^5*z^3 - 11616*t^5*z^2 + 17760*t^5*z - 10400*t^5 + 32*t^4*z^7 - 112*t^4*z^6 - 400*t^4*z^5 + 4592*t^4*z^4 - 22336*t^4*z^3 + 58384*t^4*z^2 - 74640*t^4*z + 35600*t^4 - 16*t^3*z^8 - 208*t^3*z^7 + 2448*t^3*z^6 - 6032*t^3*z^5 - 10640*t^3*z^4 + 88912*t^3*z^3 - 206560*t^3*z^2 + 217200*t^3*z - 86000*t^3 - 32*t^2*z^9 + 976*t^2*z^8 - 8720*t^2*z^7 + 38160*t^2*z^6 - 106032*t^2*z^5 + 236448*t^2*z^4 - 450832*t^2*z^3 + 616880*t^2*z^2 - 480400*t^2*z + 154000*t^2 + 32*t*z^10 - 672*t*z^9 + 4496*t*z^8 - 8432*t*z^7 - 38016*t*z^6 + 263600*t*z^5 - 743776*t*z^4 + 1253840*t*z^3 - 1313200*t*z^2 + 782000*t*z - 200000*t - 96*z^10 + 2304*z^9 - 21968*z^8 + 109744*z^7 - 310560*z^6 + 478400*z^5 - 263168*z^4 - 335440*z^3 + 696800*z^2 - 476000*z + 120000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 + 48*t^6*z - 608*t^6 + 16*t^5*z^4 - 16*t^5*z^3 + 560*t^5*z^2 - 1120*t^5*z + 3216*t^5 - 32*t^4*z^5 - 48*t^4*z^4 + 320*t^4*z^3 - 2752*t^4*z^2 + 6976*t^4*z - 9744*t^4 + 16*t^3*z^6 + 288*t^3*z^5 - 1088*t^3*z^4 - 848*t^3*z^3 + 11840*t^3*z^2 - 25472*t^3*z + 20000*t^3 + 32*t^2*z^7 - 816*t^2*z^6 + 4480*t^2*z^5 - 11680*t^2*z^4 + 25232*t^2*z^3 - 51888*t^2*z^2 + 65232*t^2*z - 31280*t^2 - 32*t*z^8 + 512*t*z^7 - 1776*t*z^6 - 3008*t*z^5 + 31856*t*z^4 - 89280*t*z^3 + 138096*t*z^2 - 116960*t*z + 37920*t + 96*z^8 - 1824*z^7 + 12368*z^6 - 38784*z^5 + 54800*z^4 - 10480*z^3 - 63232*z^2 + 71680*z - 22240)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_56 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 56) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_56 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*t^2*z + 10*t^2 + 4*t*z^2 - 24*t*z + 20*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4*t - 2)*hf
  · have hr : (16*t^8*z^4 - 320*t^8*z^3 + 2400*t^8*z^2 - 8000*t^8*z + 10000*t^8 - 80*t^7*z^5 + 1744*t^7*z^4 - 14880*t^7*z^3 + 61600*t^7*z^2 - 122000*t^7*z + 90000*t^7 + 16*t^6*z^6 - 1008*t^6*z^5 + 15648*t^6*z^4 - 106144*t^6*z^3 + 354960*t^6*z^2 - 562800*t^6*z + 328000*t^6 + 368*t^5*z^7 - 6976*t^5*z^6 + 48960*t^5*z^5 - 141728*t^5*z^4 + 46768*t^5*z^3 + 607680*t^5*z^2 - 1170400*t^5*z + 644000*t^5 - 176*t^4*z^8 + 5696*t^4*z^7 - 66560*t^4*z^6 + 375664*t^4*z^5 - 1091456*t^4*z^4 + 1492896*t^4*z^3 - 425184*t^4*z^2 - 937360*t^4*z + 664400*t^4 - 688*t^3*z^9 + 11632*t^3*z^8 - 68832*t^3*z^7 + 119840*t^3*z^6 + 421152*t^3*z^5 - 2363568*t^3*z^4 + 4422000*t^3*z^3 - 3673648*t^3*z^2 + 1020480*t^3*z + 118800*t^3 + 96*t^2*z^10 - 4480*t^2*z^9 + 57472*t^2*z^8 - 333200*t^2*z^7 + 966944*t^2*z^6 - 1188336*t^2*z^5 - 538064*t^2*z^4 + 3392000*t^2*z^3 - 3910096*t^2*z^2 + 1820736*t^2*z - 261280*t^2 + 544*t*z^11 - 8784*t*z^10 + 50272*t*z^9 - 78704*t*z^8 - 424016*t*z^7 + 2542160*t*z^6 - 6167760*t*z^5 + 8312128*t*z^4 - 6447088*t*z^3 + 2701968*t*z^2 - 503184*t*z + 22720*t + 192*z^12 - 2208*z^11 + 4832*z^10 + 49600*z^9 - 398640*z^8 + 1364432*z^7 - 2699776*z^6 + 3285792*z^5 - 2429984*z^4 + 1001200*z^3 - 168192*z^2 - 12608*z + 5376:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 + 240*t^8*z - 1120*t^8 + 80*t^7*z^3 - 1344*t^7*z^2 + 7760*t^7*z - 16080*t^7 - 16*t^6*z^4 + 928*t^6*z^3 - 10928*t^6*z^2 + 46864*t^6*z - 66000*t^6 - 368*t^5*z^5 + 5136*t^5*z^4 - 21440*t^5*z^3 + 8848*t^5*z^2 + 104672*t^5*z - 128560*t^5 + 176*t^4*z^6 - 4816*t^4*z^5 + 41600*t^4*z^4 - 143584*t^4*z^3 + 165536*t^4*z^2 + 52704*t^4*z - 138976*t^4 + 688*t^3*z^7 - 8192*t^3*z^6 + 24432*t^3*z^5 + 43280*t^3*z^4 - 326912*t^3*z^3 + 512608*t^3*z^2 - 224400*t^3*z - 11392*t^3 - 96*t^2*z^8 + 4000*t^2*z^7 - 36992*t^2*z^6 + 128240*t^2*z^5 - 140784*t^2*z^4 - 156784*t^2*z^3 + 458064*t^2*z^2 - 317760*t^2*z + 30976*t^2 - 544*t*z^9 + 6064*t*z^8 - 17232*t*z^7 - 37776*t*z^6 + 321296*t*z^5 - 746800*t*z^4 + 827280*t*z^3 - 441728*t*z^2 + 102048*t*z + 16912*t - 192*z^10 + 1248*z^9 + 2368*z^8 - 44000*z^7 + 166800*z^6 - 310432*z^5 + 313616*z^4 - 165552*z^3 + 34144*z^2 - 2720*z - 16128)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_57 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 57) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_57 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*t^2*z + 10*t^2 + 2*t*z^2 - 6*t*z - 20*t + 2*z^3 - 12*z^2 + 18*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t - 2*z + 2)*hf
  · have hr : (16*t^8*z^4 - 320*t^8*z^3 + 2400*t^8*z^2 - 8000*t^8*z + 10000*t^8 - 16*t^7*z^5 + 208*t^7*z^4 - 160*t^7*z^3 - 8800*t^7*z^2 + 46000*t^7*z - 70000*t^7 - 256*t^6*z^6 + 5376*t^6*z^5 - 44672*t^6*z^4 + 183040*t^6*z^3 - 364800*t^6*z^2 + 256000*t^6*z + 80000*t^6 + 192*t^5*z^7 - 2592*t^5*z^6 + 3840*t^5*z^5 + 103264*t^5*z^4 - 687680*t^5*z^3 + 1725600*t^5*z^2 - 1712000*t^5*z + 340000*t^5 + 1520*t^4*z^8 - 32976*t^4*z^7 + 295168*t^4*z^6 - 1395568*t^4*z^5 + 3661696*t^4*z^4 - 4953520*t^4*z^3 + 2318400*t^4*z^2 + 982000*t^4*z - 590000*t^4 - 752*t^3*z^9 + 10368*t^3*z^8 - 20368*t^3*z^7 - 400144*t^3*z^6 + 3201360*t^3*z^5 - 10661840*t^3*z^4 + 18306000*t^3*z^3 - 15774000*t^3*z^2 + 5660000*t^3*z - 550000*t^3 - 3968*t^2*z^10 + 87536*t^2*z^9 - 825344*t^2*z^8 + 4326880*t^2*z^7 - 13675296*t^2*z^6 + 26204352*t^2*z^5 - 28407712*t^2*z^4 + 13131040*t^2*z^3 + 2631200*t^2*z^2 - 4334000*t^2*z + 980000*t^2 + 960*t*z^11 - 13264*t*z^10 + 28784*t*z^9 + 527104*t*z^8 - 4787712*t*z^7 + 19229088*t*z^6 - 44420256*t*z^5 + 62135488*t*z^4 - 51748160*t*z^3 + 23809200*t*z^2 - 5074000*t*z + 280000*t + 3840*z^12 - 84800*z^11 + 826432*z^10 - 4669568*z^9 + 16885952*z^8 - 40645056*z^7 + 65444672*z^6 - 68506688*z^5 + 42610752*z^4 - 11146240*z^3 - 2819200*z^2 + 2584000*z - 480000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 + 240*t^8*z - 1120*t^8 + 16*t^7*z^3 - 128*t^7*z^2 - 560*t^7*z + 6640*t^7 + 256*t^6*z^4 - 4096*t^6*z^3 + 22912*t^6*z^2 - 48000*t^6*z + 10240*t^6 - 192*t^5*z^5 + 1632*t^5*z^4 + 5280*t^5*z^3 - 85024*t^5*z^2 + 236160*t^5*z - 119680*t^5 - 1520*t^4*z^6 + 25376*t^4*z^5 - 160688*t^4*z^4 + 465248*t^4*z^3 - 532016*t^4*z^2 - 32800*t^4*z + 177680*t^4 + 752*t^3*z^7 - 6608*t^3*z^6 - 16432*t^3*z^5 + 351024*t^3*z^4 - 1364080*t^3*z^3 + 2086320*t^3*z^2 - 1054000*t^3*z + 72400*t^3 + 3968*t^2*z^8 - 67696*t^2*z^7 + 467024*t^2*z^6 - 1653280*t^2*z^5 + 3073776*t^2*z^4 - 2569072*t^2*z^3 + 193472*t^2*z^2 + 681680*t^2*z - 190160*t^2 - 960*t*z^9 + 8464*t*z^8 + 18336*t*z^7 - 477744*t*z^6 + 2307312*t*z^5 - 5303808*t*z^4 + 6364656*t*z^3 - 3793168*t*z^2 + 959040*t*z - 48160*t - 3840*z^10 + 65600*z^9 - 479232*z^8 + 1945408*z^7 - 4762752*z^6 + 7104256*z^5 - 6109632*z^4 + 2437248*z^3 + 123648*z^2 - 421760*z + 92160)*hf
  · have hr : (16*t^8*z^4 - 320*t^8*z^3 + 2400*t^8*z^2 - 8000*t^8*z + 10000*t^8 - 16*t^7*z^5 + 208*t^7*z^4 - 160*t^7*z^3 - 8800*t^7*z^2 + 46000*t^7*z - 70000*t^7 + 448*t^6*z^4 - 8960*t^6*z^3 + 67200*t^6*z^2 - 224000*t^6*z + 280000*t^6 + 96*t^5*z^6 - 1776*t^5*z^5 + 10384*t^5*z^4 - 3680*t^5*z^3 - 182400*t^5*z^2 + 658000*t^5*z - 710000*t^5 - 16*t^4*z^8 + 432*t^4*z^7 - 5120*t^4*z^6 + 33968*t^4*z^5 - 127424*t^4*z^4 + 206480*t^4*z^3 + 206400*t^4*z^2 - 1238000*t^4*z + 1210000*t^4 + 16*t^3*z^9 - 384*t^3*z^8 + 3440*t^3*z^7 - 11856*t^3*z^6 - 12192*t^3*z^5 + 205600*t^3*z^4 - 474000*t^3*z^3 - 90000*t^3*z^2 + 1550000*t^3*z - 1400000*t^3 - 16*t^2*z^9 + 352*t^2*z^8 - 2496*t^2*z^7 + 736*t^2*z^6 + 78624*t^2*z^5 - 414752*t^2*z^4 + 799040*t^2*z^3 - 152800*t^2*z^2 - 1274000*t^2*z + 1080000*t^2 - 16*t*z^10 + 448*t*z^9 - 5184*t*z^8 + 31408*t*z^7 - 101520*t*z^6 + 138848*t*z^5 + 82208*t*z^4 - 406160*t*z^3 + 51200*t*z^2 + 696000*t*z - 520000*t + 16*z^9 - 464*z^8 + 5680*z^7 - 37952*z^6 + 148944*z^5 - 340688*z^4 + 407760*z^3 - 143200*z^2 - 156000*z + 120000:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 + 240*t^8*z - 1120*t^8 + 16*t^7*z^3 - 128*t^7*z^2 - 560*t^7*z + 6640*t^7 - 448*t^6*z^2 + 6720*t^6*z - 31360*t^6 - 96*t^5*z^4 + 1296*t^5*z^3 - 3424*t^5*z^2 - 19920*t^5*z + 99920*t^5 + 16*t^4*z^6 - 352*t^4*z^5 + 3280*t^4*z^4 - 15808*t^4*z^3 + 31984*t^4*z^2 + 32480*t^4*z - 203920*t^4 - 16*t^3*z^7 + 304*t^3*z^6 - 1840*t^3*z^5 + 1136*t^3*z^4 + 27072*t^3*z^3 - 75920*t^3*z^2 - 40960*t^3*z + 264800*t^3 + 16*t^2*z^7 - 272*t^2*z^6 + 1056*t^2*z^5 + 5904*t^2*z^4 - 54384*t^2*z^3 + 113312*t^2*z^2 + 39440*t^2*z - 216560*t^2 + 16*t*z^8 - 368*t*z^7 + 3264*t*z^6 - 13248*t*z^5 + 18960*t*z^4 + 22192*t*z^3 - 66048*t*z^2 - 35040*t*z + 103840*t - 16*z^7 + 384*z^6 - 3680*z^5 + 17632*z^4 - 42384*z^3 + 40608*z^2 + 7200*z - 23840)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_58 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 58) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_58 z t hf hn0 hn1 hn2 hn3
  · have hr : (-2*t^2*z + 10*t^2 + 6*t*z^2 - 36*t*z + 30*t - 2*z^3 + 14*z^2 - 22*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-6*t + 2*z - 4)*hf
  · have hr : (16*t^8*z^4 - 320*t^8*z^3 + 2400*t^8*z^2 - 8000*t^8*z + 10000*t^8 - 144*t^7*z^5 + 3088*t^7*z^4 - 25760*t^7*z^3 + 103200*t^7*z^2 - 194000*t^7*z + 130000*t^7 + 480*t^6*z^6 - 11216*t^6*z^5 + 105168*t^6*z^4 - 500960*t^6*z^3 + 1259200*t^6*z^2 - 1554000*t^6*z + 730000*t^6 - 704*t^5*z^7 + 18688*t^5*z^6 - 203376*t^5*z^5 + 1166944*t^5*z^4 - 3776480*t^5*z^3 + 6825600*t^5*z^2 - 6342000*t^5*z + 2340000*t^5 + 368*t^4*z^8 - 12944*t^4*z^7 + 180320*t^4*z^6 - 1317600*t^4*z^5 + 5545696*t^4*z^4 - 13770320*t^4*z^3 + 19710400*t^4*z^2 - 14928000*t^4*z + 4610000*t^4 + 80*t^3*z^9 + 288*t^3*z^8 - 38384*t^3*z^7 + 518576*t^3*z^6 - 3296912*t^3*z^5 + 11793120*t^3*z^4 - 24865600*t^3*z^3 + 30496000*t^3*z^2 - 20050000*t^3*z + 5450000*t^3 - 96*t^2*z^10 + 2944*t^2*z^9 - 33008*t^2*z^8 + 161920*t^2*z^7 - 185808*t^2*z^6 - 1645248*t^2*z^5 + 8565648*t^2*z^4 - 18999760*t^2*z^3 + 22539200*t^2*z^2 - 13934000*t^2*z + 3530000*t^2 - 208*t*z^10 + 5632*t*z^9 - 60016*t*z^8 + 326000*t*z^7 - 939136*t*z^6 + 1156656*t*z^5 + 839488*t*z^4 - 4861360*t*z^3 + 6767200*t*z^2 - 4314000*t*z + 1080000*t - 96*z^10 + 2304*z^9 - 21968*z^8 + 109744*z^7 - 310560*z^6 + 478400*z^5 - 263168*z^4 - 335440*z^3 + 696800*z^2 - 476000*z + 120000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-16*t^8*z^2 + 240*t^8*z - 1120*t^8 + 144*t^7*z^3 - 2368*t^7*z^2 + 13200*t^7*z - 25360*t^7 - 480*t^6*z^4 + 8816*t^6*z^3 - 58688*t^6*z^2 + 163440*t^6*z - 148560*t^6 + 704*t^5*z^5 - 15168*t^5*z^4 + 124016*t^5*z^3 - 471024*t^5*z^2 + 801280*t^5*z - 464080*t^5 - 368*t^4*z^6 + 11104*t^4*z^5 - 122960*t^4*z^4 + 647280*t^4*z^3 - 1694496*t^4*z^2 + 2061440*t^4*z - 930720*t^4 - 80*t^3*z^7 - 688*t^3*z^6 + 35344*t^3*z^5 - 338416*t^3*z^4 + 1428112*t^3*z^3 - 2960480*t^3*z^2 + 2922640*t^3*z - 1080400*t^3 + 96*t^2*z^8 - 2464*t^2*z^7 + 20208*t^2*z^6 - 48560*t^2*z^5 - 158032*t^2*z^4 + 1097888*t^2*z^3 - 2286048*t^2*z^2 + 2080080*t^2*z - 708560*t^2 + 208*t*z^8 - 4592*t*z^7 + 36016*t*z^6 - 122960*t*z^5 + 144256*t*z^4 + 179424*t*z^3 - 663648*t*z^2 + 646000*t*z - 218960*t + 96*z^8 - 1824*z^7 + 12368*z^6 - 38784*z^5 + 54800*z^4 - 10480*z^3 - 63232*z^2 + 71680*z - 22240)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_59 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 59) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_59 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 18*t*z + 20*t + 4*z^2 - 12*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t - 4)*hf
  · have hr : (16*t^8 - 48*t^7*z^2 - 96*t^7*z + 400*t^7 + 48*t^6*z^4 + 416*t^6*z^3 - 1312*t^6*z^2 - 1760*t^6*z + 4400*t^6 - 16*t^5*z^6 - 576*t^5*z^5 + 960*t^5*z^4 + 7296*t^5*z^3 - 11856*t^5*z^2 - 18240*t^5*z + 29600*t^5 + 288*t^4*z^7 + 784*t^4*z^6 - 10192*t^4*z^5 + 2704*t^4*z^4 + 70592*t^4*z^3 - 73616*t^4*z^2 - 100240*t^4*z + 127600*t^4 - 32*t^3*z^9 - 1024*t^3*z^8 + 4752*t^3*z^7 + 12144*t^3*z^6 - 62576*t^3*z^5 - 62032*t^3*z^4 + 455600*t^3*z^3 - 387760*t^3*z^2 - 276400*t^3*z + 346000*t^3 + 192*t^2*z^10 + 352*t^2*z^9 - 9440*t^2*z^8 + 784*t^2*z^7 + 180368*t^2*z^6 - 446064*t^2*z^5 - 83568*t^2*z^4 + 1368368*t^2*z^3 - 1211920*t^2*z^2 - 324400*t^2*z + 554000*t^2 - 352*t*z^11 + 2032*t*z^10 + 3408*t*z^9 - 28672*t*z^8 - 91392*t*z^7 + 770464*t*z^6 - 1531936*t*z^5 + 490432*t*z^4 + 1919200*t*z^3 - 2038800*t*z^2 + 82000*t*z + 440000*t + 192*z^12 - 1312*z^11 - 6080*z^10 + 90976*z^9 - 369280*z^8 + 630016*z^7 - 108096*z^6 - 1174272*z^5 + 1416192*z^4 - 35040*z^3 - 723200*z^2 + 164000*z + 120000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t^7 - 48*t^6*z^2 - 656*t^6*z - 1728*t^6 + 16*t^5*z^4 + 656*t^5*z^3 + 2240*t^5*z^2 + 624*t^5*z + 3776*t^5 - 288*t^4*z^5 - 2224*t^4*z^4 + 512*t^4*z^3 + 10976*t^4*z^2 - 18272*t^4*z - 72624*t^4 + 32*t^3*z^7 + 1184*t^3*z^6 + 1008*t^3*z^5 - 13024*t^3*z^4 - 7584*t^3*z^3 + 89232*t^3*z^2 + 28480*t^3*z + 84000*t^3 - 192*t^2*z^8 - 1312*t^2*z^7 + 3840*t^2*z^6 + 24976*t^2*z^5 - 74688*t^2*z^4 - 52256*t^2*z^3 + 195728*t^2*z^2 - 128448*t^2*z - 408960*t^2 + 352*t*z^9 - 272*t*z^8 - 6528*t*z^7 - 2608*t*z^6 + 110992*t*z^5 - 202464*t*z^4 - 35344*t*z^3 + 345168*t*z^2 - 16640*t*z + 229760*t - 192*z^10 + 352*z^9 + 8800*z^8 - 48736*z^7 + 81600*z^6 + 21664*z^5 - 191584*z^4 + 108032*z^3 + 81888*z^2 - 95680*z - 164640)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_60 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 60) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_60 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 14*t*z + 16*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 416*t^7*z + 592*t^7 + 144*t^6*z^4 - 1424*t^6*z^3 + 5648*t^6*z^2 - 10864*t^6*z + 8288*t^6 + 112*t^5*z^6 - 1488*t^5*z^5 + 8880*t^5*z^4 - 31856*t^5*z^3 + 72576*t^5*z^2 - 96000*t^5*z + 54944*t^5 + 32*t^4*z^8 - 368*t^4*z^7 + 1584*t^4*z^6 - 4016*t^4*z^5 + 15440*t^4*z^4 - 74160*t^4*z^3 + 212048*t^4*z^2 - 302960*t^4*z + 170320*t^4 + 112*t^3*z^9 - 2128*t^3*z^8 + 18192*t^3*z^7 - 93344*t^3*z^6 + 316768*t^3*z^5 - 716160*t^3*z^4 + 1006800*t^3*z^3 - 715552*t^3*z^2 + 48080*t^3*z + 165904*t^3 + 112*t^2*z^10 - 2112*t^2*z^9 + 16096*t^2*z^8 - 59088*t^2*z^7 + 67472*t^2*z^6 + 295008*t^2*z^5 - 1455616*t^2*z^4 + 2910768*t^2*z^3 - 3020512*t^2*z^2 + 1458816*t^2*z - 182272*t^2 + 32*t*z^11 - 336*t*z^10 - 2048*t*z^9 + 53840*t*z^8 - 402464*t*z^7 + 1632672*t*z^6 - 4029456*t*z^5 + 6155920*t*z^4 - 5582432*t*z^3 + 2655760*t*z^2 - 481936*t*z + 16832*t + 128*z^11 - 3168*z^10 + 34000*z^9 - 206896*z^8 + 782800*z^7 - 1897248*z^6 + 2919792*z^5 - 2717744*z^4 + 1362224*z^3 - 268448*z^2 - 6720*z + 5376:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 + 704*t^6*z - 1408*t^6 - 112*t^5*z^4 + 928*t^5*z^3 - 3680*t^5*z^2 + 8816*t^5*z - 10096*t^5 - 32*t^4*z^6 + 208*t^4*z^5 - 384*t^4*z^4 + 1056*t^4*z^3 - 8240*t^4*z^2 + 27680*t^4*z - 32448*t^4 - 112*t^3*z^7 + 1568*t^3*z^6 - 9792*t^3*z^5 + 36544*t^3*z^4 - 85088*t^3*z^3 + 108000*t^3*z^2 - 41360*t^3*z - 31248*t^3 - 112*t^2*z^8 + 1552*t^2*z^7 - 7776*t^2*z^6 + 12448*t^2*z^5 + 33648*t^2*z^4 - 189008*t^2*z^3 + 342336*t^2*z^2 - 254048*t^2*z + 38592*t^2 - 32*t*z^9 + 176*t*z^8 + 3088*t*z^7 - 39280*t*z^6 + 190624*t*z^5 - 483152*t*z^4 + 660576*t*z^3 - 437280*t*z^2 + 93152*t*z - 3600*t - 128*z^9 + 2528*z^8 - 20720*z^7 + 90656*z^6 - 225920*z^5 + 314368*z^4 - 218352*z^3 + 54144*z^2 + 256*z - 992)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_61 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 61) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_61 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 10*t*z - 2*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 288*t^7*z + 80*t^7 + 144*t^6*z^4 - 880*t^6*z^3 + 1104*t^6*z^2 + 880*t^6*z - 800*t^6 + 112*t^5*z^6 - 672*t^5*z^5 - 816*t^5*z^4 + 12096*t^5*z^3 - 24576*t^5*z^2 + 15360*t^5*z - 2400*t^5 + 32*t^4*z^8 + 144*t^4*z^7 - 5264*t^4*z^6 + 31184*t^4*z^5 - 74768*t^4*z^4 + 68048*t^4*z^3 + 5584*t^4*z^2 - 35440*t^4*z + 11600*t^4 + 224*t^3*z^9 - 2880*t^3*z^8 + 10864*t^3*z^7 + 10352*t^3*z^6 - 186896*t^3*z^5 + 554624*t^3*z^4 - 757424*t^3*z^3 + 503840*t^3*z^2 - 143600*t^3*z + 10000*t^3 + 544*t^2*z^10 - 10480*t^2*z^9 + 83824*t^2*z^8 - 358080*t^2*z^7 + 868976*t^2*z^6 - 1147008*t^2*z^5 + 605504*t^2*z^4 + 271888*t^2*z^3 - 488320*t^2*z^2 + 189600*t^2*z - 16000*t^2 + 544*t*z^11 - 12464*t*z^10 + 122848*t*z^9 - 680592*t*z^8 + 2322192*t*z^7 - 5017040*t*z^6 + 6748176*t*z^5 - 5184512*t*z^4 + 1560720*t*z^3 + 598000*t*z^2 - 578000*t*z + 120000*t + 192*z^12 - 4896*z^11 + 54336*z^10 - 343040*z^9 + 1347088*z^8 - 3350384*z^7 + 4992704*z^6 - 3245536*z^5 - 2376608*z^4 + 6981360*z^3 - 6319200*z^2 + 2744000*z - 480000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 + 160*t^6*z + 416*t^6 - 112*t^5*z^4 + 112*t^5*z^3 + 1936*t^5*z^2 - 2976*t^5*z + 16*t^5 - 32*t^4*z^6 - 304*t^4*z^5 + 3904*t^4*z^4 - 10144*t^4*z^3 + 4528*t^4*z^2 + 5312*t^4*z - 1664*t^4 - 224*t^3*z^7 + 1760*t^3*z^6 - 944*t^3*z^5 - 23872*t^3*z^4 + 72256*t^3*z^3 - 73984*t^3*z^2 + 26224*t^3*z - 2800*t^3 - 544*t^2*z^8 + 7760*t^2*z^7 - 42304*t^2*z^6 + 107760*t^2*z^5 - 118656*t^2*z^4 + 14928*t^2*z^3 + 62416*t^2*z^2 - 34448*t^2*z + 4000*t^2 - 544*t*z^9 + 9744*t*z^8 - 71408*t*z^7 + 274832*t*z^6 - 590992*t*z^5 + 687920*t*z^4 - 353616*t*z^3 - 23168*t*z^2 + 91520*t*z - 24560*t - 192*z^10 + 3936*z^9 - 33696*z^8 + 154880*z^7 - 404208*z^6 + 554944*z^5 - 196944*z^4 - 513904*z^3 + 791808*z^2 - 452800*z + 96160)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_62 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 62) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_62 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 + 2*t*z^2 - 18*t*z + 20*t + 4*z^2 - 12*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t - 4)*hf
  · have hr : (16*t^8 + 80*t^7*z^2 - 544*t^7*z + 720*t^7 + 144*t^6*z^4 - 1968*t^6*z^3 + 9456*t^6*z^2 - 18640*t^6*z + 12800*t^6 + 112*t^5*z^6 - 2304*t^5*z^5 + 19296*t^5*z^4 - 83920*t^5*z^3 + 198624*t^5*z^2 - 240240*t^5*z + 115600*t^5 + 32*t^4*z^8 - 880*t^4*z^7 + 10736*t^4*z^6 - 75696*t^4*z^5 + 333968*t^4*z^4 - 929584*t^4*z^3 + 1568784*t^4*z^2 - 1453040*t^4*z + 563600*t^4 + 144*t^3*z^8 - 4064*t^3*z^7 + 48912*t^3*z^6 - 326832*t^3*z^5 + 1321648*t^3*z^4 - 3301376*t^3*z^3 + 4963440*t^3*z^2 - 4105200*t^3*z + 1432000*t^3 - 32*t^2*z^10 + 976*t^2*z^9 - 12608*t^2*z^8 + 88944*t^2*z^7 - 364496*t^2*z^6 + 818976*t^2*z^5 - 613216*t^2*z^4 - 1491152*t^2*z^3 + 4329680*t^2*z^2 - 4352400*t^2*z + 1624000*t^2 - 32*t*z^10 + 992*t*z^9 - 13216*t*z^8 + 98544*t*z^7 - 447664*t*z^6 + 1255744*t*z^5 - 2057664*t*z^4 + 1527280*t*z^3 + 460400*t*z^2 - 1568000*t*z + 760000*t + 16*z^9 - 464*z^8 + 5680*z^7 - 37952*z^6 + 148944*z^5 - 340688*z^4 + 407760*z^3 - 143200*z^2 - 156000*z + 120000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-80*t^7 - 144*t^6*z^2 + 1248*t^6*z - 2496*t^6 - 112*t^5*z^4 + 1744*t^5*z^3 - 10016*t^5*z^2 + 25120*t^5*z - 22944*t^5 - 32*t^4*z^6 + 720*t^4*z^5 - 6976*t^4*z^4 + 37216*t^4*z^3 - 113008*t^4*z^2 + 178464*t^4*z - 111424*t^4 - 144*t^3*z^6 + 3344*t^3*z^5 - 31472*t^3*z^4 + 152752*t^3*z^3 - 400528*t^3*z^2 + 534976*t^3*z - 285920*t^3 + 32*t^2*z^8 - 816*t^2*z^7 + 8368*t^2*z^6 - 43024*t^2*z^5 + 107536*t^2*z^4 - 66176*t^2*z^3 - 255344*t^2*z^2 + 545312*t^2*z - 326400*t^2 + 32*t*z^8 - 832*t*z^7 + 8896*t*z^6 - 49904*t*z^5 + 153664*t*z^4 - 237904*t*z^3 + 99824*t*z^2 + 161360*t*z - 152720*t - 16*z^7 + 384*z^6 - 3680*z^5 + 17632*z^4 - 42384*z^3 + 40608*z^2 + 7200*z - 23840)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_2_63 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t 63) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : False := by
  apply cell_2_63 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t*z^2 - 12*t*z + 10*t - 2*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2*t)*hf
  · have hr : (160*t*z^10 - 3552*t*z^9 + 32864*t*z^8 - 162352*t*z^7 + 448336*t*z^6 - 618368*t*z^5 + 111152*t*z^4 + 794960*t*z^3 - 847200*t*z^2 + 124000*t*z + 120000*t + 160*z^11 - 3552*z^10 + 33504*z^9 - 171920*z^8 + 501424*z^7 - 737088*z^6 + 114976*z^5 + 1179712*z^4 - 1205040*z^3 - 211200*z^2 + 484000*z + 120000:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t*z^8 + 2752*t*z^7 - 18304*t*z^6 + 57072*t*z^5 - 71456*t*z^4 - 24272*t*z^3 + 124768*t*z^2 - 49760*t*z - 25440*t - 160*z^9 + 2752*z^8 - 18944*z^7 + 63440*z^6 - 89504*z^5 - 27632*z^4 + 194384*z^3 - 69632*z^2 - 115040*z - 15840)*hf


private def limit2 (_z _t : ℝ) : Fin 64→Prop := ![False,False,False,False,False,False,False,False,False,False,(((0:ℝ):ℝ)=0),False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False]

private def hue2 : Fin 64→Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma exclude_field_2 (z t : ℝ) (hf : z^2 - 5*z + 5=0) (hn0 : t-(1)≠0) (hn1 : t-(5 - z)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (g : Fin 5→Fin 64) (hinj : Function.Injective g)
    (hc : ∀ i, cell (1) (1) (5 - z) (profile4 (5 - z) (z) t (g i)) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t)
    (he : ∀ i j : Fin 5, i≠j → edge4 (1) (1) (5 - z) (profile4 (5 - z) (z) t (g i)) (profile4 (5 - z) (z) t (g j)) (5 - z) (z) t=0) : False := by
  have row (k : Fin 64) (hh : cell (1) (1) (5 - z) (profile4 (5 - z) (z) t k) ((1),(5 - z),(z)) ((1),(z),(5 - z)) (5 - z) (z) t) : limit2 z t k := by
    fin_cases k
    · exact row_2_0 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_1 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_2 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_3 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_4 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_5 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_6 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_7 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_8 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_9 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_10 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_11 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_12 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_13 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_14 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_15 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_16 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_17 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_18 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_19 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_20 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_21 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_22 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_23 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_24 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_25 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_26 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_27 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_28 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_29 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_30 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_31 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_32 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_33 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_34 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_35 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_36 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_37 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_38 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_39 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_40 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_41 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_42 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_43 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_44 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_45 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_46 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_47 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_48 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_49 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_50 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_51 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_52 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_53 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_54 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_55 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_56 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_57 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_58 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_59 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_60 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_61 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_62 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_2_63 z t hf hn0 hn1 hn2 hn3 hh
  have allowed (k : Fin 64) (hh : limit2 z t k) : k∈([10]:List (Fin 64)) := by
    fin_cases k <;> first | decide | exact False.elim hh
  have cert : ∀ i j : Fin 64, i∈([10]:List (Fin 64)) → j∈([10]:List (Fin 64)) → i<j → hue2 i=hue2 j → (i,j)∈([]:List (Fin 64×Fin 64)) := by decide
  have bad (i j : Fin 64) (hi : limit2 z t i) (hj : limit2 z t j) (hlt : i<j) (hc : hue2 i=hue2 j) (hb : edge4 (1) (1) (5 - z) (profile4 (5 - z) (z) t i) (profile4 (5 - z) (z) t j) (5 - z) (z) t=0) : False := by
    have h := cert i j (allowed i hi) (allowed j hj) hlt hc
    simpa using h
  have hi : Function.Injective (fun i : Fin 5 => hue2 (g i)) := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne (show g i≠g j from fun e => hne (hinj e)) with hl|hl
    · exact bad _ _ (row _ (hc i)) (row _ (hc j)) hl h (he i j hne)
    · exact bad _ _ (row _ (hc j)) (row _ (hc i)) hl h.symm (he j i (Ne.symm hne))
  have hh := Fintype.card_le_of_injective _ hi
  norm_num at hh

private lemma cell_3_0 (z t : ℝ) (_hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_3_1 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/8 - 3/4)*h0 + (-1/8)*hf
  norm_num at hh

private lemma cell_3_2 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (10*z - 8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (5*z/88 - 9/22)*h0 + (-25/44)*hf
  norm_num at hh

private lemma cell_3_3 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z - 112) + t^6*(384*z + 96) + t^5*(816 - 1680*z) + t^4*(2736*z - 1872) + t^3*(1800*z - 720) + t^2*(6480 - 11880*z) + t*(11232*z - 6048):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(5/648 - z/1296) - t^5/27 + t^4*(7*z/216 + 1/108) + t^3*(7/72 - 5*z/48) + t^2*(z/24 - 1/12) + t*(z/3 - 1/4) - 11*z/24 + 1/12)*h0 + (z/10368 - 5/5184)*h1 + (t^7/324 - t^6/27 + 35*t^5/216 - 19*t^4/72 - 25*t^3/144 + 55*t^2/48 - 13*t/12)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_3_4 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/8 - 3/4)*h0 + (-1/8)*hf
  norm_num at hh

private lemma cell_3_5 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h1 : (t*(5184*z - 2592):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (5/864 - z/1296)*h1 + (4*t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_3_6 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z/16 - 11/8)*h0 + (-9/8)*hf
  norm_num at hh

private lemma cell_3_7 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-z - 4) + 2*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 48) + t^6*(968*z - 496) + t^5*(3584 - 6072*z) + t^4*(17968*z - 9840) + t^3*(9904 - 19256*z) + t^2*(5296 - 9528*z) + t*(26672*z - 14112) - 8128*z + 4352:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z - 48) + t^6*(1160*z - 496) + t^5*(5888 - 11112*z) + t^4*(69376*z - 37200) + t^3*(156208 - 291320*z) + t^2*(801480*z - 429584) + t*(705024 - 1315552*z) + 978032*z - 524128:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(3691/314928 - 989*z/629856) + t^12*(5953*z/629856 - 22217/314928) + t^11*(1019/17496 - 91*z/11664) + t^10*(39773/157464 - 10663*z/314928) + t^9*(13733*z/314928 - 51013/157464) + t^8*(95*z/5832 - 389/2916) + t^7*(41933/104976 - 9367*z/209952) + t^6*(-2881*z/209952 - 17407/104976) + t^5*(439*z/5832 + 136/729) + t^4*(25399/78732 - 4285*z/19683) + t^3*(31583*z/78732 - 158675/78732) + t^2*(901*z/3888 - 19627/17496) + t*(119347/78732 - 12641*z/39366) - 10937*z/39366 + 44789/39366)*h0 + (t^7*(989*z/5038848 - 3691/2519424) + t^6*(11603/2519424 - 3109*z/5038848) + t^5*(43*z/139968 - 107/46656) + t^4*(3877/2519424 - 1037*z/5038848) + t^3*(12721/2519424 - 3419*z/5038848) + t^2*(43/23328 - 67*z/279936) + t*(12991/1259712 - 881*z/629856) - 3115*z/1259712 + 5857/314928)*h1 + (11*z/31104 - 41/15552)*h2 + (6923*t^14/629856 - 68305*t^13/314928 + 280601*t^12/157464 - 4788127*t^11/629856 + 669157*t^10/39366 - 1276247*t^9/78732 - 1166369*t^8/209952 + 3049417*t^7/104976 - 1592597*t^6/52488 + 6671177*t^5/629856 + 625379*t^4/78732 + 6673469*t^3/157464 - 85795487*t^2/314928 + 10239050*t/19683 - 57541501/157464)*hf
  norm_num at hh

private lemma cell_3_8 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (10*z - 8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (5*z/88 - 9/22)*h0 + (-25/44)*hf
  norm_num at hh

private lemma cell_3_9 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z/16 - 11/8)*h0 + (-9/8)*hf
  norm_num at hh

private lemma cell_3_10 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (8*z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z/23 - 29/46)*h0 + (-16/23)*hf
  norm_num at hh

private lemma cell_3_11 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-96*z - 48) + t^6*(2256*z - 1104) + t^5*(14400 - 26352*z) + t^4*(187632*z - 100944) + t^3*(450144 - 840456*z) + t^2*(2300400*z - 1232496) + t*(1870128 - 3489480*z) + 2220048*z - 1189728:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(139687/182736 - 37429*z/365472) + t^6*(28573*z/45684 - 426545/91368) + t^5*(276953/60912 - 8245*z/13536) + t^4*(830909/60912 - 222679*z/121824) + t^3*(2956*z/1269 - 176399/10152) + t^2*(24751*z/13536 - 92573/6768) + t*(41365/3384 - 5521*z/3384) - 85*z/94 + 3799/564)*h0 + (t*(37429*z/2923776 - 139687/1461888) - 90865*z/2923776 + 339113/1461888)*h1 + (187145*t^8/182736 - 5369521*t^7/182736 + 24287803*t^6/60912 - 195972295*t^5/60912 + 14357081*t^4/864 - 250834477*t^3/4512 + 1572036565*t^2/13536 - 617459603*t/4512 + 51892075/752)*hf
  norm_num at hh

private lemma cell_3_12 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z - 112) + t^6*(384*z + 96) + t^5*(816 - 1680*z) + t^4*(2736*z - 1872) + t^3*(1800*z - 720) + t^2*(6480 - 11880*z) + t*(11232*z - 6048):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(5/648 - z/1296) - t^5/27 + t^4*(7*z/216 + 1/108) + t^3*(7/72 - 5*z/48) + t^2*(z/24 - 1/12) + t*(z/3 - 1/4) - 11*z/24 + 1/12)*h0 + (z/10368 - 5/5184)*h1 + (t^7/324 - t^6/27 + 35*t^5/216 - 19*t^4/72 - 25*t^3/144 + 55*t^2/48 - 13*t/12)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_3_13 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-z - 4) + 2*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 48) + t^6*(968*z - 496) + t^5*(3584 - 6072*z) + t^4*(17968*z - 9840) + t^3*(9904 - 19256*z) + t^2*(5296 - 9528*z) + t*(26672*z - 14112) - 8128*z + 4352:ℝ)=0) : (t - 2:ℝ)=0 := by
  have hh : (t - 2:ℝ)=0 := by linear_combination (t^6*(97/324 - 13*z/324) + t^5*(25*z/216 - 31/36) + t^4*(2*z/9 - 91/54) + t^3*(227/81 - 235*z/648) + t^2*(10/3 - 49*z/108) + t*(5*z/24 - 185/108) + 89*z/324 - 173/81)*h0 + (13*z/2592 - 97/2592)*h1 + (91*t^7/324 - 3019*t^6/648 + 274*t^5/9 - 58919*t^4/648 + 31379*t^3/324 + 3521*t^2/72 - 10847*t/81 + 6515/162)*hf
  exact hh

private lemma cell_3_14 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-96*z - 48) + t^6*(2256*z - 1104) + t^5*(14400 - 26352*z) + t^4*(187632*z - 100944) + t^3*(450144 - 840456*z) + t^2*(2300400*z - 1232496) + t*(1870128 - 3489480*z) + 2220048*z - 1189728:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(139687/182736 - 37429*z/365472) + t^6*(28573*z/45684 - 426545/91368) + t^5*(276953/60912 - 8245*z/13536) + t^4*(830909/60912 - 222679*z/121824) + t^3*(2956*z/1269 - 176399/10152) + t^2*(24751*z/13536 - 92573/6768) + t*(41365/3384 - 5521*z/3384) - 85*z/94 + 3799/564)*h0 + (t*(37429*z/2923776 - 139687/1461888) - 90865*z/2923776 + 339113/1461888)*h1 + (187145*t^8/182736 - 5369521*t^7/182736 + 24287803*t^6/60912 - 195972295*t^5/60912 + 14357081*t^4/864 - 250834477*t^3/4512 + 1572036565*t^2/13536 - 617459603*t/4512 + 51892075/752)*hf
  norm_num at hh

private lemma cell_3_15 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 48) + t^6*(968*z - 496) + t^5*(3584 - 6072*z) + t^4*(17968*z - 9840) + t^3*(9904 - 19256*z) + t^2*(5296 - 9528*z) + t*(26672*z - 14112) - 8128*z + 4352:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(145/2916 - 13*z/1944) + t^6*(65*z/1944 - 355/1458) + t^5*(1/81 - 23*z/1944) + t^4*(725/729 - 47*z/648) + t^3*(-253*z/1944 - 835/2916) + t^2*(673*z/1944 - 481/324) + t*(119*z/972 + 185/1458) - z/3 + 1049/1458)*h0 + (t*(13*z/15552 - 145/23328) - 73*z/23328 + 181/7776)*h1 + (13*t^8/243 - 5887*t^7/5832 + 47267*t^6/5832 - 8267*t^5/243 + 421789*t^4/5832 - 304973*t^3/5832 - 469*t^2/9 + 131597*t/1458 - 18542/729)*hf
  norm_num at hh

private lemma cell_3_16 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/8 - 3/4)*h0 + (-1/8)*hf
  norm_num at hh

private lemma cell_3_17 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h2 : (t*(5184*z - 2592):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (5/864 - z/1296)*h2 + (4*t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_3_18 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z/16 - 11/8)*h0 + (-9/8)*hf
  norm_num at hh

private lemma cell_3_19 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-z - 4) + 2*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 48) + t^6*(1160*z - 496) + t^5*(5888 - 11112*z) + t^4*(69376*z - 37200) + t^3*(156208 - 291320*z) + t^2*(801480*z - 429584) + t*(705024 - 1315552*z) + 978032*z - 524128:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z - 48) + t^6*(968*z - 496) + t^5*(3584 - 6072*z) + t^4*(17968*z - 9840) + t^3*(9904 - 19256*z) + t^2*(5296 - 9528*z) + t*(26672*z - 14112) - 8128*z + 4352:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(989*z/629856 - 3691/314928) + t^12*(14305/157464 - 3833*z/314928) + t^11*(2461*z/104976 - 9185/52488) + t^10*(3863*z/157464 - 14407/78732) + t^9*(122833/157464 - 32969*z/314928) + t^8*(1477*z/34992 - 5339/17496) + t^7*(19621*z/209952 - 78803/104976) + t^6*(32861/52488 - 5953*z/104976) + t^5*(6499/17496 - 4205*z/34992) + t^4*(21139*z/314928 + 48229/157464) + t^3*(1852*z/19683 - 85123/78732) + t^2*(6923*z/52488 - 23489/13122) + t*(13685*z/157464 + 12239/19683) - 11101*z/39366 + 23429/19683)*h0 + (t^7*(3691/2519424 - 989*z/5038848) + t^6*(2411*z/2519424 - 4499/629856) + t^5*(71/419904 - 19*z/839808) + t^4*(76247/2519424 - 20431*z/5038848) + t^3*(473*z/314928 - 1765/157464) + t^2*(577*z/104976 - 17227/419904) + t*(8063/1259712 - 2161*z/2519424) - 6187*z/2519424 + 23093/1259712)*h1 + (7/324 - 5*z/1728)*h2 + (-6923*t^14/629856 + 172337*t^13/629856 - 2043725*t^12/629856 + 1889171*t^11/78732 - 9382871*t^10/78732 + 123284357*t^9/314928 - 155411239*t^8/209952 + 51460687*t^7/209952 + 490528079*t^6/209952 - 385756039*t^5/78732 + 59387687*t^4/39366 + 111765425*t^3/19683 - 1437230377*t^2/314928 - 364531411*t/157464 + 374578237/157464)*hf
  norm_num at hh

private lemma cell_3_20 (z t : ℝ) (_hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) : ((0:ℝ):ℝ)=0 := by
  rfl

private lemma cell_3_21 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 3*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (11/4 - 3*z/8)*h0 + (-9/8)*hf
  norm_num at hh

private lemma cell_3_22 (z t : ℝ) (_hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) : ((0:ℝ):ℝ)=0 := by
  rfl

private lemma cell_3_23 (z t : ℝ) (_hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 2) + 2*z:ℝ)=0) : False := by
  have hh : ((t-(1))*(t-(z)))*(1:ℝ)=0 := by linear_combination (1/2)*h0
  have hv := (mul_eq_zero.mp hh).resolve_left (mul_ne_zero hn0 hn2)
  norm_num at hv

private lemma cell_3_24 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z/16 - 11/8)*h0 + (-9/8)*hf
  norm_num at hh

private lemma cell_3_25 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h2 : (t*(85536 - 159408*z) + 2220048*z - 1189728:ℝ)=0) : (t - 2*z + 1:ℝ)=0 := by
  have hh : (t - 2*z + 1:ℝ)=0 := by linear_combination (17/1728 - 41*z/31104)*h2 + (23411/8 - 1681*t/8)*hf
  exact hh

private lemma cell_3_26 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 2)*h0 + (1/4)*hf
  norm_num at hh

private lemma cell_3_27 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-3*z - 2) + 9*z - 4:ℝ)=0) (h2 : (16*t^8 + t^7*(16 - 128*z) + t^6*(3640*z - 2016) + t^5*(31184 - 57720*z) + t^4*(593720*z - 318112) + t^3*(2170416 - 4050688*z) + t^2*(17893392*z - 9589040) + t*(25106800 - 46849688*z) + 55861264*z - 29935968:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(181/2916 - 97*z/11664) + t^6*(797*z/11664 - 1487/2916) + t^5*(85/486 - 23*z/972) + t^4*(18703/5832 - 311*z/729) + t^3*(661*z/11664 - 445/729) + t^2*(1673*z/1944 - 2651/486) + t*(-2021*z/5832 - 457/1458) + 469*z/1458 + 1054/729)*h0 + (t*(97*z/93312 - 181/23328) - 653*z/93312 + 2437/46656)*h2 + (1261*t^8/11664 - 51319*t^7/11664 + 988969*t^6/11664 - 5961347*t^5/5832 + 48811877*t^4/5832 - 547570621*t^3/11664 + 2028498121*t^2/11664 - 4501375975*t/11664 + 2279820953/5832)*hf
  norm_num at hh

private lemma cell_3_28 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-z - 4) + 2*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 48) + t^6*(1160*z - 496) + t^5*(5888 - 11112*z) + t^4*(69376*z - 37200) + t^3*(156208 - 291320*z) + t^2*(801480*z - 429584) + t*(705024 - 1315552*z) + 978032*z - 524128:ℝ)=0) : False := by
  have hh : ((t-(z/2)))*(1:ℝ)=0 := by linear_combination (t^6*(71/1944 - 19*z/3888) + t^5*(z/72 - 17/162) + t^4*(1/36 - z/648) + t^3*(-53*z/3888 - 41/1944) + t^2*(11*z/108 - 29/162) + t*(5/108 - 37*z/162) + 187*z/486 - 113/243)*h0 + (19*z/31104 - 71/15552)*h1 + (133*t^7/3888 - 2663*t^6/3888 + 8759*t^5/1296 - 164809*t^4/3888 + 692387*t^3/3888 - 635065*t^2/1296 + 781927*t/972 - 1162909/1944)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_3_29 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 2) + 2*z:ℝ)=0) (h2 : (16*t^8 - 176*t^7 + t^6*(688 - 72*z) + t^5*(648*z - 1184) + t^4*(496 - 1152*z) + t^3*(2224 - 2808*z) + t^2*(5832*z - 3152) + t*(3744*z - 2048) - 1008*z + 544:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(1549/5832 - 415*z/11664) + t^6*(4415*z/11664 - 1831/648) + t^5*(9457/972 - 1267*z/972) + t^4*(15785*z/11664 - 58865/5832) + t^3*(10013*z/11664 - 12475/1944) + t^2*(2396/243 - 2581*z/1944) + t*(5995/1458 - 3185*z/5832) - 76*z/729 + 209/243)*h0 + (t*(415*z/93312 - 1549/46656) - 487*z/93312 + 1819/46656)*h2 + (-415*t^8/5832 + 4465*t^7/3888 - 19309*t^6/2916 + 161185*t^5/11664 + 21331*t^4/3888 - 262235*t^3/5832 + 179035*t^2/11664 + 48419*t/1944 - 29465/5832)*hf
  norm_num at hh

private lemma cell_3_30 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-3*z - 2) + 9*z - 4:ℝ)=0) (h2 : (16*t^8 + t^7*(-32*z - 176) + t^6*(544*z + 528) + t^5*(656 - 3864*z) + t^4*(14816*z - 7312) + t^3*(17520 - 31648*z) + t^2*(31344*z - 17072) + t*(1240*z - 656) - 18800*z + 10080:ℝ)=0) : False := by
  have hh : ((t-(z/2)))*(1:ℝ)=0 := by linear_combination (t^6*(71*z/7776 - 265/3888) + t^5*(907/1296 - 3*z/32) + t^4*(191*z/648 - 713/324) + t^3*(6877/3888 - 1841*z/7776) + t^2*(1843/1296 - 55*z/288) + t*(47*z/648 - 355/648) + 89*z/1944 - 97/243)*h0 + (265/31104 - 71*z/62208)*h2 + (-71*t^7/7776 + 1001*t^6/3888 - 869*t^5/324 + 105341*t^4/7776 - 134381*t^3/3888 + 97745*t^2/2592 + 6997*t/7776 - 85027/3888)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_3_31 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 3*z:ℝ)=0) (h1 : (16*t^8 + t^7*(80 - 128*z) + t^6*(2904*z - 1680) + t^5*(19104 - 35736*z) + t^4*(260928*z - 139536) + t^3*(613296 - 1144440*z) + t^2*(2933064*z - 1572048) + t*(2146176 - 4004640*z) + 2220048*z - 1189728:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(3161/972 - 847*z/1944) + t^6*(1139/324 - 305*z/648) + t^5*(2069*z/648 - 7735/324) + t^4*(68*z/27 - 497/27) + t^3*(160/3 - 89*z/12) + t^2*(319/18 - 29*z/18) + t*(73*z/18 - 344/9) - z/12 + 14/3)*h0 + (t*(847*z/15552 - 3161/7776) - 17*z/144 + 571/648)*h1 + (5929*t^8/972 - 56021*t^7/324 + 186049*t^6/81 - 1327259*t^5/72 + 20111893*t^4/216 - 21227783*t^3/72 + 10158839*t^2/18 - 7124299*t/12 + 1048357/4)*hf
  norm_num at hh

private lemma cell_3_32 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (10*z - 8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (5*z/88 - 9/22)*h0 + (-25/44)*hf
  norm_num at hh

private lemma cell_3_33 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z/16 - 11/8)*h0 + (-9/8)*hf
  norm_num at hh

private lemma cell_3_34 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (8*z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z/23 - 29/46)*h0 + (-16/23)*hf
  norm_num at hh

private lemma cell_3_35 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-96*z - 48) + t^6*(2736*z - 1296) + t^5*(23472 - 43848*z) + t^4*(483120*z - 259056) + t^3*(2000592 - 3732912*z) + t^2*(20005488*z - 10720944) + t*(36483696 - 68079528*z) + 121465008*z - 65092896:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(846541/983664 - 37805*z/327888) + t^6*(694013*z/983664 - 1295045/245916) + t^5*(947131/109296 - 190339*z/163944) + t^4*(55447*z/655776 - 103285/163944) + t^3*(21961*z/19872 - 82061/9936) + t^2*(56939/9108 - 60419*z/72864) + t*(995*z/6624 - 4501/3312) + 2201*z/12144 - 1913/2024)*h0 + (t*(37805*z/2623104 - 846541/7869312) - 276703*z/7869312 + 2065339/7869312)*h1 + (189025*t^8/163944 - 2459960*t^7/61479 + 78405313*t^6/109296 - 695989187*t^5/81972 + 7736921897*t^4/109296 - 15286795277*t^3/36432 + 10229088643*t^2/6072 - 50329899461*t/12144 + 8644474021/2024)*hf
  norm_num at hh

private lemma cell_3_36 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z/16 - 11/8)*h0 + (-9/8)*hf
  norm_num at hh

private lemma cell_3_37 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(85536 - 159408*z) + 2220048*z - 1189728:ℝ)=0) : (t - 2*z + 1:ℝ)=0 := by
  have hh : (t - 2*z + 1:ℝ)=0 := by linear_combination (17/1728 - 41*z/31104)*h1 + (23411/8 - 1681*t/8)*hf
  exact hh

private lemma cell_3_38 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 2)*h0 + (1/4)*hf
  norm_num at hh

private lemma cell_3_39 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-3*z - 2) + 9*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 128*z) + t^6*(3640*z - 2016) + t^5*(31184 - 57720*z) + t^4*(593720*z - 318112) + t^3*(2170416 - 4050688*z) + t^2*(17893392*z - 9589040) + t*(25106800 - 46849688*z) + 55861264*z - 29935968:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(181/2916 - 97*z/11664) + t^6*(797*z/11664 - 1487/2916) + t^5*(85/486 - 23*z/972) + t^4*(18703/5832 - 311*z/729) + t^3*(661*z/11664 - 445/729) + t^2*(1673*z/1944 - 2651/486) + t*(-2021*z/5832 - 457/1458) + 469*z/1458 + 1054/729)*h0 + (t*(97*z/93312 - 181/23328) - 653*z/93312 + 2437/46656)*h1 + (1261*t^8/11664 - 51319*t^7/11664 + 988969*t^6/11664 - 5961347*t^5/5832 + 48811877*t^4/5832 - 547570621*t^3/11664 + 2028498121*t^2/11664 - 4501375975*t/11664 + 2279820953/5832)*hf
  norm_num at hh

private lemma cell_3_40 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (8*z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z/23 - 29/46)*h0 + (-16/23)*hf
  norm_num at hh

private lemma cell_3_41 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 2)*h0 + (1/4)*hf
  norm_num at hh

private lemma cell_3_42 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 6*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z/26 - 23/26)*h0 + (9/13)*hf
  norm_num at hh

private lemma cell_3_43 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 160*z) + t^6*(5376*z - 2880) + t^5*(51312 - 95304*z) + t^4*(1034856*z - 554688) + t^3*(3779424 - 7052904*z) + t^2*(29440584*z - 15777072) + t*(36861696 - 68784768*z) + 68846112*z - 36894528:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(1087*z/2673 - 601/198) + t^6*(3851/297 - 6191*z/3564) + t^5*(637/594 - 259*z/1782) + t^4*(3635*z/594 - 4505/99) + t^3*(148/9 - 43*z/18) + t^2*(25273/594 - 5729*z/1188) + t*(-73*z/99 - 743/66) + 134*z/33 - 823/66)*h0 + (t*(601/1584 - 1087*z/21384) + 8629*z/85536 - 8051/10692)*h1 + (-17392*t^8/2673 + 741992*t^7/2673 - 177098*t^6/33 + 221840627*t^5/3564 - 550040245*t^4/1188 + 238469659*t^3/108 - 284523803*t^2/44 + 1033436116*t/99 - 229196477/33)*hf
  norm_num at hh

private lemma cell_3_44 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-96*z - 48) + t^6*(2736*z - 1296) + t^5*(23472 - 43848*z) + t^4*(483120*z - 259056) + t^3*(2000592 - 3732912*z) + t^2*(20005488*z - 10720944) + t*(36483696 - 68079528*z) + 121465008*z - 65092896:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(846541/983664 - 37805*z/327888) + t^6*(694013*z/983664 - 1295045/245916) + t^5*(947131/109296 - 190339*z/163944) + t^4*(55447*z/655776 - 103285/163944) + t^3*(21961*z/19872 - 82061/9936) + t^2*(56939/9108 - 60419*z/72864) + t*(995*z/6624 - 4501/3312) + 2201*z/12144 - 1913/2024)*h0 + (t*(37805*z/2623104 - 846541/7869312) - 276703*z/7869312 + 2065339/7869312)*h1 + (189025*t^8/163944 - 2459960*t^7/61479 + 78405313*t^6/109296 - 695989187*t^5/81972 + 7736921897*t^4/109296 - 15286795277*t^3/36432 + 10229088643*t^2/6072 - 50329899461*t/12144 + 8644474021/2024)*hf
  norm_num at hh

private lemma cell_3_45 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-3*z - 2) + 9*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 128*z) + t^6*(3640*z - 2016) + t^5*(31184 - 57720*z) + t^4*(593720*z - 318112) + t^3*(2170416 - 4050688*z) + t^2*(17893392*z - 9589040) + t*(25106800 - 46849688*z) + 55861264*z - 29935968:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(181/2916 - 97*z/11664) + t^6*(797*z/11664 - 1487/2916) + t^5*(85/486 - 23*z/972) + t^4*(18703/5832 - 311*z/729) + t^3*(661*z/11664 - 445/729) + t^2*(1673*z/1944 - 2651/486) + t*(-2021*z/5832 - 457/1458) + 469*z/1458 + 1054/729)*h0 + (t*(97*z/93312 - 181/23328) - 653*z/93312 + 2437/46656)*h1 + (1261*t^8/11664 - 51319*t^7/11664 + 988969*t^6/11664 - 5961347*t^5/5832 + 48811877*t^4/5832 - 547570621*t^3/11664 + 2028498121*t^2/11664 - 4501375975*t/11664 + 2279820953/5832)*hf
  norm_num at hh

private lemma cell_3_46 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 160*z) + t^6*(5376*z - 2880) + t^5*(51312 - 95304*z) + t^4*(1034856*z - 554688) + t^3*(3779424 - 7052904*z) + t^2*(29440584*z - 15777072) + t*(36861696 - 68784768*z) + 68846112*z - 36894528:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(1087*z/2673 - 601/198) + t^6*(3851/297 - 6191*z/3564) + t^5*(637/594 - 259*z/1782) + t^4*(3635*z/594 - 4505/99) + t^3*(148/9 - 43*z/18) + t^2*(25273/594 - 5729*z/1188) + t*(-73*z/99 - 743/66) + 134*z/33 - 823/66)*h0 + (t*(601/1584 - 1087*z/21384) + 8629*z/85536 - 8051/10692)*h1 + (-17392*t^8/2673 + 741992*t^7/2673 - 177098*t^6/33 + 221840627*t^5/3564 - 550040245*t^4/1188 + 238469659*t^3/108 - 284523803*t^2/44 + 1033436116*t/99 - 229196477/33)*hf
  norm_num at hh

private lemma cell_3_47 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 14*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(80 - 192*z) + t^6*(7080*z - 3920) + t^5*(76496 - 142488*z) + t^4*(1752744*z - 939008) + t^3*(7213472 - 13461000*z) + t^2*(63018288*z - 33771584) + t*(88150976 - 164491680*z) + 183417216*z - 98292992:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(20173/128304 - 5405*z/256608) + t^6*(3173*z/128304 - 11887/64152) + t^5*(7519*z/42768 - 13807/10692) + t^4*(8306/8019 - 1472*z/8019) + t^3*(9467*z/256608 + 363659/128304) + t^2*(-94181*z/42768 - 8885/21384) + t*(59630*z/8019 - 98341/16038) - 141749*z/16038 + 87839/16038)*h0 + (t*(5405*z/2052864 - 20173/1026432) - 15241*z/2052864 + 56885/1026432)*h1 + (27025*t^8/64152 - 5048155*t^7/256608 + 3432761*t^6/8019 - 182059391*t^5/32076 + 565203721*t^4/11664 - 68224011337*t^3/256608 + 115603975535*t^2/128304 - 109333563649*t/64152 + 21841529713/16038)*hf
  norm_num at hh

private lemma cell_3_48 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h2 : (16*t^8 + t^7*(-32*z - 112) + t^6*(384*z + 96) + t^5*(816 - 1680*z) + t^4*(2736*z - 1872) + t^3*(1800*z - 720) + t^2*(6480 - 11880*z) + t*(11232*z - 6048):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(5/648 - z/1296) - t^5/27 + t^4*(7*z/216 + 1/108) + t^3*(7/72 - 5*z/48) + t^2*(z/24 - 1/12) + t*(z/3 - 1/4) - 11*z/24 + 1/12)*h0 + (z/10368 - 5/5184)*h2 + (t^7/324 - t^6/27 + 35*t^5/216 - 19*t^4/72 - 25*t^3/144 + 55*t^2/48 - 13*t/12)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_3_49 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-z - 4) + 2*z:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z - 48) + t^6*(968*z - 496) + t^5*(3584 - 6072*z) + t^4*(17968*z - 9840) + t^3*(9904 - 19256*z) + t^2*(5296 - 9528*z) + t*(26672*z - 14112) - 8128*z + 4352:ℝ)=0) : (t - 2:ℝ)=0 := by
  have hh : (t - 2:ℝ)=0 := by linear_combination (t^6*(97/324 - 13*z/324) + t^5*(25*z/216 - 31/36) + t^4*(2*z/9 - 91/54) + t^3*(227/81 - 235*z/648) + t^2*(10/3 - 49*z/108) + t*(5*z/24 - 185/108) + 89*z/324 - 173/81)*h0 + (13*z/2592 - 97/2592)*h2 + (91*t^7/324 - 3019*t^6/648 + 274*t^5/9 - 58919*t^4/648 + 31379*t^3/324 + 3521*t^2/72 - 10847*t/81 + 6515/162)*hf
  exact hh

private lemma cell_3_50 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 - 240*t^7 + t^6*(216*z + 1248) + t^5*(-2376*z - 2448) + t^4*(16344*z - 3744) + t^3*(32400 - 66096*z) + t^2*(214704*z - 114480) + t*(216432 - 403704*z) + 594864*z - 318816:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(683*z/85536 - 2549/42768) + t^6*(65/54 - 209*z/1296) + t^5*(421*z/352 - 127267/14256) + t^4*(431147/14256 - 115525*z/28512) + t^3*(557*z/88 - 18709/396) + t^2*(139541/4752 - 37387*z/9504) + t*(959*z/1584 - 895/198) + 17*z/88 - 47/33)*h0 + (t*(2549/342144 - 683*z/684288) + 5281*z/684288 - 19709/342144)*h1 + (683*t^8/42768 - 1927*t^7/9504 + 343*t^6/1188 + 10865*t^5/891 - 1243369*t^4/9504 + 3044009*t^3/4752 - 6372457*t^2/3168 + 3909793*t/1056 - 73491/16)*hf
  norm_num at hh

private lemma cell_3_51 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(32*z - 240) + t^6*(1280 - 208*z) + t^5*(480*z - 3184) + t^4*(3888 - 560*z) + t^3*(-152*z - 1808) + t^2*(696*z - 176) + t*(672 - 1024*z) + 3296*z - 1792:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z - 48) + t^6*(968*z - 496) + t^5*(3584 - 6072*z) + t^4*(17968*z - 9840) + t^3*(9904 - 19256*z) + t^2*(5296 - 9528*z) + t*(26672*z - 14112) - 8128*z + 4352:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(71*z/314928 - 265/157464) + t^12*(3923/157464 - 1051*z/314928) + t^11*(1913*z/104976 - 7141/52488) + t^10*(48173/157464 - 12907*z/314928) + t^9*(1535*z/314928 - 5623/157464) + t^8*(4889*z/34992 - 18289/17496) + t^7*(9554/6561 - 2557*z/13122) + t^6*(1184/6561 - 1219*z/52488) + t^5*(3793*z/17496 - 7213/4374) + t^4*(108433/78732 - 7115*z/39366) + t^3*(10393/78732 - 2525*z/157464) + t^2*(11563*z/52488 - 44201/26244) + t*(6688/19683 - 1613*z/39366) - 3221*z/39366 + 24137/39366)*h0 + (t^7*(265/1259712 - 71*z/2519424) + t^6*(173*z/1259712 - 323/314928) + t^5*(5/209952 - z/419904) + t^4*(5477/1259712 - 1477*z/2519424) + t^3*(35*z/157464 - 127/78732) + t^2*(83*z/104976 - 1237/209952) + t*(581/629856 - 163*z/1259712) - 433*z/1259712 + 1655/629856)*h1 + (7/324 - 5*z/1728)*h2 + (71*t^14/78732 - 1615*t^13/157464 + 830*t^12/19683 - 9989*t^11/157464 - 17411*t^10/314928 + 107543*t^9/314928 - 20533*t^8/52488 - 32551*t^7/104976 + 338131*t^6/104976 - 2850713*t^5/157464 + 8406713*t^4/157464 - 8755433*t^3/157464 - 1183685*t^2/39366 + 6082081*t/78732 - 881231/39366)*hf
  norm_num at hh

private lemma cell_3_52 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-z - 4) + 2*z:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z - 48) + t^6*(1160*z - 496) + t^5*(5888 - 11112*z) + t^4*(69376*z - 37200) + t^3*(156208 - 291320*z) + t^2*(801480*z - 429584) + t*(705024 - 1315552*z) + 978032*z - 524128:ℝ)=0) : False := by
  have hh : ((t-(z/2)))*(1:ℝ)=0 := by linear_combination (t^6*(71/1944 - 19*z/3888) + t^5*(z/72 - 17/162) + t^4*(1/36 - z/648) + t^3*(-53*z/3888 - 41/1944) + t^2*(11*z/108 - 29/162) + t*(5/108 - 37*z/162) + 187*z/486 - 113/243)*h0 + (19*z/31104 - 71/15552)*h2 + (133*t^7/3888 - 2663*t^6/3888 + 8759*t^5/1296 - 164809*t^4/3888 + 692387*t^3/3888 - 635065*t^2/1296 + 781927*t/972 - 1162909/1944)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_3_53 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 2) + 2*z:ℝ)=0) (h1 : (16*t^8 - 176*t^7 + t^6*(688 - 72*z) + t^5*(648*z - 1184) + t^4*(496 - 1152*z) + t^3*(2224 - 2808*z) + t^2*(5832*z - 3152) + t*(3744*z - 2048) - 1008*z + 544:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(1549/5832 - 415*z/11664) + t^6*(4415*z/11664 - 1831/648) + t^5*(9457/972 - 1267*z/972) + t^4*(15785*z/11664 - 58865/5832) + t^3*(10013*z/11664 - 12475/1944) + t^2*(2396/243 - 2581*z/1944) + t*(5995/1458 - 3185*z/5832) - 76*z/729 + 209/243)*h0 + (t*(415*z/93312 - 1549/46656) - 487*z/93312 + 1819/46656)*h1 + (-415*t^8/5832 + 4465*t^7/3888 - 19309*t^6/2916 + 161185*t^5/11664 + 21331*t^4/3888 - 262235*t^3/5832 + 179035*t^2/11664 + 48419*t/1944 - 29465/5832)*hf
  norm_num at hh

private lemma cell_3_54 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-3*z - 2) + 9*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z - 176) + t^6*(544*z + 528) + t^5*(656 - 3864*z) + t^4*(14816*z - 7312) + t^3*(17520 - 31648*z) + t^2*(31344*z - 17072) + t*(1240*z - 656) - 18800*z + 10080:ℝ)=0) : False := by
  have hh : ((t-(z/2)))*(1:ℝ)=0 := by linear_combination (t^6*(71*z/7776 - 265/3888) + t^5*(907/1296 - 3*z/32) + t^4*(191*z/648 - 713/324) + t^3*(6877/3888 - 1841*z/7776) + t^2*(1843/1296 - 55*z/288) + t*(47*z/648 - 355/648) + 89*z/1944 - 97/243)*h0 + (265/31104 - 71*z/62208)*h1 + (-71*t^7/7776 + 1001*t^6/3888 - 869*t^5/324 + 105341*t^4/7776 - 134381*t^3/3888 + 97745*t^2/2592 + 6997*t/7776 - 85027/3888)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_3_55 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 3*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z - 112) + t^6*(384*z + 96) + t^5*(816 - 1680*z) + t^4*(2736*z - 1872) + t^3*(1800*z - 720) + t^2*(6480 - 11880*z) + t*(11232*z - 6048):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(28/81 - 5*z/108) + t^6*(253*z/648 - 35/12) + t^5*(2249/324 - 601*z/648) + t^4*(7*z/72 - 85/108) + t^3*(161*z/108 - 299/27) + t^2*(59/18 - 5*z/12) + t*(79/18 - 23*z/36) - z/12 + 2/3)*h0 + (t*(5*z/864 - 7/162) - 29*z/1728 + 325/2592)*h1 + (5*t^8/54 - 149*t^7/81 + 8515*t^6/648 - 8867*t^5/216 + 8249*t^4/216 + 6743*t^3/72 - 19037*t^2/72 + 761*t/4 + 1/4)*hf
  norm_num at hh

private lemma cell_3_56 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 - 240*t^7 + t^6*(216*z + 1248) + t^5*(-2376*z - 2448) + t^4*(16344*z - 3744) + t^3*(32400 - 66096*z) + t^2*(214704*z - 114480) + t*(216432 - 403704*z) + 594864*z - 318816:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(683*z/85536 - 2549/42768) + t^6*(65/54 - 209*z/1296) + t^5*(421*z/352 - 127267/14256) + t^4*(431147/14256 - 115525*z/28512) + t^3*(557*z/88 - 18709/396) + t^2*(139541/4752 - 37387*z/9504) + t*(959*z/1584 - 895/198) + 17*z/88 - 47/33)*h0 + (t*(2549/342144 - 683*z/684288) + 5281*z/684288 - 19709/342144)*h1 + (683*t^8/42768 - 1927*t^7/9504 + 343*t^6/1188 + 10865*t^5/891 - 1243369*t^4/9504 + 3044009*t^3/4752 - 6372457*t^2/3168 + 3909793*t/1056 - 73491/16)*hf
  norm_num at hh

private lemma cell_3_57 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-3*z - 2) + 9*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z - 176) + t^6*(544*z + 528) + t^5*(656 - 3864*z) + t^4*(14816*z - 7312) + t^3*(17520 - 31648*z) + t^2*(31344*z - 17072) + t*(1240*z - 656) - 18800*z + 10080:ℝ)=0) (h2 : (16*t^8 + t^7*(16 - 128*z) + t^6*(3640*z - 2016) + t^5*(31184 - 57720*z) + t^4*(593720*z - 318112) + t^3*(2170416 - 4050688*z) + t^2*(17893392*z - 9589040) + t*(25106800 - 46849688*z) + 55861264*z - 29935968:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(191861/3779136 - 51409*z/7558272) + t^12*(683081*z/7558272 - 2549293/3779136) + t^11*(5123/1728 - 37063*z/93312) + t^10*(3021179*z/7558272 - 11275195/3779136) + t^9*(6193861*z/3779136 - 11557897/944784) + t^8*(167459/5832 - 538447*z/139968) + t^7*(9640717/1259712 - 2583101*z/2519424) + t^6*(19203361*z/2519424 - 71670263/1259712) + t^5*(452875/46656 - 363781*z/279936) + t^4*(172038623/3779136 - 46116463*z/7558272) + t^3*(558065*z/472392 - 2073865/236196) + t^2*(277661*z/139968 - 12865/864) + t*(531901/472392 - 55543*z/472392) - 321497*z/944784 + 957139/472392)*h0 + (t^7*(51409*z/60466176 - 191861/30233088) + t^6*(289637/15116544 - 9701*z/3779136) + t^5*(312869/10077696 - 83833*z/20155392) + t^4*(742127*z/60466176 - 2769655/30233088) + t^3*(99185*z/15116544 - 370165/7558272) + t^2*(1231391/10077696 - 329947*z/20155392) + t*(495695/15116544 - 66419*z/15116544) + 42467*z/7558272 - 316925/7558272)*h1 + (65/1296 - 209*z/31104)*h2 + (51409*t^14/7558272 - 100297*t^13/472392 + 19225201*t^12/7558272 - 28506473*t^11/1889568 + 165227449*t^10/3779136 - 220887065*t^9/7558272 - 212145353*t^8/1259712 + 1036246531*t^7/2519424 - 115085251*t^6/2519424 - 8501542457*t^5/7558272 + 34475588387*t^4/7558272 - 202286993195*t^3/7558272 + 113124757247*t^2/944784 - 74375994371*t/236196 + 354730942769/944784)*hf
  norm_num at hh

private lemma cell_3_58 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 176) + t^6*(1416*z + 240) + t^5*(4944 - 13080*z) + t^4*(63144*z - 32256) + t^3*(87840 - 163656*z) + t^2*(212112*z - 114048) + t*(57024 - 106272*z):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(3637/3159 - 1949*z/12636) + t^6*(12793*z/6318 - 95497/6318) + t^5*(150437/2106 - 20149*z/2106) + t^4*(6821*z/351 - 16988/117) + t^3*(24179/234 - 19337*z/1404) + t^2*(190/9 - 53*z/18) + t*(418*z/117 - 6119/234) - z/3 + 5/2)*h0 + (t*(1949*z/101088 - 3637/25272) - 167*z/4212 + 4987/16848)*h1 + (1949*t^8/3159 - 251305*t^7/12636 + 345047*t^6/1404 - 240785*t^5/156 + 7540337*t^4/1404 - 271045*t^3/26 + 1229497*t^2/117 - 166052*t/39 + 4)*hf
  norm_num at hh

private lemma cell_3_59 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 14*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-96*z - 112) + t^6*(2544*z - 800) + t^5*(16304 - 31752*z) + t^4*(233160*z - 124928) + t^3*(563744 - 1051080*z) + t^2*(2836728*z - 1520336) + t*(2233472 - 4167744*z) + 2532192*z - 1356992:ℝ)=0) (h2 : (16*t^8 + t^7*(80 - 192*z) + t^6*(7080*z - 3920) + t^5*(76496 - 142488*z) + t^4*(1752744*z - 939008) + t^3*(7213472 - 13461000*z) + t^2*(63018288*z - 33771584) + t*(88150976 - 164491680*z) + 183417216*z - 98292992:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(29681*z/7558272 - 110771/3779136) + t^12*(920111/3779136 - 82181*z/2519424) + t^11*(125087*z/2519424 - 466831/1259712) + t^10*(1470371*z/7558272 - 5487503/3779136) + t^9*(15244547/3779136 - 1361581*z/2519424) + t^8*(222077/139968 - 6613*z/31104) + t^7*(3779491*z/2519424 - 14101003/1259712) + t^6*(3317407/1259712 - 299333*z/839808) + t^5*(2345303/209952 - 38719*z/26244) + t^4*(843875*z/1889568 - 236777/59049) + t^3*(355093*z/629856 - 2048701/944784) + t^2*(7541/78732 - 179495*z/314928) + t*(235105*z/236196 - 124325/59049) - 11978*z/19683 + 58427/59049)*h0 + (t^7*(110771/30233088 - 29681*z/60466176) + t^6*(17257*z/30233088 - 1789/419904) + t^5*(79*z/19683 - 25159/839808) + t^4*(176293/7558272 - 94475*z/30233088) + t^3*(719945/10077696 - 578729*z/60466176) + t^2*(53357*z/10077696 - 66373/1679616) + t*(107335*z/15116544 - 400645/7558272) - 40939*z/15116544 + 50963/2519424)*h1 + (65/1296 - 209*z/31104)*h2 + (-29681*t^14/944784 + 2112755*t^13/1889568 - 40304813*t^12/2519424 + 923224457*t^11/7558272 - 3926102857*t^10/7558272 + 830532127*t^9/839808 + 2455176163*t^8/2519424 - 21894932855*t^7/2519424 + 11027789149*t^6/839808 + 51790488485*t^5/7558272 - 102521825141*t^4/3779136 - 42292543391*t^3/629856 + 845251593731*t^2/1889568 - 535960670461*t/472392 + 2409235403/1944)*hf
  norm_num at hh

private lemma cell_3_60 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(32*z - 240) + t^6*(1280 - 208*z) + t^5*(480*z - 3184) + t^4*(3888 - 560*z) + t^3*(-152*z - 1808) + t^2*(696*z - 176) + t*(672 - 1024*z) + 3296*z - 1792:ℝ)=0) : False := by
  have hh : ((t-(z/2)))*(1:ℝ)=0 := by linear_combination (t^6*(5/972 - z/1944) + t^5*(5*z/648 - 17/324) + t^4*(55/324 - 5*z/216) + t^3*(8*z/243 - 56/243) + t^2*(7/81 - z/162) + t*(-z/108 - 2/81) + 19*z/972 - 37/243)*h0 + (z/15552 - 5/7776)*h1 + (-t^7/486 + 13*t^6/972 - 5*t^5/162 + 35*t^4/972 + 19*t^3/1944 - 29*t^2/648 + 16*t/243 - 103/486)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_3_61 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 3*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z - 112) + t^6*(384*z + 96) + t^5*(816 - 1680*z) + t^4*(2736*z - 1872) + t^3*(1800*z - 720) + t^2*(6480 - 11880*z) + t*(11232*z - 6048):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(28/81 - 5*z/108) + t^6*(253*z/648 - 35/12) + t^5*(2249/324 - 601*z/648) + t^4*(7*z/72 - 85/108) + t^3*(161*z/108 - 299/27) + t^2*(59/18 - 5*z/12) + t*(79/18 - 23*z/36) - z/12 + 2/3)*h0 + (t*(5*z/864 - 7/162) - 29*z/1728 + 325/2592)*h1 + (5*t^8/54 - 149*t^7/81 + 8515*t^6/648 - 8867*t^5/216 + 8249*t^4/216 + 6743*t^3/72 - 19037*t^2/72 + 761*t/4 + 1/4)*hf
  norm_num at hh

private lemma cell_3_62 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 14*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-96*z - 112) + t^6*(2544*z - 800) + t^5*(16304 - 31752*z) + t^4*(233160*z - 124928) + t^3*(563744 - 1051080*z) + t^2*(2836728*z - 1520336) + t*(2233472 - 4167744*z) + 2532192*z - 1356992:ℝ)=0) : False := by
  have hh : ((t-(z/2)))*(1:ℝ)=0 := by linear_combination (t^6*(17/432 - 41*z/7776) + t^5*(293*z/7776 - 1093/3888) + t^4*(1915/3888 - 515*z/7776) + t^3*(43*z/7776 - 109/3888) + t^2*(89*z/1944 - 767/1944) + t*(5*z/243 - 25/486) + z/162 - 40/243)*h0 + (41*z/62208 - 17/3456)*h1 + (41*t^7/972 - 941*t^6/648 + 52189*t^5/2592 - 1187563*t^4/7776 + 199541*t^3/288 - 4847525*t^2/2592 + 2669705*t/972 - 1081513/648)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_3_63 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 6*t:ℝ)=0) (h1 : (t*(960 - 1728*z) + 4288*z - 2304:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7/6 - z/6)*h0 + (433/2112 - 29*z/1056)*h1 + (3886/33 - 522*t/11)*hf
  norm_num at hh

private lemma pair_3_13_20 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z - 48) + t^6*(1160*z - 496) + t^5*(5888 - 11112*z) + t^4*(69376*z - 37200) + t^3*(156208 - 291320*z) + t^2*(801480*z - 429584) + t*(705024 - 1315552*z) + 978032*z - 524128:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(41/972 - 11*z/1944) + t^6*(35*z/1944 - 43/324) + t^5*(11/162 - z/81) + t^4*(71*z/1944 - 59/972) + t^3*(-299*z/1944 - 17/324) + t^2*(209*z/324 - 32/81) + t*(229/486 - 677*z/486) + 803*z/486 - 112/81)*h0 + (11*z/31104 - 41/15552)*h2 + (11*t^7/486 - 1595*t^6/3888 + 5093*t^5/1296 - 5962*t^4/243 + 400565*t^3/3888 - 367345*t^2/1296 + 452221*t/972 - 672397/1944)*hf
  norm_num at hh

private lemma pair_3_25_49 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z + 1:ℝ)=0) (h1 : (t - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (13/23 - 2*z/23)*h0 + (2*z/23 - 13/23)*h1 + (-4/23)*hf
  norm_num at hh

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_0 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 0) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_0 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_1 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 1) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_1 z t hf hn0 hn1 hn2 hn3
  · have hr : (z^2/2 - 3*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_2 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 2) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_2 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_3 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 3) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_3 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 32*t^7*z - 112*t^7 + 40*t^6*z^2 + 64*t^6*z + 256*t^6 - 32*t^5*z^3 - 12*t^5*z^2 + 336*t^5*z - 256*t^5 + 19*t^4*z^4 - 58*t^4*z^3 - 192*t^4*z^2 - 760*t^4*z + 64*t^4 - 8*t^3*z^5 + 49*t^3*z^4 + 172*t^3*z^3 - 496*t^3*z^2 + 248*t^3*z + 224*t^3 + 5*t^2*z^6/2 - 57*t^2*z^5/2 + 24*t^2*z^4 + 76*t^2*z^3 + 672*t^2*z^2 + 336*t^2*z - 272*t^2 - t*z^7/2 + 8*t*z^6 - 15*t*z^5 - 149*t*z^4 + 302*t*z^3 + 528*t*z^2 - 728*t*z + 176*t + z^8/16 - 13*z^7/8 + 13*z^6 - 35*z^5 + 10*z^4 + 100*z^3 - 284*z^2 + 184*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 32*t^5*z + 268*t^5 - 19*t^4*z^2 - 94*t^4*z - 484*t^4 + 8*t^3*z^3 + 15*t^3*z^2 - 84*t^3*z - 236*t^3 - 5*t^2*z^4/2 + 17*t^2*z^3/2 + 54*t^2*z^2 + 322*t^2*z + 1688*t^2 + t*z^5/2 - 4*t*z^4 - 19*t*z^3 + 13*t*z^2 - 122*t*z - 1556*t - z^6/16 + 9*z^5/8 - 15*z^4/4 + z^3/2 + 9*z^2 - 30*z + 8)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_4 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 4) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_4 z t hf hn0 hn1 hn2 hn3
  · have hr : (z^2/2 - 3*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_5 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 5) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_5 z t hf hn0 hn1 hn2 hn3
  · have hr : (648*t*z^2:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-648*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_6 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 6) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_6 z t hf hn0 hn1 hn2 hn3
  · have hr : (3*z^2/2 - 6*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_7 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 7) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_7 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - t*z - 4*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 112*t^6*z^2 + 72*t^6*z - 48*t^6 - 112*t^5*z^3 + 36*t^5*z^2 + 360*t^5*z + 144*t^5 + 70*t^4*z^4 - 150*t^4*z^3 - 540*t^4*z^2 - 72*t^4*z - 28*t^3*z^5 + 135*t^3*z^4 + 300*t^3*z^3 - 432*t^3*z^2 - 648*t^3*z + 7*t^2*z^6 - 117*t^2*z^5/2 - 45*t^2*z^4 + 468*t^2*z^3 + 432*t^2*z^2 - t*z^7 + 51*t*z^6/4 - 27*t*z^5/2 - 153*t*z^4 + 54*t*z^3 + 648*t*z^2 + z^8/16 - 9*z^7/8 + 15*z^6/4 + 27*z^5/2 - 54*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 112*t^5*z + 860*t^5 - 70*t^4*z^2 - 410*t^4*z - 2460*t^4 + 28*t^3*z^3 + 89*t^3*z^2 + 300*t^3*z + 2476*t^3 - 7*t^2*z^4 + 5*t^2*z^3/2 + 93*t^2*z^2 + 266*t^2*z + 1324*t^2 + t*z^5 - 19*t*z^4/4 - 57*t*z^3/2 - 56*t*z^2 - 388*t*z - 3528*t - z^6/16 + 5*z^5/8 + 3*z^4/2 - 4*z^3 + 16*z^2 + 144*z + 1088)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 160*t^6*z^2 - 120*t^6*z + 144*t^6 - 256*t^5*z^3 + 504*t^5*z^2 + 216*t^5*z - 288*t^5 + 304*t^4*z^4 - 1248*t^4*z^3 + 1152*t^4*z^2 - 1152*t^4*z + 432*t^4 - 256*t^3*z^5 + 1560*t^3*z^4 - 2232*t^3*z^3 - 216*t^3*z^2 + 1512*t^3*z - 432*t^3 + 160*t^2*z^6 - 1440*t^2*z^5 + 4320*t^2*z^4 - 5904*t^2*z^3 + 5616*t^2*z^2 - 2808*t^2*z + 432*t^2 - 64*t*z^7 + 744*t*z^6 - 2952*t*z^5 + 4464*t*z^4 - 1296*t*z^3 - 1728*t*z^2 + 864*t*z + 16*z^8 - 264*z^7 + 1728*z^6 - 5832*z^5 + 11016*z^4 - 11664*z^3 + 6264*z^2 - 1296*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 1544*t^5 - 304*t^4*z^2 - 1184*t^4*z - 9408*t^4 + 256*t^3*z^3 + 488*t^3*z^2 + 5112*t^3*z + 39160*t^3 - 160*t^2*z^4 + 160*t^2*z^3 - 2400*t^2*z^2 - 13936*t^2*z - 107504*t^2 + 64*t*z^5 - 232*t*z^4 + 840*t*z^3 + 3184*t*z^2 + 23408*t*z + 176256*t - 16*z^6 + 136*z^5 - 576*z^4 + 680*z^3 - 3272*z^2 - 17232*z - 131032)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_8 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 8) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_8 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_9 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 9) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_9 z t hf hn0 hn1 hn2 hn3
  · have hr : (3*z^2/2 - 6*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_10 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 10) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_10 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_11 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 11) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_11 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 96*t^7*z - 48*t^7 + 264*t^6*z^2 + 144*t^6*z - 48*t^6 - 432*t^5*z^3 - 108*t^5*z^2 + 432*t^5*z + 144*t^5 + 459*t^4*z^4 - 162*t^4*z^3 - 1008*t^4*z^2 - 216*t^4*z - 324*t^3*z^5 + 405*t^3*z^4 + 1080*t^3*z^3 - 324*t^3*z^2 - 648*t^3*z + 297*t^2*z^6/2 - 729*t^2*z^5/2 - 540*t^2*z^4 + 810*t^2*z^3 + 756*t^2*z^2 - 81*t*z^7/2 + 162*t*z^6 + 81*t*z^5 - 567*t*z^4 - 162*t*z^3 + 648*t*z^2 + 81*z^8/16 - 243*z^7/8 + 81*z^6/4 + 243*z^5/2 - 162*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-264*t^6 + 432*t^5*z + 3564*t^5 - 459*t^4*z^2 - 3510*t^4*z - 25236*t^4 + 324*t^3*z^3 + 2187*t^3*z^2 + 15120*t^3*z + 112536*t^3 - 297*t^2*z^4/2 - 1647*t^2*z^3/2 - 5454*t^2*z^2 - 41148*t^2*z - 308124*t^2 + 81*t*z^5/2 + 162*t*z^4 + 1053*t*z^3 + 8343*t*z^2 + 62694*t*z + 467532*t - 81*z^6/16 - 81*z^5/8 - 81*z^4 - 729*z^3 - 5346*z^2 - 39852*z - 297432)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_12 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 12) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_12 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 32*t^7*z - 112*t^7 + 40*t^6*z^2 + 64*t^6*z + 256*t^6 - 32*t^5*z^3 - 12*t^5*z^2 + 336*t^5*z - 256*t^5 + 19*t^4*z^4 - 58*t^4*z^3 - 192*t^4*z^2 - 760*t^4*z + 64*t^4 - 8*t^3*z^5 + 49*t^3*z^4 + 172*t^3*z^3 - 496*t^3*z^2 + 248*t^3*z + 224*t^3 + 5*t^2*z^6/2 - 57*t^2*z^5/2 + 24*t^2*z^4 + 76*t^2*z^3 + 672*t^2*z^2 + 336*t^2*z - 272*t^2 - t*z^7/2 + 8*t*z^6 - 15*t*z^5 - 149*t*z^4 + 302*t*z^3 + 528*t*z^2 - 728*t*z + 176*t + z^8/16 - 13*z^7/8 + 13*z^6 - 35*z^5 + 10*z^4 + 100*z^3 - 284*z^2 + 184*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 32*t^5*z + 268*t^5 - 19*t^4*z^2 - 94*t^4*z - 484*t^4 + 8*t^3*z^3 + 15*t^3*z^2 - 84*t^3*z - 236*t^3 - 5*t^2*z^4/2 + 17*t^2*z^3/2 + 54*t^2*z^2 + 322*t^2*z + 1688*t^2 + t*z^5/2 - 4*t*z^4 - 19*t*z^3 + 13*t*z^2 - 122*t*z - 1556*t - z^6/16 + 9*z^5/8 - 15*z^4/4 + z^3/2 + 9*z^2 - 30*z + 8)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_13 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 13) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : (t - 2:ℝ)=0 := by
  apply cell_3_13 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - t*z - 4*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 112*t^6*z^2 + 72*t^6*z - 48*t^6 - 112*t^5*z^3 + 36*t^5*z^2 + 360*t^5*z + 144*t^5 + 70*t^4*z^4 - 150*t^4*z^3 - 540*t^4*z^2 - 72*t^4*z - 28*t^3*z^5 + 135*t^3*z^4 + 300*t^3*z^3 - 432*t^3*z^2 - 648*t^3*z + 7*t^2*z^6 - 117*t^2*z^5/2 - 45*t^2*z^4 + 468*t^2*z^3 + 432*t^2*z^2 - t*z^7 + 51*t*z^6/4 - 27*t*z^5/2 - 153*t*z^4 + 54*t*z^3 + 648*t*z^2 + z^8/16 - 9*z^7/8 + 15*z^6/4 + 27*z^5/2 - 54*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 112*t^5*z + 860*t^5 - 70*t^4*z^2 - 410*t^4*z - 2460*t^4 + 28*t^3*z^3 + 89*t^3*z^2 + 300*t^3*z + 2476*t^3 - 7*t^2*z^4 + 5*t^2*z^3/2 + 93*t^2*z^2 + 266*t^2*z + 1324*t^2 + t*z^5 - 19*t*z^4/4 - 57*t*z^3/2 - 56*t*z^2 - 388*t*z - 3528*t - z^6/16 + 5*z^5/8 + 3*z^4/2 - 4*z^3 + 16*z^2 + 144*z + 1088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_14 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 14) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_14 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 96*t^7*z - 48*t^7 + 264*t^6*z^2 + 144*t^6*z - 48*t^6 - 432*t^5*z^3 - 108*t^5*z^2 + 432*t^5*z + 144*t^5 + 459*t^4*z^4 - 162*t^4*z^3 - 1008*t^4*z^2 - 216*t^4*z - 324*t^3*z^5 + 405*t^3*z^4 + 1080*t^3*z^3 - 324*t^3*z^2 - 648*t^3*z + 297*t^2*z^6/2 - 729*t^2*z^5/2 - 540*t^2*z^4 + 810*t^2*z^3 + 756*t^2*z^2 - 81*t*z^7/2 + 162*t*z^6 + 81*t*z^5 - 567*t*z^4 - 162*t*z^3 + 648*t*z^2 + 81*z^8/16 - 243*z^7/8 + 81*z^6/4 + 243*z^5/2 - 162*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-264*t^6 + 432*t^5*z + 3564*t^5 - 459*t^4*z^2 - 3510*t^4*z - 25236*t^4 + 324*t^3*z^3 + 2187*t^3*z^2 + 15120*t^3*z + 112536*t^3 - 297*t^2*z^4/2 - 1647*t^2*z^3/2 - 5454*t^2*z^2 - 41148*t^2*z - 308124*t^2 + 81*t*z^5/2 + 162*t*z^4 + 1053*t*z^3 + 8343*t*z^2 + 62694*t*z + 467532*t - 81*z^6/16 - 81*z^5/8 - 81*z^4 - 729*z^3 - 5346*z^2 - 39852*z - 297432)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_15 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 15) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_15 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 112*t^6*z^2 + 72*t^6*z - 48*t^6 - 112*t^5*z^3 + 36*t^5*z^2 + 360*t^5*z + 144*t^5 + 70*t^4*z^4 - 150*t^4*z^3 - 540*t^4*z^2 - 72*t^4*z - 28*t^3*z^5 + 135*t^3*z^4 + 300*t^3*z^3 - 432*t^3*z^2 - 648*t^3*z + 7*t^2*z^6 - 117*t^2*z^5/2 - 45*t^2*z^4 + 468*t^2*z^3 + 432*t^2*z^2 - t*z^7 + 51*t*z^6/4 - 27*t*z^5/2 - 153*t*z^4 + 54*t*z^3 + 648*t*z^2 + z^8/16 - 9*z^7/8 + 15*z^6/4 + 27*z^5/2 - 54*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 112*t^5*z + 860*t^5 - 70*t^4*z^2 - 410*t^4*z - 2460*t^4 + 28*t^3*z^3 + 89*t^3*z^2 + 300*t^3*z + 2476*t^3 - 7*t^2*z^4 + 5*t^2*z^3/2 + 93*t^2*z^2 + 266*t^2*z + 1324*t^2 + t*z^5 - 19*t*z^4/4 - 57*t*z^3/2 - 56*t*z^2 - 388*t*z - 3528*t - z^6/16 + 5*z^5/8 + 3*z^4/2 - 4*z^3 + 16*z^2 + 144*z + 1088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_16 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 16) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_16 z t hf hn0 hn1 hn2 hn3
  · have hr : (z^2/2 - 3*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_17 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 17) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_17 z t hf hn0 hn1 hn2 hn3
  · have hr : (648*t*z^2:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-648*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_18 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 18) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_18 z t hf hn0 hn1 hn2 hn3
  · have hr : (3*z^2/2 - 6*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_19 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 19) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_19 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - t*z - 4*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 160*t^6*z^2 - 120*t^6*z + 144*t^6 - 256*t^5*z^3 + 504*t^5*z^2 + 216*t^5*z - 288*t^5 + 304*t^4*z^4 - 1248*t^4*z^3 + 1152*t^4*z^2 - 1152*t^4*z + 432*t^4 - 256*t^3*z^5 + 1560*t^3*z^4 - 2232*t^3*z^3 - 216*t^3*z^2 + 1512*t^3*z - 432*t^3 + 160*t^2*z^6 - 1440*t^2*z^5 + 4320*t^2*z^4 - 5904*t^2*z^3 + 5616*t^2*z^2 - 2808*t^2*z + 432*t^2 - 64*t*z^7 + 744*t*z^6 - 2952*t*z^5 + 4464*t*z^4 - 1296*t*z^3 - 1728*t*z^2 + 864*t*z + 16*z^8 - 264*z^7 + 1728*z^6 - 5832*z^5 + 11016*z^4 - 11664*z^3 + 6264*z^2 - 1296*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 1544*t^5 - 304*t^4*z^2 - 1184*t^4*z - 9408*t^4 + 256*t^3*z^3 + 488*t^3*z^2 + 5112*t^3*z + 39160*t^3 - 160*t^2*z^4 + 160*t^2*z^3 - 2400*t^2*z^2 - 13936*t^2*z - 107504*t^2 + 64*t*z^5 - 232*t*z^4 + 840*t*z^3 + 3184*t*z^2 + 23408*t*z + 176256*t - 16*z^6 + 136*z^5 - 576*z^4 + 680*z^3 - 3272*z^2 - 17232*z - 131032)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 112*t^6*z^2 + 72*t^6*z - 48*t^6 - 112*t^5*z^3 + 36*t^5*z^2 + 360*t^5*z + 144*t^5 + 70*t^4*z^4 - 150*t^4*z^3 - 540*t^4*z^2 - 72*t^4*z - 28*t^3*z^5 + 135*t^3*z^4 + 300*t^3*z^3 - 432*t^3*z^2 - 648*t^3*z + 7*t^2*z^6 - 117*t^2*z^5/2 - 45*t^2*z^4 + 468*t^2*z^3 + 432*t^2*z^2 - t*z^7 + 51*t*z^6/4 - 27*t*z^5/2 - 153*t*z^4 + 54*t*z^3 + 648*t*z^2 + z^8/16 - 9*z^7/8 + 15*z^6/4 + 27*z^5/2 - 54*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 112*t^5*z + 860*t^5 - 70*t^4*z^2 - 410*t^4*z - 2460*t^4 + 28*t^3*z^3 + 89*t^3*z^2 + 300*t^3*z + 2476*t^3 - 7*t^2*z^4 + 5*t^2*z^3/2 + 93*t^2*z^2 + 266*t^2*z + 1324*t^2 + t*z^5 - 19*t*z^4/4 - 57*t*z^3/2 - 56*t*z^2 - 388*t*z - 3528*t - z^6/16 + 5*z^5/8 + 3*z^4/2 - 4*z^3 + 16*z^2 + 144*z + 1088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_20 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (_hc : cell (1) (1) (1) (profile4 (z/2) (z) t 20) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : ((0:ℝ):ℝ)=0 := by
  apply cell_3_20 z t hf hn0 hn1 hn2 hn3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_21 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 21) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_21 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 3*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_22 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (_hc : cell (1) (1) (1) (profile4 (z/2) (z) t 22) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : ((0:ℝ):ℝ)=0 := by
  apply cell_3_22 z t hf hn0 hn1 hn2 hn3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_23 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 23) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_23 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 2*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_24 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 24) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_24 z t hf hn0 hn1 hn2 hn3
  · have hr : (3*z^2/2 - 6*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_25 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 25) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : (t - 2*z + 1:ℝ)=0 := by
  apply cell_3_25 z t hf hn0 hn1 hn2 hn3
  · have hr : (-48*t*z^6 + 504*t*z^5 - 1656*t*z^4 + 1464*t*z^3 + 1008*t*z^2 - 720*t*z + 96*t + 16*z^8 - 200*z^7 + 904*z^6 - 1760*z^5 + 1192*z^4 + 424*z^3 - 848*z^2 + 304*z - 32:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t*z^4 - 120*t*z^3 + 504*t*z^2 + 3048*t*z + 21360*t - 16*z^6 + 72*z^5 - 264*z^4 - 640*z^3 - 5256*z^2 - 39912*z - 297424)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_26 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 26) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_26 z t hf hn0 hn1 hn2 hn3
  · have hr : (z^2/2 - 5*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_27 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 27) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_27 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 3*t*z - 2*t + 3*z^2/2 - 3*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf
  · have hr : (16*t^8 - 128*t^7*z + 16*t^7 + 496*t^6*z^2 - 328*t^6*z - 32*t^6 - 1184*t^5*z^3 + 1668*t^5*z^2 - 24*t^5*z - 32*t^5 + 1894*t^4*z^4 - 4466*t^4*z^3 + 1608*t^4*z^2 + 304*t^4*z - 32*t^4 - 2072*t^3*z^5 + 7211*t^3*z^4 - 5876*t^3*z^3 + 16*t^3*z^2 - 16*t^3*z + 64*t^3 + 1519*t^2*z^6 - 14595*t^2*z^5/2 + 10266*t^2*z^4 - 3604*t^2*z^3 - 120*t^2*z^2 + 24*t^2*z + 16*t^2 - 686*t*z^7 + 17395*t*z^6/4 - 18291*t*z^5/2 + 6806*t*z^4 - 988*t*z^3 + 372*t*z^2 - 176*t*z + 16*t + 2401*z^8/16 - 9947*z^7/8 + 7595*z^6/2 - 5110*z^5 + 2452*z^4 + 728*z^3 - 1124*z^2 + 344*z - 32:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-496*t^6 + 1184*t^5*z + 7804*t^5 - 1894*t^4*z^2 - 10686*t^4*z - 79520*t^4 + 2072*t^3*z^3 + 9365*t^3*z^2 + 72508*t^3*z + 542588*t^3 - 1519*t^2*z^4 - 9709*t^2*z^3/2 - 43026*t^2*z^2 - 321186*t^2*z - 2397264*t^2 + 686*t*z^5 + 4557*t*z^4/4 + 31031*t*z^3/2 + 112761*t*z^2 + 841014*t*z + 6276696*t - 2401*z^6/16 + 343*z^5/8 - 11417*z^4/4 - 35791*z^3/2 - 134199*z^2 - 1002738*z - 7483984)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_28 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 28) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_28 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - t*z - 4*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 160*t^6*z^2 - 120*t^6*z + 144*t^6 - 256*t^5*z^3 + 504*t^5*z^2 + 216*t^5*z - 288*t^5 + 304*t^4*z^4 - 1248*t^4*z^3 + 1152*t^4*z^2 - 1152*t^4*z + 432*t^4 - 256*t^3*z^5 + 1560*t^3*z^4 - 2232*t^3*z^3 - 216*t^3*z^2 + 1512*t^3*z - 432*t^3 + 160*t^2*z^6 - 1440*t^2*z^5 + 4320*t^2*z^4 - 5904*t^2*z^3 + 5616*t^2*z^2 - 2808*t^2*z + 432*t^2 - 64*t*z^7 + 744*t*z^6 - 2952*t*z^5 + 4464*t*z^4 - 1296*t*z^3 - 1728*t*z^2 + 864*t*z + 16*z^8 - 264*z^7 + 1728*z^6 - 5832*z^5 + 11016*z^4 - 11664*z^3 + 6264*z^2 - 1296*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 1544*t^5 - 304*t^4*z^2 - 1184*t^4*z - 9408*t^4 + 256*t^3*z^3 + 488*t^3*z^2 + 5112*t^3*z + 39160*t^3 - 160*t^2*z^4 + 160*t^2*z^3 - 2400*t^2*z^2 - 13936*t^2*z - 107504*t^2 + 64*t*z^5 - 232*t*z^4 + 840*t*z^3 + 3184*t*z^2 + 23408*t*z + 176256*t - 16*z^6 + 136*z^5 - 576*z^4 + 680*z^3 - 3272*z^2 - 17232*z - 131032)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_29 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 29) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_29 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 2*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 176*t^7 - 72*t^6*z + 688*t^6 + 648*t^5*z - 1184*t^5 + 72*t^4*z^2 - 1728*t^4*z + 784*t^4 - 504*t^3*z^2 + 1224*t^3*z + 208*t^3 + 648*t^2*z^2 + 648*t^2*z - 560*t^2 + 576*t*z^2 - 864*t*z + 256*t - 144*z^2 + 144*z - 32:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-72*t^4 + 504*t^3 - 648*t^2 - 576*t + 144)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_30 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 30) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_30 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 3*t*z - 2*t + 3*z^2/2 - 3*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf
  · have hr : (16*t^8 - 32*t^7*z - 176*t^7 + 40*t^6*z^2 + 224*t^6*z + 688*t^6 - 32*t^5*z^3 - 204*t^5*z^2 - 312*t^5*z - 1184*t^5 + 19*t^4*z^4 + 94*t^4*z^3 + 132*t^4*z^2 - 392*t^4*z + 784*t^4 - 8*t^3*z^5 - 31*t^3*z^4 + 118*t^3*z^3 + 172*t^3*z^2 + 536*t^3*z + 208*t^3 + 5*t^2*z^6/2 + 3*t^2*z^5/2 - 57*t^2*z^4 - 202*t^2*z^3 + 132*t^2*z^2 + 528*t^2*z - 560*t^2 - t*z^7/2 + t*z^6 + 51*t*z^5/2 - 22*t*z^4 - 148*t*z^3 + 444*t*z^2 - 656*t*z + 256*t + z^8/16 - 5*z^7/8 - z^6/2 + 8*z^5 - 8*z^4 + 8*z^3 - 68*z^2 + 104*z - 32:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 32*t^5*z + 460*t^5 - 19*t^4*z^2 - 246*t^4*z - 2024*t^4 + 8*t^3*z^3 + 95*t^3*z^2 + 610*t^3*z + 4328*t^3 - 5*t^2*z^4/2 - 43*t^2*z^3/2 - 105*t^2*z^2 - 552*t^2*z - 4128*t^2 + t*z^5/2 + 3*t*z^4 - 7*t*z^3/2 - 18*t*z^2 + 18*t*z - 228*t - z^6/16 + z^5/8 + 7*z^4/4 + 11*z^3/2 + 45*z^2 + 330*z + 2528)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_31 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 31) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_31 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + z^2/2 - z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 128*t^7*z + 80*t^7 + 448*t^6*z^2 - 680*t^6*z + 112*t^6 - 896*t^5*z^3 + 2400*t^5*z^2 - 1176*t^5*z + 32*t^5 + 1120*t^4*z^4 - 4600*t^4*z^3 + 4488*t^4*z^2 - 736*t^4*z + 16*t^4 - 896*t^3*z^5 + 5200*t^3*z^4 - 8432*t^3*z^3 + 3560*t^3*z^2 - 376*t^3*z + 80*t^3 + 448*t^2*z^6 - 3480*t^2*z^5 + 8448*t^2*z^4 - 6800*t^2*z^3 + 1464*t^2*z^2 - 312*t^2*z + 16*t^2 - 128*t*z^7 + 1280*t*z^6 - 4344*t*z^5 + 5704*t*z^4 - 2296*t*z^3 + 240*t*z^2 + 256*t*z - 64*t + 16*z^8 - 200*z^7 + 904*z^6 - 1760*z^5 + 1192*z^4 + 424*z^3 - 848*z^2 + 304*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 4768*t^5 - 1120*t^4*z^2 - 4360*t^4*z - 34888*t^4 + 896*t^3*z^3 + 1968*t^3*z^2 + 20592*t^3*z + 153304*t^3 - 448*t^2*z^4 - 104*t^2*z^3 - 7488*t^2*z^2 - 52688*t^2*z - 393016*t^2 + 128*t*z^5 - 256*t*z^4 + 1784*t*z^3 + 9592*t*z^2 + 71896*t*z + 536560*t - 16*z^6 + 72*z^5 - 264*z^4 - 640*z^3 - 5256*z^2 - 39912*z - 297424)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_32 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 32) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_32 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_33 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 33) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_33 z t hf hn0 hn1 hn2 hn3
  · have hr : (3*z^2/2 - 6*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_34 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 34) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_34 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_35 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 35) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_35 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 96*t^7*z - 48*t^7 + 360*t^6*z^2 - 144*t^6*z + 144*t^6 - 864*t^5*z^3 + 972*t^5*z^2 + 216*t^5*z - 288*t^5 + 1539*t^4*z^4 - 3726*t^4*z^3 + 2340*t^4*z^2 - 1512*t^4*z + 432*t^4 - 1944*t^3*z^5 + 7047*t^3*z^4 - 6534*t^3*z^3 + 108*t^3*z^2 + 1944*t^3*z - 432*t^3 + 3645*t^2*z^6/2 - 19683*t^2*z^5/2 + 18711*t^2*z^4 - 17334*t^2*z^3 + 10908*t^2*z^2 - 3888*t^2*z + 432*t^2 - 2187*t*z^7/2 + 15309*t*z^6/2 - 38151*t*z^5/2 + 19440*t*z^4 - 5184*t*z^3 - 2916*t*z^2 + 1296*t*z + 6561*z^8/16 - 32805*z^7/8 + 16767*z^6 - 36450*z^5 + 45684*z^4 - 33048*z^3 + 12636*z^2 - 1944*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-360*t^6 + 864*t^5*z + 5940*t^5 - 1539*t^4*z^2 - 8586*t^4*z - 64872*t^4 + 1944*t^3*z^3 + 8505*t^3*z^2 + 66798*t^3*z + 500256*t^3 - 3645*t^2*z^4/2 - 9477*t^2*z^3/2 - 49329*t^2*z^2 - 358344*t^2*z - 2680344*t^2 + 2187*t*z^5/2 + 2187*t*z^4/2 + 46899*t*z^3/2 + 163782*t*z^2 + 1221642*t*z + 9120924*t - 6561*z^6/16 + 6561*z^5/8 - 34263*z^4/4 - 70713*z^3/2 - 294273*z^2 - 2179710*z - 16273224)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_36 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 36) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_36 z t hf hn0 hn1 hn2 hn3
  · have hr : (3*z^2/2 - 6*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_37 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 37) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : (t - 2*z + 1:ℝ)=0 := by
  apply cell_3_37 z t hf hn0 hn1 hn2 hn3
  · have hr : (-48*t*z^6 + 504*t*z^5 - 1656*t*z^4 + 1464*t*z^3 + 1008*t*z^2 - 720*t*z + 96*t + 16*z^8 - 200*z^7 + 904*z^6 - 1760*z^5 + 1192*z^4 + 424*z^3 - 848*z^2 + 304*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t*z^4 - 120*t*z^3 + 504*t*z^2 + 3048*t*z + 21360*t - 16*z^6 + 72*z^5 - 264*z^4 - 640*z^3 - 5256*z^2 - 39912*z - 297424)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_38 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 38) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_38 z t hf hn0 hn1 hn2 hn3
  · have hr : (z^2/2 - 5*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_39 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 39) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_39 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 3*t*z - 2*t + 3*z^2/2 - 3*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf
  · have hr : (16*t^8 - 128*t^7*z + 16*t^7 + 496*t^6*z^2 - 328*t^6*z - 32*t^6 - 1184*t^5*z^3 + 1668*t^5*z^2 - 24*t^5*z - 32*t^5 + 1894*t^4*z^4 - 4466*t^4*z^3 + 1608*t^4*z^2 + 304*t^4*z - 32*t^4 - 2072*t^3*z^5 + 7211*t^3*z^4 - 5876*t^3*z^3 + 16*t^3*z^2 - 16*t^3*z + 64*t^3 + 1519*t^2*z^6 - 14595*t^2*z^5/2 + 10266*t^2*z^4 - 3604*t^2*z^3 - 120*t^2*z^2 + 24*t^2*z + 16*t^2 - 686*t*z^7 + 17395*t*z^6/4 - 18291*t*z^5/2 + 6806*t*z^4 - 988*t*z^3 + 372*t*z^2 - 176*t*z + 16*t + 2401*z^8/16 - 9947*z^7/8 + 7595*z^6/2 - 5110*z^5 + 2452*z^4 + 728*z^3 - 1124*z^2 + 344*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-496*t^6 + 1184*t^5*z + 7804*t^5 - 1894*t^4*z^2 - 10686*t^4*z - 79520*t^4 + 2072*t^3*z^3 + 9365*t^3*z^2 + 72508*t^3*z + 542588*t^3 - 1519*t^2*z^4 - 9709*t^2*z^3/2 - 43026*t^2*z^2 - 321186*t^2*z - 2397264*t^2 + 686*t*z^5 + 4557*t*z^4/4 + 31031*t*z^3/2 + 112761*t*z^2 + 841014*t*z + 6276696*t - 2401*z^6/16 + 343*z^5/8 - 11417*z^4/4 - 35791*z^3/2 - 134199*z^2 - 1002738*z - 7483984)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_40 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 40) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_40 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_41 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 41) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_41 z t hf hn0 hn1 hn2 hn3
  · have hr : (z^2/2 - 5*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_42 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 42) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_42 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_43 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 43) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_43 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 160*t^7*z + 16*t^7 + 712*t^6*z^2 - 320*t^6*z - 32*t^6 - 1840*t^5*z^3 + 1884*t^5*z^2 + 24*t^5*z - 32*t^5 + 3019*t^4*z^4 - 5470*t^4*z^3 + 1284*t^4*z^2 + 272*t^4*z - 32*t^4 - 3220*t^3*z^5 + 9047*t^3*z^4 - 5626*t^3*z^3 - 92*t^3*z^2 + 16*t^3*z + 64*t^3 + 4361*t^2*z^6/2 - 17535*t^2*z^5/2 + 10023*t^2*z^4 - 2606*t^2*z^3 - 12*t^2*z^2 - 24*t^2*z + 16*t^2 - 1715*t*z^7/2 + 9359*t*z^6/2 - 16863*t*z^5/2 + 5357*t*z^4 - 578*t*z^3 + 48*t*z^2 - 112*t*z + 16*t + 2401*z^8/16 - 8575*z^7/8 + 11221*z^6/4 - 3206*z^5 + 1183*z^4 + 730*z^3 - 908*z^2 + 304*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-712*t^6 + 1840*t^5*z + 12836*t^5 - 3019*t^4*z^2 - 18682*t^4*z - 138664*t^4 + 3220*t^3*z^3 + 16713*t^3*z^2 + 126450*t^3*z + 944840*t^3 - 4361*t^2*z^4/2 - 17353*t^2*z^3/2 - 70713*t^2*z^2 - 528392*t^2*z - 3944272*t^2 + 1715*t*z^5/2 + 4361*t*z^4/2 + 44891*t*z^3/2 + 165485*t*z^2 + 1234676*t*z + 9215420*t - 2401*z^6/16 - 1029*z^5/8 - 3234*z^4 - 44303*z^3/2 - 165459*z^2 - 1235796*z - 9223624)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_44 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 44) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_44 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 96*t^7*z - 48*t^7 + 360*t^6*z^2 - 144*t^6*z + 144*t^6 - 864*t^5*z^3 + 972*t^5*z^2 + 216*t^5*z - 288*t^5 + 1539*t^4*z^4 - 3726*t^4*z^3 + 2340*t^4*z^2 - 1512*t^4*z + 432*t^4 - 1944*t^3*z^5 + 7047*t^3*z^4 - 6534*t^3*z^3 + 108*t^3*z^2 + 1944*t^3*z - 432*t^3 + 3645*t^2*z^6/2 - 19683*t^2*z^5/2 + 18711*t^2*z^4 - 17334*t^2*z^3 + 10908*t^2*z^2 - 3888*t^2*z + 432*t^2 - 2187*t*z^7/2 + 15309*t*z^6/2 - 38151*t*z^5/2 + 19440*t*z^4 - 5184*t*z^3 - 2916*t*z^2 + 1296*t*z + 6561*z^8/16 - 32805*z^7/8 + 16767*z^6 - 36450*z^5 + 45684*z^4 - 33048*z^3 + 12636*z^2 - 1944*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-360*t^6 + 864*t^5*z + 5940*t^5 - 1539*t^4*z^2 - 8586*t^4*z - 64872*t^4 + 1944*t^3*z^3 + 8505*t^3*z^2 + 66798*t^3*z + 500256*t^3 - 3645*t^2*z^4/2 - 9477*t^2*z^3/2 - 49329*t^2*z^2 - 358344*t^2*z - 2680344*t^2 + 2187*t*z^5/2 + 2187*t*z^4/2 + 46899*t*z^3/2 + 163782*t*z^2 + 1221642*t*z + 9120924*t - 6561*z^6/16 + 6561*z^5/8 - 34263*z^4/4 - 70713*z^3/2 - 294273*z^2 - 2179710*z - 16273224)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_45 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 45) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_45 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 3*t*z - 2*t + 3*z^2/2 - 3*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf
  · have hr : (16*t^8 - 128*t^7*z + 16*t^7 + 496*t^6*z^2 - 328*t^6*z - 32*t^6 - 1184*t^5*z^3 + 1668*t^5*z^2 - 24*t^5*z - 32*t^5 + 1894*t^4*z^4 - 4466*t^4*z^3 + 1608*t^4*z^2 + 304*t^4*z - 32*t^4 - 2072*t^3*z^5 + 7211*t^3*z^4 - 5876*t^3*z^3 + 16*t^3*z^2 - 16*t^3*z + 64*t^3 + 1519*t^2*z^6 - 14595*t^2*z^5/2 + 10266*t^2*z^4 - 3604*t^2*z^3 - 120*t^2*z^2 + 24*t^2*z + 16*t^2 - 686*t*z^7 + 17395*t*z^6/4 - 18291*t*z^5/2 + 6806*t*z^4 - 988*t*z^3 + 372*t*z^2 - 176*t*z + 16*t + 2401*z^8/16 - 9947*z^7/8 + 7595*z^6/2 - 5110*z^5 + 2452*z^4 + 728*z^3 - 1124*z^2 + 344*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-496*t^6 + 1184*t^5*z + 7804*t^5 - 1894*t^4*z^2 - 10686*t^4*z - 79520*t^4 + 2072*t^3*z^3 + 9365*t^3*z^2 + 72508*t^3*z + 542588*t^3 - 1519*t^2*z^4 - 9709*t^2*z^3/2 - 43026*t^2*z^2 - 321186*t^2*z - 2397264*t^2 + 686*t*z^5 + 4557*t*z^4/4 + 31031*t*z^3/2 + 112761*t*z^2 + 841014*t*z + 6276696*t - 2401*z^6/16 + 343*z^5/8 - 11417*z^4/4 - 35791*z^3/2 - 134199*z^2 - 1002738*z - 7483984)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_46 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 46) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_46 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 160*t^7*z + 16*t^7 + 712*t^6*z^2 - 320*t^6*z - 32*t^6 - 1840*t^5*z^3 + 1884*t^5*z^2 + 24*t^5*z - 32*t^5 + 3019*t^4*z^4 - 5470*t^4*z^3 + 1284*t^4*z^2 + 272*t^4*z - 32*t^4 - 3220*t^3*z^5 + 9047*t^3*z^4 - 5626*t^3*z^3 - 92*t^3*z^2 + 16*t^3*z + 64*t^3 + 4361*t^2*z^6/2 - 17535*t^2*z^5/2 + 10023*t^2*z^4 - 2606*t^2*z^3 - 12*t^2*z^2 - 24*t^2*z + 16*t^2 - 1715*t*z^7/2 + 9359*t*z^6/2 - 16863*t*z^5/2 + 5357*t*z^4 - 578*t*z^3 + 48*t*z^2 - 112*t*z + 16*t + 2401*z^8/16 - 8575*z^7/8 + 11221*z^6/4 - 3206*z^5 + 1183*z^4 + 730*z^3 - 908*z^2 + 304*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-712*t^6 + 1840*t^5*z + 12836*t^5 - 3019*t^4*z^2 - 18682*t^4*z - 138664*t^4 + 3220*t^3*z^3 + 16713*t^3*z^2 + 126450*t^3*z + 944840*t^3 - 4361*t^2*z^4/2 - 17353*t^2*z^3/2 - 70713*t^2*z^2 - 528392*t^2*z - 3944272*t^2 + 1715*t*z^5/2 + 4361*t*z^4/2 + 44891*t*z^3/2 + 165485*t*z^2 + 1234676*t*z + 9215420*t - 2401*z^6/16 - 1029*z^5/8 - 3234*z^4 - 44303*z^3/2 - 165459*z^2 - 1235796*z - 9223624)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_47 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 47) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_47 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 192*t^7*z + 80*t^7 + 1008*t^6*z^2 - 984*t^6*z + 112*t^6 - 3024*t^5*z^3 + 5076*t^5*z^2 - 1656*t^5*z + 32*t^5 + 5670*t^4*z^4 - 14310*t^4*z^3 + 9036*t^4*z^2 - 1104*t^4*z + 16*t^4 - 6804*t^3*z^5 + 23895*t^3*z^4 - 24516*t^3*z^3 + 7272*t^3*z^2 - 600*t^3*z + 80*t^3 + 5103*t^2*z^6 - 47385*t^2*z^5/2 + 35721*t^2*z^4 - 19224*t^2*z^3 + 3240*t^2*z^2 - 360*t^2*z + 16*t^2 - 2187*t*z^7 + 51759*t*z^6/4 - 53703*t*z^5/2 + 22680*t*z^4 - 6534*t*z^3 + 180*t*z^2 + 384*t*z - 64*t + 6561*z^8/16 - 24057*z^7/8 + 32805*z^6/4 - 9963*z^5 + 4455*z^4 + 918*z^3 - 1404*z^2 + 384*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1008*t^6 + 3024*t^5*z + 19116*t^5 - 5670*t^4*z^2 - 31050*t^4*z - 234756*t^4 + 6804*t^3*z^3 + 30537*t^3*z^2 + 241596*t^3*z + 1803348*t^3 - 5103*t^2*z^4 - 34263*t^2*z^3/2 - 152361*t^2*z^2 - 1131138*t^2*z - 8442900*t^2 + 2187*t*z^5 + 18225*t*z^4/4 + 109107*t*z^3/2 + 395523*t*z^2 + 2952504*t*z + 22037760*t - 6561*z^6/16 - 2187*z^5/8 - 8748*z^4 - 117855*z^3/2 - 440883*z^2 - 3292272*z - 24573240)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_48 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 48) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_48 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 32*t^7*z - 112*t^7 + 40*t^6*z^2 + 64*t^6*z + 256*t^6 - 32*t^5*z^3 - 12*t^5*z^2 + 336*t^5*z - 256*t^5 + 19*t^4*z^4 - 58*t^4*z^3 - 192*t^4*z^2 - 760*t^4*z + 64*t^4 - 8*t^3*z^5 + 49*t^3*z^4 + 172*t^3*z^3 - 496*t^3*z^2 + 248*t^3*z + 224*t^3 + 5*t^2*z^6/2 - 57*t^2*z^5/2 + 24*t^2*z^4 + 76*t^2*z^3 + 672*t^2*z^2 + 336*t^2*z - 272*t^2 - t*z^7/2 + 8*t*z^6 - 15*t*z^5 - 149*t*z^4 + 302*t*z^3 + 528*t*z^2 - 728*t*z + 176*t + z^8/16 - 13*z^7/8 + 13*z^6 - 35*z^5 + 10*z^4 + 100*z^3 - 284*z^2 + 184*z - 32:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 32*t^5*z + 268*t^5 - 19*t^4*z^2 - 94*t^4*z - 484*t^4 + 8*t^3*z^3 + 15*t^3*z^2 - 84*t^3*z - 236*t^3 - 5*t^2*z^4/2 + 17*t^2*z^3/2 + 54*t^2*z^2 + 322*t^2*z + 1688*t^2 + t*z^5/2 - 4*t*z^4 - 19*t*z^3 + 13*t*z^2 - 122*t*z - 1556*t - z^6/16 + 9*z^5/8 - 15*z^4/4 + z^3/2 + 9*z^2 - 30*z + 8)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_49 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 49) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : (t - 2:ℝ)=0 := by
  apply cell_3_49 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - t*z - 4*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 112*t^6*z^2 + 72*t^6*z - 48*t^6 - 112*t^5*z^3 + 36*t^5*z^2 + 360*t^5*z + 144*t^5 + 70*t^4*z^4 - 150*t^4*z^3 - 540*t^4*z^2 - 72*t^4*z - 28*t^3*z^5 + 135*t^3*z^4 + 300*t^3*z^3 - 432*t^3*z^2 - 648*t^3*z + 7*t^2*z^6 - 117*t^2*z^5/2 - 45*t^2*z^4 + 468*t^2*z^3 + 432*t^2*z^2 - t*z^7 + 51*t*z^6/4 - 27*t*z^5/2 - 153*t*z^4 + 54*t*z^3 + 648*t*z^2 + z^8/16 - 9*z^7/8 + 15*z^6/4 + 27*z^5/2 - 54*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 112*t^5*z + 860*t^5 - 70*t^4*z^2 - 410*t^4*z - 2460*t^4 + 28*t^3*z^3 + 89*t^3*z^2 + 300*t^3*z + 2476*t^3 - 7*t^2*z^4 + 5*t^2*z^3/2 + 93*t^2*z^2 + 266*t^2*z + 1324*t^2 + t*z^5 - 19*t*z^4/4 - 57*t*z^3/2 - 56*t*z^2 - 388*t*z - 3528*t - z^6/16 + 5*z^5/8 + 3*z^4/2 - 4*z^3 + 16*z^2 + 144*z + 1088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_50 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 50) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_50 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 240*t^7 + 48*t^6*z^2 - 168*t^6*z + 1440*t^6 - 540*t^5*z^2 + 1944*t^5*z - 4608*t^5 + 54*t^4*z^4 - 378*t^4*z^3 + 2880*t^4*z^2 - 8208*t^4*z + 8640*t^4 - 405*t^3*z^4 + 2916*t^3*z^3 - 9504*t^3*z^2 + 16416*t^3*z - 9504*t^3 + 27*t^2*z^6 - 567*t^2*z^5/2 + 1890*t^2*z^4 - 7884*t^2*z^3 + 16416*t^2*z^2 - 16200*t^2*z + 5616*t^2 - 405*t*z^6/4 + 2187*t*z^5/2 - 4536*t*z^4 + 9720*t*z^3 - 11340*t*z^2 + 6480*t*z - 1296*t + 81*z^8/16 - 567*z^7/8 + 405*z^6 - 1296*z^5 + 2592*z^4 - 3240*z^3 + 2268*z^2 - 648*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-48*t^6 + 540*t^5 - 54*t^4*z^2 - 54*t^4*z - 3096*t^4 + 405*t^3*z^2 + 324*t^3*z + 10476*t^3 - 27*t^2*z^4 + 135*t^2*z^3/2 - 1242*t^2*z^2 - 2322*t^2*z - 30024*t^2 + 405*t*z^4/4 - 567*t*z^3/2 + 1863*t*z^2 + 6318*t*z + 54432*t - 81*z^6/16 + 243*z^5/8 - 567*z^4/4 + 81*z^3/2 - 1701*z^2 - 10530*z - 79704)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_51 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 51) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_51 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 32*t^7*z - 240*t^7 + 40*t^6*z^2 - 528*t^6*z + 1440*t^6 + 32*t^5*z^3 - 612*t^5*z^2 + 3456*t^5*z - 4608*t^5 + 19*t^4*z^4 - 462*t^4*z^3 + 3744*t^4*z^2 - 11304*t^4*z + 8640*t^4 + 8*t^3*z^5 - 237*t^3*z^4 + 2520*t^3*z^3 - 11448*t^3*z^2 + 19656*t^3*z - 9504*t^3 + 5*t^2*z^6/2 - 171*t^2*z^5/2 + 1080*t^2*z^4 - 6336*t^2*z^3 + 17280*t^2*z^2 - 17712*t^2*z + 5616*t^2 + t*z^7/2 - 39*t*z^6/2 + 288*t*z^5 - 2043*t*z^4 + 7074*t*z^3 - 10800*t*z^2 + 6696*t*z - 1296*t + z^8/16 - 21*z^7/8 + 81*z^6/2 - 297*z^5 + 1134*z^4 - 2268*z^3 + 2052*z^2 - 648*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 - 32*t^5*z + 356*t^5 - 19*t^4*z^2 + 310*t^4*z - 1188*t^4 - 8*t^3*z^3 + 173*t^3*z^2 - 1104*t^3*z + 1924*t^3 - 5*t^2*z^4/2 + 131*t^2*z^3/2 - 546*t^2*z^2 + 1706*t^2*z - 1448*t^2 - t*z^5/2 + 31*t*z^4/2 - 162*t*z^3 + 685*t*z^2 - 946*t*z + 492*t - z^6/16 + 17*z^5/8 - 93*z^4/4 + 205*z^3/2 - 221*z^2 + 90*z - 448)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 112*t^6*z^2 + 72*t^6*z - 48*t^6 - 112*t^5*z^3 + 36*t^5*z^2 + 360*t^5*z + 144*t^5 + 70*t^4*z^4 - 150*t^4*z^3 - 540*t^4*z^2 - 72*t^4*z - 28*t^3*z^5 + 135*t^3*z^4 + 300*t^3*z^3 - 432*t^3*z^2 - 648*t^3*z + 7*t^2*z^6 - 117*t^2*z^5/2 - 45*t^2*z^4 + 468*t^2*z^3 + 432*t^2*z^2 - t*z^7 + 51*t*z^6/4 - 27*t*z^5/2 - 153*t*z^4 + 54*t*z^3 + 648*t*z^2 + z^8/16 - 9*z^7/8 + 15*z^6/4 + 27*z^5/2 - 54*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 112*t^5*z + 860*t^5 - 70*t^4*z^2 - 410*t^4*z - 2460*t^4 + 28*t^3*z^3 + 89*t^3*z^2 + 300*t^3*z + 2476*t^3 - 7*t^2*z^4 + 5*t^2*z^3/2 + 93*t^2*z^2 + 266*t^2*z + 1324*t^2 + t*z^5 - 19*t*z^4/4 - 57*t*z^3/2 - 56*t*z^2 - 388*t*z - 3528*t - z^6/16 + 5*z^5/8 + 3*z^4/2 - 4*z^3 + 16*z^2 + 144*z + 1088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_52 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 52) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_52 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - t*z - 4*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 160*t^6*z^2 - 120*t^6*z + 144*t^6 - 256*t^5*z^3 + 504*t^5*z^2 + 216*t^5*z - 288*t^5 + 304*t^4*z^4 - 1248*t^4*z^3 + 1152*t^4*z^2 - 1152*t^4*z + 432*t^4 - 256*t^3*z^5 + 1560*t^3*z^4 - 2232*t^3*z^3 - 216*t^3*z^2 + 1512*t^3*z - 432*t^3 + 160*t^2*z^6 - 1440*t^2*z^5 + 4320*t^2*z^4 - 5904*t^2*z^3 + 5616*t^2*z^2 - 2808*t^2*z + 432*t^2 - 64*t*z^7 + 744*t*z^6 - 2952*t*z^5 + 4464*t*z^4 - 1296*t*z^3 - 1728*t*z^2 + 864*t*z + 16*z^8 - 264*z^7 + 1728*z^6 - 5832*z^5 + 11016*z^4 - 11664*z^3 + 6264*z^2 - 1296*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 1544*t^5 - 304*t^4*z^2 - 1184*t^4*z - 9408*t^4 + 256*t^3*z^3 + 488*t^3*z^2 + 5112*t^3*z + 39160*t^3 - 160*t^2*z^4 + 160*t^2*z^3 - 2400*t^2*z^2 - 13936*t^2*z - 107504*t^2 + 64*t*z^5 - 232*t*z^4 + 840*t*z^3 + 3184*t*z^2 + 23408*t*z + 176256*t - 16*z^6 + 136*z^5 - 576*z^4 + 680*z^3 - 3272*z^2 - 17232*z - 131032)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_53 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 53) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_53 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 2*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 176*t^7 - 72*t^6*z + 688*t^6 + 648*t^5*z - 1184*t^5 + 72*t^4*z^2 - 1728*t^4*z + 784*t^4 - 504*t^3*z^2 + 1224*t^3*z + 208*t^3 + 648*t^2*z^2 + 648*t^2*z - 560*t^2 + 576*t*z^2 - 864*t*z + 256*t - 144*z^2 + 144*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-72*t^4 + 504*t^3 - 648*t^2 - 576*t + 144)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_54 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 54) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_54 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 3*t*z - 2*t + 3*z^2/2 - 3*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf
  · have hr : (16*t^8 - 32*t^7*z - 176*t^7 + 40*t^6*z^2 + 224*t^6*z + 688*t^6 - 32*t^5*z^3 - 204*t^5*z^2 - 312*t^5*z - 1184*t^5 + 19*t^4*z^4 + 94*t^4*z^3 + 132*t^4*z^2 - 392*t^4*z + 784*t^4 - 8*t^3*z^5 - 31*t^3*z^4 + 118*t^3*z^3 + 172*t^3*z^2 + 536*t^3*z + 208*t^3 + 5*t^2*z^6/2 + 3*t^2*z^5/2 - 57*t^2*z^4 - 202*t^2*z^3 + 132*t^2*z^2 + 528*t^2*z - 560*t^2 - t*z^7/2 + t*z^6 + 51*t*z^5/2 - 22*t*z^4 - 148*t*z^3 + 444*t*z^2 - 656*t*z + 256*t + z^8/16 - 5*z^7/8 - z^6/2 + 8*z^5 - 8*z^4 + 8*z^3 - 68*z^2 + 104*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 32*t^5*z + 460*t^5 - 19*t^4*z^2 - 246*t^4*z - 2024*t^4 + 8*t^3*z^3 + 95*t^3*z^2 + 610*t^3*z + 4328*t^3 - 5*t^2*z^4/2 - 43*t^2*z^3/2 - 105*t^2*z^2 - 552*t^2*z - 4128*t^2 + t*z^5/2 + 3*t*z^4 - 7*t*z^3/2 - 18*t*z^2 + 18*t*z - 228*t - z^6/16 + z^5/8 + 7*z^4/4 + 11*z^3/2 + 45*z^2 + 330*z + 2528)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_55 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 55) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_55 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + z^2/2 - z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 32*t^7*z - 112*t^7 + 40*t^6*z^2 + 64*t^6*z + 256*t^6 - 32*t^5*z^3 - 12*t^5*z^2 + 336*t^5*z - 256*t^5 + 19*t^4*z^4 - 58*t^4*z^3 - 192*t^4*z^2 - 760*t^4*z + 64*t^4 - 8*t^3*z^5 + 49*t^3*z^4 + 172*t^3*z^3 - 496*t^3*z^2 + 248*t^3*z + 224*t^3 + 5*t^2*z^6/2 - 57*t^2*z^5/2 + 24*t^2*z^4 + 76*t^2*z^3 + 672*t^2*z^2 + 336*t^2*z - 272*t^2 - t*z^7/2 + 8*t*z^6 - 15*t*z^5 - 149*t*z^4 + 302*t*z^3 + 528*t*z^2 - 728*t*z + 176*t + z^8/16 - 13*z^7/8 + 13*z^6 - 35*z^5 + 10*z^4 + 100*z^3 - 284*z^2 + 184*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 32*t^5*z + 268*t^5 - 19*t^4*z^2 - 94*t^4*z - 484*t^4 + 8*t^3*z^3 + 15*t^3*z^2 - 84*t^3*z - 236*t^3 - 5*t^2*z^4/2 + 17*t^2*z^3/2 + 54*t^2*z^2 + 322*t^2*z + 1688*t^2 + t*z^5/2 - 4*t*z^4 - 19*t*z^3 + 13*t*z^2 - 122*t*z - 1556*t - z^6/16 + 9*z^5/8 - 15*z^4/4 + z^3/2 + 9*z^2 - 30*z + 8)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_56 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 56) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_56 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 240*t^7 + 48*t^6*z^2 - 168*t^6*z + 1440*t^6 - 540*t^5*z^2 + 1944*t^5*z - 4608*t^5 + 54*t^4*z^4 - 378*t^4*z^3 + 2880*t^4*z^2 - 8208*t^4*z + 8640*t^4 - 405*t^3*z^4 + 2916*t^3*z^3 - 9504*t^3*z^2 + 16416*t^3*z - 9504*t^3 + 27*t^2*z^6 - 567*t^2*z^5/2 + 1890*t^2*z^4 - 7884*t^2*z^3 + 16416*t^2*z^2 - 16200*t^2*z + 5616*t^2 - 405*t*z^6/4 + 2187*t*z^5/2 - 4536*t*z^4 + 9720*t*z^3 - 11340*t*z^2 + 6480*t*z - 1296*t + 81*z^8/16 - 567*z^7/8 + 405*z^6 - 1296*z^5 + 2592*z^4 - 3240*z^3 + 2268*z^2 - 648*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-48*t^6 + 540*t^5 - 54*t^4*z^2 - 54*t^4*z - 3096*t^4 + 405*t^3*z^2 + 324*t^3*z + 10476*t^3 - 27*t^2*z^4 + 135*t^2*z^3/2 - 1242*t^2*z^2 - 2322*t^2*z - 30024*t^2 + 405*t*z^4/4 - 567*t*z^3/2 + 1863*t*z^2 + 6318*t*z + 54432*t - 81*z^6/16 + 243*z^5/8 - 567*z^4/4 + 81*z^3/2 - 1701*z^2 - 10530*z - 79704)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_57 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 57) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_57 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 3*t*z - 2*t + 3*z^2/2 - 3*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf
  · have hr : (16*t^8 - 32*t^7*z - 176*t^7 + 40*t^6*z^2 + 224*t^6*z + 688*t^6 - 32*t^5*z^3 - 204*t^5*z^2 - 312*t^5*z - 1184*t^5 + 19*t^4*z^4 + 94*t^4*z^3 + 132*t^4*z^2 - 392*t^4*z + 784*t^4 - 8*t^3*z^5 - 31*t^3*z^4 + 118*t^3*z^3 + 172*t^3*z^2 + 536*t^3*z + 208*t^3 + 5*t^2*z^6/2 + 3*t^2*z^5/2 - 57*t^2*z^4 - 202*t^2*z^3 + 132*t^2*z^2 + 528*t^2*z - 560*t^2 - t*z^7/2 + t*z^6 + 51*t*z^5/2 - 22*t*z^4 - 148*t*z^3 + 444*t*z^2 - 656*t*z + 256*t + z^8/16 - 5*z^7/8 - z^6/2 + 8*z^5 - 8*z^4 + 8*z^3 - 68*z^2 + 104*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 32*t^5*z + 460*t^5 - 19*t^4*z^2 - 246*t^4*z - 2024*t^4 + 8*t^3*z^3 + 95*t^3*z^2 + 610*t^3*z + 4328*t^3 - 5*t^2*z^4/2 - 43*t^2*z^3/2 - 105*t^2*z^2 - 552*t^2*z - 4128*t^2 + t*z^5/2 + 3*t*z^4 - 7*t*z^3/2 - 18*t*z^2 + 18*t*z - 228*t - z^6/16 + z^5/8 + 7*z^4/4 + 11*z^3/2 + 45*z^2 + 330*z + 2528)*hf
  · have hr : (16*t^8 - 128*t^7*z + 16*t^7 + 496*t^6*z^2 - 328*t^6*z - 32*t^6 - 1184*t^5*z^3 + 1668*t^5*z^2 - 24*t^5*z - 32*t^5 + 1894*t^4*z^4 - 4466*t^4*z^3 + 1608*t^4*z^2 + 304*t^4*z - 32*t^4 - 2072*t^3*z^5 + 7211*t^3*z^4 - 5876*t^3*z^3 + 16*t^3*z^2 - 16*t^3*z + 64*t^3 + 1519*t^2*z^6 - 14595*t^2*z^5/2 + 10266*t^2*z^4 - 3604*t^2*z^3 - 120*t^2*z^2 + 24*t^2*z + 16*t^2 - 686*t*z^7 + 17395*t*z^6/4 - 18291*t*z^5/2 + 6806*t*z^4 - 988*t*z^3 + 372*t*z^2 - 176*t*z + 16*t + 2401*z^8/16 - 9947*z^7/8 + 7595*z^6/2 - 5110*z^5 + 2452*z^4 + 728*z^3 - 1124*z^2 + 344*z - 32:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-496*t^6 + 1184*t^5*z + 7804*t^5 - 1894*t^4*z^2 - 10686*t^4*z - 79520*t^4 + 2072*t^3*z^3 + 9365*t^3*z^2 + 72508*t^3*z + 542588*t^3 - 1519*t^2*z^4 - 9709*t^2*z^3/2 - 43026*t^2*z^2 - 321186*t^2*z - 2397264*t^2 + 686*t*z^5 + 4557*t*z^4/4 + 31031*t*z^3/2 + 112761*t*z^2 + 841014*t*z + 6276696*t - 2401*z^6/16 + 343*z^5/8 - 11417*z^4/4 - 35791*z^3/2 - 134199*z^2 - 1002738*z - 7483984)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_58 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 58) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_58 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 176*t^7 + 112*t^6*z^2 + 520*t^6*z + 688*t^6 - 112*t^5*z^3 - 636*t^5*z^2 - 1272*t^5*z - 1184*t^5 + 70*t^4*z^4 + 410*t^4*z^3 + 780*t^4*z^2 + 944*t^4*z + 784*t^4 - 28*t^3*z^5 - 145*t^3*z^4 - 100*t^3*z^3 + 136*t^3*z^2 - 152*t^3*z + 208*t^3 + 7*t^2*z^6 + 51*t^2*z^5/2 - 75*t^2*z^4 - 248*t^2*z^3 + 24*t^2*z^2 + 408*t^2*z - 560*t^2 - t*z^7 - 5*t*z^6/4 + 57*t*z^5/2 + 44*t*z^4 - 86*t*z^3 + 228*t*z^2 - 448*t*z + 256*t + z^8/16 - z^7/8 - 11*z^6/4 + z^5 + 7*z^4 - 26*z^3 + 4*z^2 + 64*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 112*t^5*z + 1532*t^5 - 70*t^4*z^2 - 970*t^4*z - 8260*t^4 + 28*t^3*z^3 + 369*t^3*z^2 + 2940*t^3*z + 21908*t^3 - 7*t^2*z^4 - 163*t^2*z^3/2 - 549*t^2*z^2 - 3818*t^2*z - 28372*t^2 + t*z^5 + 37*t*z^4/4 + 83*t*z^3/2 + 251*t*z^2 + 1928*t*z + 14192*t - z^6/16 - 3*z^5/8 + z^3/2 - 3*z^2 + 8)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_59 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 59) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_59 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 96*t^7*z - 112*t^7 + 264*t^6*z^2 + 432*t^6*z + 256*t^6 - 432*t^5*z^3 - 684*t^5*z^2 - 360*t^5*z - 256*t^5 + 459*t^4*z^4 + 486*t^4*z^3 - 180*t^4*z^2 - 192*t^4*z + 64*t^4 - 324*t^3*z^5 - 27*t^3*z^4 + 702*t^3*z^3 + 276*t^3*z^2 + 144*t^3*z + 224*t^3 + 297*t^2*z^6/2 - 405*t^2*z^5/2 - 459*t^2*z^4 + 162*t^2*z^3 + 396*t^2*z^2 + 72*t^2*z - 272*t^2 - 81*t*z^7/2 + 135*t*z^6 + 81*t*z^5/2 - 297*t*z^4 + 54*t*z^3 + 360*t*z^2 - 528*t*z + 176*t + 81*z^8/16 - 243*z^7/8 + 189*z^6/4 - 81*z^4 + 162*z^3 - 204*z^2 + 144*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-264*t^6 + 432*t^5*z + 4140*t^5 - 459*t^4*z^2 - 4158*t^4*z - 31248*t^4 + 324*t^3*z^3 + 2619*t^3*z^2 + 18954*t^3*z + 140880*t^3 - 297*t^2*z^4/2 - 1971*t^2*z^3/2 - 6831*t^2*z^2 - 50868*t^2*z - 380016*t^2 + 81*t*z^5/2 + 189*t*z^4 + 2619*t*z^3/2 + 10017*t*z^2 + 74844*t*z + 558324*t - 81*z^6/16 - 81*z^5/8 - 108*z^4 - 1647*z^3/2 - 6075*z^2 - 45468*z - 339240)*hf
  · have hr : (16*t^8 - 192*t^7*z + 80*t^7 + 1008*t^6*z^2 - 984*t^6*z + 112*t^6 - 3024*t^5*z^3 + 5076*t^5*z^2 - 1656*t^5*z + 32*t^5 + 5670*t^4*z^4 - 14310*t^4*z^3 + 9036*t^4*z^2 - 1104*t^4*z + 16*t^4 - 6804*t^3*z^5 + 23895*t^3*z^4 - 24516*t^3*z^3 + 7272*t^3*z^2 - 600*t^3*z + 80*t^3 + 5103*t^2*z^6 - 47385*t^2*z^5/2 + 35721*t^2*z^4 - 19224*t^2*z^3 + 3240*t^2*z^2 - 360*t^2*z + 16*t^2 - 2187*t*z^7 + 51759*t*z^6/4 - 53703*t*z^5/2 + 22680*t*z^4 - 6534*t*z^3 + 180*t*z^2 + 384*t*z - 64*t + 6561*z^8/16 - 24057*z^7/8 + 32805*z^6/4 - 9963*z^5 + 4455*z^4 + 918*z^3 - 1404*z^2 + 384*z - 32:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1008*t^6 + 3024*t^5*z + 19116*t^5 - 5670*t^4*z^2 - 31050*t^4*z - 234756*t^4 + 6804*t^3*z^3 + 30537*t^3*z^2 + 241596*t^3*z + 1803348*t^3 - 5103*t^2*z^4 - 34263*t^2*z^3/2 - 152361*t^2*z^2 - 1131138*t^2*z - 8442900*t^2 + 2187*t*z^5 + 18225*t*z^4/4 + 109107*t*z^3/2 + 395523*t*z^2 + 2952504*t*z + 22037760*t - 6561*z^6/16 - 2187*z^5/8 - 8748*z^4 - 117855*z^3/2 - 440883*z^2 - 3292272*z - 24573240)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_60 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 60) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_60 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 32*t^7*z - 240*t^7 + 40*t^6*z^2 - 528*t^6*z + 1440*t^6 + 32*t^5*z^3 - 612*t^5*z^2 + 3456*t^5*z - 4608*t^5 + 19*t^4*z^4 - 462*t^4*z^3 + 3744*t^4*z^2 - 11304*t^4*z + 8640*t^4 + 8*t^3*z^5 - 237*t^3*z^4 + 2520*t^3*z^3 - 11448*t^3*z^2 + 19656*t^3*z - 9504*t^3 + 5*t^2*z^6/2 - 171*t^2*z^5/2 + 1080*t^2*z^4 - 6336*t^2*z^3 + 17280*t^2*z^2 - 17712*t^2*z + 5616*t^2 + t*z^7/2 - 39*t*z^6/2 + 288*t*z^5 - 2043*t*z^4 + 7074*t*z^3 - 10800*t*z^2 + 6696*t*z - 1296*t + z^8/16 - 21*z^7/8 + 81*z^6/2 - 297*z^5 + 1134*z^4 - 2268*z^3 + 2052*z^2 - 648*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 - 32*t^5*z + 356*t^5 - 19*t^4*z^2 + 310*t^4*z - 1188*t^4 - 8*t^3*z^3 + 173*t^3*z^2 - 1104*t^3*z + 1924*t^3 - 5*t^2*z^4/2 + 131*t^2*z^3/2 - 546*t^2*z^2 + 1706*t^2*z - 1448*t^2 - t*z^5/2 + 31*t*z^4/2 - 162*t*z^3 + 685*t*z^2 - 946*t*z + 492*t - z^6/16 + 17*z^5/8 - 93*z^4/4 + 205*z^3/2 - 221*z^2 + 90*z - 448)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_61 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 61) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_61 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + z^2/2 - z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 32*t^7*z - 112*t^7 + 40*t^6*z^2 + 64*t^6*z + 256*t^6 - 32*t^5*z^3 - 12*t^5*z^2 + 336*t^5*z - 256*t^5 + 19*t^4*z^4 - 58*t^4*z^3 - 192*t^4*z^2 - 760*t^4*z + 64*t^4 - 8*t^3*z^5 + 49*t^3*z^4 + 172*t^3*z^3 - 496*t^3*z^2 + 248*t^3*z + 224*t^3 + 5*t^2*z^6/2 - 57*t^2*z^5/2 + 24*t^2*z^4 + 76*t^2*z^3 + 672*t^2*z^2 + 336*t^2*z - 272*t^2 - t*z^7/2 + 8*t*z^6 - 15*t*z^5 - 149*t*z^4 + 302*t*z^3 + 528*t*z^2 - 728*t*z + 176*t + z^8/16 - 13*z^7/8 + 13*z^6 - 35*z^5 + 10*z^4 + 100*z^3 - 284*z^2 + 184*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 32*t^5*z + 268*t^5 - 19*t^4*z^2 - 94*t^4*z - 484*t^4 + 8*t^3*z^3 + 15*t^3*z^2 - 84*t^3*z - 236*t^3 - 5*t^2*z^4/2 + 17*t^2*z^3/2 + 54*t^2*z^2 + 322*t^2*z + 1688*t^2 + t*z^5/2 - 4*t*z^4 - 19*t*z^3 + 13*t*z^2 - 122*t*z - 1556*t - z^6/16 + 9*z^5/8 - 15*z^4/4 + z^3/2 + 9*z^2 - 30*z + 8)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_62 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 62) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_62 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 96*t^7*z - 112*t^7 + 264*t^6*z^2 + 432*t^6*z + 256*t^6 - 432*t^5*z^3 - 684*t^5*z^2 - 360*t^5*z - 256*t^5 + 459*t^4*z^4 + 486*t^4*z^3 - 180*t^4*z^2 - 192*t^4*z + 64*t^4 - 324*t^3*z^5 - 27*t^3*z^4 + 702*t^3*z^3 + 276*t^3*z^2 + 144*t^3*z + 224*t^3 + 297*t^2*z^6/2 - 405*t^2*z^5/2 - 459*t^2*z^4 + 162*t^2*z^3 + 396*t^2*z^2 + 72*t^2*z - 272*t^2 - 81*t*z^7/2 + 135*t*z^6 + 81*t*z^5/2 - 297*t*z^4 + 54*t*z^3 + 360*t*z^2 - 528*t*z + 176*t + 81*z^8/16 - 243*z^7/8 + 189*z^6/4 - 81*z^4 + 162*z^3 - 204*z^2 + 144*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-264*t^6 + 432*t^5*z + 4140*t^5 - 459*t^4*z^2 - 4158*t^4*z - 31248*t^4 + 324*t^3*z^3 + 2619*t^3*z^2 + 18954*t^3*z + 140880*t^3 - 297*t^2*z^4/2 - 1971*t^2*z^3/2 - 6831*t^2*z^2 - 50868*t^2*z - 380016*t^2 + 81*t*z^5/2 + 189*t*z^4 + 2619*t*z^3/2 + 10017*t*z^2 + 74844*t*z + 558324*t - 81*z^6/16 - 81*z^5/8 - 108*z^4 - 1647*z^3/2 - 6075*z^2 - 45468*z - 339240)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_3_63 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 63) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : False := by
  apply cell_3_63 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (-3*t*z^6/4 + 45*t*z^5/2 - 198*t*z^4 + 426*t*z^3 + 684*t*z^2 - 576*t*z + 96*t + z^8/16 - 17*z^7/8 + 97*z^6/4 - 109*z^5 + 151*z^4 + 134*z^3 - 428*z^2 + 224*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(3*t*z^4/4 - 33*t*z^3/2 + 63*t*z^2 + 144*t*z + 216*t - z^6/16 + 13*z^5/8 - 11*z^4 + 29*z^3/2 + 9*z^2 - 120*z - 568)*hf


private def limit3 (z t : ℝ) : Fin 64→Prop := ![False,False,False,False,False,False,False,False,False,False,False,False,False,((t - 2:ℝ)=0),False,False,False,False,False,False,(((0:ℝ):ℝ)=0),False,(((0:ℝ):ℝ)=0),False,False,((t - 2*z + 1:ℝ)=0),False,False,False,False,False,False,False,False,False,False,False,((t - 2*z + 1:ℝ)=0),False,False,False,False,False,False,False,False,False,False,False,((t - 2:ℝ)=0),False,False,False,False,False,False,False,False,False,False,False,False,False,False]

private def hue3 : Fin 64→Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_3_13_20 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit3 z t 13) (_hj : limit3 z t 20) (he : edge4 (1) (1) (1) (profile4 (z/2) (z) t 13) (profile4 (z/2) (z) t 20) (z/2) (z) t=0) : False := by
  apply pair_3_13_20 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (16*t^8 - 64*t^7*z - 48*t^7 + 160*t^6*z^2 - 120*t^6*z + 144*t^6 - 256*t^5*z^3 + 504*t^5*z^2 + 216*t^5*z - 288*t^5 + 304*t^4*z^4 - 1248*t^4*z^3 + 1152*t^4*z^2 - 1152*t^4*z + 432*t^4 - 256*t^3*z^5 + 1560*t^3*z^4 - 2232*t^3*z^3 - 216*t^3*z^2 + 1512*t^3*z - 432*t^3 + 160*t^2*z^6 - 1440*t^2*z^5 + 4320*t^2*z^4 - 5904*t^2*z^3 + 5616*t^2*z^2 - 2808*t^2*z + 432*t^2 - 64*t*z^7 + 744*t*z^6 - 2952*t*z^5 + 4464*t*z^4 - 1296*t*z^3 - 1728*t*z^2 + 864*t*z + 16*z^8 - 264*z^7 + 1728*z^6 - 5832*z^5 + 11016*z^4 - 11664*z^3 + 6264*z^2 - 1296*z:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-160*t^6 + 256*t^5*z + 1544*t^5 - 304*t^4*z^2 - 1184*t^4*z - 9408*t^4 + 256*t^3*z^3 + 488*t^3*z^2 + 5112*t^3*z + 39160*t^3 - 160*t^2*z^4 + 160*t^2*z^3 - 2400*t^2*z^2 - 13936*t^2*z - 107504*t^2 + 64*t*z^5 - 232*t*z^4 + 840*t*z^3 + 3184*t*z^2 + 23408*t*z + 176256*t - 16*z^6 + 136*z^5 - 576*z^4 + 680*z^3 - 3272*z^2 - 17232*z - 131032)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_3_25_49 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit3 z t 25) (hj : limit3 z t 49) (_he : edge4 (1) (1) (1) (profile4 (z/2) (z) t 25) (profile4 (z/2) (z) t 49) (z/2) (z) t=0) : False := by
  apply pair_3_25_49 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma exclude_field_3 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (g : Fin 5→Fin 64) (hinj : Function.Injective g)
    (hc : ∀ i, cell (1) (1) (1) (profile4 (z/2) (z) t (g i)) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t)
    (he : ∀ i j : Fin 5, i≠j → edge4 (1) (1) (1) (profile4 (z/2) (z) t (g i)) (profile4 (z/2) (z) t (g j)) (z/2) (z) t=0) : False := by
  have row (k : Fin 64) (hh : cell (1) (1) (1) (profile4 (z/2) (z) t k) ((1),(z/2),(z/2)) ((z/2),(1),(z/2)) (z/2) (z) t) : limit3 z t k := by
    fin_cases k
    · exact row_3_0 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_1 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_2 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_3 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_4 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_5 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_6 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_7 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_8 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_9 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_10 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_11 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_12 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_13 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_14 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_15 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_16 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_17 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_18 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_19 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_20 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_21 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_22 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_23 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_24 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_25 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_26 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_27 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_28 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_29 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_30 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_31 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_32 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_33 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_34 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_35 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_36 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_37 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_38 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_39 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_40 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_41 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_42 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_43 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_44 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_45 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_46 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_47 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_48 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_49 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_50 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_51 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_52 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_53 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_54 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_55 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_56 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_57 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_58 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_59 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_60 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_61 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_62 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_3_63 z t hf hn0 hn1 hn2 hn3 hh
  have allowed (k : Fin 64) (hh : limit3 z t k) : k∈([13,20,22,25,37,49]:List (Fin 64)) := by
    fin_cases k <;> first | decide | exact False.elim hh
  have cert : ∀ i j : Fin 64, i∈([13,20,22,25,37,49]:List (Fin 64)) → j∈([13,20,22,25,37,49]:List (Fin 64)) → i<j → hue3 i=hue3 j → (i,j)∈([(13,20),(25,49)]:List (Fin 64×Fin 64)) := by decide
  have bad (i j : Fin 64) (hi : limit3 z t i) (hj : limit3 z t j) (hlt : i<j) (hc : hue3 i=hue3 j) (hb : edge4 (1) (1) (1) (profile4 (z/2) (z) t i) (profile4 (z/2) (z) t j) (z/2) (z) t=0) : False := by
    have h := cert i j (allowed i hi) (allowed j hj) hlt hc
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact rowpair_3_13_20 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_3_25_49 z t hf hn0 hn1 hn2 hn3 hi hj hb
  have hi : Function.Injective (fun i : Fin 5 => hue3 (g i)) := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne (show g i≠g j from fun e => hne (hinj e)) with hl|hl
    · exact bad _ _ (row _ (hc i)) (row _ (hc j)) hl h (he i j hne)
    · exact bad _ _ (row _ (hc j)) (row _ (hc i)) hl h.symm (he j i (Ne.symm hne))
  have hh := Fintype.card_le_of_injective _ hi
  norm_num at hh

private lemma cell_4_0 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_4_1 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_4_2 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 3/4)*h0 + (-1/2)*hf
  norm_num at hh

private lemma cell_4_3 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 128*z) + t^6*(1584*z - 576) + t^5*(2640 - 9168*z) + t^4*(29232*z - 7488) + t^3*(13104 - 50400*z) + t^2*(43200*z - 11664) + t*(3888 - 14256*z):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (-t^6/648 + t^5*(z/81 - 1/162) + t^4*(1/27 - 25*z/216) + t^3*(29*z/54 - 31/216) + t^2*(7/24 - 29*z/24) + t*(89*z/72 - 7/18) - 11*z/24 - 1/24)*h0 + (1/5184)*h1
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_4_4 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_4_5 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/6)*h0
  norm_num at hh

private lemma cell_4_6 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h1 : (2592*t*z:ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (1/648 - z/2592)*h1 + (t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_4_7 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 48) + t^6*(2032*z - 592) + t^5*(4448 - 14160*z) + t^4*(54080*z - 14736) + t^3*(29872 - 116656*z) + t^2*(137040*z - 36176) + t*(21600 - 77984*z) + 15232*z - 4096:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(19/1458 - 5*z/1458) + t^6*(11*z/729 - 187/2916) + t^5*(11*z/243 - 61/972) + t^4*(427/729 - 1043*z/2916) + t^3*(2515*z/2916 - 863/2916) + t^2*(-1441*z/972 - 673/972) + t*(2791*z/1458 - 569/1458) - 766*z/729 + 1201/1458)*h0 + (t*(5*z/11664 - 19/11664) - 19*z/11664 + 145/23328)*h1 + (40*t^8/729 - 787*t^7/729 + 6838*t^6/729 - 33715*t^5/729 + 100675*t^4/729 - 181354*t^3/729 + 187105*t^2/729 - 97366*t/729 + 18088/729)*hf
  norm_num at hh

private lemma cell_4_8 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 3/4)*h0 + (-1/2)*hf
  norm_num at hh

private lemma cell_4_9 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(2592*z - 7776) - 7776*z + 23328:ℝ)=0) (h2 : (t*(2592 - 12960*z) + 75168*z - 18144:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/5184)*h1 + (7*z/15552 - 13/7776)*h2 + (35*t/6 - 203/6)*hf
  norm_num at hh

private lemma cell_4_10 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) : ((0:ℝ):ℝ)=0 := by
  rfl

private lemma cell_4_11 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 4*z:ℝ)=0) (h1 : (16*t^8 + t^7*(80 - 192*z) + t^6*(3072*z - 848) + t^5*(7520 - 27936*z) + t^4*(151680*z - 40592) + t^3*(134528 - 502032*z) + t^2*(987264*z - 264656) + t*(282032 - 1053840*z) + 467328*z - 125120:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(-z/648 - 1/648) + t^5*(2*z/27 - 1/36) + t^4*(53/216 - 209*z/216) + t^3*(4309*z/648 - 1175/648) + t^2*(19/3 - 2581*z/108) + t*(9181*z/216 - 2491/216) - 9257*z/324 + 598/81)*h0 + (z/5184 + 1/5184)*h1 + (11*t^7/324 - 71*t^6/162 + 341*t^5/108 - 3917*t^4/324 + 7273*t^3/324 - 1063*t^2/108 - 7735*t/324 + 1955/81)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_4_12 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h2 : (16*t^8 + t^7*(64*z - 176) + t^6*(624 - 192*z) + t^5*(192*z - 960) + 432*t^4 + t^3*(864 - 432*z) - 1296*t^2 + t*(432*z + 432):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(13/324 - 7*z/648) + t^5*(2*z/27 - 5/18) + t^4*(65/108 - 35*z/216) + t^3*(z/8 - 17/36) + t^2*(z/12 - 1/3) + t*(7/8 - z/4) + z/8 - 5/8)*h0 + (7*z/5184 - 13/2592)*h2 + (-7*t^7/81 + 7*t^6/27 - 7*t^5/27 + 7*t^3/12 - 7*t/12)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_4_13 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 432) + t^6*(4784 - 1088*z) + t^5*(7584*z - 28672) + t^4*(102288 - 28192*z) + t^3*(60848*z - 222752) + t^2*(288400 - 77088*z) + t*(53392*z - 201840) - 15392*z + 58016:ℝ)=0) : (t + z - 4:ℝ)=0 := by
  have hh : (t + z - 4:ℝ)=0 := by linear_combination (t^6*(1/324 - z/162) + t^5*(z/18 - 5/108) + t^4*(17/54 - 4*z/27) + t^3*(14*z/81 - 421/324) + t^2*(361/108 - 5*z/9) + t*(149*z/108 - 521/108) - 89*z/81 + 527/162)*h0 + (z/1296 - 1/2592)*h1 + (-4*t^7/81 + 68*t^6/81 - 158*t^5/27 + 1762*t^4/81 - 3803*t^3/81 + 1606*t^2/27 - 3337*t/81 + 962/81)*hf
  exact hh

private lemma cell_4_14 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 4*z:ℝ)=0) (h1 : (16*t^8 - 304*t^7 + t^6*(2224 - 48*z) + t^5*(720*z - 7888) + t^4*(13792 - 3600*z) + t^3*(6384*z - 9952) + t^2*(-1440*z - 128) + t*(2432 - 1440*z) + 384*z - 512:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(z/324 - 7/648) + t^5*(13/72 - 11*z/216) + t^4*(8*z/27 - 29/27) + t^3*(1711/648 - 455*z/648) + t^2*(14*z/27 - 49/24) + t*(11*z/108 - 14/27) - 11*z/81 + 85/324)*h0 + (7/5184 - z/2592)*h1 + (t^7/162 - 43*t^6/324 + 29*t^5/27 - 1289*t^4/324 + 511*t^3/81 - 131*t^2/54 - 100*t/81 + 56/81)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_4_15 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 176) + t^6*(992*z + 624) + t^5*(-6144*z - 352) + t^4*(19264*z - 2992) + t^3*(8064 - 31664*z) + t^2*(24960*z - 8144) + t*(2800 - 6160*z) - 1120*z + 96:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(1/162 - z/324) + t^5*(5*z/108 - 1/18) + t^4*(11/54 - 17*z/54) + t^3*(367*z/324 - 73/162) + t^2*(5/9 - 217*z/108) + t*(161*z/108 - 35/108) - 7*z/81 - 29/162)*h0 + (z/2592 - 1/1296)*h1 + (2*t^7/81 - 31*t^6/81 + 64*t^5/27 - 602*t^4/81 + 1979*t^3/162 - 260*t^2/27 + 385*t/162 + 35/81)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_4_16 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_4_17 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/6)*h0
  norm_num at hh

private lemma cell_4_18 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h2 : (2592*t*z:ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (1/648 - z/2592)*h2 + (t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_4_19 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 48) + t^6*(2032*z - 400) + t^5*(4016 - 15312*z) + t^4*(66896*z - 18048) + t^3*(47392 - 175120*z) + t^2*(266784*z - 72032) + t*(57600 - 214208*z) + 68224*z - 18304:ℝ)=0) (h2 : (16*t^8 + t^7*(-128*z - 48) + t^6*(2032*z - 592) + t^5*(4448 - 14160*z) + t^4*(54080*z - 14736) + t^3*(29872 - 116656*z) + t^2*(137040*z - 36176) + t*(21600 - 77984*z) + 15232*z - 4096:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(13/472392 - 7*z/944784) + t^12*(11*z/236196 - 157/944784) + t^11*(23/157464 - 29*z/314928) + t^10*(563*z/944784 + 749/944784) + t^9*(7/472392 - 7651*z/944784) + t^8*(3161*z/52488 - 1667/104976) + t^7*(26527/314928 - 46723*z/157464) + t^6*(330625*z/314928 - 104513/314928) + t^5*(79159/104976 - 273743*z/104976) + t^4*(525871*z/118098 - 190441/236196) + t^3*(262967/236196 - 2530145*z/472392) + t^2*(85267*z/19683 - 82801/39366) + t*(83551/118098 - 95854*z/59049) - 3853*z/59049 + 65539/118098)*h0 + (t^7*(7*z/7558272 - 13/3779136) + t^6*(127/7558272 - 35*z/7558272) + t^5*(1/69984 - z/419904) + t^4*(53*z/1889568 - 1015/7558272) + t^3*(73*z/3779136 + 37/3779136) + t^2*(29/93312 - 95*z/839808) + t*(29*z/944784 - 157/3779136) + 79*z/1889568 - 607/3779136)*h1 + (5/864 - z/648)*h2 + (7*t^14/59049 - 1169*t^13/472392 + 1375*t^12/59049 - 14695*t^11/118098 + 22496*t^10/59049 - 247033*t^9/472392 - 51971*t^8/157464 + 191045*t^7/157464 + 1069771*t^6/157464 - 19867591*t^5/472392 + 27974657*t^4/236196 - 12190157*t^3/59049 + 12673114*t^2/59049 - 6701122*t/59049 + 1219588/59049)*hf
  norm_num at hh

private lemma cell_4_20 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/6)*h0
  norm_num at hh

private lemma cell_4_21 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-10:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/10)*h0
  norm_num at hh

private lemma cell_4_22 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 2)*h0 + (1)*hf
  norm_num at hh

private lemma cell_4_23 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 10*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-128*z - 112) + t^6*(2480*z - 288) + t^5*(5680 - 21072*z) + t^4*(99856*z - 27904) + t^3*(75408 - 278176*z) + t^2*(446592*z - 119312) + t*(100592 - 377072*z) + 127520*z - 34080:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(317/2916 - 85*z/2916) + t^6*(761*z/2916 - 2833/2916) + t^5*(191/81 - 311*z/486) + t^4*(515/729 - 203*z/1458) + t^3*(5465*z/2916 - 22165/2916) + t^2*(1375/324 - 845*z/972) + t*(4873/1458 - 1577*z/1458) + 455*z/729 - 3431/1458)*h0 + (t*(85*z/23328 - 317/23328) - 407*z/23328 + 1519/23328)*h1 + (340*t^8/729 - 5477*t^7/486 + 87515*t^6/729 - 533252*t^5/729 + 148811*t^4/54 - 4724311*t^3/729 + 13363379*t^2/1458 - 3423073*t/486 + 1621895/729)*hf
  norm_num at hh

private lemma cell_4_24 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(2592 - 12960*z) + 75168*z - 18144:ℝ)=0) (h2 : (t*(12960 - 49248*z) + 368064*z - 98496:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (11/15552 - z/5184)*h1 + (11*z/15552 - 41/15552)*h2 + (97*t/3 - 1475/6)*hf
  norm_num at hh

private lemma cell_4_25 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 2)*h0 + (1)*hf
  norm_num at hh

private lemma cell_4_26 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3/8 - z/8)*h0 + (-1/2)*hf
  norm_num at hh

private lemma cell_4_27 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 6) + 2*z + 4:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 192*z) + t^6*(3648*z - 800) + t^5*(9616 - 36720*z) + t^4*(216528*z - 57344) + t^3*(206944 - 772944*z) + t^2*(1629936*z - 436016) + t*(499264 - 1861824*z) + 883776*z - 237248:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(137/23328 - 37*z/23328) + t^6*(29*z/11664 - 11/1458) + t^5*(29/486 - 89*z/3888) + t^4*(371*z/5832 - 247/5832) + t^3*(6505/23328 - 6743*z/23328) + t^2*(113*z/243 + 11/3888) + t*(1453/2916 - 1757*z/2916) + 29*z/2916 + 541/1458)*h0 + (t*(37*z/186624 - 137/186624) - 85*z/186624 + 317/186624)*h1 + (407*t^8/11664 - 9361*t^7/11664 + 103703*t^6/11664 - 346889*t^5/5832 + 2929511*t^4/11664 - 7857901*t^3/11664 + 12939599*t^2/11664 - 745024*t/729 + 1173707/2916)*hf
  norm_num at hh

private lemma cell_4_28 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 432) + t^6*(4592 - 896*z) + t^5*(5424*z - 25360) + t^4*(78960 - 17248*z) + t^3*(29984*z - 140336) + t^2*(137488 - 26976*z) + t*(10768*z - 67056) - 1952*z + 12320:ℝ)=0) : (t + z - 4:ℝ)=0 := by
  have hh : (t + z - 4:ℝ)=0 := by linear_combination (t^6*(11/648 - z/216) + t^5*(65*z/648 - 241/648) + t^4*(1007/324 - 271*z/324) + t^3*(2183*z/648 - 2707/216) + t^2*(16553/648 - 4453*z/648) + t*(1111*z/162 - 8263/324) - 233*z/81 + 851/81)*h0 + (z/1728 - 11/5184)*h1 + (-t^7/27 + 14*t^6/27 - 113*t^5/36 + 539*t^4/54 - 937*t^3/54 + 281*t^2/18 - 673*t/108 + 61/54)*hf
  exact hh

private lemma cell_4_29 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 10*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 496) + t^6*(6240 - 1216*z) + t^5*(9600*z - 41840) + t^4*(163664 - 40640*z) + t^3*(99152*z - 382032) + t^2*(519184 - 138768*z) + t*(102784*z - 375712) - 30976*z + 110976:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(1/324 - z/972) + t^6*(23*z/972 - 25/324) + t^5*(743/972 - 217*z/972) + t^4*(1069*z/972 - 3769/972) + t^3*(5287/486 - 1471*z/486) + t^2*(2255*z/486 - 4121/243) + t*(3340/243 - 595*z/162) + 94*z/81 - 2257/486)*h0 + (t*(z/7776 - 1/2592) - z/7776 + 1/7776)*h1 + (-2*t^8/243 + 40*t^7/243 - 338*t^6/243 + 1570*t^5/243 - 8737*t^4/486 + 7435*t^3/243 - 15097*t^2/486 + 4180*t/243 - 968/243)*hf
  norm_num at hh

private lemma cell_4_30 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 6) + 2*z + 4:ℝ)=0) (h2 : (16*t^8 - 176*t^7 + t^6*(592 - 48*z) + t^5*(432*z - 320) + t^4*(-864*z - 1520) + t^3*(1840 - 1200*z) + t^2*(3024*z + 304) + t*(1728*z - 896) - 480*z + 160:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(77/2916 - 41*z/5832) + t^6*(377*z/5832 - 1417/5832) + t^5*(257/486 - 137*z/972) + t^4*(3127/5832 - 203*z/1458) + t^3*(352*z/729 - 5357/2916) + t^2*(211*z/1944 - 911/1944) + t*(2261/2916 - 559*z/2916) - 71*z/2916 + 571/2916)*h0 + (t*(41*z/46656 - 77/23328) - 59*z/46656 + 113/23328)*h2 + (-41*t^8/2916 + 541*t^7/2916 - 2483*t^6/2916 + 3817*t^5/2916 + 3517*t^4/2916 - 14357*t^3/2916 + 1243*t^2/729 + 4289*t/1458 - 407/729)*hf
  norm_num at hh

private lemma cell_4_31 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 12*t + 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 304) + t^6*(1440*z + 2256) + t^5*(-13296*z - 8112) + t^4*(65088*z + 12816) + t^3*(2160 - 181440*z) + t^2*(285984*z - 36720) + t*(46224 - 233712*z) + 75168*z - 18144:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(5*z/3888 - 1/243) + t^6*(35/432 - 35*z/1296) + t^5*(19*z/81 - 839/1296) + t^4*(1183/432 - 79*z/72) + t^3*(161*z/54 - 179/27) + t^2*(653/72 - 673*z/144) + t*(557*z/144 - 895/144) - 31*z/24 + 11/8)*h0 + (t*(1/1944 - 5*z/31104) + z/1296 - 29/10368)*h1 + (-5*t^8/486 + 91*t^7/324 - 2105*t^6/648 + 373*t^5/18 - 1429*t^4/18 + 6695*t^3/36 - 18593*t^2/72 + 2309*t/12 - 58)*hf
  norm_num at hh

private lemma cell_4_32 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 3/4)*h0 + (-1/2)*hf
  norm_num at hh

private lemma cell_4_33 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(2592 - 12960*z) + 75168*z - 18144:ℝ)=0) (h2 : (t*(2592*z - 7776) - 7776*z + 23328:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7*z/15552 - 13/7776)*h1 + (1/5184)*h2 + (35*t/6 - 203/6)*hf
  norm_num at hh

private lemma cell_4_34 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) : ((0:ℝ):ℝ)=0 := by
  rfl

private lemma cell_4_35 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 4*z:ℝ)=0) (h1 : (16*t^8 + t^7*(80 - 192*z) + t^6*(3264*z - 1040) + t^5*(8528 - 32400*z) + t^4*(206400*z - 54704) + t^3*(227888 - 850272*z) + t^2*(2208384*z - 592400) + t*(885680 - 3304272*z) + 2176512*z - 583232:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(11*z/648 - 41/648) + t^5*(11*z/162 - 83/324) + t^4*(67/648 - 11*z/648) + t^3*(655/648 - 77*z/216) + t^2*(157*z/324 - 101/324) + t*(-533*z/648 - 581/648) + 455*z/324 - 10/27)*h0 + (41/5184 - 11*z/5184)*h1 + (-121*t^7/324 + 1133*t^6/162 - 1243*t^5/18 + 141691*t^4/324 - 291893*t^3/162 + 56189*t^2/12 - 2269711*t/324 + 373633/81)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_4_36 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(12960 - 49248*z) + 368064*z - 98496:ℝ)=0) (h2 : (t*(2592 - 12960*z) + 75168*z - 18144:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (11*z/15552 - 41/15552)*h1 + (11/15552 - z/5184)*h2 + (97*t/3 - 1475/6)*hf
  norm_num at hh

private lemma cell_4_37 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/2 - 2)*h0 + (1)*hf
  norm_num at hh

private lemma cell_4_38 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3/8 - z/8)*h0 + (-1/2)*hf
  norm_num at hh

private lemma cell_4_39 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 6) + 2*z + 4:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 192*z) + t^6*(3840*z - 1184) + t^5*(11056 - 40032*z) + t^4*(257856*z - 68720) + t^3*(279856 - 1047216*z) + t^2*(2609136*z - 699248) + t*(975904 - 3641088*z) + 2176512*z - 583232:ℝ)=0) (h2 : (16*t^8 + t^7*(16 - 192*z) + t^6*(3648*z - 800) + t^5*(9616 - 36720*z) + t^4*(216528*z - 57344) + t^3*(206944 - 772944*z) + t^2*(1629936*z - 436016) + t*(499264 - 1861824*z) + 883776*z - 237248:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(97/1889568 - 13*z/944784) + t^12*(107/1889568 - 7*z/472392) + t^11*(91/629856 - z/19683) + t^10*(161*z/1889568 + 1145/1889568) + t^9*(701/944784 - 6797*z/1889568) + t^8*(7409*z/209952 - 881/104976) + t^7*(41357/629856 - 9913*z/39366) + t^6*(208909*z/157464 - 29371/78732) + t^5*(258727/209952 - 1066859*z/209952) + t^4*(13797907*z/944784 - 1020617/236196) + t^3*(907027/118098 - 27464137*z/944784) + t^2*(12279733*z/314928 - 3071615/314928) + t*(534842/59049 - 3746915*z/118098) + 2673877*z/236196 - 673727/236196)*h0 + (t^7*(13*z/7558272 - 97/15116544) + t^6*(z/15116544 - 5/15116544) + t^5*(11*z/559872 - 121/1679616) + t^4*(127*z/7558272 - 551/7558272) + t^3*(1969*z/15116544 - 1667/3779136) + t^2*(121*z/559872 - 1541/1679616) + t*(161*z/236196 - 2269/944784) + 5569*z/3779136 - 21059/3779136)*h1 + (1/31104)*h2 + (143*t^14/472392 - 3115*t^13/472392 + 17077*t^12/236196 - 484489*t^11/944784 + 1192207*t^10/472392 - 8685217*t^9/944784 + 8274227*t^8/314928 - 19299361*t^7/314928 + 18429901*t^6/157464 - 162984781*t^5/944784 + 113659307*t^4/944784 + 95481803*t^3/236196 - 932877253*t^2/472392 + 468621587*t/118098 - 381454981/118098)*hf
  norm_num at hh

private lemma cell_4_40 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(23328 - 85536*z) + 723168*z - 194400:ℝ)=0) : (t - 2*z - 1:ℝ)=0 := by
  have hh : (t - 2*z - 1:ℝ)=0 := by linear_combination (41/15552 - 11*z/15552)*h1 + (1023/2 - 121*t/2)*hf
  exact hh

private lemma cell_4_41 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4 - 4*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3/8 - z/8)*h0 + (-1/2)*hf
  norm_num at hh

private lemma cell_4_42 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 6*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (11/4 - 3*z/4)*h0 + (-9/2)*hf
  norm_num at hh

private lemma cell_4_43 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 4*z:ℝ)=0) (h1 : (16*t^8 + t^7*(144 - 256*z) + t^6*(5008*z - 1312) + t^5*(15712 - 59136*z) + t^4*(419888*z - 112416) + t^3*(491552 - 1834448*z) + t^2*(4819776*z - 1291856) + t*(1867920 - 6971344*z) + 4258144*z - 1140832:ℝ)=0) : (t - 2*z:ℝ)=0 := by
  have hh : (t - 2*z:ℝ)=0 := by linear_combination (t^6*(71/3888 - 19*z/3888) + t^5*(37/324 - 5*z/162) + t^4*(257/1296 - 7*z/144) + t^3*(407/3888 - 265*z/3888) + t^2*(113*z/648 + 55/648) + t*(433/1296 - 265*z/432) + 737*z/972 - 851/1944)*h0 + (19*z/31104 - 71/31104)*h1 + (133*t^7/972 - 6149*t^6/1944 + 11681*t^5/324 - 498769*t^4/1944 + 2180293*t^3/1944 - 954935*t^2/324 + 8289137*t/1944 - 2531221/972)*hf
  exact hh

private lemma cell_4_44 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 4*z:ℝ)=0) (h1 : (16*t^8 - 304*t^7 + t^6*(336*z + 2224) + t^5*(-4752*z - 7888) + t^4*(34128*z + 11200) + t^3*(14240 - 146640*z) + t^2*(431136*z - 100352) + t*(208928 - 790560*z) + 883776*z - 237248:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(7/1458 - 5*z/3888) + t^6*(203*z/11664 - 379/5832) + t^5*(983/3888 - 263*z/3888) + t^4*(919/11664 - 85*z/3888) + t^3*(1037*z/1458 - 30793/11664) + t^2*(23219/3888 - 3139*z/1944) + t*(304*z/243 - 3307/729) - 737*z/5832 + 1367/5832)*h0 + (t*(5*z/31104 - 7/11664) + z/1944 - 179/93312)*h1 + (-5*t^8/1944 - 41*t^7/2916 + 563*t^6/1458 - 76*t^5/27 + 43897*t^4/5832 + 38*t^3/729 - 83333*t^2/972 + 756241*t/2916 - 662095/1458)*hf
  norm_num at hh

private lemma cell_4_45 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 6) + 2*z + 4:ℝ)=0) (h1 : (16*t^8 - 368*t^7 + t^6*(144*z + 3616) + t^5*(-2448*z - 20048) + t^4*(18864*z + 68416) + t^3*(-83232*z - 144752) + t^2*(223200*z + 176848) + t*(-346320*z - 96560) + 252000*z - 2720:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(13*z/2916 - 97/5832) + t^6*(983/2916 - 527*z/5832) + t^5*(1493*z/1944 - 5569/1944) + t^4*(39169/2916 - 21007*z/5832) + t^3*(58705*z/5832 - 109405/2916) + t^2*(119617/1944 - 32129*z/1944) + t*(10402*z/729 - 38606/729) - 3229*z/729 + 23593/1458)*h0 + (t*(97/46656 - 13*z/23328) + 7*z/23328 - 13/11664)*h1 + (13*t^8/1458 - 319*t^7/2916 + 451*t^6/1458 + 3655*t^5/1458 - 36023*t^4/1458 + 70109*t^3/729 - 578467*t^2/2916 + 301741*t/1458 - 48667/729)*hf
  norm_num at hh

private lemma cell_4_46 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 4*z:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z - 48) + t^6*(544*z - 112) + t^5*(592 - 1680*z) + t^4*(1760*z - 720) + t^3*(1120*z - 16) + t^2*(688 - 3072*z) + t*(1328*z - 528) + 64*z + 128:ℝ)=0) : False := by
  have hh : ((t-(1)))*(1:ℝ)=0 := by linear_combination (t^6*(653/7128 - 175*z/7128) + t^5*(37*z/594 - 23/99) + t^4*(5*z/88 - 505/2376) + t^3*(4349/7128 - 1165*z/7128) + t^2*(59*z/594 - 49/132) + t*(1735/2376 - 157*z/792) - 295*z/1782 + 1963/3564)*h0 + (175*z/57024 - 653/57024)*h2 + (175*t^7/1782 - 1178*t^6/891 + 2033*t^5/396 - 11195*t^4/1782 - 2126*t^3/891 + 1631*t^2/198 - 14059*t/3564 + 415/891)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn0
  norm_num at hv

private lemma cell_4_47 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 6*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-192*z - 48) + t^6*(4416*z - 1008) + t^5*(13392 - 49968*z) + t^4*(337824*z - 90864) + t^3*(378864 - 1411776*z) + t^2*(3563136*z - 955152) + t*(1330992 - 4967568*z) + 2931552*z - 785376:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(13/486 - 7*z/972) + t^6*(5*z/81 - 73/324) + t^5*(40/81 - 25*z/162) + t^4*(7*z/36 - 1/54) + t^3*(-83*z/108 - 17/27) + t^2*(5*z/2 + 11/18) + t*(1/9 - 73*z/18) + 17*z/6 - 4/3)*h0 + (t*(7*z/7776 - 13/3888) - 11*z/2592 + 41/2592)*h1 + (35*t^8/243 - 9*t^7/2 + 10163*t^6/162 - 27781*t^5/54 + 145817*t^4/54 - 165317*t^3/18 + 352115*t^2/18 - 142109*t/6 + 12424)*hf
  norm_num at hh

private lemma cell_4_48 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 176) + t^6*(624 - 192*z) + t^5*(192*z - 960) + 432*t^4 + t^3*(864 - 432*z) - 1296*t^2 + t*(432*z + 432):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(13/324 - 7*z/648) + t^5*(2*z/27 - 5/18) + t^4*(65/108 - 35*z/216) + t^3*(z/8 - 17/36) + t^2*(z/12 - 1/3) + t*(7/8 - z/4) + z/8 - 5/8)*h0 + (7*z/5184 - 13/2592)*h1 + (-7*t^7/81 + 7*t^6/27 - 7*t^5/27 + 7*t^3/12 - 7*t/12)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_4_49 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 240) + t^6*(1568 - 512*z) + t^5*(1680*z - 6064) + t^4*(15552 - 3568*z) + t^3*(6704*z - 27296) + t^2*(31504 - 9552*z) + t*(7168*z - 20928) - 1856*z + 5696:ℝ)=0) : (t + z - 4:ℝ)=0 := by
  have hh : (t + z - 4:ℝ)=0 := by linear_combination (t^6*(11/648 - z/216) + t^5*(29*z/648 - 109/648) + t^4*(535/648 - 143*z/648) + t^3*(431*z/648 - 535/216) + t^2*(767/162 - 413*z/324) + t*(241*z/162 - 454/81) - 157*z/162 + 284/81)*h0 + (z/1728 - 11/5184)*h1 + (-t^7/27 + 8*t^6/27 - 35*t^5/36 + 223*t^4/108 - 419*t^3/108 + 199*t^2/36 - 112*t/27 + 29/27)*hf
  exact hh

private lemma cell_4_50 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 4*z:ℝ)=0) (h2 : (16*t^8 - 304*t^7 + t^6*(2224 - 48*z) + t^5*(720*z - 7888) + t^4*(13792 - 3600*z) + t^3*(6384*z - 9952) + t^2*(-1440*z - 128) + t*(2432 - 1440*z) + 384*z - 512:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(z/324 - 7/648) + t^5*(13/72 - 11*z/216) + t^4*(8*z/27 - 29/27) + t^3*(1711/648 - 455*z/648) + t^2*(14*z/27 - 49/24) + t*(11*z/108 - 14/27) - 11*z/81 + 85/324)*h0 + (7/5184 - z/2592)*h2 + (t^7/162 - 43*t^6/324 + 29*t^5/27 - 1289*t^4/324 + 511*t^3/81 - 131*t^2/54 - 100*t/81 + 56/81)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_4_51 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 64*z) + t^6*(416*z - 288) + t^5*(368 - 1104*z) + t^4*(1552*z + 128) + t^3*(-848*z - 96) + t^2*(-1104*z - 80) + t*(2048*z - 320) - 832*z + 192:ℝ)=0) : False := by
  have hh : ((t-(z)))*(1:ℝ)=0 := by linear_combination (t^6*(1/648 - z/162) + t^5*(5*z/81 - 11/648) + t^4*(41/648 - 77*z/324) + t^3*(287*z/648 - 13/108) + t^2*(43/648 - 185*z/648) + t*(4/81 - 26*z/81) + 17*z/27 - 49/162)*h0 + (z/1296 - 1/5184)*h1 + (4*t^7/81 - 26*t^6/81 + 23*t^5/27 - 97*t^4/81 + 53*t^3/81 + 23*t^2/27 - 128*t/81 + 52/81)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn2
  norm_num at hv

private lemma cell_4_52 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 240) + t^6*(1184 - 320*z) + t^5*(672*z - 2320) + t^4*(720 - 256*z) + t^3*(2608 - 688*z) + t^2*(240*z - 1904) + t*(96 - 320*z) + 64*z + 128:ℝ)=0) : (t + z - 4:ℝ)=0 := by
  have hh : (t + z - 4:ℝ)=0 := by linear_combination (t^6*(17/36 - 41*z/324) + t^5*(407*z/324 - 1519/324) + t^4*(4273/324 - 1145*z/324) + t^3*(124*z/81 - 463/81) + t^2*(365*z/81 - 1363/81) + t*(805/81 - 433*z/162) - 35*z/54 + 185/81)*h0 + (41*z/2592 - 17/288)*h1 + (-82*t^7/81 + 410*t^6/81 - 287*t^5/27 + 328*t^4/81 + 1763*t^3/162 - 205*t^2/54 + 410*t/81 - 82/81)*hf
  exact hh

private lemma cell_4_53 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 10*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(64*z - 304) + t^6*(2256 - 640*z) + t^5*(2544*z - 8720) + t^4*(19280 - 5216*z) + t^3*(5984*z - 24432) + t^2*(16048 - 3840*z) + t*(1264*z - 3856) - 160*z - 288:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(5*z/86022 - 125/43011) + t^6*(9425/172044 - 2047*z/172044) + t^5*(3271*z/28674 - 11507/28674) + t^4*(65290/43011 - 18935*z/43011) + t^3*(74761*z/86022 - 278585/86022) + t^2*(220411/57348 - 53639*z/57348) + t*(45155*z/86022 - 187381/86022) - 5191*z/43011 + 20491/86022)*h0 + (t*(125/344088 - 5*z/688176) + 67*z/1376352 - 2465/1376352)*h1 + (20*t^8/43011 - 334*t^7/43011 + 2135*t^6/43011 - 13913*t^5/86022 + 12791*t^4/43011 - 13729*t^3/43011 + 8435*t^2/43011 - 5393*t/86022 + 335/43011)*hf
  norm_num at hh

private lemma cell_4_54 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 6) + 2*z + 4:ℝ)=0) (h1 : (16*t^8 - 176*t^7 + t^6*(592 - 48*z) + t^5*(432*z - 320) + t^4*(-864*z - 1520) + t^3*(1840 - 1200*z) + t^2*(3024*z + 304) + t*(1728*z - 896) - 480*z + 160:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(77/2916 - 41*z/5832) + t^6*(377*z/5832 - 1417/5832) + t^5*(257/486 - 137*z/972) + t^4*(3127/5832 - 203*z/1458) + t^3*(352*z/729 - 5357/2916) + t^2*(211*z/1944 - 911/1944) + t*(2261/2916 - 559*z/2916) - 71*z/2916 + 571/2916)*h0 + (t*(41*z/46656 - 77/23328) - 59*z/46656 + 113/23328)*h1 + (-41*t^8/2916 + 541*t^7/2916 - 2483*t^6/2916 + 3817*t^5/2916 + 3517*t^4/2916 - 14357*t^3/2916 + 1243*t^2/729 + 4289*t/1458 - 407/729)*hf
  norm_num at hh

private lemma cell_4_55 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 12*t + 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 112) + 864*t^6*z + t^5*(1680 - 4800*z) + t^4*(14400*z - 5040) + t^3*(6768 - 25200*z) + t^2*(24624*z - 5616) + t*(2592 - 10368*z):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(707/45684 - 383*z/91368) + t^6*(989*z/30456 - 3553/30456) + t^5*(4975/30456 - 1715*z/30456) + t^4*(4561/10152 - 68*z/1269) + t^3*(49*z/2538 - 1048/1269) + t^2*(1679*z/3384 - 1933/3384) + t*(433/564 - 23*z/47) + 1/6)*h0 + (t*(383*z/730944 - 707/365472) - 11*z/3807 + 857/81216)*h1 + (383*t^8/11421 - 4855*t^7/7614 + 19079*t^6/3807 - 27175*t^5/1269 + 278225*t^4/5076 - 145031*t^3/1692 + 10798*t^2/141 - 1408*t/47)*hf
  norm_num at hh

private lemma cell_4_56 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 4*z:ℝ)=0) (h1 : (16*t^8 - 112*t^7 + t^6*(144*z + 352) + t^5*(-720*z - 688) + t^4*(3600*z + 352) + t^3*(1136 - 8352*z) + t^2*(21312*z - 5456) + t*(6512 - 22320*z) + 31680*z - 9152:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(2*z/243 - 179/5832) + t^6*(124/729 - 133*z/2916) + t^5*(34*z/243 - 1013/1944) + t^4*(1493/1458 - 535*z/1944) + t^3*(2045*z/5832 - 7547/5832) + t^2*(1321/1944 - 91*z/486) + t*(11*z/972 + 37/1458) + 701*z/2916 - 668/729)*h0 + (t*(179/46656 - z/972) + 13*z/15552 - 145/46656)*h1 + (4*t^8/243 + 35*t^7/1458 - 1163*t^6/2916 + 1553*t^5/486 - 7144*t^4/729 + 19778*t^3/729 - 6481*t^2/162 + 150715*t/2916 - 20006/729)*hf
  norm_num at hh

private lemma cell_4_57 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 6) + 2*z + 4:ℝ)=0) (h1 : (16*t^8 - 176*t^7 + t^6*(1168 - 48*z) + t^5*(432*z - 5072) + t^4*(16192 - 2160*z) + t^3*(6576*z - 36896) + t^2*(62080 - 13824*z) + t*(17280*z - 66560) - 13440*z + 44800:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(79/416988 - 71*z/416988) + t^6*(3023*z/1667952 - 3847/1667952) + t^5*(8123/555984 - 5617*z/555984) + t^4*(60649*z/1667952 - 104135/1667952) + t^3*(308543/1667952 - 151183*z/1667952) + t^2*(5548*z/34749 - 28183/69498) + t*(60487/104247 - 19124*z/104247) + 15713*z/104247 - 130211/208494)*h0 + (t*(71*z/3335904 - 79/3335904) - 1571*z/13343616 + 1603/13343616)*h1 + (-71*t^8/208494 + 4159*t^7/833976 - 32255*t^6/833976 + 14387*t^5/75816 - 540641*t^4/833976 + 163568*t^3/104247 - 279544*t^2/104247 + 311579*t/104247 - 196381/104247)*hf
  norm_num at hh

private lemma cell_4_58 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 4*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 48) + t^6*(544*z - 112) + t^5*(592 - 1680*z) + t^4*(1760*z - 720) + t^3*(1120*z - 16) + t^2*(688 - 3072*z) + t*(1328*z - 528) + 64*z + 128:ℝ)=0) : False := by
  have hh : ((t-(1)))*(1:ℝ)=0 := by linear_combination (t^6*(653/7128 - 175*z/7128) + t^5*(37*z/594 - 23/99) + t^4*(5*z/88 - 505/2376) + t^3*(4349/7128 - 1165*z/7128) + t^2*(59*z/594 - 49/132) + t*(1735/2376 - 157*z/792) - 295*z/1782 + 1963/3564)*h0 + (175*z/57024 - 653/57024)*h1 + (175*t^7/1782 - 1178*t^6/891 + 2033*t^5/396 - 11195*t^4/1782 - 2126*t^3/891 + 1631*t^2/198 - 14059*t/3564 + 415/891)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn0
  norm_num at hv

private lemma cell_4_59 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 6*z:ℝ)=0) (h1 : (16*t^8 + t^7*(144 - 192*z) + t^6*(2496*z - 576) + t^5*(5616 - 21456*z) + t^4*(111888*z - 29952) + t^3*(97632 - 364176*z) + t^2*(721872*z - 193968) + t*(212544 - 793152*z) + 368064*z - 98496:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(3493/44712 - 935*z/44712) + t^6*(2389/4968 - 1931*z/14904) + t^5*(9337/14904 - 2351*z/14904) + t^4*(139*z/4968 - 1987/4968) + t^3*(1009*z/2484 - 341/2484) + t^2*(47/92 - 967*z/828) + t*(503*z/207 - 640/207) - 125*z/138 - 47/69)*h0 + (t*(935*z/357696 - 3493/357696) - 337*z/59616 + 631/29808)*h1 + (4675*t^8/11178 - 59635*t^7/7452 + 131045*t^6/1863 - 256286*t^5/621 + 984832*t^4/621 - 1090939*t^3/276 + 1277318*t^2/207 - 125669*t/23 + 47979/23)*hf
  norm_num at hh

private lemma cell_4_60 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(128*z - 368) + t^6*(2976 - 784*z) + t^5*(3216*z - 12592) + t^4*(29312 - 7856*z) + t^3*(9856*z - 36624) + t^2*(22384 - 6720*z) + t*(2384*z - 4880) - 160*z - 288:ℝ)=0) : (t + z - 4:ℝ)=0 := by
  have hh : (t + z - 4:ℝ)=0 := by linear_combination (t^6*(5*z/324 - 14/243) + t^5*(236/243 - 253*z/972) + t^4*(1567*z/972 - 5849/972) + t^3*(16717/972 - 1120*z/243) + t^2*(6029*z/972 - 11255/486) + t*(12187/972 - 3275*z/972) + 44*z/243 - 131/162)*h0 + (7/972 - 5*z/2592)*h1 + (20*t^7/81 - 245*t^6/162 + 335*t^5/54 - 2455*t^4/162 + 1540*t^3/81 - 350*t^2/27 + 745*t/162 - 25/81)*hf
  exact hh

private lemma cell_4_61 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 12*t + 6:ℝ)=0) (h1 : (16*t^8 + t^7*(128*z - 496) + t^6*(5952 - 1680*z) + t^5*(10320*z - 38064) + t^4*(143136 - 37872*z) + t^3*(85824*z - 323280) + t^2*(426384 - 114912*z) + t*(81648*z - 299376) - 23328*z + 85536:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(173*z/89424 - 223/89424) + t^6*(727/14904 - 103*z/7452) + t^5*(2627*z/29808 - 12649/29808) + t^4*(19129/9936 - 1637*z/3312) + t^3*(6985*z/4968 - 23213/4968) + t^2*(19063/3312 - 5609*z/3312) + t*(271*z/552 - 397/138) + 25*z/92 - 2/69)*h0 + (t*(223/715392 - 173*z/715392) + 221*z/238464 - 19/79488)*h1 + (173*t^8/5589 - 7823*t^7/14904 + 7550*t^6/1863 - 46507*t^5/2484 + 277477*t^4/4968 - 88867*t^3/828 + 69685*t^2/552 - 14961*t/184 + 1989/92)*hf
  norm_num at hh

private lemma cell_4_62 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 6*z:ℝ)=0) (h1 : (16*t^8 - 240*t^7 + t^6*(1344 - 48*z) + t^5*(576*z - 3456) + t^4*(3744 - 2160*z) + 2160*t^3*z + t^2*(1728*z - 3024) + t*(1296 - 1296*z):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(3953/45684 - 1057*z/45684) + t^6*(1258*z/3807 - 18817/15228) + t^5*(24188/3807 - 25885*z/15228) + t^4*(6269*z/1692 - 70195/5076) + t^3*(23819/2538 - 12833*z/5076) + t^2*(3913/564 - 784*z/423) + t*(4331*z/1692 - 16051/1692) - z/6 + 2/3)*h0 + (t*(1057*z/365472 - 3953/365472) - 635*z/121824 + 299/15228)*h1 + (-1057*t^8/11421 + 6089*t^7/3807 - 81455*t^6/7614 + 43487*t^5/1269 - 126517*t^4/2538 + 5929*t^3/423 + 28861*t^2/846 - 3212*t/141 + 1)*hf
  norm_num at hh

private lemma cell_4_63 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 6*t:ℝ)=0) (h1 : (-192*t + 64*z + 128:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/12 - 5/12)*h0 + (5/384 - z/384)*h1 + (1/6)*hf
  norm_num at hh

private lemma pair_4_10_13 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t + z - 4:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z - 176) + t^6*(992*z + 624) + t^5*(-6144*z - 352) + t^4*(19264*z - 2992) + t^3*(8064 - 31664*z) + t^2*(24960*z - 8144) + t*(2800 - 6160*z) - 1120*z + 96:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7/324 + t^6*(-5*z/324 - 7/324) + t^5*(23*z/108 + 1/54) + t^4*(71/324 - 65*z/54) + t^3*(1133*z/324 - 293/324) + t^2*(155/108 - 281*z/54) + t*(365*z/108 - 335/324) - 25*z/162 - 35/162)*h1 + (-1/5184)*h2 + (5*t^6/324 - 23*t^5/108 + 65*t^4/54 - 1133*t^3/324 + 281*t^2/54 - 365*t/108 + 25/162)*hf
  norm_num at hh

private lemma pair_4_28_52 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t + z - 4:ℝ)=0) (h2 : (1296*t^8 - 22032*t^7 + t^6*(156816 - 1296*z) + t^5*(16848*z - 607824) + t^4*(1397088 - 84240*z) + t^3*(203472*z - 1941408) + t^2*(1586304 - 246240*z) + t*(142560*z - 694656) - 31104*z + 124416:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7/4 + t^6*(-z/4 - 13/4) + t^5*(3*z + 17) + t^4*(-55*z/4 - 185/4) + t^3*(30*z + 283/4) + t^2*(-63*z/2 - 123/2) + t*(14*z + 57/2) - z - 6)*h0 + (-1/5184)*h2 + (t^6/4 - 3*t^5 + 55*t^4/4 - 30*t^3 + 63*t^2/2 - 14*t + 1)*hf
  norm_num at hh

private lemma pair_4_34_49 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t + z - 4:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z - 176) + t^6*(992*z + 624) + t^5*(-6144*z - 352) + t^4*(19264*z - 2992) + t^3*(8064 - 31664*z) + t^2*(24960*z - 8144) + t*(2800 - 6160*z) - 1120*z + 96:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7/324 + t^6*(-5*z/324 - 7/324) + t^5*(23*z/108 + 1/54) + t^4*(71/324 - 65*z/54) + t^3*(1133*z/324 - 293/324) + t^2*(155/108 - 281*z/54) + t*(365*z/108 - 335/324) - 25*z/162 - 35/162)*h1 + (-1/5184)*h2 + (5*t^6/324 - 23*t^5/108 + 65*t^4/54 - 1133*t^3/324 + 281*t^2/54 - 365*t/108 + 25/162)*hf
  norm_num at hh

private lemma pair_4_40_43 (z t : ℝ) (_hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z - 1:ℝ)=0) (h1 : (t - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1)*h0 + (1)*h1
  norm_num at hh

private lemma pair_4_40_60 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z - 1:ℝ)=0) (h1 : (t + z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/2 - z/6)*h0 + (z/6 - 1/2)*h1 + (-1/2)*hf
  norm_num at hh

private lemma pair_4_43_60 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z:ℝ)=0) (h1 : (t + z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (8/23 - 3*z/23)*h0 + (3*z/23 - 8/23)*h1 + (-9/23)*hf
  norm_num at hh

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_0 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 0) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_0 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_1 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 1) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_1 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_2 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 2) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_2 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_3 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 3) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_3 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z + 16*t^7 + 448*t^6*z^2 - 208*t^6*z - 128*t^6 - 896*t^5*z^3 + 912*t^5*z^2 + 624*t^5*z - 32*t^5 + 1120*t^4*z^4 - 2000*t^4*z^3 - 1056*t^4*z^2 + 736*t^4*z + 256*t^4 - 896*t^3*z^5 + 2480*t^3*z^4 + 544*t^3*z^3 - 2336*t^3*z^2 - 832*t^3*z - 32*t^3 + 448*t^2*z^6 - 1776*t^2*z^5 + 384*t^2*z^4 + 2912*t^2*z^3 + 96*t^2*z^2 - 624*t^2*z + 16*t^2 - 128*t*z^7 + 688*t*z^6 - 528*t*z^5 - 1600*t*z^4 + 1280*t*z^3 + 336*t*z^2 + 1120*t*z - 272*t + 16*z^8 - 112*z^7 + 160*z^6 + 320*z^5 - 800*z^4 + 320*z^3 + 304*z^2 - 688*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 2672*t^5 - 1120*t^4*z^2 - 2480*t^4*z - 7744*t^4 + 896*t^3*z^3 + 1104*t^3*z^2 + 2976*t^3*z + 13136*t^3 - 448*t^2*z^4 - 16*t^2*z^3 - 2896*t^2*z - 11680*t^2 + 128*t*z^5 - 176*t*z^4 - 304*t*z^3 + 560*t*z^2 + 1264*t*z + 4160*t - 16*z^6 + 48*z^5 + 48*z^4 - 176*z^3 + 48*z^2 + 48*z - 160)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_4 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 4) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_4 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_5 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 5) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_5 z t hf hn0 hn1 hn2 hn3
  · have hr : (-6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_6 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 6) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_6 z t hf hn0 hn1 hn2 hn3
  · have hr : (2592*t*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_7 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 7) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_7 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 448*t^6*z^2 + 240*t^6*z - 144*t^6 - 896*t^5*z^3 - 432*t^5*z^2 + 1008*t^5*z + 432*t^5 + 1120*t^4*z^4 + 240*t^4*z^3 - 2736*t^4*z^2 - 1296*t^4*z + 288*t^4 - 896*t^3*z^5 + 240*t^3*z^4 + 3744*t^3*z^3 + 864*t^3*z^2 - 2448*t^3*z - 864*t^3 + 448*t^2*z^6 - 432*t^2*z^5 - 2736*t^2*z^4 + 864*t^2*z^3 + 4320*t^2*z^2 + 864*t^2*z - 128*t*z^7 + 240*t*z^6 + 1008*t*z^5 - 1296*t*z^4 - 2448*t*z^3 + 864*t*z^2 + 2592*t*z + 16*z^8 - 48*z^7 - 144*z^6 + 432*z^5 + 288*z^4 - 864*z^3:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 4016*t^5 - 1120*t^4*z^2 - 4720*t^4*z - 15024*t^4 + 896*t^3*z^3 + 3344*t^3*z^2 + 8736*t^3*z + 30736*t^3 - 448*t^2*z^4 - 1360*t^2*z^3 - 2256*t^2*z^2 - 8528*t^2*z - 36176*t^2 + 128*t*z^5 + 272*t*z^4 - 48*t*z^3 + 832*t*z^2 + 5824*t*z + 21600*t - 16*z^6 - 16*z^5 + 96*z^4 - 32*z^3 - 512*z^2 - 1152*z - 4096)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_8 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 8) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_8 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_9 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 9) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_9 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^6 + 16848*t*z^5 - 84240*t*z^4 + 203472*t*z^3 - 246240*t*z^2 + 142560*t*z - 31104*t + 1296*z^8 - 22032*z^7 + 156816*z^6 - 607824*z^5 + 1397088*z^4 - 1941408*z^3 + 1586304*z^2 - 694656*z + 124416:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^4 - 11664*t*z^3 + 36288*t*z^2 - 46656*t*z + 23328*t - 1296*z^6 + 16848*z^5 - 88128*z^4 + 238464*z^3 - 355104*z^2 + 282528*z - 101088)*hf
  · have hr : (-1296*t*z^6 + 12960*t*z^5 - 50544*t*z^4 + 97200*t*z^3 - 95904*t*z^2 + 45360*t*z - 7776*t + 1296*z^8 - 16848*z^7 + 93312*z^6 - 287712*z^5 + 539136*z^4 - 624672*z^3 + 431568*z^2 - 159408*z + 23328:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^4 - 7776*t*z^3 + 18144*t*z^2 - 16848*t*z + 10368*t - 1296*z^6 + 11664*z^5 - 45360*z^4 + 94608*z^3 - 115344*z^2 + 68688*z - 41472)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_10 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (_hc : cell (1) (1) (1) (profile4 (2) (z) t 10) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : ((0:ℝ):ℝ)=0 := by
  apply cell_4_10 z t hf hn0 hn1 hn2 hn3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_11 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 11) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_11 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 192*t^7*z + 80*t^7 + 1056*t^6*z^2 - 1152*t^6*z + 208*t^6 - 3456*t^5*z^3 + 6768*t^5*z^2 - 3168*t^5*z + 464*t^5 + 7344*t^4*z^4 - 22032*t^4*z^3 + 19296*t^4*z^2 - 6288*t^4*z + 736*t^4 - 10368*t^3*z^5 + 43632*t^3*z^4 - 60480*t^3*z^3 + 34512*t^3*z^2 - 9360*t^3*z + 992*t^3 + 9504*t^2*z^6 - 53136*t^2*z^5 + 106272*t^2*z^4 - 95472*t^2*z^3 + 42192*t^2*z^2 - 8352*t^2*z + 448*t^2 - 5184*t*z^7 + 37152*t*z^6 - 101088*t*z^5 + 131760*t*z^4 - 86832*t*z^3 + 27936*t*z^2 - 2208*t*z - 640*t + 1296*z^8 - 11664*z^7 + 41904*z^6 - 76464*z^5 + 73440*z^4 - 31968*z^3 + 192*z^2 + 3456*z - 512:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6 + 3456*t^5*z + 7056*t^5 - 7344*t^4*z^2 - 7344*t^4*z - 41328*t^4 + 10368*t^3*z^3 - 2160*t^3*z^2 + 41472*t^3*z + 133536*t^3 - 9504*t^2*z^4 + 15120*t^2*z^3 - 36288*t^2*z^2 - 64800*t^2*z - 265104*t^2 + 5184*t*z^5 - 16416*t*z^4 + 30240*t*z^3 + 5616*t*z^2 + 79056*t*z + 282672*t - 1296*z^6 + 6480*z^5 - 14688*z^4 + 11232*z^3 - 13824*z^2 - 34560*z - 124608)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_12 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 12) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_12 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 176*t^7 + 160*t^6*z^2 - 832*t^6*z + 784*t^6 + 256*t^5*z^3 - 1968*t^5*z^2 + 4224*t^5*z - 1904*t^5 + 304*t^4*z^4 - 3056*t^4*z^3 + 9888*t^4*z^2 - 10736*t^4*z + 2656*t^4 + 256*t^3*z^5 - 3184*t^3*z^4 + 13984*t^3*z^3 - 24944*t^3*z^2 + 14384*t^3*z - 1568*t^3 + 160*t^2*z^6 - 2352*t^2*z^5 + 12768*t^2*z^4 - 30928*t^2*z^3 + 31056*t^2*z^2 - 8544*t^2*z - 704*t^2 + 64*t*z^7 - 1088*t*z^6 + 7104*t*z^5 - 22096*t*z^4 + 31856*t*z^3 - 15360*t*z^2 - 992*t*z + 1408*t + 16*z^8 - 304*z^7 + 2224*z^6 - 7888*z^5 + 13792*z^4 - 9952*z^3 - 128*z^2 + 2432*z - 512:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 944*t^5 - 304*t^4*z^2 + 1840*t^4*z - 2224*t^4 - 256*t^3*z^3 + 2160*t^3*z^2 - 5088*t^3*z + 2432*t^3 - 160*t^2*z^4 + 1712*t^2*z^3 - 5760*t^2*z^2 + 6176*t^2*z - 592*t^2 - 64*t*z^5 + 832*t*z^4 - 3712*t*z^3 + 6416*t*z^2 - 2480*t*z - 976*t - 16*z^6 + 240*z^5 - 1248*z^4 + 2656*z^3 - 1920*z^2 - 384*z + 512)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_13 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 13) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : (t + z - 4:ℝ)=0 := by
  apply cell_4_13 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 432*t^7 + 160*t^6*z^2 - 1728*t^6*z + 4944*t^6 + 256*t^5*z^3 - 3888*t^5*z^2 + 19296*t^5*z - 31536*t^5 + 304*t^4*z^4 - 5616*t^4*z^3 + 38592*t^4*z^2 - 115344*t^4*z + 122976*t^4 + 256*t^3*z^5 - 5616*t^3*z^4 + 48000*t^3*z^3 - 199152*t^3*z^2 + 398448*t^3*z - 299808*t^3 + 160*t^2*z^6 - 3888*t^2*z^5 + 38592*t^2*z^4 - 199152*t^2*z^3 + 557712*t^2*z^2 - 794016*t^2*z + 444096*t^2 + 64*t*z^7 - 1728*t*z^6 + 19296*t*z^5 - 115344*t*z^4 + 398448*t*z^3 - 794016*t*z^2 + 840672*t*z - 362880*t + 16*z^8 - 432*z^7 + 4944*z^6 - 31536*z^5 + 122976*z^4 - 299808*z^3 + 444096*z^2 - 362880*z + 124416:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 2864*t^5 - 304*t^4*z^2 + 4400*t^4*z - 20688*t^4 - 256*t^3*z^3 + 4592*t^3*z^2 - 29376*t^3*z + 77056*t^3 - 160*t^2*z^4 + 3248*t^2*z^3 - 25440*t^2*z^2 + 94144*t^2*z - 155696*t^2 - 64*t*z^5 + 1472*t*z^4 - 13344*t*z^3 + 60496*t*z^2 - 143120*t*z + 161040*t - 16*z^6 + 368*z^5 - 3456*z^4 + 17344*z^3 - 50144*z^2 + 81888*z - 66400)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_14 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 14) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_14 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 304*t^7 - 48*t^6*z + 2224*t^6 + 720*t^5*z - 7888*t^5 - 3600*t^4*z + 13792*t^4 + 6384*t^3*z - 9952*t^3 - 1440*t^2*z - 128*t^2 - 1440*t*z + 2432*t + 384*z - 512:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_15 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 15) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_15 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z - 176*t^7 + 160*t^6*z^2 + 352*t^6*z + 784*t^6 - 256*t^5*z^3 - 528*t^5*z^2 - 192*t^5*z - 1904*t^5 + 304*t^4*z^4 + 176*t^4*z^3 + 384*t^4*z^2 - 1936*t^4*z + 2656*t^4 - 256*t^3*z^5 + 176*t^3*z^4 + 992*t^3*z^3 - 1904*t^3*z^2 + 4720*t^3*z - 1568*t^3 + 160*t^2*z^6 - 528*t^2*z^5 + 384*t^2*z^4 - 1904*t^2*z^3 + 5424*t^2*z^2 - 4128*t^2*z - 704*t^2 - 64*t*z^7 + 352*t*z^6 - 192*t*z^5 - 1936*t*z^4 + 4720*t*z^3 - 4128*t*z^2 - 160*t*z + 1408*t + 16*z^8 - 176*z^7 + 784*z^6 - 1904*z^5 + 2656*z^4 - 1568*z^3 - 704*z^2 + 1408*z - 512:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 1552*t^5 - 304*t^4*z^2 - 1392*t^4*z - 5648*t^4 + 256*t^3*z^3 + 848*t^3*z^2 + 2144*t^3*z + 9632*t^3 - 160*t^2*z^4 - 112*t^2*z^3 - 672*t^2*z^2 - 672*t^2*z - 7440*t^2 + 64*t*z^5 - 96*t*z^4 - 256*t*z^3 + 1008*t*z^2 - 432*t*z + 1392*t - 16*z^6 + 112*z^5 - 320*z^4 + 512*z^3 - 288*z^2 - 96*z + 608)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_16 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 16) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_16 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_17 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 17) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_17 z t hf hn0 hn1 hn2 hn3
  · have hr : (-6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_18 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 18) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_18 z t hf hn0 hn1 hn2 hn3
  · have hr : (2592*t*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_19 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 19) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_19 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 448*t^6*z^2 + 240*t^6*z + 48*t^6 - 896*t^5*z^3 - 432*t^5*z^2 - 144*t^5*z + 1120*t^4*z^4 + 240*t^4*z^3 + 144*t^4*z^2 - 144*t^4 - 896*t^3*z^5 + 240*t^3*z^4 - 96*t^3*z^3 + 144*t^3*z + 432*t^3 + 448*t^2*z^6 - 432*t^2*z^5 + 144*t^2*z^4 - 432*t^2*z - 432*t^2 - 128*t*z^7 + 240*t*z^6 - 144*t*z^5 + 144*t*z^3 - 432*t*z^2 + 864*t*z + 16*z^8 - 48*z^7 + 48*z^6 - 144*z^4 + 432*z^3 - 432*z^2:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 4016*t^5 - 1120*t^4*z^2 - 4720*t^4*z - 17904*t^4 + 896*t^3*z^3 + 3344*t^3*z^2 + 12576*t^3*z + 46960*t^3 - 448*t^2*z^4 - 1360*t^2*z^3 - 5136*t^2*z^2 - 19184*t^2*z - 71600*t^2 + 128*t*z^5 + 272*t*z^4 + 1104*t*z^3 + 4144*t*z^2 + 15328*t*z + 57600*t - 16*z^6 - 16*z^5 - 96*z^4 - 368*z^3 - 1232*z^2 - 4992*z - 18304)*hf
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 448*t^6*z^2 + 240*t^6*z - 144*t^6 - 896*t^5*z^3 - 432*t^5*z^2 + 1008*t^5*z + 432*t^5 + 1120*t^4*z^4 + 240*t^4*z^3 - 2736*t^4*z^2 - 1296*t^4*z + 288*t^4 - 896*t^3*z^5 + 240*t^3*z^4 + 3744*t^3*z^3 + 864*t^3*z^2 - 2448*t^3*z - 864*t^3 + 448*t^2*z^6 - 432*t^2*z^5 - 2736*t^2*z^4 + 864*t^2*z^3 + 4320*t^2*z^2 + 864*t^2*z - 128*t*z^7 + 240*t*z^6 + 1008*t*z^5 - 1296*t*z^4 - 2448*t*z^3 + 864*t*z^2 + 2592*t*z + 16*z^8 - 48*z^7 - 144*z^6 + 432*z^5 + 288*z^4 - 864*z^3:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 4016*t^5 - 1120*t^4*z^2 - 4720*t^4*z - 15024*t^4 + 896*t^3*z^3 + 3344*t^3*z^2 + 8736*t^3*z + 30736*t^3 - 448*t^2*z^4 - 1360*t^2*z^3 - 2256*t^2*z^2 - 8528*t^2*z - 36176*t^2 + 128*t*z^5 + 272*t*z^4 - 48*t*z^3 + 832*t*z^2 + 5824*t*z + 21600*t - 16*z^6 - 16*z^5 + 96*z^4 - 32*z^3 - 512*z^2 - 1152*z - 4096)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_20 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 20) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_20 z t hf hn0 hn1 hn2 hn3
  · have hr : (-6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_21 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 21) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_21 z t hf hn0 hn1 hn2 hn3
  · have hr : (-10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_22 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 22) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_22 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 10*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_23 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 23) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_23 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 10*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z - 112*t^7 + 448*t^6*z^2 + 688*t^6*z + 160*t^6 - 896*t^5*z^3 - 1776*t^5*z^2 - 528*t^5*z + 320*t^5 + 1120*t^4*z^4 + 2480*t^4*z^3 + 384*t^4*z^2 - 1600*t^4*z - 800*t^4 - 896*t^3*z^5 - 2000*t^3*z^4 + 544*t^3*z^3 + 2912*t^3*z^2 + 1280*t^3*z + 320*t^3 + 448*t^2*z^6 + 912*t^2*z^5 - 1056*t^2*z^4 - 2336*t^2*z^3 + 96*t^2*z^2 + 336*t^2*z + 304*t^2 - 128*t*z^7 - 208*t*z^6 + 624*t*z^5 + 736*t*z^4 - 832*t*z^3 - 624*t*z^2 + 1120*t*z - 688*t + 16*z^8 + 16*z^7 - 128*z^6 - 32*z^5 + 256*z^4 - 32*z^3 + 16*z^2 - 272*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 5360*t^5 - 1120*t^4*z^2 - 6960*t^4*z - 27104*t^4 + 896*t^3*z^3 + 5584*t^3*z^2 + 20896*t^3*z + 75088*t^3 - 448*t^2*z^4 - 2704*t^2*z^3 - 9312*t^2*z^2 - 32208*t^2*z - 119616*t^2 + 128*t*z^5 + 720*t*z^4 + 2128*t*z^3 + 7056*t*z^2 + 26928*t*z + 101280*t - 16*z^6 - 80*z^5 - 176*z^4 - 592*z^3 - 2448*z^2 - 9168*z - 34240)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_24 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 24) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_24 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^6 + 12960*t*z^5 - 50544*t*z^4 + 97200*t*z^3 - 95904*t*z^2 + 45360*t*z - 7776*t + 1296*z^8 - 16848*z^7 + 93312*z^6 - 287712*z^5 + 539136*z^4 - 624672*z^3 + 431568*z^2 - 159408*z + 23328:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^4 - 7776*t*z^3 + 18144*t*z^2 - 16848*t*z + 10368*t - 1296*z^6 + 11664*z^5 - 45360*z^4 + 94608*z^3 - 115344*z^2 + 68688*z - 41472)*hf
  · have hr : (-1296*t*z^6 + 9072*t*z^5 - 20736*t*z^4 + 14256*t*z^3 + 3888*t*z^2 - 2592*t*z + 1296*z^8 - 11664*z^7 + 40176*z^6 - 64800*z^5 + 45360*z^4 - 3888*z^3 - 9072*z^2 + 2592*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^4 - 3888*t*z^3 + 3888*t*z^2 + 5184*t*z + 12960*t - 1296*z^6 + 6480*z^5 - 12960*z^4 + 6480*z^3 - 6480*z^2 - 28512*z - 98496)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_25 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 25) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_25 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 10*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_26 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 26) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_26 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 12*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_27 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 27) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_27 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 6*t + 2*z^2 - 6*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 192*t^7*z + 16*t^7 + 1056*t^6*z^2 - 576*t^6*z + 256*t^6 - 3456*t^5*z^3 + 4464*t^5*z^2 - 2736*t^5*z + 256*t^5 + 7344*t^4*z^4 - 16848*t^4*z^3 + 16272*t^4*z^2 - 7104*t^4*z + 1696*t^4 - 10368*t^3*z^5 + 36720*t^3*z^4 - 54000*t^3*z^3 + 40656*t^3*z^2 - 14976*t^3*z + 1792*t^3 + 9504*t^2*z^6 - 47952*t^2*z^5 + 102384*t^2*z^4 - 118800*t^2*z^3 + 79344*t^2*z^2 - 30096*t^2*z + 4912*t^2 - 5184*t*z^7 + 35424*t*z^6 - 104976*t*z^5 + 174096*t*z^4 - 171504*t*z^3 + 97344*t*z^2 - 28128*t*z + 3472*t + 1296*z^8 - 11664*z^7 + 47088*z^6 - 111456*z^5 + 168048*z^4 - 162864*z^3 + 96528*z^2 - 30240*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6 + 3456*t^5*z + 9360*t^5 - 7344*t^4*z^2 - 12528*t^4*z - 59040*t^4 + 10368*t^3*z^3 + 4752*t^3*z^2 + 62640*t^3*z + 205152*t^3 - 9504*t^2*z^4 + 9936*t^2*z^3 - 53136*t^2*z^2 - 103680*t^2*z - 440928*t^2 + 5184*t*z^5 - 14688*t*z^4 + 41040*t*z^3 + 4752*t*z^2 + 149472*t*z + 495792*t - 1296*z^6 + 6480*z^5 - 19872*z^4 + 25488*z^3 - 46224*z^2 - 47520*z - 240384)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_28 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 28) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : (t + z - 4:ℝ)=0 := by
  apply cell_4_28 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 432*t^7 + 160*t^6*z^2 - 1536*t^6*z + 4752*t^6 + 256*t^5*z^3 - 3312*t^5*z^2 + 14832*t^5*z - 27648*t^5 + 304*t^4*z^4 - 4464*t^4*z^3 + 26640*t^4*z^2 - 73872*t^4*z + 92304*t^4 + 256*t^3*z^5 - 4272*t^3*z^4 + 28944*t^3*z^3 - 104976*t^3*z^2 + 201456*t^3*z - 179280*t^3 + 160*t^2*z^6 - 2736*t^2*z^5 + 20592*t^2*z^4 - 85104*t^2*z^3 + 209520*t^2*z^2 - 294624*t^2*z + 195696*t^2 + 64*t*z^7 - 1152*t*z^6 + 8784*t*z^5 - 38880*t*z^4 + 109440*t*z^3 - 197424*t*z^2 + 212544*t*z - 108864*t + 16*z^8 - 240*z^7 + 1728*z^6 - 7776*z^5 + 23616*z^4 - 49248*z^3 + 68688*z^2 - 58320*z + 23328:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 2288*t^5 - 304*t^4*z^2 + 3248*t^4*z - 13344*t^4 - 256*t^3*z^3 + 3248*t^3*z^2 - 15696*t^3*z + 38944*t^3 - 160*t^2*z^4 + 2096*t^2*z^3 - 12048*t^2*z^2 + 34816*t^2*z - 58208*t^2 - 64*t*z^5 + 896*t*z^4 - 5136*t*z^3 + 17440*t*z^2 - 34544*t*z + 41808*t - 16*z^6 + 176*z^5 - 1008*z^4 + 3568*z^3 - 8336*z^2 + 12336*z - 11008)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_29 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 29) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_29 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 10*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 496*t^7 + 160*t^6*z^2 - 1856*t^6*z + 6400*t^6 + 256*t^5*z^3 - 4080*t^5*z^2 + 22080*t^5*z - 44896*t^5 + 304*t^4*z^4 - 5680*t^4*z^3 + 41568*t^4*z^2 - 138736*t^4*z + 187072*t^4 + 256*t^3*z^5 - 5552*t^3*z^4 + 48256*t^3*z^3 - 215104*t^3*z^2 + 493136*t^3*z - 473056*t^3 + 160*t^2*z^6 - 3696*t^2*z^5 + 36384*t^2*z^4 - 193568*t^2*z^3 + 589632*t^2*z^2 - 983616*t^2*z + 706768*t^2 + 64*t*z^7 - 1600*t*z^6 + 16896*t*z^5 - 99728*t*z^4 + 360080*t*z^3 - 799680*t*z^2 + 1015504*t*z - 569296*t + 16*z^8 - 368*z^7 + 3808*z^6 - 23360*z^5 + 92896*z^4 - 244928*z^3 + 417328*z^2 - 419120*z + 189280:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 3056*t^5 - 304*t^4*z^2 + 4464*t^4*z - 23408*t^4 - 256*t^3*z^3 + 4528*t^3*z^2 - 29888*t^3*z + 91024*t^3 - 160*t^2*z^4 + 3056*t^2*z^3 - 24000*t^2*z^2 + 94512*t^2*z - 187584*t^2 - 64*t*z^5 + 1344*t*z^4 - 11456*t*z^3 + 52560*t*z^2 - 138384*t*z + 193584*t - 16*z^6 + 304*z^5 - 2576*z^4 + 12752*z^3 - 39312*z^2 + 74928*z - 78304)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_30 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 30) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_30 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 6*t + 2*z^2 - 6*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 176*t^7 - 48*t^6*z + 592*t^6 + 432*t^5*z - 320*t^5 - 864*t^4*z - 1520*t^4 - 1200*t^3*z + 1840*t^3 + 3024*t^2*z + 304*t^2 + 1728*t*z - 896*t - 480*z + 160:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_31 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 31) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_31 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 12*t + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z - 304*t^7 + 160*t^6*z^2 + 800*t^6*z + 2416*t^6 - 256*t^5*z^3 - 1488*t^5*z^2 - 3504*t^5*z - 10624*t^5 + 304*t^4*z^4 + 1456*t^4*z^3 + 5136*t^4*z^2 + 5680*t^4*z + 28336*t^4 - 256*t^3*z^5 - 1040*t^3*z^4 - 1936*t^3*z^3 - 10768*t^3*z^2 + 2416*t^3*z - 46288*t^3 + 160*t^2*z^6 + 240*t^2*z^5 + 1392*t^2*z^4 - 1552*t^2*z^3 + 18960*t^2*z^2 - 19488*t^2*z + 43792*t^2 - 64*t*z^7 + 32*t*z^6 + 240*t*z^5 - 3392*t*z^4 + 8800*t*z^3 - 21360*t*z^2 + 20864*t*z - 20608*t + 16*z^8 - 112*z^7 + 544*z^6 - 1696*z^5 + 4096*z^4 - 6688*z^3 + 8656*z^2 - 6160*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 2512*t^5 - 304*t^4*z^2 - 2672*t^4*z - 15520*t^4 + 256*t^3*z^3 + 2064*t^3*z^2 + 9936*t^3*z + 48448*t^3 - 160*t^2*z^4 - 880*t^2*z^3 - 4752*t^2*z^2 - 16576*t^2*z - 80512*t^2 + 64*t*z^5 + 224*t*z^4 + 592*t*z^3 + 5536*t*z^2 + 12752*t*z + 66832*t - 16*z^6 + 48*z^5 - 336*z^4 + 304*z^3 - 2544*z^2 - 3792*z - 21280)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_32 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 32) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_32 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_33 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 33) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_33 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^6 + 12960*t*z^5 - 50544*t*z^4 + 97200*t*z^3 - 95904*t*z^2 + 45360*t*z - 7776*t + 1296*z^8 - 16848*z^7 + 93312*z^6 - 287712*z^5 + 539136*z^4 - 624672*z^3 + 431568*z^2 - 159408*z + 23328:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^4 - 7776*t*z^3 + 18144*t*z^2 - 16848*t*z + 10368*t - 1296*z^6 + 11664*z^5 - 45360*z^4 + 94608*z^3 - 115344*z^2 + 68688*z - 41472)*hf
  · have hr : (-1296*t*z^6 + 16848*t*z^5 - 84240*t*z^4 + 203472*t*z^3 - 246240*t*z^2 + 142560*t*z - 31104*t + 1296*z^8 - 22032*z^7 + 156816*z^6 - 607824*z^5 + 1397088*z^4 - 1941408*z^3 + 1586304*z^2 - 694656*z + 124416:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^4 - 11664*t*z^3 + 36288*t*z^2 - 46656*t*z + 23328*t - 1296*z^6 + 16848*z^5 - 88128*z^4 + 238464*z^3 - 355104*z^2 + 282528*z - 101088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_34 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (_hc : cell (1) (1) (1) (profile4 (2) (z) t 34) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : ((0:ℝ):ℝ)=0 := by
  apply cell_4_34 z t hf hn0 hn1 hn2 hn3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_35 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 35) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_35 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 192*t^7*z + 80*t^7 + 1056*t^6*z^2 - 960*t^6*z + 16*t^6 - 3456*t^5*z^3 + 5040*t^5*z^2 - 720*t^5*z - 256*t^5 + 7344*t^4*z^4 - 15120*t^4*z^3 + 5040*t^4*z^2 + 1776*t^4*z + 16*t^4 - 10368*t^3*z^5 + 28080*t^3*z^4 - 15984*t^3*z^3 - 4368*t^3*z^2 + 1392*t^3*z + 176*t^3 + 9504*t^2*z^6 - 32400*t^2*z^5 + 27216*t^2*z^4 + 4752*t^2*z^3 - 7056*t^2*z^2 - 288*t^2*z - 272*t^2 - 5184*t*z^7 + 21600*t*z^6 - 24624*t*z^5 - 1728*t*z^4 + 12960*t*z^3 - 3600*t*z^2 + 1536*t*z - 64*t + 1296*z^8 - 6480*z^7 + 9504*z^6 - 9504*z^4 + 5184*z^3 + 624*z^2 - 1104*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6 + 3456*t^5*z + 8784*t^5 - 7344*t^4*z^2 - 14256*t^4*z - 54720*t^4 + 10368*t^3*z^3 + 13392*t^3*z^2 + 59184*t^3*z + 227712*t^3 - 9504*t^2*z^4 - 5616*t^2*z^3 - 40176*t^2*z^2 - 159840*t^2*z - 592128*t^2 + 5184*t*z^5 - 864*t*z^4 + 15984*t*z^3 + 66528*t*z^2 + 237168*t*z + 885744*t - 1296*z^6 + 1296*z^5 - 3024*z^4 - 13392*z^3 - 41040*z^2 - 155952*z - 583392)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_36 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 36) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_36 z t hf hn0 hn1 hn2 hn3
  · have hr : (-1296*t*z^6 + 9072*t*z^5 - 20736*t*z^4 + 14256*t*z^3 + 3888*t*z^2 - 2592*t*z + 1296*z^8 - 11664*z^7 + 40176*z^6 - 64800*z^5 + 45360*z^4 - 3888*z^3 - 9072*z^2 + 2592*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^4 - 3888*t*z^3 + 3888*t*z^2 + 5184*t*z + 12960*t - 1296*z^6 + 6480*z^5 - 12960*z^4 + 6480*z^3 - 6480*z^2 - 28512*z - 98496)*hf
  · have hr : (-1296*t*z^6 + 12960*t*z^5 - 50544*t*z^4 + 97200*t*z^3 - 95904*t*z^2 + 45360*t*z - 7776*t + 1296*z^8 - 16848*z^7 + 93312*z^6 - 287712*z^5 + 539136*z^4 - 624672*z^3 + 431568*z^2 - 159408*z + 23328:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(1296*t*z^4 - 7776*t*z^3 + 18144*t*z^2 - 16848*t*z + 10368*t - 1296*z^6 + 11664*z^5 - 45360*z^4 + 94608*z^3 - 115344*z^2 + 68688*z - 41472)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_37 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 37) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_37 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 10*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_38 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 38) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_38 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 12*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_39 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 39) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_39 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 6*t + 2*z^2 - 6*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 192*t^7*z + 16*t^7 + 1056*t^6*z^2 - 384*t^6*z - 128*t^6 - 3456*t^5*z^3 + 2736*t^5*z^2 + 864*t^5*z - 32*t^5 + 7344*t^4*z^4 - 9936*t^4*z^3 - 1440*t^4*z^2 + 1392*t^4*z + 256*t^4 - 10368*t^3*z^5 + 21168*t^3*z^4 - 2592*t^3*z^3 - 6432*t^3*z^2 - 1104*t^3*z - 32*t^3 + 9504*t^2*z^6 - 27216*t^2*z^5 + 12960*t^2*z^4 + 11232*t^2*z^3 - 2304*t^2*z^2 - 864*t^2*z + 16*t^2 - 5184*t*z^7 + 19872*t*z^6 - 18144*t*z^5 - 7344*t*z^4 + 9936*t*z^3 + 576*t*z^2 + 1392*t*z - 272*t + 1296*z^8 - 6480*z^7 + 9504*z^6 - 9504*z^4 + 5184*z^3 + 624*z^2 - 1104*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6 + 3456*t^5*z + 11088*t^5 - 7344*t^4*z^2 - 19440*t^4*z - 68976*t^4 + 10368*t^3*z^3 + 20304*t^3*z^2 + 73440*t^3*z + 279888*t^3 - 9504*t^2*z^4 - 10800*t^2*z^3 - 46656*t^2*z^2 - 187056*t^2*z - 699264*t^2 + 5184*t*z^5 + 864*t*z^4 + 16416*t*z^3 + 72144*t*z^2 + 262224*t*z + 976176*t - 1296*z^6 + 1296*z^5 - 3024*z^4 - 13392*z^3 - 41040*z^2 - 155952*z - 583392)*hf
  · have hr : (16*t^8 - 192*t^7*z + 16*t^7 + 1056*t^6*z^2 - 576*t^6*z + 256*t^6 - 3456*t^5*z^3 + 4464*t^5*z^2 - 2736*t^5*z + 256*t^5 + 7344*t^4*z^4 - 16848*t^4*z^3 + 16272*t^4*z^2 - 7104*t^4*z + 1696*t^4 - 10368*t^3*z^5 + 36720*t^3*z^4 - 54000*t^3*z^3 + 40656*t^3*z^2 - 14976*t^3*z + 1792*t^3 + 9504*t^2*z^6 - 47952*t^2*z^5 + 102384*t^2*z^4 - 118800*t^2*z^3 + 79344*t^2*z^2 - 30096*t^2*z + 4912*t^2 - 5184*t*z^7 + 35424*t*z^6 - 104976*t*z^5 + 174096*t*z^4 - 171504*t*z^3 + 97344*t*z^2 - 28128*t*z + 3472*t + 1296*z^8 - 11664*z^7 + 47088*z^6 - 111456*z^5 + 168048*z^4 - 162864*z^3 + 96528*z^2 - 30240*z + 3136:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6 + 3456*t^5*z + 9360*t^5 - 7344*t^4*z^2 - 12528*t^4*z - 59040*t^4 + 10368*t^3*z^3 + 4752*t^3*z^2 + 62640*t^3*z + 205152*t^3 - 9504*t^2*z^4 + 9936*t^2*z^3 - 53136*t^2*z^2 - 103680*t^2*z - 440928*t^2 + 5184*t*z^5 - 14688*t*z^4 + 41040*t*z^3 + 4752*t*z^2 + 149472*t*z + 495792*t - 1296*z^6 + 6480*z^5 - 19872*z^4 + 25488*z^3 - 46224*z^2 - 47520*z - 240384)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_40 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 40) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : (t - 2*z - 1:ℝ)=0 := by
  apply cell_4_40 z t hf hn0 hn1 hn2 hn3
  · have hr : (-3072*t*z^6 + 25344*t*z^5 - 78336*t*z^4 + 111360*t*z^3 - 72288*t*z^2 + 19296*t*z - 1344*t + 4096*z^8 - 44032*z^7 + 196096*z^6 - 468736*z^5 + 650368*z^4 - 526528*z^3 + 234784*z^2 - 49504*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(3072*t*z^4 - 13056*t*z^3 + 23040*t*z^2 - 6144*t*z + 24672*t - 4096*z^6 + 27648*z^5 - 81408*z^4 + 115456*z^3 - 107136*z^2 - 17472*z - 197536)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_41 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 41) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_41 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 12*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_42 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 42) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_42 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_43 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 43) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : (t - 2*z:ℝ)=0 := by
  apply cell_4_43 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 256*t^7*z + 144*t^7 + 1792*t^6*z^2 - 2160*t^6*z + 480*t^6 - 7168*t^5*z^3 + 13824*t^5*z^2 - 6912*t^5*z + 864*t^5 + 17920*t^4*z^4 - 48960*t^4*z^3 + 40608*t^4*z^2 - 11664*t^4*z + 1152*t^4 - 28672*t^3*z^5 + 103680*t^3*z^4 - 125184*t^3*z^3 + 60480*t^3*z^2 - 12240*t^3*z + 864*t^3 + 28672*t^2*z^6 - 131328*t^2*z^5 + 214272*t^2*z^4 - 152064*t^2*z^3 + 47520*t^2*z^2 - 5184*t^2*z - 432*t^2 - 16384*t*z^7 + 92160*t*z^6 - 193536*t*z^5 + 186624*t*z^4 - 80064*t*z^3 + 7776*t*z^2 + 5616*t*z - 1296*t + 4096*z^8 - 27648*z^7 + 72192*z^6 - 89856*z^5 + 49536*z^4 - 1728*z^3 - 9504*z^2 + 2592*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1792*t^6 + 7168*t^5*z + 14848*t^5 - 17920*t^4*z^2 - 22720*t^4*z - 113568*t^4 + 28672*t^3*z^3 + 11008*t^3*z^2 + 140544*t^3*z + 490688*t^3 - 28672*t^2*z^4 + 16640*t^2*z^3 - 119040*t^2*z^2 - 340736*t^2*z - 1291424*t^2 + 16384*t*z^5 - 26624*t*z^4 + 70656*t*z^3 + 122624*t*z^2 + 499904*t*z + 1869216*t - 4096*z^6 + 11264*z^5 - 23040*z^4 - 13568*z^3 - 80768*z^2 - 307776*z - 1140832)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_44 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 44) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_44 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 304*t^7 + 192*t^6*z^2 - 432*t^6*z + 2416*t^6 - 2736*t^5*z^2 + 6192*t^5*z - 10624*t^5 + 864*t^4*z^4 - 3888*t^4*z^3 + 19728*t^4*z^2 - 34848*t^4*z + 28336*t^4 - 8208*t^3*z^4 + 37152*t^3*z^3 - 86016*t^3*z^2 + 99792*t^3*z - 46288*t^3 + 1728*t^2*z^6 - 11664*t^2*z^5 + 53136*t^2*z^4 - 141696*t^2*z^3 + 205920*t^2*z^2 - 152784*t^2*z + 43792*t^2 - 8208*t*z^6 + 55728*t*z^5 - 162432*t*z^4 + 259632*t*z^3 - 236880*t*z^2 + 113760*t*z - 20608*t + 1296*z^8 - 11664*z^7 + 47088*z^6 - 111456*z^5 + 168048*z^4 - 162864*z^3 + 96528*z^2 - 30240*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6 + 2736*t^5 - 864*t^4*z^2 + 432*t^4*z - 17136*t^4 + 8208*t^3*z^2 - 4320*t^3*z + 60528*t^3 - 1728*t^2*z^4 + 4752*t^2*z^3 - 32400*t^2*z^2 + 7344*t^2*z - 144144*t^2 + 8208*t*z^4 - 22896*t*z^3 + 62640*t*z^2 + 13824*t*z + 229536*t - 1296*z^6 + 6480*z^5 - 19872*z^4 + 25488*z^3 - 46224*z^2 - 47520*z - 240384)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_45 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 45) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_45 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 6*t + 2*z^2 - 6*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 368*t^7 + 192*t^6*z^2 - 624*t^6*z + 3808*t^6 - 3312*t^5*z^2 + 10800*t^5*z - 23360*t^5 + 864*t^4*z^4 - 5616*t^4*z^3 + 33984*t^4*z^2 - 81216*t^4*z + 92896*t^4 - 9936*t^3*z^4 + 64800*t^3*z^3 - 210336*t^3*z^2 + 342528*t^3*z - 244928*t^3 + 1728*t^2*z^6 - 16848*t^2*z^5 + 101088*t^2*z^4 - 362016*t^2*z^3 + 754560*t^2*z^2 - 852336*t^2*z + 417328*t^2 - 9936*t*z^6 + 97200*t*z^5 - 420768*t*z^4 + 1023840*t*z^3 - 1472976*t*z^2 + 1186272*t*z - 419120*t + 1296*z^8 - 16848*z^7 + 100224*z^6 - 355104*z^5 + 817344*z^4 - 1248480*z^3 + 1233552*z^2 - 719472*z + 189280:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6 + 3312*t^5 - 864*t^4*z^2 + 2160*t^4*z - 24480*t^4 + 9936*t^3*z^2 - 25056*t^3*z + 100176*t^3 - 1728*t^2*z^4 + 9936*t^2*z^3 - 59616*t^2*z^2 + 113616*t^2*z - 240480*t^2 + 9936*t*z^4 - 57456*t*z^3 + 181008*t*z^2 - 242352*t*z + 322560*t - 1296*z^6 + 11664*z^5 - 52272*z^4 + 134352*z^3 - 227664*z^2 + 203472*z - 192000)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_46 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 46) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_46 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 160*t^6*z^2 - 96*t^6*z + 48*t^6 - 256*t^5*z^3 + 432*t^5*z^2 + 432*t^5*z + 304*t^4*z^4 - 1104*t^4*z^3 + 432*t^4*z^2 - 432*t^4*z - 144*t^4 - 256*t^3*z^5 + 1392*t^3*z^4 - 1200*t^3*z^3 - 1296*t^3*z^2 - 144*t^3*z + 432*t^3 + 160*t^2*z^6 - 1296*t^2*z^5 + 3024*t^2*z^4 - 2160*t^2*z^3 + 1296*t^2*z^2 + 864*t^2*z - 432*t^2 - 64*t*z^7 + 672*t*z^6 - 2160*t*z^5 + 1728*t*z^4 + 1152*t*z^3 + 432*t*z^2 - 864*t*z + 16*z^8 - 240*z^7 + 1344*z^6 - 3456*z^5 + 3744*z^4 - 3024*z^2 + 1296*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 592*t^5 - 304*t^4*z^2 - 112*t^4*z - 576*t^4 + 256*t^3*z^3 - 368*t^3*z^2 - 528*t^3*z - 448*t^3 - 160*t^2*z^4 + 656*t^2*z^3 - 240*t^2*z^2 + 544*t^2*z + 1120*t^2 + 64*t*z^5 - 416*t*z^4 + 432*t*z^3 + 416*t*z^2 + 80*t*z - 528*t - 16*z^6 + 176*z^5 - 624*z^4 + 784*z^3 + 16*z^2 - 720*z + 128)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_47 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 47) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_47 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 192*t^7*z - 48*t^7 + 1056*t^6*z^2 + 192*t^6*z + 48*t^6 - 3456*t^5*z^3 + 432*t^5*z^2 + 144*t^5*z + 7344*t^4*z^4 - 4752*t^4*z^3 - 432*t^4*z^2 - 432*t^4*z - 144*t^4 - 10368*t^3*z^5 + 14256*t^3*z^4 - 3024*t^3*z^3 + 432*t^3*z^2 + 432*t^3*z + 432*t^3 + 9504*t^2*z^6 - 22032*t^2*z^5 + 14256*t^2*z^4 - 3024*t^2*z^3 + 432*t^2*z^2 - 432*t^2 - 5184*t*z^7 + 18144*t*z^6 - 22032*t*z^5 + 10368*t*z^4 - 1296*t*z^2 + 1296*z^8 - 6480*z^7 + 12960*z^6 - 12960*z^5 + 5184*z^4 + 2592*z^3 - 3888*z^2 + 1296*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6 + 3456*t^5*z + 13392*t^5 - 7344*t^4*z^2 - 24624*t^4*z - 90720*t^4 + 10368*t^3*z^3 + 27216*t^3*z^2 + 101520*t^3*z + 378432*t^3 - 9504*t^2*z^4 - 15984*t^2*z^3 - 68688*t^2*z^2 - 255744*t^2*z - 954720*t^2 + 5184*t*z^5 + 2592*t*z^4 + 27216*t*z^3 + 95904*t*z^2 + 356400*t*z + 1330992*t - 1296*z^6 + 1296*z^5 - 6480*z^4 - 14256*z^3 - 55728*z^2 - 211248*z - 785376)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_48 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 48) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_48 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 176*t^7 + 160*t^6*z^2 - 832*t^6*z + 784*t^6 + 256*t^5*z^3 - 1968*t^5*z^2 + 4224*t^5*z - 1904*t^5 + 304*t^4*z^4 - 3056*t^4*z^3 + 9888*t^4*z^2 - 10736*t^4*z + 2656*t^4 + 256*t^3*z^5 - 3184*t^3*z^4 + 13984*t^3*z^3 - 24944*t^3*z^2 + 14384*t^3*z - 1568*t^3 + 160*t^2*z^6 - 2352*t^2*z^5 + 12768*t^2*z^4 - 30928*t^2*z^3 + 31056*t^2*z^2 - 8544*t^2*z - 704*t^2 + 64*t*z^7 - 1088*t*z^6 + 7104*t*z^5 - 22096*t*z^4 + 31856*t*z^3 - 15360*t*z^2 - 992*t*z + 1408*t + 16*z^8 - 304*z^7 + 2224*z^6 - 7888*z^5 + 13792*z^4 - 9952*z^3 - 128*z^2 + 2432*z - 512:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 944*t^5 - 304*t^4*z^2 + 1840*t^4*z - 2224*t^4 - 256*t^3*z^3 + 2160*t^3*z^2 - 5088*t^3*z + 2432*t^3 - 160*t^2*z^4 + 1712*t^2*z^3 - 5760*t^2*z^2 + 6176*t^2*z - 592*t^2 - 64*t*z^5 + 832*t*z^4 - 3712*t*z^3 + 6416*t*z^2 - 2480*t*z - 976*t - 16*z^6 + 240*z^5 - 1248*z^4 + 2656*z^3 - 1920*z^2 - 384*z + 512)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_49 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 49) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : (t + z - 4:ℝ)=0 := by
  apply cell_4_49 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 240*t^7 + 160*t^6*z^2 - 1152*t^6*z + 1728*t^6 + 256*t^5*z^3 - 2736*t^5*z^2 + 8784*t^5*z - 7776*t^5 + 304*t^4*z^4 - 4272*t^4*z^3 + 20592*t^4*z^2 - 38880*t^4*z + 23616*t^4 + 256*t^3*z^5 - 4464*t^3*z^4 + 28944*t^3*z^3 - 85104*t^3*z^2 + 109440*t^3*z - 49248*t^3 + 160*t^2*z^6 - 3312*t^2*z^5 + 26640*t^2*z^4 - 104976*t^2*z^3 + 209520*t^2*z^2 - 197424*t^2*z + 68688*t^2 + 64*t*z^7 - 1536*t*z^6 + 14832*t*z^5 - 73872*t*z^4 + 201456*t*z^3 - 294624*t*z^2 + 212544*t*z - 58320*t + 16*z^8 - 432*z^7 + 4752*z^6 - 27648*z^5 + 92304*z^4 - 179280*z^3 + 195696*z^2 - 108864*z + 23328:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 1712*t^5 - 304*t^4*z^2 + 3056*t^4*z - 8064*t^4 - 256*t^3*z^3 + 3440*t^3*z^2 - 14928*t^3*z + 21952*t^3 - 160*t^2*z^4 + 2672*t^2*z^3 - 15792*t^2*z^2 + 39136*t^2*z - 37184*t^2 - 64*t*z^5 + 1280*t*z^4 - 9648*t*z^3 + 34000*t*z^2 - 55808*t*z + 37392*t - 16*z^6 + 368*z^5 - 3264*z^4 + 14224*z^3 - 32144*z^2 + 36480*z - 17632)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_50 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 50) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_50 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 304*t^7 - 48*t^6*z + 2224*t^6 + 720*t^5*z - 7888*t^5 - 3600*t^4*z + 13792*t^4 + 6384*t^3*z - 9952*t^3 - 1440*t^2*z - 128*t^2 - 1440*t*z + 2432*t + 384*z - 512:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_51 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 51) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_51 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z + 16*t^7 + 160*t^6*z^2 - 224*t^6*z - 128*t^6 - 256*t^5*z^3 + 624*t^5*z^2 + 240*t^5*z - 32*t^5 + 304*t^4*z^4 - 1168*t^4*z^3 + 240*t^4*z^2 + 1088*t^4*z + 256*t^4 - 256*t^3*z^5 + 1328*t^3*z^4 - 976*t^3*z^3 - 1616*t^3*z^2 - 608*t^3*z - 32*t^3 + 160*t^2*z^6 - 1104*t^2*z^5 + 1680*t^2*z^4 + 1264*t^2*z^3 - 1776*t^2*z^2 - 1104*t^2*z + 16*t^2 - 64*t*z^7 + 544*t*z^6 - 1200*t*z^5 - 208*t*z^4 + 1456*t*z^3 + 768*t*z^2 + 1568*t*z - 272*t + 16*z^8 - 176*z^7 + 592*z^6 - 320*z^5 - 1520*z^4 + 1840*z^3 + 304*z^2 - 896*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 400*t^5 - 304*t^4*z^2 - 48*t^4*z - 128*t^4 + 256*t^3*z^3 - 304*t^3*z^2 - 496*t^3*z - 64*t^3 - 160*t^2*z^4 + 464*t^2*z^3 + 336*t^2*z^2 - 384*t^2*z - 96*t^2 + 64*t*z^5 - 288*t*z^4 - 16*t*z^3 + 432*t*z^2 + 288*t*z - 48*t - 16*z^6 + 112*z^5 - 128*z^4 - 304*z^3 + 432*z^2 + 192*z + 32)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_52 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 52) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : (t + z - 4:ℝ)=0 := by
  apply cell_4_52 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 240*t^7 + 160*t^6*z^2 - 960*t^6*z + 1344*t^6 + 256*t^5*z^3 - 2160*t^5*z^2 + 5472*t^5*z - 3456*t^5 + 304*t^4*z^4 - 3120*t^4*z^3 + 10944*t^4*z^2 - 14256*t^4*z + 3744*t^4 + 256*t^3*z^5 - 3120*t^3*z^4 + 13728*t^3*z^3 - 25056*t^3*z^2 + 14832*t^3*z + 160*t^2*z^6 - 2160*t^2*z^5 + 10944*t^2*z^4 - 25056*t^2*z^3 + 22464*t^2*z^2 - 3024*t^2 + 64*t*z^7 - 960*t*z^6 + 5472*t*z^5 - 14256*t*z^4 + 14832*t*z^3 - 5616*t*z + 1296*t + 16*z^8 - 240*z^7 + 1344*z^6 - 3456*z^5 + 3744*z^4 - 3024*z^2 + 1296*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 1136*t^5 - 304*t^4*z^2 + 1904*t^4*z - 3024*t^4 - 256*t^3*z^3 + 2096*t^3*z^2 - 5088*t^3*z + 2608*t^3 - 160*t^2*z^4 + 1520*t^2*z^3 - 4704*t^2*z^2 + 4720*t^2*z + 1120*t^2 - 64*t*z^5 + 704*t*z^4 - 2592*t*z^3 + 3184*t*z^2 + 496*t*z - 1200*t - 16*z^6 + 176*z^5 - 624*z^4 + 784*z^3 + 16*z^2 - 720*z + 128)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_53 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 53) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_53 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 10*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 64*t^7*z - 304*t^7 + 160*t^6*z^2 - 1280*t^6*z + 2416*t^6 + 256*t^5*z^3 - 2928*t^5*z^2 + 10416*t^5*z - 10624*t^5 + 304*t^4*z^4 - 4336*t^4*z^3 + 21840*t^4*z^2 - 44560*t^4*z + 28336*t^4 + 256*t^3*z^5 - 4400*t^3*z^4 + 28432*t^3*z^3 - 83920*t^3*z^2 + 108080*t^3*z - 46288*t^3 + 160*t^2*z^6 - 3120*t^2*z^5 + 23856*t^2*z^4 - 90032*t^2*z^3 + 171312*t^2*z^2 - 147264*t^2*z + 43792*t^2 + 64*t*z^7 - 1408*t*z^6 + 12432*t*z^5 - 56096*t*z^4 + 136064*t*z^3 - 171408*t*z^2 + 100960*t*z - 20608*t + 16*z^8 - 368*z^7 + 3424*z^6 - 16736*z^5 + 46528*z^4 - 73952*z^3 + 63376*z^2 - 25424*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 - 256*t^5*z + 1904*t^5 - 304*t^4*z^2 + 3120*t^4*z - 9056*t^4 - 256*t^3*z^3 + 3376*t^3*z^2 - 14672*t^3*z + 21856*t^3 - 160*t^2*z^4 + 2480*t^2*z^3 - 13776*t^2*z^2 + 32448*t^2*z - 27744*t^2 - 64*t*z^5 + 1152*t*z^4 - 7760*t*z^3 + 23904*t*z^2 - 32688*t*z + 16752*t - 16*z^6 + 304*z^5 - 2192*z^4 + 7664*z^3 - 13680*z^2 + 11568*z - 3424)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_54 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 54) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_54 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 6*t + 2*z^2 - 6*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 176*t^7 - 48*t^6*z + 592*t^6 + 432*t^5*z - 320*t^5 - 864*t^4*z - 1520*t^4 - 1200*t^3*z + 1840*t^3 + 3024*t^2*z + 304*t^2 + 1728*t*z - 896*t - 480*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_55 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 55) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_55 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 12*t + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z - 112*t^7 + 160*t^6*z^2 + 224*t^6*z + 160*t^6 - 256*t^5*z^3 - 336*t^5*z^2 + 384*t^5*z + 320*t^5 + 304*t^4*z^4 + 112*t^4*z^3 - 768*t^4*z^2 - 1232*t^4*z - 800*t^4 - 256*t^3*z^5 + 112*t^3*z^4 + 1472*t^3*z^3 + 320*t^3*z^2 - 1328*t^3*z + 320*t^3 + 160*t^2*z^6 - 336*t^2*z^5 - 768*t^2*z^4 + 320*t^2*z^3 + 1536*t^2*z^2 + 2112*t^2*z + 304*t^2 - 64*t*z^7 + 224*t*z^6 + 384*t*z^5 - 1232*t*z^4 - 1328*t*z^3 + 2112*t*z^2 + 1424*t*z - 688*t + 16*z^8 - 112*z^7 + 160*z^6 + 320*z^5 - 800*z^4 + 320*z^3 + 304*z^2 - 688*z + 160:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 1360*t^5 - 304*t^4*z^2 - 1328*t^4*z - 4240*t^4 + 256*t^3*z^3 + 912*t^3*z^2 + 1920*t^3*z + 6448*t^3 - 160*t^2*z^4 - 304*t^2*z^3 - 288*t^2*z^2 - 1168*t^2*z - 5920*t^2 + 64*t*z^5 + 32*t*z^4 - 320*t*z^3 - 80*t*z^2 + 1328*t*z + 3280*t - 16*z^6 + 48*z^5 + 48*z^4 - 176*z^3 + 48*z^2 + 48*z - 160)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_56 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 56) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_56 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 112*t^7 + 192*t^6*z^2 - 624*t^6*z + 544*t^6 - 1008*t^5*z^2 + 3312*t^5*z - 1696*t^5 + 864*t^4*z^4 - 5616*t^4*z^3 + 13248*t^4*z^2 - 13536*t^4*z + 4096*t^4 - 3024*t^3*z^4 + 19872*t^3*z^3 - 41952*t^3*z^2 + 30720*t^3*z - 6688*t^3 + 1728*t^2*z^6 - 16848*t^2*z^5 + 64800*t^2*z^4 - 125280*t^2*z^3 + 125568*t^2*z^2 - 57168*t^2*z + 8656*t^2 - 3024*t*z^6 + 29808*t*z^5 - 110592*t*z^4 + 190944*t*z^3 - 154800*t*z^2 + 54720*t*z - 6160*t + 1296*z^8 - 16848*z^7 + 89856*z^6 - 254016*z^5 + 410400*z^4 - 380160*z^3 + 190704*z^2 - 44688*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6 + 1008*t^5 - 864*t^4*z^2 + 2160*t^4*z - 3744*t^4 + 3024*t^3*z^2 - 7776*t^3*z + 7824*t^3 - 1728*t^2*z^4 + 9936*t^2*z^3 - 23328*t^2*z^2 + 22032*t^2*z - 14112*t^2 + 3024*t*z^4 - 17712*t*z^3 + 36720*t*z^2 - 26352*t*z + 12672*t - 1296*z^6 + 11664*z^5 - 41904*z^4 + 74736*z^3 - 69552*z^2 + 27216*z - 12288)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_57 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 57) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_57 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 6*t + 2*z^2 - 6*z + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 176*t^7 + 192*t^6*z^2 - 816*t^6*z + 1360*t^6 - 1584*t^5*z^2 + 6768*t^5*z - 6656*t^5 + 864*t^4*z^4 - 7344*t^4*z^3 + 25776*t^4*z^2 - 43488*t^4*z + 25552*t^4 - 4752*t^3*z^4 + 40608*t^3*z^3 - 123072*t^3*z^2 + 155856*t^3*z - 68816*t^3 + 1728*t^2*z^6 - 22032*t^2*z^5 + 117936*t^2*z^4 - 340416*t^2*z^3 + 549792*t^2*z^2 - 454320*t^2*z + 146608*t^2 - 4752*t*z^6 + 60912*t*z^5 - 309312*t*z^4 + 791856*t*z^3 - 1072944*t*z^2 + 728640*t*z - 193856*t + 1296*z^8 - 22032*z^7 + 158544*z^6 - 629856*z^5 + 1508112*z^4 - 2222640*z^3 + 1961904*z^2 - 944736*z + 189280:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-192*t^6 + 1584*t^5 - 864*t^4*z^2 + 3888*t^4*z - 9360*t^4 + 4752*t^3*z^2 - 21600*t^3*z + 31920*t^3 - 1728*t^2*z^4 + 15120*t^2*z^3 - 55728*t^2*z^2 + 102384*t^2*z - 84528*t^2 + 4752*t*z^4 - 41904*t*z^3 + 136944*t*z^2 - 202176*t*z + 127296*t - 1296*z^6 + 16848*z^5 - 89856*z^4 + 253584*z^3 - 403920*z^2 + 353376*z - 144480)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_58 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 58) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_58 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 160*t^6*z^2 - 96*t^6*z + 48*t^6 - 256*t^5*z^3 + 432*t^5*z^2 + 432*t^5*z + 304*t^4*z^4 - 1104*t^4*z^3 + 432*t^4*z^2 - 432*t^4*z - 144*t^4 - 256*t^3*z^5 + 1392*t^3*z^4 - 1200*t^3*z^3 - 1296*t^3*z^2 - 144*t^3*z + 432*t^3 + 160*t^2*z^6 - 1296*t^2*z^5 + 3024*t^2*z^4 - 2160*t^2*z^3 + 1296*t^2*z^2 + 864*t^2*z - 432*t^2 - 64*t*z^7 + 672*t*z^6 - 2160*t*z^5 + 1728*t*z^4 + 1152*t*z^3 + 432*t*z^2 - 864*t*z + 16*z^8 - 240*z^7 + 1344*z^6 - 3456*z^5 + 3744*z^4 - 3024*z^2 + 1296*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 592*t^5 - 304*t^4*z^2 - 112*t^4*z - 576*t^4 + 256*t^3*z^3 - 368*t^3*z^2 - 528*t^3*z - 448*t^3 - 160*t^2*z^4 + 656*t^2*z^3 - 240*t^2*z^2 + 544*t^2*z + 1120*t^2 + 64*t*z^5 - 416*t*z^4 + 432*t*z^3 + 416*t*z^2 + 80*t*z - 528*t - 16*z^6 + 176*z^5 - 624*z^4 + 784*z^3 + 16*z^2 - 720*z + 128)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_59 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 59) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_59 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 192*t^7*z + 144*t^7 + 1056*t^6*z^2 - 1728*t^6*z + 480*t^6 - 3456*t^5*z^3 + 9072*t^5*z^2 - 5904*t^5*z + 864*t^5 + 7344*t^4*z^4 - 27216*t^4*z^3 + 29808*t^4*z^2 - 10368*t^4*z + 1152*t^4 - 10368*t^3*z^5 + 50544*t^3*z^4 - 80784*t^3*z^3 + 48816*t^3*z^2 - 11232*t^3*z + 864*t^3 + 9504*t^2*z^6 - 58320*t^2*z^5 + 125712*t^2*z^4 - 113616*t^2*z^3 + 41904*t^2*z^2 - 5616*t^2*z - 432*t^2 - 5184*t*z^7 + 38880*t*z^6 - 107568*t*z^5 + 133488*t*z^4 - 71280*t*z^3 + 10368*t*z^2 + 5184*t*z - 1296*t + 1296*z^8 - 11664*z^7 + 40176*z^6 - 64800*z^5 + 45360*z^4 - 3888*z^3 - 9072*z^2 + 2592*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1056*t^6 + 3456*t^5*z + 4752*t^5 - 7344*t^4*z^2 - 2160*t^4*z - 31104*t^4 + 10368*t^3*z^3 - 9072*t^3*z^2 + 34128*t^3*z + 96768*t^3 - 9504*t^2*z^4 + 20304*t^2*z^3 - 34992*t^2*z^2 - 46656*t^2*z - 193536*t^2 + 5184*t*z^5 - 18144*t*z^4 + 29808*t*z^3 + 3888*t*z^2 + 57024*t*z + 213840*t - 1296*z^6 + 6480*z^5 - 12960*z^4 + 6480*z^3 - 6480*z^2 - 28512*z - 98496)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_60 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 60) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : (t + z - 4:ℝ)=0 := by
  apply cell_4_60 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z - 368*t^7 + 448*t^6*z^2 - 2576*t^6*z + 3424*t^6 + 896*t^5*z^3 - 7728*t^5*z^2 + 20688*t^5*z - 16736*t^5 + 1120*t^4*z^4 - 12880*t^4*z^3 + 51936*t^4*z^2 - 85120*t^4*z + 46528*t^4 + 896*t^3*z^5 - 12880*t^3*z^4 + 69344*t^3*z^3 - 171680*t^3*z^2 + 190432*t^3*z - 73952*t^3 + 448*t^2*z^6 - 7728*t^2*z^5 + 51936*t^2*z^4 - 171680*t^2*z^3 + 287808*t^2*z^2 - 225456*t^2*z + 63376*t^2 + 128*t*z^7 - 2576*t*z^6 + 20688*t*z^5 - 85120*t*z^4 + 190432*t*z^3 - 225456*t*z^2 + 127328*t*z - 25424*t + 16*z^8 - 368*z^7 + 3424*z^6 - 16736*z^5 + 46528*z^4 - 73952*z^3 + 63376*z^2 - 25424*z + 3136:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 - 896*t^5*z + 4144*t^5 - 1120*t^4*z^2 + 8400*t^4*z - 17216*t^4 - 896*t^3*z^3 + 9296*t^3*z^2 - 31264*t^3*z + 37328*t^3 - 448*t^2*z^4 + 5936*t^2*z^3 - 27744*t^2*z^2 + 54768*t^2*z - 40992*t^2 - 128*t*z^5 + 2064*t*z^4 - 12304*t*z^3 + 33840*t*z^2 - 42768*t*z + 20544*t - 16*z^6 + 304*z^5 - 2192*z^4 + 7664*z^3 - 13680*z^2 + 11568*z - 3424)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_61 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 61) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_61 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 12*t + 6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z - 496*t^7 + 448*t^6*z^2 - 3472*t^6*z + 6400*t^6 + 896*t^5*z^3 - 10416*t^5*z^2 + 38544*t^5*z - 44896*t^5 + 1120*t^4*z^4 - 17360*t^4*z^3 + 96576*t^4*z^2 - 226496*t^4*z + 187072*t^4 + 896*t^3*z^5 - 17360*t^3*z^4 + 128864*t^3*z^3 - 455008*t^3*z^2 + 757792*t^3*z - 473056*t^3 + 448*t^2*z^6 - 10416*t^2*z^5 + 96576*t^2*z^4 - 455008*t^2*z^3 + 1141440*t^2*z^2 - 1436304*t^2*z + 706768*t^2 + 128*t*z^7 - 3472*t*z^6 + 38544*t*z^5 - 226496*t*z^4 + 757792*t*z^3 - 1436304*t*z^2 + 1423616*t*z - 569296*t + 16*z^8 - 496*z^7 + 6400*z^6 - 44896*z^5 + 187072*z^4 - 473056*z^3 + 706768*z^2 - 569296*z + 189280:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 - 896*t^5*z + 6832*t^5 - 1120*t^4*z^2 + 12880*t^4*z - 43936*t^4 - 896*t^3*z^3 + 13776*t^3*z^2 - 72864*t^3*z + 149776*t^3 - 448*t^2*z^4 + 8624*t^2*z^3 - 61632*t^2*z^2 + 199856*t^2*z - 280384*t^2 - 128*t*z^5 + 2960*t*z^4 - 26576*t*z^3 + 117232*t*z^2 - 262288*t*z + 269920*t - 16*z^6 + 432*z^5 - 4656*z^4 + 25840*z^3 - 79056*z^2 + 130992*z - 103744)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_62 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 62) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_62 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 240*t^7 - 48*t^6*z + 1344*t^6 + 576*t^5*z - 3456*t^5 - 2160*t^4*z + 3744*t^4 + 2160*t^3*z + 1728*t^2*z - 3024*t^2 - 1296*t*z + 1296*t:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_4_63 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (2) (z) t 63) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : False := by
  apply cell_4_63 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (-48*t*z^6 + 576*t*z^5 - 2160*t*z^4 + 2160*t*z^3 + 1728*t*z^2 - 1296*t*z + 16*z^8 - 240*z^7 + 1344*z^6 - 3456*z^5 + 3744*z^4 - 3024*z^2 + 1296*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t*z^4 - 384*t*z^3 + 576*t*z^2 + 528*t*z - 192*t - 16*z^6 + 176*z^5 - 624*z^4 + 784*z^3 + 16*z^2 - 720*z + 128)*hf


private def limit4 (z t : ℝ) : Fin 64→Prop := ![False,False,False,False,False,False,False,False,False,False,(((0:ℝ):ℝ)=0),False,False,((t + z - 4:ℝ)=0),False,False,False,False,False,False,False,False,False,False,False,False,False,False,((t + z - 4:ℝ)=0),False,False,False,False,False,(((0:ℝ):ℝ)=0),False,False,False,False,False,((t - 2*z - 1:ℝ)=0),False,False,((t - 2*z:ℝ)=0),False,False,False,False,False,((t + z - 4:ℝ)=0),False,False,((t + z - 4:ℝ)=0),False,False,False,False,False,False,False,((t + z - 4:ℝ)=0),False,False,False]

private def hue4 : Fin 64→Fin 4 := ![0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,3,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_4_10_13 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (_hi : limit4 z t 10) (hj : limit4 z t 13) (he : edge4 (1) (1) (1) (profile4 (2) (z) t 10) (profile4 (2) (z) t 13) (2) (z) t=0) : False := by
  apply pair_4_10_13 z t hf hn0 hn1 hn2 hn3
  · exact hj
  · have hraw : (16*t^8 - 64*t^7*z - 176*t^7 + 160*t^6*z^2 + 352*t^6*z + 784*t^6 - 256*t^5*z^3 - 528*t^5*z^2 - 192*t^5*z - 1904*t^5 + 304*t^4*z^4 + 176*t^4*z^3 + 384*t^4*z^2 - 1936*t^4*z + 2656*t^4 - 256*t^3*z^5 + 176*t^3*z^4 + 992*t^3*z^3 - 1904*t^3*z^2 + 4720*t^3*z - 1568*t^3 + 160*t^2*z^6 - 528*t^2*z^5 + 384*t^2*z^4 - 1904*t^2*z^3 + 5424*t^2*z^2 - 4128*t^2*z - 704*t^2 - 64*t*z^7 + 352*t*z^6 - 192*t*z^5 - 1936*t*z^4 + 4720*t*z^3 - 4128*t*z^2 - 160*t*z + 1408*t + 16*z^8 - 176*z^7 + 784*z^6 - 1904*z^5 + 2656*z^4 - 1568*z^3 - 704*z^2 + 1408*z - 512:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-160*t^6 + 256*t^5*z + 1552*t^5 - 304*t^4*z^2 - 1392*t^4*z - 5648*t^4 + 256*t^3*z^3 + 848*t^3*z^2 + 2144*t^3*z + 9632*t^3 - 160*t^2*z^4 - 112*t^2*z^3 - 672*t^2*z^2 - 672*t^2*z - 7440*t^2 + 64*t*z^5 - 96*t*z^4 - 256*t*z^3 + 1008*t*z^2 - 432*t*z + 1392*t - 16*z^6 + 112*z^5 - 320*z^4 + 512*z^3 - 288*z^2 - 96*z + 608)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_4_28_52 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit4 z t 28) (_hj : limit4 z t 52) (he : edge4 (1) (1) (1) (profile4 (2) (z) t 28) (profile4 (2) (z) t 52) (2) (z) t=0) : False := by
  apply pair_4_28_52 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (1296*t^8 - 22032*t^7 - 1296*t^6*z + 156816*t^6 + 16848*t^5*z - 607824*t^5 - 84240*t^4*z + 1397088*t^4 + 203472*t^3*z - 1941408*t^3 - 246240*t^2*z + 1586304*t^2 + 142560*t*z - 694656*t - 31104*z + 124416:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_4_34_49 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (_hi : limit4 z t 34) (hj : limit4 z t 49) (he : edge4 (1) (1) (1) (profile4 (2) (z) t 34) (profile4 (2) (z) t 49) (2) (z) t=0) : False := by
  apply pair_4_34_49 z t hf hn0 hn1 hn2 hn3
  · exact hj
  · have hraw : (16*t^8 - 64*t^7*z - 176*t^7 + 160*t^6*z^2 + 352*t^6*z + 784*t^6 - 256*t^5*z^3 - 528*t^5*z^2 - 192*t^5*z - 1904*t^5 + 304*t^4*z^4 + 176*t^4*z^3 + 384*t^4*z^2 - 1936*t^4*z + 2656*t^4 - 256*t^3*z^5 + 176*t^3*z^4 + 992*t^3*z^3 - 1904*t^3*z^2 + 4720*t^3*z - 1568*t^3 + 160*t^2*z^6 - 528*t^2*z^5 + 384*t^2*z^4 - 1904*t^2*z^3 + 5424*t^2*z^2 - 4128*t^2*z - 704*t^2 - 64*t*z^7 + 352*t*z^6 - 192*t*z^5 - 1936*t*z^4 + 4720*t*z^3 - 4128*t*z^2 - 160*t*z + 1408*t + 16*z^8 - 176*z^7 + 784*z^6 - 1904*z^5 + 2656*z^4 - 1568*z^3 - 704*z^2 + 1408*z - 512:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-160*t^6 + 256*t^5*z + 1552*t^5 - 304*t^4*z^2 - 1392*t^4*z - 5648*t^4 + 256*t^3*z^3 + 848*t^3*z^2 + 2144*t^3*z + 9632*t^3 - 160*t^2*z^4 - 112*t^2*z^3 - 672*t^2*z^2 - 672*t^2*z - 7440*t^2 + 64*t*z^5 - 96*t*z^4 - 256*t*z^3 + 1008*t*z^2 - 432*t*z + 1392*t - 16*z^6 + 112*z^5 - 320*z^4 + 512*z^3 - 288*z^2 - 96*z + 608)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_4_40_43 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit4 z t 40) (hj : limit4 z t 43) (_he : edge4 (1) (1) (1) (profile4 (2) (z) t 40) (profile4 (2) (z) t 43) (2) (z) t=0) : False := by
  apply pair_4_40_43 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_4_40_60 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit4 z t 40) (hj : limit4 z t 60) (_he : edge4 (1) (1) (1) (profile4 (2) (z) t 40) (profile4 (2) (z) t 60) (2) (z) t=0) : False := by
  apply pair_4_40_60 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_4_43_60 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit4 z t 43) (hj : limit4 z t 60) (_he : edge4 (1) (1) (1) (profile4 (2) (z) t 43) (profile4 (2) (z) t 60) (2) (z) t=0) : False := by
  apply pair_4_43_60 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma exclude_field_4 (z t : ℝ) (hf : z^2 - 4*z + 1=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (g : Fin 5→Fin 64) (hinj : Function.Injective g)
    (hc : ∀ i, cell (1) (1) (1) (profile4 (2) (z) t (g i)) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t)
    (he : ∀ i j : Fin 5, i≠j → edge4 (1) (1) (1) (profile4 (2) (z) t (g i)) (profile4 (2) (z) t (g j)) (2) (z) t=0) : False := by
  have row (k : Fin 64) (hh : cell (1) (1) (1) (profile4 (2) (z) t k) ((1),(2),(z)) ((2),(1),(z)) (2) (z) t) : limit4 z t k := by
    fin_cases k
    · exact row_4_0 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_1 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_2 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_3 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_4 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_5 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_6 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_7 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_8 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_9 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_10 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_11 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_12 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_13 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_14 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_15 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_16 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_17 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_18 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_19 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_20 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_21 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_22 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_23 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_24 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_25 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_26 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_27 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_28 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_29 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_30 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_31 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_32 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_33 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_34 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_35 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_36 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_37 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_38 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_39 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_40 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_41 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_42 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_43 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_44 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_45 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_46 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_47 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_48 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_49 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_50 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_51 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_52 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_53 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_54 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_55 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_56 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_57 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_58 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_59 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_60 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_61 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_62 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_4_63 z t hf hn0 hn1 hn2 hn3 hh
  have allowed (k : Fin 64) (hh : limit4 z t k) : k∈([10,13,28,34,40,43,49,52,60]:List (Fin 64)) := by
    fin_cases k <;> first | decide | exact False.elim hh
  have cert : ∀ i j : Fin 64, i∈([10,13,28,34,40,43,49,52,60]:List (Fin 64)) → j∈([10,13,28,34,40,43,49,52,60]:List (Fin 64)) → i<j → hue4 i=hue4 j → (i,j)∈([(10,13),(28,52),(34,49),(40,43),(40,60),(43,60)]:List (Fin 64×Fin 64)) := by decide
  have bad (i j : Fin 64) (hi : limit4 z t i) (hj : limit4 z t j) (hlt : i<j) (hc : hue4 i=hue4 j) (hb : edge4 (1) (1) (1) (profile4 (2) (z) t i) (profile4 (2) (z) t j) (2) (z) t=0) : False := by
    have h := cert i j (allowed i hi) (allowed j hj) hlt hc
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact rowpair_4_10_13 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_4_28_52 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_4_34_49 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_4_40_43 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_4_40_60 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_4_43_60 z t hf hn0 hn1 hn2 hn3 hi hj hb
  have hi : Function.Injective (fun i : Fin 5 => hue4 (g i)) := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne (show g i≠g j from fun e => hne (hinj e)) with hl|hl
    · exact bad _ _ (row _ (hc i)) (row _ (hc j)) hl h (he i j hne)
    · exact bad _ _ (row _ (hc j)) (row _ (hc i)) hl h.symm (he j i (Ne.symm hne))
  have hh := Fintype.card_le_of_injective _ hi
  norm_num at hh

private lemma no_0000112212 (x y t : ℝ) (H : admissible ![0,0,0,0,1,1,2,2,1,2] x y) (E : hasExtension ![0,0,0,0,1,1,2,2,1,2] x y t)
    (t1 : t-1≠0) (tx : t-x≠0) (ty : t-y≠0) (t0 : t≠0) : False := by
  obtain ⟨h0,h1⟩ := shape_0000112212 x y H
  by_cases G0 : y^2 - 5*y + 5=0
  · have ex : x=5 - y := by linear_combination (1)*h0
    obtain ⟨u,hu,hc,he⟩ := E
    change ∀ i, cell (1) (1) (x) (profile4 x y t (u i)) ((1),(x),(y)) ((1),(y),(x)) x y t at hc
    change ∀ i j, i≠j → edge4 (1) (1) (x) (profile4 x y t (u i)) (profile4 x y t (u j)) x y t=0 at he
    simp only [ex] at hc he tx ty
    apply exclude_field_2 y t (by linear_combination (1)*G0) t1 tx ty (by simpa using t0) u hu hc he
  apply G0
  linear_combination (1)*h1

private lemma no_0001010112 (x y t : ℝ) (H : admissible ![0,0,0,1,0,1,0,1,1,2] x y) (E : hasExtension ![0,0,0,1,0,1,0,1,1,2] x y t)
    (t1 : t-1≠0) (tx : t-x≠0) (ty : t-y≠0) (t0 : t≠0) : False := by
  obtain ⟨h0,h1⟩ := shape_0001010112 x y H
  by_cases G0 : y^2 - 8*y + 4=0
  · have ex : x=y/2 := by linear_combination (1)*h0
    obtain ⟨u,hu,hc,he⟩ := E
    change ∀ i, cell (1) (1) (1) (profile4 x y t (u i)) ((1),(x),(x)) ((x),(1),(x)) x y t at hc
    change ∀ i j, i≠j → edge4 (1) (1) (1) (profile4 x y t (u i)) (profile4 x y t (u j)) x y t=0 at he
    simp only [ex] at hc he tx ty
    apply exclude_field_3 y t (by linear_combination (1)*G0) t1 tx ty (by simpa using t0) u hu hc he
  apply G0
  linear_combination (1)*h1

private lemma no_0001010220 (x y t : ℝ) (H : admissible ![0,0,0,1,0,1,0,2,2,0] x y) (E : hasExtension ![0,0,0,1,0,1,0,2,2,0] x y t)
    (t1 : t-1≠0) (tx : t-x≠0) (ty : t-y≠0) (t0 : t≠0) : False := by
  obtain ⟨h0,h1⟩ := shape_0001010220 x y H
  by_cases G0 : y^2 - 4*y + 1=0
  · have ex : x=2 := by linear_combination (1)*h0
    obtain ⟨u,hu,hc,he⟩ := E
    change ∀ i, cell (1) (1) (1) (profile4 x y t (u i)) ((1),(x),(y)) ((x),(1),(y)) x y t at hc
    change ∀ i j, i≠j → edge4 (1) (1) (1) (profile4 x y t (u i)) (profile4 x y t (u j)) x y t=0 at he
    simp only [ex] at hc he tx ty
    apply exclude_field_4 y t (by linear_combination (1)*G0) t1 tx ty (by simpa using t0) u hu hc he
  apply G0
  linear_combination (1)*h1

end Erdos1082Ten

open Erdos1082Ten EuclideanGeometry

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H4_R1.H1 := by
  intro A hn hA hd M hm B hBA hB hf hthree p r c hc hh
  obtain ⟨x,y,t,H,E,t1,tx,ty,t0⟩ := given_extension A B M hm hBA hA hB hd hthree hn hf p r c hc
  change colorCode c∈([401,824,834]:List ℕ) at hh
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with eq|eq|eq
  · have cc : c=![0,0,0,0,1,1,2,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact no_0000112212 x y t H E t1 tx ty t0
  · have cc : c=![0,0,0,1,0,1,0,1,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact no_0001010112 x y t H E t1 tx ty t0
  · have cc : c=![0,0,0,1,0,1,0,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact no_0001010220 x y t H E t1 tx ty t0
