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
private lemma base_0001011121 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : -x^2 + x*y - 2*y + (1:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 3*x^2≠0) (_n14 : 4*x*y - y^2≠0) : (x - y/(2:ℝ)=0) ∧ (y^2 - 8*y + (4:ℝ)=0) := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y + 2*y - (1:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : 2*x - y=0 := by linear_combination (-x/6 + y/6 - 5/6)*h1 + (x/3 - y/6 - 1/2)*h2 + (1/3 - x/6)*h3
  have h5 : y^2 - 8*y + (4:ℝ)=0 := by linear_combination (-x/2 + y/2 - 3/2)*h1 + (x - y/2 - 7/2)*h2 + (2 - x/2)*h3
  have h6 : x - y/(2:ℝ)=0 := by linear_combination (1/2)*h4
  have h7 : y^2 - 8*y + (4:ℝ)=0 := by linear_combination (1)*h5
  exact ⟨h6, h7⟩



private lemma shape_0001011121 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,1,1,2,1] x y) : (x - y/2=0) ∧ (y^2 - 8*y + 4=0) := by
  apply base_0001011121 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x x x y x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x y x x y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
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
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma base_0011101022 (x y : ℝ) (g0 : 4*x^3 - 8*x^2=0) (g1 : 3*x^3 - 2*x^2*y - 6*x^2 + 4*x*y=0) (g2 : 2*x^3 - 4*x^2 - 6*x*y + 2*x + 2*y^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x*y - y^2≠0) (n11 : -x^2 + 4*x≠0) (_n12 : 4*x*y - y^2≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : (x - (2:ℝ)=0) ∧ (y^2 - 6*y + (2:ℝ)=0) := by
  have h2 : x≠0 := by
    intro he
    apply n11
    linear_combination (4 - x)*he
  have h3 : ((x) * (x))*(x - 2)=0 := by linear_combination (1/4)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 h2)
  have h5 : ((x))*(x^2 - 2*x*y/3 - 2*x + 4*y/3)=0 := by linear_combination (1/3)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^3 - 2*x^2 - 3*x*y + x + y^2=0 := by linear_combination (1/2)*g2
  have h7 : y^2 - 6*y + (2:ℝ)=0 := by linear_combination (-x^2 + 3*y - 1)*h1 + (1)*h6
  exact ⟨h1, h7⟩



private lemma base_0011102200 (x y : ℝ) (g0 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : 4*x^3 - 2*x^2*y - 7*x^2 + x*y^2 - 2*x*y + 5*x - 2*y^2 + 4*y - (2:ℝ)=0) (g2 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -y^2 + 4*y≠0) (n14 : -y^2 + 4*y≠0) : (x - 184*y^4/9075 + 1268*y^3/3025 - 23479*y^2/9075 + 11598*y/3025 - 4513/(3025:ℝ)=0) ∧ (y^5 - 45*y^4/2 + 335*y^3/2 - 465*y^2 + 945*y/2 - 243/(2:ℝ)=0) := by
  have h1 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g0
  have h2 : x^3 - x^2*y/2 - 7*x^2/4 + x*y^2/4 - x*y/2 + 5*x/4 - y^2/2 + y - 1/(2:ℝ)=0 := by linear_combination (1/4)*g1
  have h3 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g2
  have h4 : x - 991*y^7/7840800 + 34681*y^6/15681600 - 21551*y^5/1960200 + 371563*y^4/15681600 - 387413*y^3/15681600 - 161389*y^2/163350 + 1160389*y/580800 - (1:ℝ)=0 := by linear_combination (991*x^2*y^3/980100 + 551*x^2*y^2/217800 + 1141*x^2*y/49005 + 189967*x^2/1960200 - 991*x*y^4/1960200 + 4951*x*y^3/3920400 - 379*x*y^2/71280 + 36251*x*y/3920400 + 971633*x/3920400 - 991*y^4/490050 + 8911*y^3/1960200 - 56627*y^2/3920400 + 305*y/13068 + 3875633/3920400)*h2 + (-991*x^2*y^3/980100 - 551*x^2*y^2/217800 - 1141*x^2*y/49005 - 189967*x^2/1960200 + 991*x*y^4/1960200 - x*y^3/990 + 46649*x*y^2/7840800 - 37*x*y/10800 - 64937*x/290400 - 991*y^5/3920400 + 1351*y^4/712800 - 1667*y^3/178200 + 1201*y^2/980100 + 50101*y/2613600 - 3965167/3920400)*h3
  have h5 : y^8 - 49*y^7/2 + 427*y^6/2 - 1645*y^5/2 + 1570*y^4 - 3063*y^3/2 + 1431*y^2/2 - 243*y/(2:ℝ)=0 := by linear_combination (-8*x^2*y^4 + 36*x^2*y^3 - 76*x^2*y^2 + 92*x^2*y - 108*x^2 + 4*x*y^5 - 38*x*y^4 + 128*x*y^3 - 232*x*y^2 + 212*x*y + 54*x + 16*y^5 - 148*y^4 + 430*y^3 - 426*y^2 + 74*y + 54)*h2 + (8*x^2*y^4 - 36*x^2*y^3 + 76*x^2*y^2 - 92*x^2*y + 108*x^2 - 4*x*y^5 + 36*x*y^4 - 119*x*y^3 + 213*x*y^2 - 189*x*y - 81*x + 2*y^6 - 29*y^5 + 187*y^4 - 500*y^3 + 519*y^2 - 169*y + 54)*h3
  have h7 : y≠0 := by
    intro he
    apply n14
    linear_combination (4 - y)*he
  have h8 : y - (1:ℝ)≠0 := by
    intro he
    apply n3
    linear_combination (1)*he
  have h9 : ((y) * (y - 1) * (y - 1))*(y^5 - 45*y^4/2 + 335*y^3/2 - 465*y^2 + 945*y/2 - 243/2)=0 := by linear_combination (1)*h5
  have h6 := (mul_eq_zero.mp h9).resolve_left (mul_ne_zero (mul_ne_zero h7 h8) h8)
  have h10 : x - 184*y^4/9075 + 1268*y^3/3025 - 23479*y^2/9075 + 11598*y/3025 - 4513/(3025:ℝ)=0 := by linear_combination (1)*h4 + (991*y^2/7840800 + 4957*y/7840800 + 992/245025)*h6
  exact ⟨h10, h6⟩



private lemma shape_0011101022 (x y : ℝ) (ha : admissible ![0,0,1,1,1,0,1,0,2,2] x y) : (x - 2=0) ∧ (y^2 - 6*y + 2=0) := by
  apply base_0011101022 x y
  · have hg : gram 1 1 x x 1 1 x 1 1 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 1 x x y y=0 := ha.2.2.2.1
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 3 (by decide) (by decide)
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
  · have hn : area x 1 1≠0 := ha.2.1 1 2 3 (by decide) (by decide)
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
  · have hn : area 1 y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0011102200 (x y : ℝ) (ha : admissible ![0,0,1,1,1,0,2,2,0,0] x y) : (x - 184*y^4/9075 + 1268*y^3/3025 - 23479*y^2/9075 + 11598*y/3025 - 4513/3025=0) ∧ (y^5 - 45*y^4/2 + 335*y^3/2 - 465*y^2 + 945*y/2 - 243/2=0) := by
  apply base_0011102200 x y
  · have hg : gram 1 1 x x 1 y x 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 y x y 1 1=0 := ha.2.2.2.1
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
  · have hn : area x x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
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
  · have hn : area 1 y 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring

private lemma cell_6_0 (z t : ℝ) (_hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_6_1 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/8 - 3/4)*h0 + (-1/8)*hf
  norm_num at hh

private lemma cell_6_2 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (10*z - 8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (5*z/88 - 9/22)*h0 + (-25/44)*hf
  norm_num at hh

private lemma cell_6_3 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z - 112) + t^6*(384*z + 96) + t^5*(816 - 1680*z) + t^4*(2736*z - 1872) + t^3*(1800*z - 720) + t^2*(6480 - 11880*z) + t*(11232*z - 6048):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(5/648 - z/1296) - t^5/27 + t^4*(7*z/216 + 1/108) + t^3*(7/72 - 5*z/48) + t^2*(z/24 - 1/12) + t*(z/3 - 1/4) - 11*z/24 + 1/12)*h0 + (z/10368 - 5/5184)*h1 + (t^7/324 - t^6/27 + 35*t^5/216 - 19*t^4/72 - 25*t^3/144 + 55*t^2/48 - 13*t/12)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_6_4 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/8 - 3/4)*h0 + (-1/8)*hf
  norm_num at hh

private lemma cell_6_5 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h1 : (t*(5184*z - 2592):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (5/864 - z/1296)*h1 + (4*t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_6_6 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z/16 - 11/8)*h0 + (-9/8)*hf
  norm_num at hh

private lemma cell_6_7 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-z - 4) + 2*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 48) + t^6*(968*z - 496) + t^5*(3584 - 6072*z) + t^4*(17968*z - 9840) + t^3*(9904 - 19256*z) + t^2*(5296 - 9528*z) + t*(26672*z - 14112) - 8128*z + 4352:ℝ)=0) : (t - 2:ℝ)=0 := by
  have hh : (t - 2:ℝ)=0 := by linear_combination (t^6*(97/324 - 13*z/324) + t^5*(25*z/216 - 31/36) + t^4*(2*z/9 - 91/54) + t^3*(227/81 - 235*z/648) + t^2*(10/3 - 49*z/108) + t*(5*z/24 - 185/108) + 89*z/324 - 173/81)*h0 + (13*z/2592 - 97/2592)*h1 + (91*t^7/324 - 3019*t^6/648 + 274*t^5/9 - 58919*t^4/648 + 31379*t^3/324 + 3521*t^2/72 - 10847*t/81 + 6515/162)*hf
  exact hh

private lemma cell_6_8 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (10*z - 8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (5*z/88 - 9/22)*h0 + (-25/44)*hf
  norm_num at hh

private lemma cell_6_9 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z/16 - 11/8)*h0 + (-9/8)*hf
  norm_num at hh

private lemma cell_6_10 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (8*z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z/23 - 29/46)*h0 + (-16/23)*hf
  norm_num at hh

private lemma cell_6_11 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-96*z - 48) + t^6*(2256*z - 1104) + t^5*(14400 - 26352*z) + t^4*(187632*z - 100944) + t^3*(450144 - 840456*z) + t^2*(2300400*z - 1232496) + t*(1870128 - 3489480*z) + 2220048*z - 1189728:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(139687/182736 - 37429*z/365472) + t^6*(28573*z/45684 - 426545/91368) + t^5*(276953/60912 - 8245*z/13536) + t^4*(830909/60912 - 222679*z/121824) + t^3*(2956*z/1269 - 176399/10152) + t^2*(24751*z/13536 - 92573/6768) + t*(41365/3384 - 5521*z/3384) - 85*z/94 + 3799/564)*h0 + (t*(37429*z/2923776 - 139687/1461888) - 90865*z/2923776 + 339113/1461888)*h1 + (187145*t^8/182736 - 5369521*t^7/182736 + 24287803*t^6/60912 - 195972295*t^5/60912 + 14357081*t^4/864 - 250834477*t^3/4512 + 1572036565*t^2/13536 - 617459603*t/4512 + 51892075/752)*hf
  norm_num at hh

private lemma cell_6_12 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z - 112) + t^6*(384*z + 96) + t^5*(816 - 1680*z) + t^4*(2736*z - 1872) + t^3*(1800*z - 720) + t^2*(6480 - 11880*z) + t*(11232*z - 6048):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(5/648 - z/1296) - t^5/27 + t^4*(7*z/216 + 1/108) + t^3*(7/72 - 5*z/48) + t^2*(z/24 - 1/12) + t*(z/3 - 1/4) - 11*z/24 + 1/12)*h0 + (z/10368 - 5/5184)*h1 + (t^7/324 - t^6/27 + 35*t^5/216 - 19*t^4/72 - 25*t^3/144 + 55*t^2/48 - 13*t/12)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_6_13 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-z - 4) + 2*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 48) + t^6*(968*z - 496) + t^5*(3584 - 6072*z) + t^4*(17968*z - 9840) + t^3*(9904 - 19256*z) + t^2*(5296 - 9528*z) + t*(26672*z - 14112) - 8128*z + 4352:ℝ)=0) : (t - 2:ℝ)=0 := by
  have hh : (t - 2:ℝ)=0 := by linear_combination (t^6*(97/324 - 13*z/324) + t^5*(25*z/216 - 31/36) + t^4*(2*z/9 - 91/54) + t^3*(227/81 - 235*z/648) + t^2*(10/3 - 49*z/108) + t*(5*z/24 - 185/108) + 89*z/324 - 173/81)*h0 + (13*z/2592 - 97/2592)*h1 + (91*t^7/324 - 3019*t^6/648 + 274*t^5/9 - 58919*t^4/648 + 31379*t^3/324 + 3521*t^2/72 - 10847*t/81 + 6515/162)*hf
  exact hh

private lemma cell_6_14 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-96*z - 48) + t^6*(2256*z - 1104) + t^5*(14400 - 26352*z) + t^4*(187632*z - 100944) + t^3*(450144 - 840456*z) + t^2*(2300400*z - 1232496) + t*(1870128 - 3489480*z) + 2220048*z - 1189728:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(139687/182736 - 37429*z/365472) + t^6*(28573*z/45684 - 426545/91368) + t^5*(276953/60912 - 8245*z/13536) + t^4*(830909/60912 - 222679*z/121824) + t^3*(2956*z/1269 - 176399/10152) + t^2*(24751*z/13536 - 92573/6768) + t*(41365/3384 - 5521*z/3384) - 85*z/94 + 3799/564)*h0 + (t*(37429*z/2923776 - 139687/1461888) - 90865*z/2923776 + 339113/1461888)*h1 + (187145*t^8/182736 - 5369521*t^7/182736 + 24287803*t^6/60912 - 195972295*t^5/60912 + 14357081*t^4/864 - 250834477*t^3/4512 + 1572036565*t^2/13536 - 617459603*t/4512 + 51892075/752)*hf
  norm_num at hh

private lemma cell_6_15 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 48) + t^6*(968*z - 496) + t^5*(3584 - 6072*z) + t^4*(17968*z - 9840) + t^3*(9904 - 19256*z) + t^2*(5296 - 9528*z) + t*(26672*z - 14112) - 8128*z + 4352:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(145/2916 - 13*z/1944) + t^6*(65*z/1944 - 355/1458) + t^5*(1/81 - 23*z/1944) + t^4*(725/729 - 47*z/648) + t^3*(-253*z/1944 - 835/2916) + t^2*(673*z/1944 - 481/324) + t*(119*z/972 + 185/1458) - z/3 + 1049/1458)*h0 + (t*(13*z/15552 - 145/23328) - 73*z/23328 + 181/7776)*h1 + (13*t^8/243 - 5887*t^7/5832 + 47267*t^6/5832 - 8267*t^5/243 + 421789*t^4/5832 - 304973*t^3/5832 - 469*t^2/9 + 131597*t/1458 - 18542/729)*hf
  norm_num at hh

private lemma cell_6_16 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/8 - 3/4)*h0 + (-1/8)*hf
  norm_num at hh

private lemma cell_6_17 (z t : ℝ) (_hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) : ((0:ℝ):ℝ)=0 := by
  rfl

private lemma cell_6_18 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z/16 - 11/8)*h0 + (-9/8)*hf
  norm_num at hh

private lemma cell_6_19 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-z - 4) + 2*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 48) + t^6*(1160*z - 496) + t^5*(5888 - 11112*z) + t^4*(69376*z - 37200) + t^3*(156208 - 291320*z) + t^2*(801480*z - 429584) + t*(705024 - 1315552*z) + 978032*z - 524128:ℝ)=0) : False := by
  have hh : ((t-(z/2)))*(1:ℝ)=0 := by linear_combination (t^6*(71/1944 - 19*z/3888) + t^5*(z/72 - 17/162) + t^4*(1/36 - z/648) + t^3*(-53*z/3888 - 41/1944) + t^2*(11*z/108 - 29/162) + t*(5/108 - 37*z/162) + 187*z/486 - 113/243)*h0 + (19*z/31104 - 71/15552)*h1 + (133*t^7/3888 - 2663*t^6/3888 + 8759*t^5/1296 - 164809*t^4/3888 + 692387*t^3/3888 - 635065*t^2/1296 + 781927*t/972 - 1162909/1944)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_6_20 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h2 : (t*(85536 - 159408*z) + 2220048*z - 1189728:ℝ)=0) : (t - 2*z + 1:ℝ)=0 := by
  have hh : (t - 2*z + 1:ℝ)=0 := by linear_combination (17/1728 - 41*z/31104)*h2 + (23411/8 - 1681*t/8)*hf
  exact hh

private lemma cell_6_21 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 3*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (11/4 - 3*z/8)*h0 + (-9/8)*hf
  norm_num at hh

private lemma cell_6_22 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h2 : (t*(5184*z - 2592):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (5/864 - z/1296)*h2 + (4*t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_6_23 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 2) + 2*z:ℝ)=0) (h2 : (16*t^8 + t^7*(-128*z - 48) + t^6*(3800*z - 1840) + t^5*(29968 - 55560*z) + t^4*(482104*z - 258912) + t^3*(1370720 - 2557960*z) + t^2*(8095296*z - 4337888) + t*(7485024 - 13967072*z) + 10060160*z - 5391232:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(41/11664 - 11*z/23328) + t^6*(85*z/5832 - 211/1944) + t^5*(14/27 - 91*z/1296) + t^4*(101*z/2916 - 281/1458) + t^3*(4015*z/23328 - 2231/1296) + t^2*(19*z/108 + 203/648) + t*(14095/5832 - 8683*z/11664) + 1141*z/5832 + 221/243)*h0 + (t*(11*z/186624 - 41/93312) - 23*z/15552 + 515/46656)*h2 + (77*t^8/11664 - 8939*t^7/23328 + 203539*t^6/23328 - 2574821*t^5/23328 + 20156197*t^4/23328 - 49690237*t^3/11664 + 37306187*t^2/2916 - 123913211*t/5832 + 43383299/2916)*hf
  norm_num at hh

private lemma cell_6_24 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z/16 - 11/8)*h0 + (-9/8)*hf
  norm_num at hh

private lemma cell_6_25 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h2 : (t*(85536 - 159408*z) + 2220048*z - 1189728:ℝ)=0) : (t - 2*z + 1:ℝ)=0 := by
  have hh : (t - 2*z + 1:ℝ)=0 := by linear_combination (17/1728 - 41*z/31104)*h2 + (23411/8 - 1681*t/8)*hf
  exact hh

private lemma cell_6_26 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 2)*h0 + (1/4)*hf
  norm_num at hh

private lemma cell_6_27 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-3*z - 2) + 9*z - 4:ℝ)=0) (h2 : (16*t^8 + t^7*(-160*z - 48) + t^6*(5984*z - 2896) + t^5*(61472 - 114720*z) + t^4*(1351648*z - 724944) + t^3*(5409856 - 10094552*z) + t^2*(46658784*z - 25004048) + t*(65355984 - 121955896*z) + 137911088*z - 73906336:ℝ)=0) : (t - z - 1:ℝ)=0 := by
  have hh : (t - z - 1:ℝ)=0 := by linear_combination (t^6*(989/1944 - 265*z/3888) + t^5*(193*z/432 - 2161/648) + t^4*(395/108 - 317*z/648) + t^3*(15121/1944 - 4097*z/3888) + t^2*(421*z/432 - 4249/648) + t*(439*z/648 - 223/27) + 601*z/486 - 731/243)*h0 + (265*z/31104 - 989/15552)*h2 + (4505*t^7/3888 - 11914*t^6/243 + 1259587*t^5/1296 - 44768513*t^4/3888 + 334430275*t^3/3888 - 515199473*t^2/1296 + 4039779773*t/3888 - 2284174031/1944)*hf
  exact hh

private lemma cell_6_28 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-z - 4) + 2*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 48) + t^6*(1160*z - 496) + t^5*(5888 - 11112*z) + t^4*(69376*z - 37200) + t^3*(156208 - 291320*z) + t^2*(801480*z - 429584) + t*(705024 - 1315552*z) + 978032*z - 524128:ℝ)=0) (h2 : (16*t^8 - 112*t^7 + t^6*(216*z + 64) + t^5*(752 - 1080*z) + t^4*(8136*z - 4832) + t^3*(11216 - 21024*z) + t^2*(101520*z - 54128) + t*(66992 - 124920*z) + 391104*z - 209600:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(13775*z/3779136 - 51409/1889568) + t^12*(246961/944784 - 66173*z/1889568) + t^11*(45281*z/419904 - 168991/209952) + t^10*(256463/472392 - 68719*z/944784) + t^9*(352495/236196 - 94451*z/472392) + t^8*(22855*z/69984 - 85295/34992) + t^7*(261673/629856 - 70145*z/1259712) + t^6*(343793/314928 - 23011*z/157464) + t^5*(12533/69984 - 3427*z/139968) + t^4*(343033/944784 - 44491*z/944784) + t^3*(1104829*z/1889568 - 2072779/472392) + t^2*(14707*z/209952 - 55079/104976) + t*(810829/236196 - 207347*z/472392) - 15472*z/59049 + 86566/59049)*h0 + (t^7*(51409/15116544 - 13775*z/30233088) + t^6*(46367*z/15116544 - 43261/1889568) + t^5*(161609/5038848 - 43303*z/10077696) + t^4*(686507/15116544 - 183949*z/30233088) + t^3*(178507*z/15116544 - 666197/7558272) + t^2*(46445*z/10077696 - 173335/5038848) + t*(23399/472392 - 100315*z/15116544) - 11839*z/3779136 + 22093/944784)*h1 + (65/1296 - 209*z/31104)*h2 + (-96425*t^14/3779136 + 2579351*t^13/3779136 - 8236739*t^12/944784 + 264539605*t^11/3779136 - 1456926613*t^10/3779136 + 1395028927*t^9/944784 - 4739932447*t^8/1259712 + 6791914081*t^7/1259712 - 228085051*t^6/314928 - 43480087529*t^5/3779136 + 60962602403*t^4/3779136 - 72194270*t^3/59049 - 18981089599*t^2/1889568 + 361448201*t/236196 + 1344525043/236196)*hf
  norm_num at hh

private lemma cell_6_29 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 2) + 2*z:ℝ)=0) (h2 : (16*t^8 + t^7*(-32*z - 48) + t^6*(320*z - 208) + t^5*(1024 - 1344*z) + t^4*(2896*z - 1584) + t^3*(608 - 1912*z) + t^2*(3280 - 6000*z) + t*(14200*z - 7440) - 8128*z + 4352:ℝ)=0) : False := by
  have hh : ((t-(1)))*(1:ℝ)=0 := by linear_combination (t^6*(17/216 - 41*z/3888) + t^5*(13*z/486 - 97/486) + t^4*(275*z/3888 - 1027/1944) + t^3*(1535/1944 - 137*z/1296) + t^2*(1301/972 - 349*z/1944) + t*(211*z/3888 - 809/1944) + 253*z/1944 - 503/486)*h0 + (41*z/31104 - 17/1728)*h2 + (41*t^7/1944 - 25*t^6/72 + 1205*t^5/648 - 8107*t^4/1944 + 1025*t^3/432 + 1357*t^2/162 - 72185*t/3888 + 1129/108)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn0
  norm_num at hv

private lemma cell_6_30 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-3*z - 2) + 9*z - 4:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z - 48) + t^6*(968*z - 496) + t^5*(3584 - 6072*z) + t^4*(17968*z - 9840) + t^3*(9904 - 19256*z) + t^2*(5296 - 9528*z) + t*(26672*z - 14112) - 8128*z + 4352:ℝ)=0) : (t - z - 1:ℝ)=0 := by
  have hh : (t - z - 1:ℝ)=0 := by linear_combination (t^6*(71/324 - 19*z/648) + t^5*(7*z/72 - 79/108) + t^4*(11*z/72 - 119/108) + t^3*(461/162 - 127*z/324) + t^2*(145/54 - 13*z/36) + t*(5*z/18 - 109/54) + 85*z/324 - 172/81)*h0 + (19*z/5184 - 71/2592)*h2 + (95*t^7/648 - 1939*t^6/648 + 4717*t^5/216 - 44327*t^4/648 + 47317*t^3/648 + 8425*t^2/216 - 8057*t/81 + 8887/324)*hf
  exact hh

private lemma cell_6_31 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 3*z:ℝ)=0) (h1 : (16*t^8 + t^7*(80 - 128*z) + t^6*(2904*z - 1680) + t^5*(19104 - 35736*z) + t^4*(260928*z - 139536) + t^3*(613296 - 1144440*z) + t^2*(2933064*z - 1572048) + t*(2146176 - 4004640*z) + 2220048*z - 1189728:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(3161/972 - 847*z/1944) + t^6*(1139/324 - 305*z/648) + t^5*(2069*z/648 - 7735/324) + t^4*(68*z/27 - 497/27) + t^3*(160/3 - 89*z/12) + t^2*(319/18 - 29*z/18) + t*(73*z/18 - 344/9) - z/12 + 14/3)*h0 + (t*(847*z/15552 - 3161/7776) - 17*z/144 + 571/648)*h1 + (5929*t^8/972 - 56021*t^7/324 + 186049*t^6/81 - 1327259*t^5/72 + 20111893*t^4/216 - 21227783*t^3/72 + 10158839*t^2/18 - 7124299*t/12 + 1048357/4)*hf
  norm_num at hh

private lemma cell_6_32 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (10*z - 8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (5*z/88 - 9/22)*h0 + (-25/44)*hf
  norm_num at hh

private lemma cell_6_33 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z/16 - 11/8)*h0 + (-9/8)*hf
  norm_num at hh

private lemma cell_6_34 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (8*z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z/23 - 29/46)*h0 + (-16/23)*hf
  norm_num at hh

private lemma cell_6_35 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-96*z - 48) + t^6*(2736*z - 1296) + t^5*(23472 - 43848*z) + t^4*(483120*z - 259056) + t^3*(2000592 - 3732912*z) + t^2*(20005488*z - 10720944) + t*(36483696 - 68079528*z) + 121465008*z - 65092896:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(846541/983664 - 37805*z/327888) + t^6*(694013*z/983664 - 1295045/245916) + t^5*(947131/109296 - 190339*z/163944) + t^4*(55447*z/655776 - 103285/163944) + t^3*(21961*z/19872 - 82061/9936) + t^2*(56939/9108 - 60419*z/72864) + t*(995*z/6624 - 4501/3312) + 2201*z/12144 - 1913/2024)*h0 + (t*(37805*z/2623104 - 846541/7869312) - 276703*z/7869312 + 2065339/7869312)*h1 + (189025*t^8/163944 - 2459960*t^7/61479 + 78405313*t^6/109296 - 695989187*t^5/81972 + 7736921897*t^4/109296 - 15286795277*t^3/36432 + 10229088643*t^2/6072 - 50329899461*t/12144 + 8644474021/2024)*hf
  norm_num at hh

private lemma cell_6_36 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z/16 - 11/8)*h0 + (-9/8)*hf
  norm_num at hh

private lemma cell_6_37 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t*(85536 - 159408*z) + 2220048*z - 1189728:ℝ)=0) : (t - 2*z + 1:ℝ)=0 := by
  have hh : (t - 2*z + 1:ℝ)=0 := by linear_combination (17/1728 - 41*z/31104)*h1 + (23411/8 - 1681*t/8)*hf
  exact hh

private lemma cell_6_38 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 2)*h0 + (1/4)*hf
  norm_num at hh

private lemma cell_6_39 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-3*z - 2) + 9*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 128*z) + t^6*(3640*z - 2016) + t^5*(31184 - 57720*z) + t^4*(593720*z - 318112) + t^3*(2170416 - 4050688*z) + t^2*(17893392*z - 9589040) + t*(25106800 - 46849688*z) + 55861264*z - 29935968:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(181/2916 - 97*z/11664) + t^6*(797*z/11664 - 1487/2916) + t^5*(85/486 - 23*z/972) + t^4*(18703/5832 - 311*z/729) + t^3*(661*z/11664 - 445/729) + t^2*(1673*z/1944 - 2651/486) + t*(-2021*z/5832 - 457/1458) + 469*z/1458 + 1054/729)*h0 + (t*(97*z/93312 - 181/23328) - 653*z/93312 + 2437/46656)*h1 + (1261*t^8/11664 - 51319*t^7/11664 + 988969*t^6/11664 - 5961347*t^5/5832 + 48811877*t^4/5832 - 547570621*t^3/11664 + 2028498121*t^2/11664 - 4501375975*t/11664 + 2279820953/5832)*hf
  norm_num at hh

private lemma cell_6_40 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (8*z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z/23 - 29/46)*h0 + (-16/23)*hf
  norm_num at hh

private lemma cell_6_41 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/4 - 2)*h0 + (1/4)*hf
  norm_num at hh

private lemma cell_6_42 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 6*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3*z/26 - 23/26)*h0 + (9/13)*hf
  norm_num at hh

private lemma cell_6_43 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 160*z) + t^6*(5376*z - 2880) + t^5*(51312 - 95304*z) + t^4*(1034856*z - 554688) + t^3*(3779424 - 7052904*z) + t^2*(29440584*z - 15777072) + t*(36861696 - 68784768*z) + 68846112*z - 36894528:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(1087*z/2673 - 601/198) + t^6*(3851/297 - 6191*z/3564) + t^5*(637/594 - 259*z/1782) + t^4*(3635*z/594 - 4505/99) + t^3*(148/9 - 43*z/18) + t^2*(25273/594 - 5729*z/1188) + t*(-73*z/99 - 743/66) + 134*z/33 - 823/66)*h0 + (t*(601/1584 - 1087*z/21384) + 8629*z/85536 - 8051/10692)*h1 + (-17392*t^8/2673 + 741992*t^7/2673 - 177098*t^6/33 + 221840627*t^5/3564 - 550040245*t^4/1188 + 238469659*t^3/108 - 284523803*t^2/44 + 1033436116*t/99 - 229196477/33)*hf
  norm_num at hh

private lemma cell_6_44 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-96*z - 48) + t^6*(2736*z - 1296) + t^5*(23472 - 43848*z) + t^4*(483120*z - 259056) + t^3*(2000592 - 3732912*z) + t^2*(20005488*z - 10720944) + t*(36483696 - 68079528*z) + 121465008*z - 65092896:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(846541/983664 - 37805*z/327888) + t^6*(694013*z/983664 - 1295045/245916) + t^5*(947131/109296 - 190339*z/163944) + t^4*(55447*z/655776 - 103285/163944) + t^3*(21961*z/19872 - 82061/9936) + t^2*(56939/9108 - 60419*z/72864) + t*(995*z/6624 - 4501/3312) + 2201*z/12144 - 1913/2024)*h0 + (t*(37805*z/2623104 - 846541/7869312) - 276703*z/7869312 + 2065339/7869312)*h1 + (189025*t^8/163944 - 2459960*t^7/61479 + 78405313*t^6/109296 - 695989187*t^5/81972 + 7736921897*t^4/109296 - 15286795277*t^3/36432 + 10229088643*t^2/6072 - 50329899461*t/12144 + 8644474021/2024)*hf
  norm_num at hh

private lemma cell_6_45 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-3*z - 2) + 9*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 128*z) + t^6*(3640*z - 2016) + t^5*(31184 - 57720*z) + t^4*(593720*z - 318112) + t^3*(2170416 - 4050688*z) + t^2*(17893392*z - 9589040) + t*(25106800 - 46849688*z) + 55861264*z - 29935968:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(181/2916 - 97*z/11664) + t^6*(797*z/11664 - 1487/2916) + t^5*(85/486 - 23*z/972) + t^4*(18703/5832 - 311*z/729) + t^3*(661*z/11664 - 445/729) + t^2*(1673*z/1944 - 2651/486) + t*(-2021*z/5832 - 457/1458) + 469*z/1458 + 1054/729)*h0 + (t*(97*z/93312 - 181/23328) - 653*z/93312 + 2437/46656)*h1 + (1261*t^8/11664 - 51319*t^7/11664 + 988969*t^6/11664 - 5961347*t^5/5832 + 48811877*t^4/5832 - 547570621*t^3/11664 + 2028498121*t^2/11664 - 4501375975*t/11664 + 2279820953/5832)*hf
  norm_num at hh

private lemma cell_6_46 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(16 - 160*z) + t^6*(5376*z - 2880) + t^5*(51312 - 95304*z) + t^4*(1034856*z - 554688) + t^3*(3779424 - 7052904*z) + t^2*(29440584*z - 15777072) + t*(36861696 - 68784768*z) + 68846112*z - 36894528:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(1087*z/2673 - 601/198) + t^6*(3851/297 - 6191*z/3564) + t^5*(637/594 - 259*z/1782) + t^4*(3635*z/594 - 4505/99) + t^3*(148/9 - 43*z/18) + t^2*(25273/594 - 5729*z/1188) + t*(-73*z/99 - 743/66) + 134*z/33 - 823/66)*h0 + (t*(601/1584 - 1087*z/21384) + 8629*z/85536 - 8051/10692)*h1 + (-17392*t^8/2673 + 741992*t^7/2673 - 177098*t^6/33 + 221840627*t^5/3564 - 550040245*t^4/1188 + 238469659*t^3/108 - 284523803*t^2/44 + 1033436116*t/99 - 229196477/33)*hf
  norm_num at hh

private lemma cell_6_47 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 14*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(80 - 192*z) + t^6*(7080*z - 3920) + t^5*(76496 - 142488*z) + t^4*(1752744*z - 939008) + t^3*(7213472 - 13461000*z) + t^2*(63018288*z - 33771584) + t*(88150976 - 164491680*z) + 183417216*z - 98292992:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(20173/128304 - 5405*z/256608) + t^6*(3173*z/128304 - 11887/64152) + t^5*(7519*z/42768 - 13807/10692) + t^4*(8306/8019 - 1472*z/8019) + t^3*(9467*z/256608 + 363659/128304) + t^2*(-94181*z/42768 - 8885/21384) + t*(59630*z/8019 - 98341/16038) - 141749*z/16038 + 87839/16038)*h0 + (t*(5405*z/2052864 - 20173/1026432) - 15241*z/2052864 + 56885/1026432)*h1 + (27025*t^8/64152 - 5048155*t^7/256608 + 3432761*t^6/8019 - 182059391*t^5/32076 + 565203721*t^4/11664 - 68224011337*t^3/256608 + 115603975535*t^2/128304 - 109333563649*t/64152 + 21841529713/16038)*hf
  norm_num at hh

private lemma cell_6_48 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 6*t:ℝ)=0) (h2 : (16*t^8 + t^7*(32*z - 176) + t^6*(528 - 48*z) + t^5*(168*z - 528) - 432*t^4 + t^3*(720 - 288*z) + t^2*(1296 - 2160*z) + t*(2160 - 4104*z):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(13/648 - 7*z/2592) + t^5*(z/54 - 5/36) + t^4*(23/108 - 25*z/864) + t^3*(13/144 - z/72) + t^2*(z/32 - 13/48) - 5*t/48 - z/96 - 7/48)*h0 + (7*z/20736 - 13/5184)*h2 + (-7*t^7/648 + 7*t^6/432 - 49*t^5/864 + 7*t^3/72 + 35*t^2/48 + 133*t/96)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_6_49 (z t : ℝ) (_hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-z - 4) + 2*z:ℝ)=0) : (t - 2:ℝ)=0 := by
  have hh : ((t-(z/2)))*(t - 2:ℝ)=0 := by linear_combination (1/2)*h0
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  exact hv

private lemma cell_6_50 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 - 240*t^7 + t^6*(216*z + 1248) + t^5*(-2376*z - 2448) + t^4*(16344*z - 3744) + t^3*(32400 - 66096*z) + t^2*(214704*z - 114480) + t*(216432 - 403704*z) + 594864*z - 318816:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(683*z/85536 - 2549/42768) + t^6*(65/54 - 209*z/1296) + t^5*(421*z/352 - 127267/14256) + t^4*(431147/14256 - 115525*z/28512) + t^3*(557*z/88 - 18709/396) + t^2*(139541/4752 - 37387*z/9504) + t*(959*z/1584 - 895/198) + 17*z/88 - 47/33)*h0 + (t*(2549/342144 - 683*z/684288) + 5281*z/684288 - 19709/342144)*h1 + (683*t^8/42768 - 1927*t^7/9504 + 343*t^6/1188 + 10865*t^5/891 - 1243369*t^4/9504 + 3044009*t^3/4752 - 6372457*t^2/3168 + 3909793*t/1056 - 73491/16)*hf
  norm_num at hh

private lemma cell_6_51 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(32*z - 240) + t^6*(1280 - 208*z) + t^5*(480*z - 3184) + t^4*(3888 - 560*z) + t^3*(-152*z - 1808) + t^2*(696*z - 176) + t*(672 - 1024*z) + 3296*z - 1792:ℝ)=0) : False := by
  have hh : ((t-(z/2)))*(1:ℝ)=0 := by linear_combination (t^6*(5/972 - z/1944) + t^5*(5*z/648 - 17/324) + t^4*(55/324 - 5*z/216) + t^3*(8*z/243 - 56/243) + t^2*(7/81 - z/162) + t*(-z/108 - 2/81) + 19*z/972 - 37/243)*h0 + (z/15552 - 5/7776)*h1 + (-t^7/486 + 13*t^6/972 - 5*t^5/162 + 35*t^4/972 + 19*t^3/1944 - 29*t^2/648 + 16*t/243 - 103/486)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn1
  norm_num at hv

private lemma cell_6_52 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-z - 4) + 2*z:ℝ)=0) (h2 : (16*t^8 - 112*t^7 + t^6*(216*z + 64) + t^5*(752 - 1080*z) + t^4*(8136*z - 4832) + t^3*(11216 - 21024*z) + t^2*(101520*z - 54128) + t*(66992 - 124920*z) + 391104*z - 209600:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(3775/32076 - 2023*z/128304) + t^6*(4253*z/32076 - 31745/32076) + t^5*(10927/5346 - 11711*z/42768) + t^4*(101245/64152 - 13567*z/64152) + t^3*(97567*z/128304 - 363947/64152) + t^2*(7531*z/42768 - 7055/5346) + t*(110635/32076 - 14695*z/32076) - 563*z/2916 + 4115/2916)*h0 + (t*(2023*z/1026432 - 3775/256608) - 7439*z/1026432 + 27763/513216)*h2 + (-2023*t^8/128304 - 33563*t^7/128304 + 404801*t^6/128304 - 754631*t^5/32076 + 6516871*t^4/64152 - 45394103*t^3/128304 + 125886089*t^2/128304 - 19542511*t/11664 + 22732961/8019)*hf
  norm_num at hh

private lemma cell_6_53 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 2) + 2*z:ℝ)=0) (h1 : (16*t^8 - 176*t^7 + t^6*(688 - 72*z) + t^5*(648*z - 1184) + t^4*(496 - 1152*z) + t^3*(2224 - 2808*z) + t^2*(5832*z - 3152) + t*(3744*z - 2048) - 1008*z + 544:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(1549/5832 - 415*z/11664) + t^6*(4415*z/11664 - 1831/648) + t^5*(9457/972 - 1267*z/972) + t^4*(15785*z/11664 - 58865/5832) + t^3*(10013*z/11664 - 12475/1944) + t^2*(2396/243 - 2581*z/1944) + t*(5995/1458 - 3185*z/5832) - 76*z/729 + 209/243)*h0 + (t*(415*z/93312 - 1549/46656) - 487*z/93312 + 1819/46656)*h1 + (-415*t^8/5832 + 4465*t^7/3888 - 19309*t^6/2916 + 161185*t^5/11664 + 21331*t^4/3888 - 262235*t^3/5832 + 179035*t^2/11664 + 48419*t/1944 - 29465/5832)*hf
  norm_num at hh

private lemma cell_6_54 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-3*z - 2) + 9*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z - 176) + t^6*(544*z + 528) + t^5*(656 - 3864*z) + t^4*(14816*z - 7312) + t^3*(17520 - 31648*z) + t^2*(31344*z - 17072) + t*(1240*z - 656) - 18800*z + 10080:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z - 48) + t^6*(968*z - 496) + t^5*(3584 - 6072*z) + t^4*(17968*z - 9840) + t^3*(9904 - 19256*z) + t^2*(5296 - 9528*z) + t*(26672*z - 14112) - 8128*z + 4352:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(13775/629856 - 3691*z/1259712) + t^12*(55895*z/1259712 - 208603/629856) + t^11*(63109/34992 - 8455*z/34992) + t^10*(302479*z/629856 - 1128869/314928) + t^9*(203671*z/629856 - 760097/314928) + t^8*(210269/11664 - 28171*z/11664) + t^7*(648349*z/419904 - 2419559/209952) + t^6*(1472419*z/419904 - 5495339/209952) + t^5*(30209/1296 - 72845*z/23328) + t^4*(3221969/157464 - 1727255*z/629856) + t^3*(1268281*z/629856 - 4728539/314928) + t^2*(80353*z/69984 - 299777/34992) + t*(108983/39366 - 117349*z/314928) - 8423*z/39366 + 127459/78732)*h0 + (t^7*(3691*z/10077696 - 13775/5038848) + t^6*(33581/2519424 - 4499*z/2519424) + t^5*(71*z/1679616 - 265/839808) + t^4*(76247*z/10077696 - 284557/5038848) + t^3*(6587/314928 - 1765*z/629856) + t^2*(16073/209952 - 17227*z/1679616) + t*(8063*z/5038848 - 30091/2519424) + 23093*z/5038848 - 86185/2519424)*h1 + (7/324 - 5*z/1728)*h2 + (3691*t^14/1259712 - 30517*t^13/314928 + 795995*t^12/629856 - 5348743*t^11/629856 + 19307797*t^10/629856 - 60901775*t^9/1259712 - 3576451*t^8/104976 + 25700431*t^7/104976 - 101587675*t^6/419904 - 313723751*t^5/1259712 + 335490793*t^4/629856 - 9745429*t^3/629856 - 59438989*t^2/157464 + 65686333*t/629856 + 20334091/314928)*hf
  norm_num at hh

private lemma cell_6_55 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 3*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z - 112) + t^6*(384*z + 96) + t^5*(816 - 1680*z) + t^4*(2736*z - 1872) + t^3*(1800*z - 720) + t^2*(6480 - 11880*z) + t*(11232*z - 6048):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(28/81 - 5*z/108) + t^6*(253*z/648 - 35/12) + t^5*(2249/324 - 601*z/648) + t^4*(7*z/72 - 85/108) + t^3*(161*z/108 - 299/27) + t^2*(59/18 - 5*z/12) + t*(79/18 - 23*z/36) - z/12 + 2/3)*h0 + (t*(5*z/864 - 7/162) - 29*z/1728 + 325/2592)*h1 + (5*t^8/54 - 149*t^7/81 + 8515*t^6/648 - 8867*t^5/216 + 8249*t^4/216 + 6743*t^3/72 - 19037*t^2/72 + 761*t/4 + 1/4)*hf
  norm_num at hh

private lemma cell_6_56 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 - 240*t^7 + t^6*(216*z + 1248) + t^5*(-2376*z - 2448) + t^4*(16344*z - 3744) + t^3*(32400 - 66096*z) + t^2*(214704*z - 114480) + t*(216432 - 403704*z) + 594864*z - 318816:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(683*z/85536 - 2549/42768) + t^6*(65/54 - 209*z/1296) + t^5*(421*z/352 - 127267/14256) + t^4*(431147/14256 - 115525*z/28512) + t^3*(557*z/88 - 18709/396) + t^2*(139541/4752 - 37387*z/9504) + t*(959*z/1584 - 895/198) + 17*z/88 - 47/33)*h0 + (t*(2549/342144 - 683*z/684288) + 5281*z/684288 - 19709/342144)*h1 + (683*t^8/42768 - 1927*t^7/9504 + 343*t^6/1188 + 10865*t^5/891 - 1243369*t^4/9504 + 3044009*t^3/4752 - 6372457*t^2/3168 + 3909793*t/1056 - 73491/16)*hf
  norm_num at hh

private lemma cell_6_57 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-3*z - 2) + 9*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z - 176) + t^6*(544*z + 528) + t^5*(656 - 3864*z) + t^4*(14816*z - 7312) + t^3*(17520 - 31648*z) + t^2*(31344*z - 17072) + t*(1240*z - 656) - 18800*z + 10080:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z - 48) + t^6*(1352*z - 688) + t^5*(8624 - 15576*z) + t^4*(125176*z - 67296) + t^3*(380896 - 711272*z) + t^2*(2842752*z - 1523264) + t*(3887712 - 7254400*z) + 10060160*z - 5391232:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(191861/3779136 - 51409*z/7558272) + t^12*(778517*z/7558272 - 2905465/3779136) + t^11*(2664535/629856 - 89245*z/157464) + t^10*(9039779*z/7558272 - 33736915/3779136) + t^9*(333043*z/944784 - 4971731/1889568) + t^8*(15377489/419904 - 4120387*z/839808) + t^7*(5019359*z/1259712 - 4683115/157464) + t^6*(14268019*z/2519424 - 53249375/1259712) + t^5*(19612133/419904 - 5254927*z/839808) + t^4*(25760465/944784 - 13806515*z/3779136) + t^3*(12654313*z/3779136 - 47214557/1889568) + t^2*(946553*z/629856 - 442109/39366) + t*(512167/118098 - 68011*z/118098) - 69263*z/236196 + 498113/236196)*h0 + (t^7*(51409*z/60466176 - 191861/30233088) + t^6*(467723/15116544 - 62663*z/15116544) + t^5*(8371*z/10077696 - 31241/5038848) + t^4*(112873*z/7558272 - 1684991/15116544) + t^3*(1667759/30233088 - 446875*z/60466176) + t^2*(621115/5038848 - 166427*z/10077696) + t*(126803*z/30233088 - 473245/15116544) + 89893*z/15116544 - 335477/7558272)*h1 + (65/1296 - 209*z/31104)*h2 + (51409*t^14/7558272 - 425047*t^13/1889568 + 11108927*t^12/3779136 - 150404639*t^11/7558272 + 555285275*t^10/7558272 - 958713347*t^9/7558272 - 74123449*t^8/2519424 + 1239565999*t^7/2519424 - 735603989*t^6/1259712 - 2965639793*t^5/7558272 + 13122738593*t^4/7558272 - 18391806703*t^3/3779136 + 70232413631*t^2/3779136 - 45982055909*t/944784 + 63973785983/944784)*hf
  norm_num at hh

private lemma cell_6_58 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 2) + 12*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-64*z - 176) + t^6*(1416*z + 240) + t^5*(4944 - 13080*z) + t^4*(63144*z - 32256) + t^3*(87840 - 163656*z) + t^2*(212112*z - 114048) + t*(57024 - 106272*z):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(3637/3159 - 1949*z/12636) + t^6*(12793*z/6318 - 95497/6318) + t^5*(150437/2106 - 20149*z/2106) + t^4*(6821*z/351 - 16988/117) + t^3*(24179/234 - 19337*z/1404) + t^2*(190/9 - 53*z/18) + t*(418*z/117 - 6119/234) - z/3 + 5/2)*h0 + (t*(1949*z/101088 - 3637/25272) - 167*z/4212 + 4987/16848)*h1 + (1949*t^8/3159 - 251305*t^7/12636 + 345047*t^6/1404 - 240785*t^5/156 + 7540337*t^4/1404 - 271045*t^3/26 + 1229497*t^2/117 - 166052*t/39 + 4)*hf
  norm_num at hh

private lemma cell_6_59 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 14*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-96*z - 112) + t^6*(2544*z - 800) + t^5*(16304 - 31752*z) + t^4*(233160*z - 124928) + t^3*(563744 - 1051080*z) + t^2*(2836728*z - 1520336) + t*(2233472 - 4167744*z) + 2532192*z - 1356992:ℝ)=0) (h2 : (16*t^8 + t^7*(-160*z - 48) + t^6*(5984*z - 2896) + t^5*(61472 - 114720*z) + t^4*(1351648*z - 724944) + t^3*(5409856 - 10094552*z) + t^2*(46658784*z - 25004048) + t*(65355984 - 121955896*z) + 137911088*z - 73906336:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(29681*z/7558272 - 110771/3779136) + t^12*(1687555/3779136 - 452179*z/7558272) + t^11*(72199*z/209952 - 808351/314928) + t^10*(24478171/3779136 - 6558907*z/7558272) + t^9*(2150269*z/3779136 - 8024881/1889568) + t^8*(421879*z/279936 - 4723525/419904) + t^7*(11570587/629856 - 3099889*z/1259712) + t^6*(3930893/1259712 - 1060193*z/2519424) + t^5*(550627*z/279936 - 6114979/419904) + t^4*(76871*z/472392 - 1623383/944784) + t^3*(2964881/1889568 - 27533*z/3779136) + t^2*(1019711/314928 - 178001*z/209952) + t*(10894*z/59049 + 152806/59049) - 117713*z/236196 + 124763/118098)*h0 + (t^7*(110771/30233088 - 29681*z/60466176) + t^6*(40025*z/10077696 - 224063/7558272) + t^5*(637229/10077696 - 56915*z/6718464) + t^4*(468877/30233088 - 125635*z/60466176) + t^3*(59761*z/3359232 - 501821/3779136) + t^2*(107333/10077696 - 355*z/248832) + t*(1147345/15116544 - 1201*z/118098) - 16243*z/5038848 + 11371/472392)*h1 + (65/1296 - 209*z/31104)*h2 + (-29681*t^14/944784 + 2524027*t^13/1889568 - 183591247*t^12/7558272 + 1916967281*t^11/7558272 - 6384991747*t^10/3779136 + 56149415237*t^9/7558272 - 6675025507*t^8/314928 + 89457240641*t^7/2519424 - 26074693975*t^6/1259712 - 284965413349*t^5/7558272 + 624278842327*t^4/7558272 - 44105574349*t^3/472392 + 33528529385*t^2/118098 - 762589909033*t/944784 + 55201865263/59049)*hf
  norm_num at hh

private lemma cell_6_60 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h1 : (16*t^8 + t^7*(32*z - 240) + t^6*(1280 - 208*z) + t^5*(480*z - 3184) + t^4*(3888 - 560*z) + t^3*(-152*z - 1808) + t^2*(696*z - 176) + t*(672 - 1024*z) + 3296*z - 1792:ℝ)=0) (h2 : (16*t^8 + t^7*(64*z - 176) + t^6*(232*z + 240) + t^5*(744*z - 496) + t^4*(392*z - 832) + t^3*(1824 - 2824*z) + t^2*(4672 - 8112*z) + t*(640 - 1184*z) + 4288*z - 2304:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(989*z/1889568 - 3691/944784) + t^12*(68345/944784 - 18313*z/1889568) + t^11*(5057*z/69984 - 233/432) + t^10*(242275/118098 - 129835*z/472392) + t^9*(1009727*z/1889568 - 3768367/944784) + t^8*(91631/34992 - 24553*z/69984) + t^7*(1142989/314928 - 306281*z/629856) + t^6*(38977*z/39366 - 290959/39366) + t^5*(67019/17496 - 17965*z/34992) + t^4*(173749/118098 - 186293*z/944784) + t^3*(293591*z/472392 - 2193761/472392) + t^2*(9893/8748 - 665*z/4374) + t*(161420/59049 - 85697*z/236196) - 11539*z/118098 + 86329/118098)*h0 + (t^7*(3691/7558272 - 989*z/15116544) + t^6*(4247*z/7558272 - 7925/1889568) + t^5*(787/78732 - 1687*z/1259712) + t^4*(295*z/7558272 - 275/944784) + t^3*(38603*z/15116544 - 144061/7558272) + t^2*(5509/1259712 - 1475*z/2519424) + t*(1309/118098 - 2803*z/1889568) - 1565*z/3779136 + 5923/1889568)*h1 + (65/1296 - 209*z/31104)*h2 + (989*t^14/472392 - 29845*t^13/944784 + 45145*t^12/236196 - 553787*t^11/944784 + 1651357*t^10/1889568 - 165973*t^9/1889568 - 610915*t^8/314928 + 562913*t^7/157464 - 633269*t^6/629856 + 13141739*t^5/1889568 + 2395231*t^4/472392 - 25530455*t^3/944784 - 3177359*t^2/59049 - 824443*t/236196 + 1781962/59049)*hf
  norm_num at hh

private lemma cell_6_61 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-2*z - 4) + 3*z:ℝ)=0) (h1 : (16*t^8 + t^7*(-32*z - 112) + t^6*(384*z + 96) + t^5*(816 - 1680*z) + t^4*(2736*z - 1872) + t^3*(1800*z - 720) + t^2*(6480 - 11880*z) + t*(11232*z - 6048):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(28/81 - 5*z/108) + t^6*(253*z/648 - 35/12) + t^5*(2249/324 - 601*z/648) + t^4*(7*z/72 - 85/108) + t^3*(161*z/108 - 299/27) + t^2*(59/18 - 5*z/12) + t*(79/18 - 23*z/36) - z/12 + 2/3)*h0 + (t*(5*z/864 - 7/162) - 29*z/1728 + 325/2592)*h1 + (5*t^8/54 - 149*t^7/81 + 8515*t^6/648 - 8867*t^5/216 + 8249*t^4/216 + 6743*t^3/72 - 19037*t^2/72 + 761*t/4 + 1/4)*hf
  norm_num at hh

private lemma cell_6_62 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 14*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(-96*z - 112) + t^6*(2544*z - 800) + t^5*(16304 - 31752*z) + t^4*(233160*z - 124928) + t^3*(563744 - 1051080*z) + t^2*(2836728*z - 1520336) + t*(2233472 - 4167744*z) + 2532192*z - 1356992:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z - 48) + t^6*(968*z - 496) + t^5*(3584 - 6072*z) + t^4*(17968*z - 9840) + t^3*(9904 - 19256*z) + t^2*(5296 - 9528*z) + t*(26672*z - 14112) - 8128*z + 4352:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(2131*z/1259712 - 2651/209952) + t^12*(10621/69984 - 25613*z/1259712) + t^11*(11237*z/139968 - 13979/23328) + t^10*(1156/2187 - 44605*z/629856) + t^9*(425639/209952 - 342125*z/1259712) + t^8*(78907*z/139968 - 294557/69984) + t^7*(67301*z/419904 - 9263/7776) + t^6*(1505/216 - 49115*z/52488) + t^5*(4933*z/69984 - 1073/2187) + t^4*(373919*z/629856 - 469549/104976) + t^3*(13457*z/629856 - 5291/34992) + t^2*(839/8748 - 65*z/11664) + t*(103/243 - 5213*z/78732) - 1712*z/19683 + 4555/6561)*h0 + (t^7*(2651/1679616 - 2131*z/10077696) + t^6*(5195*z/5038848 - 4847/629856) + t^5*(17/93312 - 41*z/1679616) + t^4*(54763/1679616 - 44021*z/10077696) + t^3*(1019*z/629856 - 3803/314928) + t^2*(4973*z/839808 - 12373/279936) + t*(5791/839808 - 4655*z/5038848) - 13333*z/5038848 + 49759/2519424)*h1 + (7/324 - 5*z/1728)*h2 + (-2131*t^14/157464 + 167513*t^13/314928 - 11001797*t^12/1259712 + 101123179*t^11/1259712 - 569699593*t^10/1259712 + 978167867*t^9/629856 - 1169074915*t^8/419904 + 49146685*t^7/419904 + 4195788839*t^6/419904 - 5162817359*t^5/314928 + 109513783*t^4/157464 + 6413953969*t^3/314928 - 7159269805*t^2/629856 - 1355918171*t/157464 + 1051542047/157464)*hf
  norm_num at hh

private lemma cell_6_63 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2 - 6*t:ℝ)=0) (h1 : (t*(960 - 1728*z) + 4288*z - 2304:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7/6 - z/6)*h0 + (433/2112 - 29*z/1056)*h1 + (3886/33 - 522*t/11)*hf
  norm_num at hh

private lemma pair_6_7_17 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2:ℝ)=0) (h2 : (16*t^8 + t^7*(-64*z - 48) + t^6*(1160*z - 496) + t^5*(5888 - 11112*z) + t^4*(69376*z - 37200) + t^3*(156208 - 291320*z) + t^2*(801480*z - 429584) + t*(705024 - 1315552*z) + 978032*z - 524128:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(41/972 - 11*z/1944) + t^6*(35*z/1944 - 43/324) + t^5*(11/162 - z/81) + t^4*(71*z/1944 - 59/972) + t^3*(-299*z/1944 - 17/324) + t^2*(209*z/324 - 32/81) + t*(229/486 - 677*z/486) + 803*z/486 - 112/81)*h0 + (11*z/31104 - 41/15552)*h2 + (11*t^7/486 - 1595*t^6/3888 + 5093*t^5/1296 - 5962*t^4/243 + 400565*t^3/3888 - 367345*t^2/1296 + 452221*t/972 - 672397/1944)*hf
  norm_num at hh

private lemma pair_6_7_27 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2:ℝ)=0) (h1 : (t - z - 1:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/3 - 7/3)*h0 + (7/3 - z/3)*h1 + (-1/3)*hf
  norm_num at hh

private lemma pair_6_13_20 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2:ℝ)=0) (h1 : (t - 2*z + 1:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2*z/23 - 13/23)*h0 + (13/23 - 2*z/23)*h1 + (-4/23)*hf
  norm_num at hh

private lemma pair_6_13_30 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2:ℝ)=0) (h1 : (t - z - 1:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/3 - 7/3)*h0 + (7/3 - z/3)*h1 + (-1/3)*hf
  norm_num at hh

private lemma pair_6_17_27 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h1 : (t - z - 1:ℝ)=0) (h2 : (16*t^8 + t^7*(16 - 128*z) + t^6*(3640*z - 2016) + t^5*(31184 - 57720*z) + t^4*(593720*z - 318112) + t^3*(2170416 - 4050688*z) + t^2*(17893392*z - 9589040) + t*(25106800 - 46849688*z) + 55861264*z - 29935968:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(7*z/81 - 209/324) + t^6*(61/54 - 49*z/324) + t^5*(118/27 - 127*z/216) + t^4*(161*z/324 - 1123/324) + t^3*(485*z/648 - 823/108) + t^2*(281*z/216 + 53/54) + t*(1723/324 - 3307*z/648) + 2159*z/324 - 79/18)*h1 + (209/5184 - 7*z/1296)*h2 + (-49*t^7/81 + 2107*t^6/108 - 22489*t^5/72 + 1039171*t^4/324 - 4725641*t^3/216 + 2319545*t^2/24 - 163977215*t/648 + 32586457/108)*hf
  norm_num at hh

private lemma pair_6_20_30 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z + 1:ℝ)=0) (h1 : (t - z - 1:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3/4 - z/8)*h0 + (z/8 - 3/4)*h1 + (-1/8)*hf
  norm_num at hh

private lemma pair_6_25_49 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (_hn0 : t-(1)≠0) (_hn1 : t-(z/2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z + 1:ℝ)=0) (h1 : (t - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (13/23 - 2*z/23)*h0 + (2*z/23 - 13/23)*h1 + (-4/23)*hf
  norm_num at hh

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_0 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 0) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_0 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_1 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 1) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_1 z t hf hn0 hn1 hn2 hn3
  · have hr : (z^2/2 - 3*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_2 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 2) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_2 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_3 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 3) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_3 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 32*t^7*z - 112*t^7 + 40*t^6*z^2 + 64*t^6*z + 256*t^6 - 32*t^5*z^3 - 12*t^5*z^2 + 336*t^5*z - 256*t^5 + 19*t^4*z^4 - 58*t^4*z^3 - 192*t^4*z^2 - 760*t^4*z + 64*t^4 - 8*t^3*z^5 + 49*t^3*z^4 + 172*t^3*z^3 - 496*t^3*z^2 + 248*t^3*z + 224*t^3 + 5*t^2*z^6/2 - 57*t^2*z^5/2 + 24*t^2*z^4 + 76*t^2*z^3 + 672*t^2*z^2 + 336*t^2*z - 272*t^2 - t*z^7/2 + 8*t*z^6 - 15*t*z^5 - 149*t*z^4 + 302*t*z^3 + 528*t*z^2 - 728*t*z + 176*t + z^8/16 - 13*z^7/8 + 13*z^6 - 35*z^5 + 10*z^4 + 100*z^3 - 284*z^2 + 184*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 32*t^5*z + 268*t^5 - 19*t^4*z^2 - 94*t^4*z - 484*t^4 + 8*t^3*z^3 + 15*t^3*z^2 - 84*t^3*z - 236*t^3 - 5*t^2*z^4/2 + 17*t^2*z^3/2 + 54*t^2*z^2 + 322*t^2*z + 1688*t^2 + t*z^5/2 - 4*t*z^4 - 19*t*z^3 + 13*t*z^2 - 122*t*z - 1556*t - z^6/16 + 9*z^5/8 - 15*z^4/4 + z^3/2 + 9*z^2 - 30*z + 8)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_4 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 4) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_4 z t hf hn0 hn1 hn2 hn3
  · have hr : (z^2/2 - 3*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_5 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 5) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_5 z t hf hn0 hn1 hn2 hn3
  · have hr : (648*t*z^2:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-648*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_6 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 6) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_6 z t hf hn0 hn1 hn2 hn3
  · have hr : (3*z^2/2 - 6*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_7 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 7) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : (t - 2:ℝ)=0 := by
  apply cell_6_7 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - t*z - 4*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 112*t^6*z^2 + 72*t^6*z - 48*t^6 - 112*t^5*z^3 + 36*t^5*z^2 + 360*t^5*z + 144*t^5 + 70*t^4*z^4 - 150*t^4*z^3 - 540*t^4*z^2 - 72*t^4*z - 28*t^3*z^5 + 135*t^3*z^4 + 300*t^3*z^3 - 432*t^3*z^2 - 648*t^3*z + 7*t^2*z^6 - 117*t^2*z^5/2 - 45*t^2*z^4 + 468*t^2*z^3 + 432*t^2*z^2 - t*z^7 + 51*t*z^6/4 - 27*t*z^5/2 - 153*t*z^4 + 54*t*z^3 + 648*t*z^2 + z^8/16 - 9*z^7/8 + 15*z^6/4 + 27*z^5/2 - 54*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 112*t^5*z + 860*t^5 - 70*t^4*z^2 - 410*t^4*z - 2460*t^4 + 28*t^3*z^3 + 89*t^3*z^2 + 300*t^3*z + 2476*t^3 - 7*t^2*z^4 + 5*t^2*z^3/2 + 93*t^2*z^2 + 266*t^2*z + 1324*t^2 + t*z^5 - 19*t*z^4/4 - 57*t*z^3/2 - 56*t*z^2 - 388*t*z - 3528*t - z^6/16 + 5*z^5/8 + 3*z^4/2 - 4*z^3 + 16*z^2 + 144*z + 1088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_8 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 8) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_8 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_9 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 9) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_9 z t hf hn0 hn1 hn2 hn3
  · have hr : (3*z^2/2 - 6*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_10 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 10) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_10 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_11 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 11) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_11 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 96*t^7*z - 48*t^7 + 264*t^6*z^2 + 144*t^6*z - 48*t^6 - 432*t^5*z^3 - 108*t^5*z^2 + 432*t^5*z + 144*t^5 + 459*t^4*z^4 - 162*t^4*z^3 - 1008*t^4*z^2 - 216*t^4*z - 324*t^3*z^5 + 405*t^3*z^4 + 1080*t^3*z^3 - 324*t^3*z^2 - 648*t^3*z + 297*t^2*z^6/2 - 729*t^2*z^5/2 - 540*t^2*z^4 + 810*t^2*z^3 + 756*t^2*z^2 - 81*t*z^7/2 + 162*t*z^6 + 81*t*z^5 - 567*t*z^4 - 162*t*z^3 + 648*t*z^2 + 81*z^8/16 - 243*z^7/8 + 81*z^6/4 + 243*z^5/2 - 162*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-264*t^6 + 432*t^5*z + 3564*t^5 - 459*t^4*z^2 - 3510*t^4*z - 25236*t^4 + 324*t^3*z^3 + 2187*t^3*z^2 + 15120*t^3*z + 112536*t^3 - 297*t^2*z^4/2 - 1647*t^2*z^3/2 - 5454*t^2*z^2 - 41148*t^2*z - 308124*t^2 + 81*t*z^5/2 + 162*t*z^4 + 1053*t*z^3 + 8343*t*z^2 + 62694*t*z + 467532*t - 81*z^6/16 - 81*z^5/8 - 81*z^4 - 729*z^3 - 5346*z^2 - 39852*z - 297432)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_12 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 12) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_12 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 32*t^7*z - 112*t^7 + 40*t^6*z^2 + 64*t^6*z + 256*t^6 - 32*t^5*z^3 - 12*t^5*z^2 + 336*t^5*z - 256*t^5 + 19*t^4*z^4 - 58*t^4*z^3 - 192*t^4*z^2 - 760*t^4*z + 64*t^4 - 8*t^3*z^5 + 49*t^3*z^4 + 172*t^3*z^3 - 496*t^3*z^2 + 248*t^3*z + 224*t^3 + 5*t^2*z^6/2 - 57*t^2*z^5/2 + 24*t^2*z^4 + 76*t^2*z^3 + 672*t^2*z^2 + 336*t^2*z - 272*t^2 - t*z^7/2 + 8*t*z^6 - 15*t*z^5 - 149*t*z^4 + 302*t*z^3 + 528*t*z^2 - 728*t*z + 176*t + z^8/16 - 13*z^7/8 + 13*z^6 - 35*z^5 + 10*z^4 + 100*z^3 - 284*z^2 + 184*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 32*t^5*z + 268*t^5 - 19*t^4*z^2 - 94*t^4*z - 484*t^4 + 8*t^3*z^3 + 15*t^3*z^2 - 84*t^3*z - 236*t^3 - 5*t^2*z^4/2 + 17*t^2*z^3/2 + 54*t^2*z^2 + 322*t^2*z + 1688*t^2 + t*z^5/2 - 4*t*z^4 - 19*t*z^3 + 13*t*z^2 - 122*t*z - 1556*t - z^6/16 + 9*z^5/8 - 15*z^4/4 + z^3/2 + 9*z^2 - 30*z + 8)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_13 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 13) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : (t - 2:ℝ)=0 := by
  apply cell_6_13 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - t*z - 4*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 112*t^6*z^2 + 72*t^6*z - 48*t^6 - 112*t^5*z^3 + 36*t^5*z^2 + 360*t^5*z + 144*t^5 + 70*t^4*z^4 - 150*t^4*z^3 - 540*t^4*z^2 - 72*t^4*z - 28*t^3*z^5 + 135*t^3*z^4 + 300*t^3*z^3 - 432*t^3*z^2 - 648*t^3*z + 7*t^2*z^6 - 117*t^2*z^5/2 - 45*t^2*z^4 + 468*t^2*z^3 + 432*t^2*z^2 - t*z^7 + 51*t*z^6/4 - 27*t*z^5/2 - 153*t*z^4 + 54*t*z^3 + 648*t*z^2 + z^8/16 - 9*z^7/8 + 15*z^6/4 + 27*z^5/2 - 54*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 112*t^5*z + 860*t^5 - 70*t^4*z^2 - 410*t^4*z - 2460*t^4 + 28*t^3*z^3 + 89*t^3*z^2 + 300*t^3*z + 2476*t^3 - 7*t^2*z^4 + 5*t^2*z^3/2 + 93*t^2*z^2 + 266*t^2*z + 1324*t^2 + t*z^5 - 19*t*z^4/4 - 57*t*z^3/2 - 56*t*z^2 - 388*t*z - 3528*t - z^6/16 + 5*z^5/8 + 3*z^4/2 - 4*z^3 + 16*z^2 + 144*z + 1088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_14 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 14) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_14 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 96*t^7*z - 48*t^7 + 264*t^6*z^2 + 144*t^6*z - 48*t^6 - 432*t^5*z^3 - 108*t^5*z^2 + 432*t^5*z + 144*t^5 + 459*t^4*z^4 - 162*t^4*z^3 - 1008*t^4*z^2 - 216*t^4*z - 324*t^3*z^5 + 405*t^3*z^4 + 1080*t^3*z^3 - 324*t^3*z^2 - 648*t^3*z + 297*t^2*z^6/2 - 729*t^2*z^5/2 - 540*t^2*z^4 + 810*t^2*z^3 + 756*t^2*z^2 - 81*t*z^7/2 + 162*t*z^6 + 81*t*z^5 - 567*t*z^4 - 162*t*z^3 + 648*t*z^2 + 81*z^8/16 - 243*z^7/8 + 81*z^6/4 + 243*z^5/2 - 162*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-264*t^6 + 432*t^5*z + 3564*t^5 - 459*t^4*z^2 - 3510*t^4*z - 25236*t^4 + 324*t^3*z^3 + 2187*t^3*z^2 + 15120*t^3*z + 112536*t^3 - 297*t^2*z^4/2 - 1647*t^2*z^3/2 - 5454*t^2*z^2 - 41148*t^2*z - 308124*t^2 + 81*t*z^5/2 + 162*t*z^4 + 1053*t*z^3 + 8343*t*z^2 + 62694*t*z + 467532*t - 81*z^6/16 - 81*z^5/8 - 81*z^4 - 729*z^3 - 5346*z^2 - 39852*z - 297432)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_15 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 15) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_15 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 112*t^6*z^2 + 72*t^6*z - 48*t^6 - 112*t^5*z^3 + 36*t^5*z^2 + 360*t^5*z + 144*t^5 + 70*t^4*z^4 - 150*t^4*z^3 - 540*t^4*z^2 - 72*t^4*z - 28*t^3*z^5 + 135*t^3*z^4 + 300*t^3*z^3 - 432*t^3*z^2 - 648*t^3*z + 7*t^2*z^6 - 117*t^2*z^5/2 - 45*t^2*z^4 + 468*t^2*z^3 + 432*t^2*z^2 - t*z^7 + 51*t*z^6/4 - 27*t*z^5/2 - 153*t*z^4 + 54*t*z^3 + 648*t*z^2 + z^8/16 - 9*z^7/8 + 15*z^6/4 + 27*z^5/2 - 54*z^4:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 112*t^5*z + 860*t^5 - 70*t^4*z^2 - 410*t^4*z - 2460*t^4 + 28*t^3*z^3 + 89*t^3*z^2 + 300*t^3*z + 2476*t^3 - 7*t^2*z^4 + 5*t^2*z^3/2 + 93*t^2*z^2 + 266*t^2*z + 1324*t^2 + t*z^5 - 19*t*z^4/4 - 57*t*z^3/2 - 56*t*z^2 - 388*t*z - 3528*t - z^6/16 + 5*z^5/8 + 3*z^4/2 - 4*z^3 + 16*z^2 + 144*z + 1088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_16 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 16) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_16 z t hf hn0 hn1 hn2 hn3
  · have hr : (z^2/2 - 3*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_17 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (_hc : cell (1) (1) (1) (profile4 (z/2) (z) t 17) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : ((0:ℝ):ℝ)=0 := by
  apply cell_6_17 z t hf hn0 hn1 hn2 hn3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_18 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 18) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_18 z t hf hn0 hn1 hn2 hn3
  · have hr : (3*z^2/2 - 6*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_19 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 19) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_19 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - t*z - 4*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 160*t^6*z^2 - 120*t^6*z + 144*t^6 - 256*t^5*z^3 + 504*t^5*z^2 + 216*t^5*z - 288*t^5 + 304*t^4*z^4 - 1248*t^4*z^3 + 1152*t^4*z^2 - 1152*t^4*z + 432*t^4 - 256*t^3*z^5 + 1560*t^3*z^4 - 2232*t^3*z^3 - 216*t^3*z^2 + 1512*t^3*z - 432*t^3 + 160*t^2*z^6 - 1440*t^2*z^5 + 4320*t^2*z^4 - 5904*t^2*z^3 + 5616*t^2*z^2 - 2808*t^2*z + 432*t^2 - 64*t*z^7 + 744*t*z^6 - 2952*t*z^5 + 4464*t*z^4 - 1296*t*z^3 - 1728*t*z^2 + 864*t*z + 16*z^8 - 264*z^7 + 1728*z^6 - 5832*z^5 + 11016*z^4 - 11664*z^3 + 6264*z^2 - 1296*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 1544*t^5 - 304*t^4*z^2 - 1184*t^4*z - 9408*t^4 + 256*t^3*z^3 + 488*t^3*z^2 + 5112*t^3*z + 39160*t^3 - 160*t^2*z^4 + 160*t^2*z^3 - 2400*t^2*z^2 - 13936*t^2*z - 107504*t^2 + 64*t*z^5 - 232*t*z^4 + 840*t*z^3 + 3184*t*z^2 + 23408*t*z + 176256*t - 16*z^6 + 136*z^5 - 576*z^4 + 680*z^3 - 3272*z^2 - 17232*z - 131032)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_20 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 20) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : (t - 2*z + 1:ℝ)=0 := by
  apply cell_6_20 z t hf hn0 hn1 hn2 hn3
  · have hr : (-48*t*z^6 + 504*t*z^5 - 1656*t*z^4 + 1464*t*z^3 + 1008*t*z^2 - 720*t*z + 96*t + 16*z^8 - 200*z^7 + 904*z^6 - 1760*z^5 + 1192*z^4 + 424*z^3 - 848*z^2 + 304*z - 32:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t*z^4 - 120*t*z^3 + 504*t*z^2 + 3048*t*z + 21360*t - 16*z^6 + 72*z^5 - 264*z^4 - 640*z^3 - 5256*z^2 - 39912*z - 297424)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_21 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 21) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_21 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 3*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_22 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 22) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_22 z t hf hn0 hn1 hn2 hn3
  · have hr : (648*t*z^2:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-648*t)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_23 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 23) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_23 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 2*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 128*t^7*z - 48*t^7 + 448*t^6*z^2 + 216*t^6*z - 48*t^6 - 896*t^5*z^3 - 288*t^5*z^2 + 504*t^5*z + 144*t^5 + 1120*t^4*z^4 - 120*t^4*z^3 - 1512*t^4*z^2 - 360*t^4*z - 896*t^3*z^5 + 720*t^3*z^4 + 1968*t^3*z^3 - 216*t^3*z^2 - 648*t^3*z + 448*t^2*z^6 - 792*t^2*z^5 - 1152*t^2*z^4 + 1152*t^2*z^3 + 1080*t^2*z^2 - 128*t*z^7 + 384*t*z^6 + 216*t*z^5 - 936*t*z^4 - 216*t*z^3 + 648*t*z^2 + 16*z^8 - 72*z^7 + 24*z^6 + 216*z^5 - 216*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 7456*t^5 - 1120*t^4*z^2 - 8840*t^4*z - 64728*t^4 + 896*t^3*z^3 + 6448*t^3*z^2 + 46032*t^3*z + 342680*t^3 - 448*t^2*z^4 - 2792*t^2*z^3 - 19392*t^2*z^2 - 145120*t^2*z - 1084472*t^2 + 128*t*z^5 + 640*t*z^4 + 4392*t*z^3 + 33512*t*z^2 + 250744*t*z + 1871256*t - 16*z^6 - 56*z^5 - 408*z^4 - 3256*z^3 - 24200*z^2 - 180576*z - 1347808)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_24 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 24) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_24 z t hf hn0 hn1 hn2 hn3
  · have hr : (3*z^2/2 - 6*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_25 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 25) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : (t - 2*z + 1:ℝ)=0 := by
  apply cell_6_25 z t hf hn0 hn1 hn2 hn3
  · have hr : (-81*t*z^6/4 + 243*t*z^5/2 - 81*t*z^4 - 486*t*z^3 + 648*t*z^2 + 81*z^8/16 - 243*z^7/8 + 81*z^6/4 + 243*z^5/2 - 162*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(81*t*z^4/4 + 81*t*z^3/2 + 324*t*z^2 + 2916*t*z + 21384*t - 81*z^6/16 - 81*z^5/8 - 81*z^4 - 729*z^3 - 5346*z^2 - 39852*z - 297432)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_26 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 26) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_26 z t hf hn0 hn1 hn2 hn3
  · have hr : (z^2/2 - 5*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_27 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 27) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : (t - z - 1:ℝ)=0 := by
  apply cell_6_27 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 3*t*z - 2*t + 3*z^2/2 - 3*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf
  · have hr : (16*t^8 - 160*t^7*z - 48*t^7 + 712*t^6*z^2 + 288*t^6*z - 48*t^6 - 1840*t^5*z^3 - 612*t^5*z^2 + 576*t^5*z + 144*t^5 + 3019*t^4*z^4 + 282*t^4*z^3 - 2160*t^4*z^2 - 504*t^4*z - 3220*t^3*z^5 + 999*t^3*z^4 + 3756*t^3*z^3 + 108*t^3*z^2 - 648*t^3*z + 4361*t^2*z^6/2 - 3843*t^2*z^5/2 - 3204*t^2*z^4 + 1386*t^2*z^3 + 1404*t^2*z^2 - 1715*t*z^7/2 + 2793*t*z^6/2 + 1134*t*z^5 - 1827*t*z^4 - 594*t*z^3 + 648*t*z^2 + 2401*z^8/16 - 3087*z^7/8 - 147*z^6/4 + 1323*z^5/2 - 378*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-712*t^6 + 1840*t^5*z + 15332*t^5 - 3019*t^4*z^2 - 24434*t^4*z - 181236*t^4 + 3220*t^3*z^3 + 24761*t^3*z^2 + 181452*t^3*z + 1352464*t^3 - 4361*t^2*z^4/2 - 31045*t^2*z^3/2 - 112254*t^2*z^2 - 837328*t^2*z - 6251012*t^2 + 1715*t*z^5/2 + 10927*t*z^4/2 + 39144*t*z^3 + 293125*t*z^2 + 2189018*t*z + 16338996*t - 2401*z^6/16 - 6517*z^5/8 - 5880*z^4 - 44443*z^3 - 331646*z^2 - 2475396*z - 18476584)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_28 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 28) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_28 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - t*z - 4*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 160*t^6*z^2 - 120*t^6*z + 144*t^6 - 256*t^5*z^3 + 504*t^5*z^2 + 216*t^5*z - 288*t^5 + 304*t^4*z^4 - 1248*t^4*z^3 + 1152*t^4*z^2 - 1152*t^4*z + 432*t^4 - 256*t^3*z^5 + 1560*t^3*z^4 - 2232*t^3*z^3 - 216*t^3*z^2 + 1512*t^3*z - 432*t^3 + 160*t^2*z^6 - 1440*t^2*z^5 + 4320*t^2*z^4 - 5904*t^2*z^3 + 5616*t^2*z^2 - 2808*t^2*z + 432*t^2 - 64*t*z^7 + 744*t*z^6 - 2952*t*z^5 + 4464*t*z^4 - 1296*t*z^3 - 1728*t*z^2 + 864*t*z + 16*z^8 - 264*z^7 + 1728*z^6 - 5832*z^5 + 11016*z^4 - 11664*z^3 + 6264*z^2 - 1296*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 1544*t^5 - 304*t^4*z^2 - 1184*t^4*z - 9408*t^4 + 256*t^3*z^3 + 488*t^3*z^2 + 5112*t^3*z + 39160*t^3 - 160*t^2*z^4 + 160*t^2*z^3 - 2400*t^2*z^2 - 13936*t^2*z - 107504*t^2 + 64*t*z^5 - 232*t*z^4 + 840*t*z^3 + 3184*t*z^2 + 23408*t*z + 176256*t - 16*z^6 + 136*z^5 - 576*z^4 + 680*z^3 - 3272*z^2 - 17232*z - 131032)*hf
  · have hr : (16*t^8 - 112*t^7 + 48*t^6*z^2 - 168*t^6*z + 256*t^6 - 252*t^5*z^2 + 936*t^5*z - 256*t^5 + 54*t^4*z^4 - 378*t^4*z^3 + 1008*t^4*z^2 - 1440*t^4*z + 64*t^4 - 189*t^3*z^4 + 1404*t^3*z^3 - 2640*t^3*z^2 + 528*t^3*z + 224*t^3 + 27*t^2*z^6 - 567*t^2*z^5/2 + 1080*t^2*z^4 - 2052*t^2*z^3 + 1800*t^2*z^2 + 504*t^2*z - 272*t^2 - 189*t*z^6/4 + 1053*t*z^5/2 - 1836*t*z^4 + 1836*t*z^3 + 900*t*z^2 - 1008*t*z + 176*t + 81*z^8/16 - 567*z^7/8 + 351*z^6 - 729*z^5 + 486*z^4 + 324*z^3 - 636*z^2 + 264*z - 32:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-48*t^6 + 252*t^5 - 54*t^4*z^2 - 54*t^4*z - 1224*t^4 + 189*t^3*z^2 + 108*t^3*z + 2748*t^3 - 27*t^2*z^4 + 135*t^2*z^3/2 - 432*t^2*z^2 - 1674*t^2*z - 13464*t^2 + 189*t*z^4/4 - 297*t*z^3/2 + 459*t*z^2 + 2430*t*z + 16704*t - 81*z^6/16 + 243*z^5/8 - 351*z^4/4 - 189*z^3/2 - 891*z^2 - 7074*z - 52392)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_29 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 29) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_29 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 2*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 32*t^7*z - 48*t^7 + 40*t^6*z^2 - 48*t^6 - 32*t^5*z^3 + 36*t^5*z^2 + 288*t^5*z + 144*t^5 + 19*t^4*z^4 - 66*t^4*z^3 - 216*t^4*z^2 + 72*t^4*z - 8*t^3*z^5 + 45*t^3*z^4 + 132*t^3*z^3 - 324*t^3*z^2 - 648*t^3*z + 5*t^2*z^6/2 - 45*t^2*z^5/2 - 18*t^2*z^4 + 234*t^2*z^3 + 108*t^2*z^2 - t*z^7/2 + 6*t*z^6 - 99*t*z^4 - 54*t*z^3 + 648*t*z^2 + z^8/16 - 9*z^7/8 + 15*z^6/4 + 27*z^5/2 - 54*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 32*t^5*z + 220*t^5 - 19*t^4*z^2 - 86*t^4*z - 396*t^4 + 8*t^3*z^3 + 19*t^3*z^2 - 12*t^3*z + 152*t^3 - 5*t^2*z^4/2 + 5*t^2*z^3/2 + 48*t^2*z^2 + 140*t^2*z + 820*t^2 + t*z^5/2 - 2*t*z^4 - 18*t*z^3 - 37*t*z^2 - 170*t*z - 1860*t - z^6/16 + 5*z^5/8 + 3*z^4/2 - 4*z^3 + 16*z^2 + 144*z + 1088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_30 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 30) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : (t - z - 1:ℝ)=0 := by
  apply cell_6_30 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 3*t*z - 2*t + 3*z^2/2 - 3*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 112*t^6*z^2 + 72*t^6*z - 48*t^6 - 112*t^5*z^3 + 36*t^5*z^2 + 360*t^5*z + 144*t^5 + 70*t^4*z^4 - 150*t^4*z^3 - 540*t^4*z^2 - 72*t^4*z - 28*t^3*z^5 + 135*t^3*z^4 + 300*t^3*z^3 - 432*t^3*z^2 - 648*t^3*z + 7*t^2*z^6 - 117*t^2*z^5/2 - 45*t^2*z^4 + 468*t^2*z^3 + 432*t^2*z^2 - t*z^7 + 51*t*z^6/4 - 27*t*z^5/2 - 153*t*z^4 + 54*t*z^3 + 648*t*z^2 + z^8/16 - 9*z^7/8 + 15*z^6/4 + 27*z^5/2 - 54*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 112*t^5*z + 860*t^5 - 70*t^4*z^2 - 410*t^4*z - 2460*t^4 + 28*t^3*z^3 + 89*t^3*z^2 + 300*t^3*z + 2476*t^3 - 7*t^2*z^4 + 5*t^2*z^3/2 + 93*t^2*z^2 + 266*t^2*z + 1324*t^2 + t*z^5 - 19*t*z^4/4 - 57*t*z^3/2 - 56*t*z^2 - 388*t*z - 3528*t - z^6/16 + 5*z^5/8 + 3*z^4/2 - 4*z^3 + 16*z^2 + 144*z + 1088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_31 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 31) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_31 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + z^2/2 - z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 128*t^7*z + 80*t^7 + 448*t^6*z^2 - 680*t^6*z + 112*t^6 - 896*t^5*z^3 + 2400*t^5*z^2 - 1176*t^5*z + 32*t^5 + 1120*t^4*z^4 - 4600*t^4*z^3 + 4488*t^4*z^2 - 736*t^4*z + 16*t^4 - 896*t^3*z^5 + 5200*t^3*z^4 - 8432*t^3*z^3 + 3560*t^3*z^2 - 376*t^3*z + 80*t^3 + 448*t^2*z^6 - 3480*t^2*z^5 + 8448*t^2*z^4 - 6800*t^2*z^3 + 1464*t^2*z^2 - 312*t^2*z + 16*t^2 - 128*t*z^7 + 1280*t*z^6 - 4344*t*z^5 + 5704*t*z^4 - 2296*t*z^3 + 240*t*z^2 + 256*t*z - 64*t + 16*z^8 - 200*z^7 + 904*z^6 - 1760*z^5 + 1192*z^4 + 424*z^3 - 848*z^2 + 304*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 4768*t^5 - 1120*t^4*z^2 - 4360*t^4*z - 34888*t^4 + 896*t^3*z^3 + 1968*t^3*z^2 + 20592*t^3*z + 153304*t^3 - 448*t^2*z^4 - 104*t^2*z^3 - 7488*t^2*z^2 - 52688*t^2*z - 393016*t^2 + 128*t*z^5 - 256*t*z^4 + 1784*t*z^3 + 9592*t*z^2 + 71896*t*z + 536560*t - 16*z^6 + 72*z^5 - 264*z^4 - 640*z^3 - 5256*z^2 - 39912*z - 297424)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_32 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 32) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_32 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_33 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 33) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_33 z t hf hn0 hn1 hn2 hn3
  · have hr : (3*z^2/2 - 6*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_34 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 34) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_34 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_35 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 35) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_35 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 96*t^7*z - 48*t^7 + 360*t^6*z^2 - 144*t^6*z + 144*t^6 - 864*t^5*z^3 + 972*t^5*z^2 + 216*t^5*z - 288*t^5 + 1539*t^4*z^4 - 3726*t^4*z^3 + 2340*t^4*z^2 - 1512*t^4*z + 432*t^4 - 1944*t^3*z^5 + 7047*t^3*z^4 - 6534*t^3*z^3 + 108*t^3*z^2 + 1944*t^3*z - 432*t^3 + 3645*t^2*z^6/2 - 19683*t^2*z^5/2 + 18711*t^2*z^4 - 17334*t^2*z^3 + 10908*t^2*z^2 - 3888*t^2*z + 432*t^2 - 2187*t*z^7/2 + 15309*t*z^6/2 - 38151*t*z^5/2 + 19440*t*z^4 - 5184*t*z^3 - 2916*t*z^2 + 1296*t*z + 6561*z^8/16 - 32805*z^7/8 + 16767*z^6 - 36450*z^5 + 45684*z^4 - 33048*z^3 + 12636*z^2 - 1944*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-360*t^6 + 864*t^5*z + 5940*t^5 - 1539*t^4*z^2 - 8586*t^4*z - 64872*t^4 + 1944*t^3*z^3 + 8505*t^3*z^2 + 66798*t^3*z + 500256*t^3 - 3645*t^2*z^4/2 - 9477*t^2*z^3/2 - 49329*t^2*z^2 - 358344*t^2*z - 2680344*t^2 + 2187*t*z^5/2 + 2187*t*z^4/2 + 46899*t*z^3/2 + 163782*t*z^2 + 1221642*t*z + 9120924*t - 6561*z^6/16 + 6561*z^5/8 - 34263*z^4/4 - 70713*z^3/2 - 294273*z^2 - 2179710*z - 16273224)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_36 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 36) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_36 z t hf hn0 hn1 hn2 hn3
  · have hr : (3*z^2/2 - 6*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_37 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 37) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : (t - 2*z + 1:ℝ)=0 := by
  apply cell_6_37 z t hf hn0 hn1 hn2 hn3
  · have hr : (-48*t*z^6 + 504*t*z^5 - 1656*t*z^4 + 1464*t*z^3 + 1008*t*z^2 - 720*t*z + 96*t + 16*z^8 - 200*z^7 + 904*z^6 - 1760*z^5 + 1192*z^4 + 424*z^3 - 848*z^2 + 304*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(48*t*z^4 - 120*t*z^3 + 504*t*z^2 + 3048*t*z + 21360*t - 16*z^6 + 72*z^5 - 264*z^4 - 640*z^3 - 5256*z^2 - 39912*z - 297424)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_38 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 38) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_38 z t hf hn0 hn1 hn2 hn3
  · have hr : (z^2/2 - 5*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_39 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 39) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_39 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 3*t*z - 2*t + 3*z^2/2 - 3*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf
  · have hr : (16*t^8 - 128*t^7*z + 16*t^7 + 496*t^6*z^2 - 328*t^6*z - 32*t^6 - 1184*t^5*z^3 + 1668*t^5*z^2 - 24*t^5*z - 32*t^5 + 1894*t^4*z^4 - 4466*t^4*z^3 + 1608*t^4*z^2 + 304*t^4*z - 32*t^4 - 2072*t^3*z^5 + 7211*t^3*z^4 - 5876*t^3*z^3 + 16*t^3*z^2 - 16*t^3*z + 64*t^3 + 1519*t^2*z^6 - 14595*t^2*z^5/2 + 10266*t^2*z^4 - 3604*t^2*z^3 - 120*t^2*z^2 + 24*t^2*z + 16*t^2 - 686*t*z^7 + 17395*t*z^6/4 - 18291*t*z^5/2 + 6806*t*z^4 - 988*t*z^3 + 372*t*z^2 - 176*t*z + 16*t + 2401*z^8/16 - 9947*z^7/8 + 7595*z^6/2 - 5110*z^5 + 2452*z^4 + 728*z^3 - 1124*z^2 + 344*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-496*t^6 + 1184*t^5*z + 7804*t^5 - 1894*t^4*z^2 - 10686*t^4*z - 79520*t^4 + 2072*t^3*z^3 + 9365*t^3*z^2 + 72508*t^3*z + 542588*t^3 - 1519*t^2*z^4 - 9709*t^2*z^3/2 - 43026*t^2*z^2 - 321186*t^2*z - 2397264*t^2 + 686*t*z^5 + 4557*t*z^4/4 + 31031*t*z^3/2 + 112761*t*z^2 + 841014*t*z + 6276696*t - 2401*z^6/16 + 343*z^5/8 - 11417*z^4/4 - 35791*z^3/2 - 134199*z^2 - 1002738*z - 7483984)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_40 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 40) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_40 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_41 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 41) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_41 z t hf hn0 hn1 hn2 hn3
  · have hr : (z^2/2 - 5*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_42 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 42) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_42 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 6*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_43 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 43) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_43 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 160*t^7*z + 16*t^7 + 712*t^6*z^2 - 320*t^6*z - 32*t^6 - 1840*t^5*z^3 + 1884*t^5*z^2 + 24*t^5*z - 32*t^5 + 3019*t^4*z^4 - 5470*t^4*z^3 + 1284*t^4*z^2 + 272*t^4*z - 32*t^4 - 3220*t^3*z^5 + 9047*t^3*z^4 - 5626*t^3*z^3 - 92*t^3*z^2 + 16*t^3*z + 64*t^3 + 4361*t^2*z^6/2 - 17535*t^2*z^5/2 + 10023*t^2*z^4 - 2606*t^2*z^3 - 12*t^2*z^2 - 24*t^2*z + 16*t^2 - 1715*t*z^7/2 + 9359*t*z^6/2 - 16863*t*z^5/2 + 5357*t*z^4 - 578*t*z^3 + 48*t*z^2 - 112*t*z + 16*t + 2401*z^8/16 - 8575*z^7/8 + 11221*z^6/4 - 3206*z^5 + 1183*z^4 + 730*z^3 - 908*z^2 + 304*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-712*t^6 + 1840*t^5*z + 12836*t^5 - 3019*t^4*z^2 - 18682*t^4*z - 138664*t^4 + 3220*t^3*z^3 + 16713*t^3*z^2 + 126450*t^3*z + 944840*t^3 - 4361*t^2*z^4/2 - 17353*t^2*z^3/2 - 70713*t^2*z^2 - 528392*t^2*z - 3944272*t^2 + 1715*t*z^5/2 + 4361*t*z^4/2 + 44891*t*z^3/2 + 165485*t*z^2 + 1234676*t*z + 9215420*t - 2401*z^6/16 - 1029*z^5/8 - 3234*z^4 - 44303*z^3/2 - 165459*z^2 - 1235796*z - 9223624)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_44 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 44) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_44 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 96*t^7*z - 48*t^7 + 360*t^6*z^2 - 144*t^6*z + 144*t^6 - 864*t^5*z^3 + 972*t^5*z^2 + 216*t^5*z - 288*t^5 + 1539*t^4*z^4 - 3726*t^4*z^3 + 2340*t^4*z^2 - 1512*t^4*z + 432*t^4 - 1944*t^3*z^5 + 7047*t^3*z^4 - 6534*t^3*z^3 + 108*t^3*z^2 + 1944*t^3*z - 432*t^3 + 3645*t^2*z^6/2 - 19683*t^2*z^5/2 + 18711*t^2*z^4 - 17334*t^2*z^3 + 10908*t^2*z^2 - 3888*t^2*z + 432*t^2 - 2187*t*z^7/2 + 15309*t*z^6/2 - 38151*t*z^5/2 + 19440*t*z^4 - 5184*t*z^3 - 2916*t*z^2 + 1296*t*z + 6561*z^8/16 - 32805*z^7/8 + 16767*z^6 - 36450*z^5 + 45684*z^4 - 33048*z^3 + 12636*z^2 - 1944*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-360*t^6 + 864*t^5*z + 5940*t^5 - 1539*t^4*z^2 - 8586*t^4*z - 64872*t^4 + 1944*t^3*z^3 + 8505*t^3*z^2 + 66798*t^3*z + 500256*t^3 - 3645*t^2*z^4/2 - 9477*t^2*z^3/2 - 49329*t^2*z^2 - 358344*t^2*z - 2680344*t^2 + 2187*t*z^5/2 + 2187*t*z^4/2 + 46899*t*z^3/2 + 163782*t*z^2 + 1221642*t*z + 9120924*t - 6561*z^6/16 + 6561*z^5/8 - 34263*z^4/4 - 70713*z^3/2 - 294273*z^2 - 2179710*z - 16273224)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_45 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 45) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_45 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 3*t*z - 2*t + 3*z^2/2 - 3*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf
  · have hr : (16*t^8 - 128*t^7*z + 16*t^7 + 496*t^6*z^2 - 328*t^6*z - 32*t^6 - 1184*t^5*z^3 + 1668*t^5*z^2 - 24*t^5*z - 32*t^5 + 1894*t^4*z^4 - 4466*t^4*z^3 + 1608*t^4*z^2 + 304*t^4*z - 32*t^4 - 2072*t^3*z^5 + 7211*t^3*z^4 - 5876*t^3*z^3 + 16*t^3*z^2 - 16*t^3*z + 64*t^3 + 1519*t^2*z^6 - 14595*t^2*z^5/2 + 10266*t^2*z^4 - 3604*t^2*z^3 - 120*t^2*z^2 + 24*t^2*z + 16*t^2 - 686*t*z^7 + 17395*t*z^6/4 - 18291*t*z^5/2 + 6806*t*z^4 - 988*t*z^3 + 372*t*z^2 - 176*t*z + 16*t + 2401*z^8/16 - 9947*z^7/8 + 7595*z^6/2 - 5110*z^5 + 2452*z^4 + 728*z^3 - 1124*z^2 + 344*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-496*t^6 + 1184*t^5*z + 7804*t^5 - 1894*t^4*z^2 - 10686*t^4*z - 79520*t^4 + 2072*t^3*z^3 + 9365*t^3*z^2 + 72508*t^3*z + 542588*t^3 - 1519*t^2*z^4 - 9709*t^2*z^3/2 - 43026*t^2*z^2 - 321186*t^2*z - 2397264*t^2 + 686*t*z^5 + 4557*t*z^4/4 + 31031*t*z^3/2 + 112761*t*z^2 + 841014*t*z + 6276696*t - 2401*z^6/16 + 343*z^5/8 - 11417*z^4/4 - 35791*z^3/2 - 134199*z^2 - 1002738*z - 7483984)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_46 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 46) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_46 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 160*t^7*z + 16*t^7 + 712*t^6*z^2 - 320*t^6*z - 32*t^6 - 1840*t^5*z^3 + 1884*t^5*z^2 + 24*t^5*z - 32*t^5 + 3019*t^4*z^4 - 5470*t^4*z^3 + 1284*t^4*z^2 + 272*t^4*z - 32*t^4 - 3220*t^3*z^5 + 9047*t^3*z^4 - 5626*t^3*z^3 - 92*t^3*z^2 + 16*t^3*z + 64*t^3 + 4361*t^2*z^6/2 - 17535*t^2*z^5/2 + 10023*t^2*z^4 - 2606*t^2*z^3 - 12*t^2*z^2 - 24*t^2*z + 16*t^2 - 1715*t*z^7/2 + 9359*t*z^6/2 - 16863*t*z^5/2 + 5357*t*z^4 - 578*t*z^3 + 48*t*z^2 - 112*t*z + 16*t + 2401*z^8/16 - 8575*z^7/8 + 11221*z^6/4 - 3206*z^5 + 1183*z^4 + 730*z^3 - 908*z^2 + 304*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-712*t^6 + 1840*t^5*z + 12836*t^5 - 3019*t^4*z^2 - 18682*t^4*z - 138664*t^4 + 3220*t^3*z^3 + 16713*t^3*z^2 + 126450*t^3*z + 944840*t^3 - 4361*t^2*z^4/2 - 17353*t^2*z^3/2 - 70713*t^2*z^2 - 528392*t^2*z - 3944272*t^2 + 1715*t*z^5/2 + 4361*t*z^4/2 + 44891*t*z^3/2 + 165485*t*z^2 + 1234676*t*z + 9215420*t - 2401*z^6/16 - 1029*z^5/8 - 3234*z^4 - 44303*z^3/2 - 165459*z^2 - 1235796*z - 9223624)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_47 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 47) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_47 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 192*t^7*z + 80*t^7 + 1008*t^6*z^2 - 984*t^6*z + 112*t^6 - 3024*t^5*z^3 + 5076*t^5*z^2 - 1656*t^5*z + 32*t^5 + 5670*t^4*z^4 - 14310*t^4*z^3 + 9036*t^4*z^2 - 1104*t^4*z + 16*t^4 - 6804*t^3*z^5 + 23895*t^3*z^4 - 24516*t^3*z^3 + 7272*t^3*z^2 - 600*t^3*z + 80*t^3 + 5103*t^2*z^6 - 47385*t^2*z^5/2 + 35721*t^2*z^4 - 19224*t^2*z^3 + 3240*t^2*z^2 - 360*t^2*z + 16*t^2 - 2187*t*z^7 + 51759*t*z^6/4 - 53703*t*z^5/2 + 22680*t*z^4 - 6534*t*z^3 + 180*t*z^2 + 384*t*z - 64*t + 6561*z^8/16 - 24057*z^7/8 + 32805*z^6/4 - 9963*z^5 + 4455*z^4 + 918*z^3 - 1404*z^2 + 384*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1008*t^6 + 3024*t^5*z + 19116*t^5 - 5670*t^4*z^2 - 31050*t^4*z - 234756*t^4 + 6804*t^3*z^3 + 30537*t^3*z^2 + 241596*t^3*z + 1803348*t^3 - 5103*t^2*z^4 - 34263*t^2*z^3/2 - 152361*t^2*z^2 - 1131138*t^2*z - 8442900*t^2 + 2187*t*z^5 + 18225*t*z^4/4 + 109107*t*z^3/2 + 395523*t*z^2 + 2952504*t*z + 22037760*t - 6561*z^6/16 - 2187*z^5/8 - 8748*z^4 - 117855*z^3/2 - 440883*z^2 - 3292272*z - 24573240)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_48 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 48) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_48 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 32*t^7*z - 176*t^7 + 40*t^6*z^2 - 368*t^6*z + 688*t^6 + 32*t^5*z^3 - 420*t^5*z^2 + 1608*t^5*z - 1184*t^5 + 19*t^4*z^4 - 310*t^4*z^3 + 1644*t^4*z^2 - 3064*t^4*z + 784*t^4 + 8*t^3*z^5 - 157*t^3*z^4 + 1070*t^3*z^3 - 2852*t^3*z^2 + 1912*t^3*z + 208*t^3 + 5*t^2*z^6/2 - 111*t^2*z^5/2 + 429*t^2*z^4 - 1418*t^2*z^3 + 1644*t^2*z^2 + 768*t^2*z - 560*t^2 + t*z^7/2 - 25*t*z^6/2 + 219*t*z^5/2 - 400*t*z^4 + 364*t*z^3 + 876*t*z^2 - 1072*t*z + 256*t + z^8/16 - 13*z^7/8 + 13*z^6 - 35*z^5 + 10*z^4 + 100*z^3 - 284*z^2 + 184*z - 32:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 - 32*t^5*z + 164*t^5 - 19*t^4*z^2 + 158*t^4*z - 304*t^4 - 8*t^3*z^3 + 93*t^3*z^2 - 294*t^3*z + 128*t^3 - 5*t^2*z^4/2 + 71*t^2*z^3/2 - 135*t^2*z^2 + 196*t^2*z + 464*t^2 - t*z^5/2 + 17*t*z^4/2 - 79*t*z^3/2 + 50*t*z^2 + 194*t*z + 476*t - z^6/16 + 9*z^5/8 - 15*z^4/4 + z^3/2 + 9*z^2 - 30*z + 8)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_49 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 49) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : (t - 2:ℝ)=0 := by
  apply cell_6_49 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - t*z - 4*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_50 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 50) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_50 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 240*t^7 + 48*t^6*z^2 - 168*t^6*z + 1440*t^6 - 540*t^5*z^2 + 1944*t^5*z - 4608*t^5 + 54*t^4*z^4 - 378*t^4*z^3 + 2880*t^4*z^2 - 8208*t^4*z + 8640*t^4 - 405*t^3*z^4 + 2916*t^3*z^3 - 9504*t^3*z^2 + 16416*t^3*z - 9504*t^3 + 27*t^2*z^6 - 567*t^2*z^5/2 + 1890*t^2*z^4 - 7884*t^2*z^3 + 16416*t^2*z^2 - 16200*t^2*z + 5616*t^2 - 405*t*z^6/4 + 2187*t*z^5/2 - 4536*t*z^4 + 9720*t*z^3 - 11340*t*z^2 + 6480*t*z - 1296*t + 81*z^8/16 - 567*z^7/8 + 405*z^6 - 1296*z^5 + 2592*z^4 - 3240*z^3 + 2268*z^2 - 648*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-48*t^6 + 540*t^5 - 54*t^4*z^2 - 54*t^4*z - 3096*t^4 + 405*t^3*z^2 + 324*t^3*z + 10476*t^3 - 27*t^2*z^4 + 135*t^2*z^3/2 - 1242*t^2*z^2 - 2322*t^2*z - 30024*t^2 + 405*t*z^4/4 - 567*t*z^3/2 + 1863*t*z^2 + 6318*t*z + 54432*t - 81*z^6/16 + 243*z^5/8 - 567*z^4/4 + 81*z^3/2 - 1701*z^2 - 10530*z - 79704)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_51 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 51) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_51 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 32*t^7*z - 240*t^7 + 40*t^6*z^2 - 528*t^6*z + 1440*t^6 + 32*t^5*z^3 - 612*t^5*z^2 + 3456*t^5*z - 4608*t^5 + 19*t^4*z^4 - 462*t^4*z^3 + 3744*t^4*z^2 - 11304*t^4*z + 8640*t^4 + 8*t^3*z^5 - 237*t^3*z^4 + 2520*t^3*z^3 - 11448*t^3*z^2 + 19656*t^3*z - 9504*t^3 + 5*t^2*z^6/2 - 171*t^2*z^5/2 + 1080*t^2*z^4 - 6336*t^2*z^3 + 17280*t^2*z^2 - 17712*t^2*z + 5616*t^2 + t*z^7/2 - 39*t*z^6/2 + 288*t*z^5 - 2043*t*z^4 + 7074*t*z^3 - 10800*t*z^2 + 6696*t*z - 1296*t + z^8/16 - 21*z^7/8 + 81*z^6/2 - 297*z^5 + 1134*z^4 - 2268*z^3 + 2052*z^2 - 648*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 - 32*t^5*z + 356*t^5 - 19*t^4*z^2 + 310*t^4*z - 1188*t^4 - 8*t^3*z^3 + 173*t^3*z^2 - 1104*t^3*z + 1924*t^3 - 5*t^2*z^4/2 + 131*t^2*z^3/2 - 546*t^2*z^2 + 1706*t^2*z - 1448*t^2 - t*z^5/2 + 31*t*z^4/2 - 162*t*z^3 + 685*t*z^2 - 946*t*z + 492*t - z^6/16 + 17*z^5/8 - 93*z^4/4 + 205*z^3/2 - 221*z^2 + 90*z - 448)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_52 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 52) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_52 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - t*z - 4*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 112*t^7 + 48*t^6*z^2 - 168*t^6*z + 256*t^6 - 252*t^5*z^2 + 936*t^5*z - 256*t^5 + 54*t^4*z^4 - 378*t^4*z^3 + 1008*t^4*z^2 - 1440*t^4*z + 64*t^4 - 189*t^3*z^4 + 1404*t^3*z^3 - 2640*t^3*z^2 + 528*t^3*z + 224*t^3 + 27*t^2*z^6 - 567*t^2*z^5/2 + 1080*t^2*z^4 - 2052*t^2*z^3 + 1800*t^2*z^2 + 504*t^2*z - 272*t^2 - 189*t*z^6/4 + 1053*t*z^5/2 - 1836*t*z^4 + 1836*t*z^3 + 900*t*z^2 - 1008*t*z + 176*t + 81*z^8/16 - 567*z^7/8 + 351*z^6 - 729*z^5 + 486*z^4 + 324*z^3 - 636*z^2 + 264*z - 32:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-48*t^6 + 252*t^5 - 54*t^4*z^2 - 54*t^4*z - 1224*t^4 + 189*t^3*z^2 + 108*t^3*z + 2748*t^3 - 27*t^2*z^4 + 135*t^2*z^3/2 - 432*t^2*z^2 - 1674*t^2*z - 13464*t^2 + 189*t*z^4/4 - 297*t*z^3/2 + 459*t*z^2 + 2430*t*z + 16704*t - 81*z^6/16 + 243*z^5/8 - 351*z^4/4 - 189*z^3/2 - 891*z^2 - 7074*z - 52392)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_53 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 53) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_53 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 2*t + z^2/2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 176*t^7 - 72*t^6*z + 688*t^6 + 648*t^5*z - 1184*t^5 + 72*t^4*z^2 - 1728*t^4*z + 784*t^4 - 504*t^3*z^2 + 1224*t^3*z + 208*t^3 + 648*t^2*z^2 + 648*t^2*z - 560*t^2 + 576*t*z^2 - 864*t*z + 256*t - 144*z^2 + 144*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-72*t^4 + 504*t^3 - 648*t^2 - 576*t + 144)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_54 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 54) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_54 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 3*t*z - 2*t + 3*z^2/2 - 3*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf
  · have hr : (16*t^8 - 32*t^7*z - 176*t^7 + 40*t^6*z^2 + 224*t^6*z + 688*t^6 - 32*t^5*z^3 - 204*t^5*z^2 - 312*t^5*z - 1184*t^5 + 19*t^4*z^4 + 94*t^4*z^3 + 132*t^4*z^2 - 392*t^4*z + 784*t^4 - 8*t^3*z^5 - 31*t^3*z^4 + 118*t^3*z^3 + 172*t^3*z^2 + 536*t^3*z + 208*t^3 + 5*t^2*z^6/2 + 3*t^2*z^5/2 - 57*t^2*z^4 - 202*t^2*z^3 + 132*t^2*z^2 + 528*t^2*z - 560*t^2 - t*z^7/2 + t*z^6 + 51*t*z^5/2 - 22*t*z^4 - 148*t*z^3 + 444*t*z^2 - 656*t*z + 256*t + z^8/16 - 5*z^7/8 - z^6/2 + 8*z^5 - 8*z^4 + 8*z^3 - 68*z^2 + 104*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 32*t^5*z + 460*t^5 - 19*t^4*z^2 - 246*t^4*z - 2024*t^4 + 8*t^3*z^3 + 95*t^3*z^2 + 610*t^3*z + 4328*t^3 - 5*t^2*z^4/2 - 43*t^2*z^3/2 - 105*t^2*z^2 - 552*t^2*z - 4128*t^2 + t*z^5/2 + 3*t*z^4 - 7*t*z^3/2 - 18*t*z^2 + 18*t*z - 228*t - z^6/16 + z^5/8 + 7*z^4/4 + 11*z^3/2 + 45*z^2 + 330*z + 2528)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 112*t^6*z^2 + 72*t^6*z - 48*t^6 - 112*t^5*z^3 + 36*t^5*z^2 + 360*t^5*z + 144*t^5 + 70*t^4*z^4 - 150*t^4*z^3 - 540*t^4*z^2 - 72*t^4*z - 28*t^3*z^5 + 135*t^3*z^4 + 300*t^3*z^3 - 432*t^3*z^2 - 648*t^3*z + 7*t^2*z^6 - 117*t^2*z^5/2 - 45*t^2*z^4 + 468*t^2*z^3 + 432*t^2*z^2 - t*z^7 + 51*t*z^6/4 - 27*t*z^5/2 - 153*t*z^4 + 54*t*z^3 + 648*t*z^2 + z^8/16 - 9*z^7/8 + 15*z^6/4 + 27*z^5/2 - 54*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 112*t^5*z + 860*t^5 - 70*t^4*z^2 - 410*t^4*z - 2460*t^4 + 28*t^3*z^3 + 89*t^3*z^2 + 300*t^3*z + 2476*t^3 - 7*t^2*z^4 + 5*t^2*z^3/2 + 93*t^2*z^2 + 266*t^2*z + 1324*t^2 + t*z^5 - 19*t*z^4/4 - 57*t*z^3/2 - 56*t*z^2 - 388*t*z - 3528*t - z^6/16 + 5*z^5/8 + 3*z^4/2 - 4*z^3 + 16*z^2 + 144*z + 1088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_55 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 55) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_55 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + z^2/2 - z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 32*t^7*z - 112*t^7 + 40*t^6*z^2 + 64*t^6*z + 256*t^6 - 32*t^5*z^3 - 12*t^5*z^2 + 336*t^5*z - 256*t^5 + 19*t^4*z^4 - 58*t^4*z^3 - 192*t^4*z^2 - 760*t^4*z + 64*t^4 - 8*t^3*z^5 + 49*t^3*z^4 + 172*t^3*z^3 - 496*t^3*z^2 + 248*t^3*z + 224*t^3 + 5*t^2*z^6/2 - 57*t^2*z^5/2 + 24*t^2*z^4 + 76*t^2*z^3 + 672*t^2*z^2 + 336*t^2*z - 272*t^2 - t*z^7/2 + 8*t*z^6 - 15*t*z^5 - 149*t*z^4 + 302*t*z^3 + 528*t*z^2 - 728*t*z + 176*t + z^8/16 - 13*z^7/8 + 13*z^6 - 35*z^5 + 10*z^4 + 100*z^3 - 284*z^2 + 184*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 32*t^5*z + 268*t^5 - 19*t^4*z^2 - 94*t^4*z - 484*t^4 + 8*t^3*z^3 + 15*t^3*z^2 - 84*t^3*z - 236*t^3 - 5*t^2*z^4/2 + 17*t^2*z^3/2 + 54*t^2*z^2 + 322*t^2*z + 1688*t^2 + t*z^5/2 - 4*t*z^4 - 19*t*z^3 + 13*t*z^2 - 122*t*z - 1556*t - z^6/16 + 9*z^5/8 - 15*z^4/4 + z^3/2 + 9*z^2 - 30*z + 8)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_56 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 56) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_56 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 240*t^7 + 48*t^6*z^2 - 168*t^6*z + 1440*t^6 - 540*t^5*z^2 + 1944*t^5*z - 4608*t^5 + 54*t^4*z^4 - 378*t^4*z^3 + 2880*t^4*z^2 - 8208*t^4*z + 8640*t^4 - 405*t^3*z^4 + 2916*t^3*z^3 - 9504*t^3*z^2 + 16416*t^3*z - 9504*t^3 + 27*t^2*z^6 - 567*t^2*z^5/2 + 1890*t^2*z^4 - 7884*t^2*z^3 + 16416*t^2*z^2 - 16200*t^2*z + 5616*t^2 - 405*t*z^6/4 + 2187*t*z^5/2 - 4536*t*z^4 + 9720*t*z^3 - 11340*t*z^2 + 6480*t*z - 1296*t + 81*z^8/16 - 567*z^7/8 + 405*z^6 - 1296*z^5 + 2592*z^4 - 3240*z^3 + 2268*z^2 - 648*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-48*t^6 + 540*t^5 - 54*t^4*z^2 - 54*t^4*z - 3096*t^4 + 405*t^3*z^2 + 324*t^3*z + 10476*t^3 - 27*t^2*z^4 + 135*t^2*z^3/2 - 1242*t^2*z^2 - 2322*t^2*z - 30024*t^2 + 405*t*z^4/4 - 567*t*z^3/2 + 1863*t*z^2 + 6318*t*z + 54432*t - 81*z^6/16 + 243*z^5/8 - 567*z^4/4 + 81*z^3/2 - 1701*z^2 - 10530*z - 79704)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_57 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 57) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_57 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 3*t*z - 2*t + 3*z^2/2 - 3*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-3/2)*hf
  · have hr : (16*t^8 - 32*t^7*z - 176*t^7 + 40*t^6*z^2 + 224*t^6*z + 688*t^6 - 32*t^5*z^3 - 204*t^5*z^2 - 312*t^5*z - 1184*t^5 + 19*t^4*z^4 + 94*t^4*z^3 + 132*t^4*z^2 - 392*t^4*z + 784*t^4 - 8*t^3*z^5 - 31*t^3*z^4 + 118*t^3*z^3 + 172*t^3*z^2 + 536*t^3*z + 208*t^3 + 5*t^2*z^6/2 + 3*t^2*z^5/2 - 57*t^2*z^4 - 202*t^2*z^3 + 132*t^2*z^2 + 528*t^2*z - 560*t^2 - t*z^7/2 + t*z^6 + 51*t*z^5/2 - 22*t*z^4 - 148*t*z^3 + 444*t*z^2 - 656*t*z + 256*t + z^8/16 - 5*z^7/8 - z^6/2 + 8*z^5 - 8*z^4 + 8*z^3 - 68*z^2 + 104*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 32*t^5*z + 460*t^5 - 19*t^4*z^2 - 246*t^4*z - 2024*t^4 + 8*t^3*z^3 + 95*t^3*z^2 + 610*t^3*z + 4328*t^3 - 5*t^2*z^4/2 - 43*t^2*z^3/2 - 105*t^2*z^2 - 552*t^2*z - 4128*t^2 + t*z^5/2 + 3*t*z^4 - 7*t*z^3/2 - 18*t*z^2 + 18*t*z - 228*t - z^6/16 + z^5/8 + 7*z^4/4 + 11*z^3/2 + 45*z^2 + 330*z + 2528)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 160*t^6*z^2 + 72*t^6*z - 48*t^6 - 256*t^5*z^3 - 72*t^5*z^2 + 360*t^5*z + 144*t^5 + 304*t^4*z^4 - 96*t^4*z^3 - 648*t^4*z^2 - 72*t^4*z - 256*t^3*z^5 + 216*t^3*z^4 + 840*t^3*z^3 - 216*t^3*z^2 - 648*t^3*z + 160*t^2*z^6 - 288*t^2*z^5 - 504*t^2*z^4 + 576*t^2*z^3 + 432*t^2*z^2 - 64*t*z^7 + 168*t*z^6 + 216*t*z^5 - 504*t*z^4 - 432*t*z^3 + 648*t*z^2 + 16*z^8 - 72*z^7 + 24*z^6 + 216*z^5 - 216*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-160*t^6 + 256*t^5*z + 2120*t^5 - 304*t^4*z^2 - 2336*t^4*z - 16824*t^4 + 256*t^3*z^3 + 1832*t^3*z^2 + 12792*t^3*z + 95224*t^3 - 160*t^2*z^4 - 992*t^2*z^3 - 6792*t^2*z^2 - 50944*t^2*z - 380816*t^2 + 64*t*z^5 + 344*t*z^4 + 2280*t*z^3 + 17368*t*z^2 + 130256*t*z + 971928*t - 16*z^6 - 56*z^5 - 408*z^4 - 3256*z^3 - 24200*z^2 - 180576*z - 1347808)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_58 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 58) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_58 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 2*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 64*t^7*z - 176*t^7 + 112*t^6*z^2 + 520*t^6*z + 688*t^6 - 112*t^5*z^3 - 636*t^5*z^2 - 1272*t^5*z - 1184*t^5 + 70*t^4*z^4 + 410*t^4*z^3 + 780*t^4*z^2 + 944*t^4*z + 784*t^4 - 28*t^3*z^5 - 145*t^3*z^4 - 100*t^3*z^3 + 136*t^3*z^2 - 152*t^3*z + 208*t^3 + 7*t^2*z^6 + 51*t^2*z^5/2 - 75*t^2*z^4 - 248*t^2*z^3 + 24*t^2*z^2 + 408*t^2*z - 560*t^2 - t*z^7 - 5*t*z^6/4 + 57*t*z^5/2 + 44*t*z^4 - 86*t*z^3 + 228*t*z^2 - 448*t*z + 256*t + z^8/16 - z^7/8 - 11*z^6/4 + z^5 + 7*z^4 - 26*z^3 + 4*z^2 + 64*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 112*t^5*z + 1532*t^5 - 70*t^4*z^2 - 970*t^4*z - 8260*t^4 + 28*t^3*z^3 + 369*t^3*z^2 + 2940*t^3*z + 21908*t^3 - 7*t^2*z^4 - 163*t^2*z^3/2 - 549*t^2*z^2 - 3818*t^2*z - 28372*t^2 + t*z^5 + 37*t*z^4/4 + 83*t*z^3/2 + 251*t*z^2 + 1928*t*z + 14192*t - z^6/16 - 3*z^5/8 + z^3/2 - 3*z^2 + 8)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_59 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 59) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_59 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 96*t^7*z - 112*t^7 + 264*t^6*z^2 + 432*t^6*z + 256*t^6 - 432*t^5*z^3 - 684*t^5*z^2 - 360*t^5*z - 256*t^5 + 459*t^4*z^4 + 486*t^4*z^3 - 180*t^4*z^2 - 192*t^4*z + 64*t^4 - 324*t^3*z^5 - 27*t^3*z^4 + 702*t^3*z^3 + 276*t^3*z^2 + 144*t^3*z + 224*t^3 + 297*t^2*z^6/2 - 405*t^2*z^5/2 - 459*t^2*z^4 + 162*t^2*z^3 + 396*t^2*z^2 + 72*t^2*z - 272*t^2 - 81*t*z^7/2 + 135*t*z^6 + 81*t*z^5/2 - 297*t*z^4 + 54*t*z^3 + 360*t*z^2 - 528*t*z + 176*t + 81*z^8/16 - 243*z^7/8 + 189*z^6/4 - 81*z^4 + 162*z^3 - 204*z^2 + 144*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-264*t^6 + 432*t^5*z + 4140*t^5 - 459*t^4*z^2 - 4158*t^4*z - 31248*t^4 + 324*t^3*z^3 + 2619*t^3*z^2 + 18954*t^3*z + 140880*t^3 - 297*t^2*z^4/2 - 1971*t^2*z^3/2 - 6831*t^2*z^2 - 50868*t^2*z - 380016*t^2 + 81*t*z^5/2 + 189*t*z^4 + 2619*t*z^3/2 + 10017*t*z^2 + 74844*t*z + 558324*t - 81*z^6/16 - 81*z^5/8 - 108*z^4 - 1647*z^3/2 - 6075*z^2 - 45468*z - 339240)*hf
  · have hr : (16*t^8 - 160*t^7*z - 48*t^7 + 712*t^6*z^2 + 288*t^6*z - 48*t^6 - 1840*t^5*z^3 - 612*t^5*z^2 + 576*t^5*z + 144*t^5 + 3019*t^4*z^4 + 282*t^4*z^3 - 2160*t^4*z^2 - 504*t^4*z - 3220*t^3*z^5 + 999*t^3*z^4 + 3756*t^3*z^3 + 108*t^3*z^2 - 648*t^3*z + 4361*t^2*z^6/2 - 3843*t^2*z^5/2 - 3204*t^2*z^4 + 1386*t^2*z^3 + 1404*t^2*z^2 - 1715*t*z^7/2 + 2793*t*z^6/2 + 1134*t*z^5 - 1827*t*z^4 - 594*t*z^3 + 648*t*z^2 + 2401*z^8/16 - 3087*z^7/8 - 147*z^6/4 + 1323*z^5/2 - 378*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-712*t^6 + 1840*t^5*z + 15332*t^5 - 3019*t^4*z^2 - 24434*t^4*z - 181236*t^4 + 3220*t^3*z^3 + 24761*t^3*z^2 + 181452*t^3*z + 1352464*t^3 - 4361*t^2*z^4/2 - 31045*t^2*z^3/2 - 112254*t^2*z^2 - 837328*t^2*z - 6251012*t^2 + 1715*t*z^5/2 + 10927*t*z^4/2 + 39144*t*z^3 + 293125*t*z^2 + 2189018*t*z + 16338996*t - 2401*z^6/16 - 6517*z^5/8 - 5880*z^4 - 44443*z^3 - 331646*z^2 - 2475396*z - 18476584)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_60 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 60) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_60 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 32*t^7*z - 240*t^7 + 40*t^6*z^2 - 528*t^6*z + 1440*t^6 + 32*t^5*z^3 - 612*t^5*z^2 + 3456*t^5*z - 4608*t^5 + 19*t^4*z^4 - 462*t^4*z^3 + 3744*t^4*z^2 - 11304*t^4*z + 8640*t^4 + 8*t^3*z^5 - 237*t^3*z^4 + 2520*t^3*z^3 - 11448*t^3*z^2 + 19656*t^3*z - 9504*t^3 + 5*t^2*z^6/2 - 171*t^2*z^5/2 + 1080*t^2*z^4 - 6336*t^2*z^3 + 17280*t^2*z^2 - 17712*t^2*z + 5616*t^2 + t*z^7/2 - 39*t*z^6/2 + 288*t*z^5 - 2043*t*z^4 + 7074*t*z^3 - 10800*t*z^2 + 6696*t*z - 1296*t + z^8/16 - 21*z^7/8 + 81*z^6/2 - 297*z^5 + 1134*z^4 - 2268*z^3 + 2052*z^2 - 648*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 - 32*t^5*z + 356*t^5 - 19*t^4*z^2 + 310*t^4*z - 1188*t^4 - 8*t^3*z^3 + 173*t^3*z^2 - 1104*t^3*z + 1924*t^3 - 5*t^2*z^4/2 + 131*t^2*z^3/2 - 546*t^2*z^2 + 1706*t^2*z - 1448*t^2 - t*z^5/2 + 31*t*z^4/2 - 162*t*z^3 + 685*t*z^2 - 946*t*z + 492*t - z^6/16 + 17*z^5/8 - 93*z^4/4 + 205*z^3/2 - 221*z^2 + 90*z - 448)*hf
  · have hr : (16*t^8 + 64*t^7*z - 176*t^7 + 112*t^6*z^2 - 664*t^6*z + 688*t^6 + 112*t^5*z^3 - 1068*t^5*z^2 + 2568*t^5*z - 1184*t^5 + 70*t^4*z^4 - 950*t^4*z^3 + 3804*t^4*z^2 - 4400*t^4*z + 784*t^4 + 28*t^3*z^5 - 505*t^3*z^4 + 2908*t^3*z^3 - 5912*t^3*z^2 + 2600*t^3*z + 208*t^3 + 7*t^2*z^6 - 321*t^2*z^5/2 + 1221*t^2*z^4 - 3640*t^2*z^3 + 3048*t^2*z^2 + 888*t^2*z - 560*t^2 + t*z^7 - 113*t*z^6/4 + 537*t*z^5/2 - 1036*t*z^4 + 1274*t*z^3 + 1092*t*z^2 - 1280*t*z + 256*t + z^8/16 - 17*z^7/8 + 97*z^6/4 - 109*z^5 + 151*z^4 + 134*z^3 - 428*z^2 + 224*z - 32:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 - 112*t^5*z + 172*t^5 - 70*t^4*z^2 + 390*t^4*z - 404*t^4 - 28*t^3*z^3 + 281*t^3*z^2 - 548*t^3*z + 404*t^3 - 7*t^2*z^4 + 209*t^2*z^3/2 - 357*t^2*z^2 + 366*t^2*z + 1308*t^2 - t*z^5 + 81*t*z^4/4 - 205*t*z^3/2 + 135*t*z^2 + 216*t*z + 96*t - z^6/16 + 13*z^5/8 - 11*z^4 + 29*z^3/2 + 9*z^2 - 120*z - 568)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_61 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 61) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_61 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 2*t*z - 4*t + z^2/2 - z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1/2)*hf
  · have hr : (16*t^8 - 32*t^7*z - 112*t^7 + 40*t^6*z^2 + 64*t^6*z + 256*t^6 - 32*t^5*z^3 - 12*t^5*z^2 + 336*t^5*z - 256*t^5 + 19*t^4*z^4 - 58*t^4*z^3 - 192*t^4*z^2 - 760*t^4*z + 64*t^4 - 8*t^3*z^5 + 49*t^3*z^4 + 172*t^3*z^3 - 496*t^3*z^2 + 248*t^3*z + 224*t^3 + 5*t^2*z^6/2 - 57*t^2*z^5/2 + 24*t^2*z^4 + 76*t^2*z^3 + 672*t^2*z^2 + 336*t^2*z - 272*t^2 - t*z^7/2 + 8*t*z^6 - 15*t*z^5 - 149*t*z^4 + 302*t*z^3 + 528*t*z^2 - 728*t*z + 176*t + z^8/16 - 13*z^7/8 + 13*z^6 - 35*z^5 + 10*z^4 + 100*z^3 - 284*z^2 + 184*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-40*t^6 + 32*t^5*z + 268*t^5 - 19*t^4*z^2 - 94*t^4*z - 484*t^4 + 8*t^3*z^3 + 15*t^3*z^2 - 84*t^3*z - 236*t^3 - 5*t^2*z^4/2 + 17*t^2*z^3/2 + 54*t^2*z^2 + 322*t^2*z + 1688*t^2 + t*z^5/2 - 4*t*z^4 - 19*t*z^3 + 13*t*z^2 - 122*t*z - 1556*t - z^6/16 + 9*z^5/8 - 15*z^4/4 + z^3/2 + 9*z^2 - 30*z + 8)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_62 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 62) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_62 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 2*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 96*t^7*z - 112*t^7 + 264*t^6*z^2 + 432*t^6*z + 256*t^6 - 432*t^5*z^3 - 684*t^5*z^2 - 360*t^5*z - 256*t^5 + 459*t^4*z^4 + 486*t^4*z^3 - 180*t^4*z^2 - 192*t^4*z + 64*t^4 - 324*t^3*z^5 - 27*t^3*z^4 + 702*t^3*z^3 + 276*t^3*z^2 + 144*t^3*z + 224*t^3 + 297*t^2*z^6/2 - 405*t^2*z^5/2 - 459*t^2*z^4 + 162*t^2*z^3 + 396*t^2*z^2 + 72*t^2*z - 272*t^2 - 81*t*z^7/2 + 135*t*z^6 + 81*t*z^5/2 - 297*t*z^4 + 54*t*z^3 + 360*t*z^2 - 528*t*z + 176*t + 81*z^8/16 - 243*z^7/8 + 189*z^6/4 - 81*z^4 + 162*z^3 - 204*z^2 + 144*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-264*t^6 + 432*t^5*z + 4140*t^5 - 459*t^4*z^2 - 4158*t^4*z - 31248*t^4 + 324*t^3*z^3 + 2619*t^3*z^2 + 18954*t^3*z + 140880*t^3 - 297*t^2*z^4/2 - 1971*t^2*z^3/2 - 6831*t^2*z^2 - 50868*t^2*z - 380016*t^2 + 81*t*z^5/2 + 189*t*z^4 + 2619*t*z^3/2 + 10017*t*z^2 + 74844*t*z + 558324*t - 81*z^6/16 - 81*z^5/8 - 108*z^4 - 1647*z^3/2 - 6075*z^2 - 45468*z - 339240)*hf
  · have hr : (16*t^8 - 64*t^7*z - 48*t^7 + 112*t^6*z^2 + 72*t^6*z - 48*t^6 - 112*t^5*z^3 + 36*t^5*z^2 + 360*t^5*z + 144*t^5 + 70*t^4*z^4 - 150*t^4*z^3 - 540*t^4*z^2 - 72*t^4*z - 28*t^3*z^5 + 135*t^3*z^4 + 300*t^3*z^3 - 432*t^3*z^2 - 648*t^3*z + 7*t^2*z^6 - 117*t^2*z^5/2 - 45*t^2*z^4 + 468*t^2*z^3 + 432*t^2*z^2 - t*z^7 + 51*t*z^6/4 - 27*t*z^5/2 - 153*t*z^4 + 54*t*z^3 + 648*t*z^2 + z^8/16 - 9*z^7/8 + 15*z^6/4 + 27*z^5/2 - 54*z^4:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-112*t^6 + 112*t^5*z + 860*t^5 - 70*t^4*z^2 - 410*t^4*z - 2460*t^4 + 28*t^3*z^3 + 89*t^3*z^2 + 300*t^3*z + 2476*t^3 - 7*t^2*z^4 + 5*t^2*z^3/2 + 93*t^2*z^2 + 266*t^2*z + 1324*t^2 + t*z^5 - 19*t*z^4/4 - 57*t*z^3/2 - 56*t*z^2 - 388*t*z - 3528*t - z^6/16 + 5*z^5/8 + 3*z^4/2 - 4*z^3 + 16*z^2 + 144*z + 1088)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_6_63 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (1) (profile4 (z/2) (z) t 63) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : False := by
  apply cell_6_63 z t hf hn0 hn1 hn2 hn3
  · have hr : (2 - 6*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (-3*t*z^6/4 + 45*t*z^5/2 - 198*t*z^4 + 426*t*z^3 + 684*t*z^2 - 576*t*z + 96*t + z^8/16 - 17*z^7/8 + 97*z^6/4 - 109*z^5 + 151*z^4 + 134*z^3 - 428*z^2 + 224*z - 32:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(3*t*z^4/4 - 33*t*z^3/2 + 63*t*z^2 + 144*t*z + 216*t - z^6/16 + 13*z^5/8 - 11*z^4 + 29*z^3/2 + 9*z^2 - 120*z - 568)*hf


private def limit6 (z t : ℝ) : Fin 64→Prop := ![False,False,False,False,False,False,False,((t - 2:ℝ)=0),False,False,False,False,False,((t - 2:ℝ)=0),False,False,False,(((0:ℝ):ℝ)=0),False,False,((t - 2*z + 1:ℝ)=0),False,False,False,False,((t - 2*z + 1:ℝ)=0),False,((t - z - 1:ℝ)=0),False,False,((t - z - 1:ℝ)=0),False,False,False,False,False,False,((t - 2*z + 1:ℝ)=0),False,False,False,False,False,False,False,False,False,False,False,((t - 2:ℝ)=0),False,False,False,False,False,False,False,False,False,False,False,False,False,False]

private def hue6 : Fin 64→Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,2,0,0,0,0,1,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_6_7_17 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit6 z t 7) (_hj : limit6 z t 17) (he : edge4 (1) (1) (1) (profile4 (z/2) (z) t 7) (profile4 (z/2) (z) t 17) (z/2) (z) t=0) : False := by
  apply pair_6_7_17 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (16*t^8 - 64*t^7*z - 48*t^7 + 160*t^6*z^2 - 120*t^6*z + 144*t^6 - 256*t^5*z^3 + 504*t^5*z^2 + 216*t^5*z - 288*t^5 + 304*t^4*z^4 - 1248*t^4*z^3 + 1152*t^4*z^2 - 1152*t^4*z + 432*t^4 - 256*t^3*z^5 + 1560*t^3*z^4 - 2232*t^3*z^3 - 216*t^3*z^2 + 1512*t^3*z - 432*t^3 + 160*t^2*z^6 - 1440*t^2*z^5 + 4320*t^2*z^4 - 5904*t^2*z^3 + 5616*t^2*z^2 - 2808*t^2*z + 432*t^2 - 64*t*z^7 + 744*t*z^6 - 2952*t*z^5 + 4464*t*z^4 - 1296*t*z^3 - 1728*t*z^2 + 864*t*z + 16*z^8 - 264*z^7 + 1728*z^6 - 5832*z^5 + 11016*z^4 - 11664*z^3 + 6264*z^2 - 1296*z:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-160*t^6 + 256*t^5*z + 1544*t^5 - 304*t^4*z^2 - 1184*t^4*z - 9408*t^4 + 256*t^3*z^3 + 488*t^3*z^2 + 5112*t^3*z + 39160*t^3 - 160*t^2*z^4 + 160*t^2*z^3 - 2400*t^2*z^2 - 13936*t^2*z - 107504*t^2 + 64*t*z^5 - 232*t*z^4 + 840*t*z^3 + 3184*t*z^2 + 23408*t*z + 176256*t - 16*z^6 + 136*z^5 - 576*z^4 + 680*z^3 - 3272*z^2 - 17232*z - 131032)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_6_7_27 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit6 z t 7) (hj : limit6 z t 27) (_he : edge4 (1) (1) (1) (profile4 (z/2) (z) t 7) (profile4 (z/2) (z) t 27) (z/2) (z) t=0) : False := by
  apply pair_6_7_27 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_6_13_20 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit6 z t 13) (hj : limit6 z t 20) (_he : edge4 (1) (1) (1) (profile4 (z/2) (z) t 13) (profile4 (z/2) (z) t 20) (z/2) (z) t=0) : False := by
  apply pair_6_13_20 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_6_13_30 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit6 z t 13) (hj : limit6 z t 30) (_he : edge4 (1) (1) (1) (profile4 (z/2) (z) t 13) (profile4 (z/2) (z) t 30) (z/2) (z) t=0) : False := by
  apply pair_6_13_30 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_6_17_27 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (_hi : limit6 z t 17) (hj : limit6 z t 27) (he : edge4 (1) (1) (1) (profile4 (z/2) (z) t 17) (profile4 (z/2) (z) t 27) (z/2) (z) t=0) : False := by
  apply pair_6_17_27 z t hf hn0 hn1 hn2 hn3
  · exact hj
  · have hraw : (16*t^8 - 128*t^7*z + 16*t^7 + 496*t^6*z^2 - 328*t^6*z - 32*t^6 - 1184*t^5*z^3 + 1668*t^5*z^2 - 24*t^5*z - 32*t^5 + 1894*t^4*z^4 - 4466*t^4*z^3 + 1608*t^4*z^2 + 304*t^4*z - 32*t^4 - 2072*t^3*z^5 + 7211*t^3*z^4 - 5876*t^3*z^3 + 16*t^3*z^2 - 16*t^3*z + 64*t^3 + 1519*t^2*z^6 - 14595*t^2*z^5/2 + 10266*t^2*z^4 - 3604*t^2*z^3 - 120*t^2*z^2 + 24*t^2*z + 16*t^2 - 686*t*z^7 + 17395*t*z^6/4 - 18291*t*z^5/2 + 6806*t*z^4 - 988*t*z^3 + 372*t*z^2 - 176*t*z + 16*t + 2401*z^8/16 - 9947*z^7/8 + 7595*z^6/2 - 5110*z^5 + 2452*z^4 + 728*z^3 - 1124*z^2 + 344*z - 32:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-496*t^6 + 1184*t^5*z + 7804*t^5 - 1894*t^4*z^2 - 10686*t^4*z - 79520*t^4 + 2072*t^3*z^3 + 9365*t^3*z^2 + 72508*t^3*z + 542588*t^3 - 1519*t^2*z^4 - 9709*t^2*z^3/2 - 43026*t^2*z^2 - 321186*t^2*z - 2397264*t^2 + 686*t*z^5 + 4557*t*z^4/4 + 31031*t*z^3/2 + 112761*t*z^2 + 841014*t*z + 6276696*t - 2401*z^6/16 + 343*z^5/8 - 11417*z^4/4 - 35791*z^3/2 - 134199*z^2 - 1002738*z - 7483984)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_6_20_30 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit6 z t 20) (hj : limit6 z t 30) (_he : edge4 (1) (1) (1) (profile4 (z/2) (z) t 20) (profile4 (z/2) (z) t 30) (z/2) (z) t=0) : False := by
  apply pair_6_20_30 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_6_25_49 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit6 z t 25) (hj : limit6 z t 49) (_he : edge4 (1) (1) (1) (profile4 (z/2) (z) t 25) (profile4 (z/2) (z) t 49) (z/2) (z) t=0) : False := by
  apply pair_6_25_49 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma exclude_field_6 (z t : ℝ) (hf : z^2 - 8*z + 4=0) (hn0 : t-(1)≠0) (hn1 : t-(z/2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (g : Fin 5→Fin 64) (hinj : Function.Injective g)
    (hc : ∀ i, cell (1) (1) (1) (profile4 (z/2) (z) t (g i)) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t)
    (he : ∀ i j : Fin 5, i≠j → edge4 (1) (1) (1) (profile4 (z/2) (z) t (g i)) (profile4 (z/2) (z) t (g j)) (z/2) (z) t=0) : False := by
  have row (k : Fin 64) (hh : cell (1) (1) (1) (profile4 (z/2) (z) t k) ((1),(z/2),(z/2)) ((z/2),(z/2),(z)) (z/2) (z) t) : limit6 z t k := by
    fin_cases k
    · exact row_6_0 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_1 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_2 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_3 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_4 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_5 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_6 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_7 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_8 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_9 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_10 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_11 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_12 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_13 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_14 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_15 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_16 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_17 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_18 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_19 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_20 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_21 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_22 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_23 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_24 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_25 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_26 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_27 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_28 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_29 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_30 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_31 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_32 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_33 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_34 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_35 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_36 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_37 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_38 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_39 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_40 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_41 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_42 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_43 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_44 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_45 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_46 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_47 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_48 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_49 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_50 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_51 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_52 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_53 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_54 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_55 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_56 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_57 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_58 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_59 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_60 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_61 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_62 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_6_63 z t hf hn0 hn1 hn2 hn3 hh
  have allowed (k : Fin 64) (hh : limit6 z t k) : k∈([7,13,17,20,25,27,30,37,49]:List (Fin 64)) := by
    fin_cases k <;> first | decide | exact False.elim hh
  have cert : ∀ i j : Fin 64, i∈([7,13,17,20,25,27,30,37,49]:List (Fin 64)) → j∈([7,13,17,20,25,27,30,37,49]:List (Fin 64)) → i<j → hue6 i=hue6 j → (i,j)∈([(7,17),(7,27),(13,20),(13,30),(17,27),(20,30),(25,49)]:List (Fin 64×Fin 64)) := by decide
  have bad (i j : Fin 64) (hi : limit6 z t i) (hj : limit6 z t j) (hlt : i<j) (hc : hue6 i=hue6 j) (hb : edge4 (1) (1) (1) (profile4 (z/2) (z) t i) (profile4 (z/2) (z) t j) (z/2) (z) t=0) : False := by
    have h := cert i j (allowed i hi) (allowed j hj) hlt hc
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact rowpair_6_7_17 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_6_7_27 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_6_13_20 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_6_13_30 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_6_17_27 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_6_20_30 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_6_25_49 z t hf hn0 hn1 hn2 hn3 hi hj hb
  have hi : Function.Injective (fun i : Fin 5 => hue6 (g i)) := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne (show g i≠g j from fun e => hne (hinj e)) with hl|hl
    · exact bad _ _ (row _ (hc i)) (row _ (hc j)) hl h (he i j hne)
    · exact bad _ _ (row _ (hc j)) (row _ (hc i)) hl h.symm (he j i (Ne.symm hne))
  have hh := Fintype.card_le_of_injective _ hi
  norm_num at hh

private lemma cell_9_0 (z t : ℝ) (_hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/4)*h0
  norm_num at hh

private lemma cell_9_1 (z t : ℝ) (_hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/6)*h0
  norm_num at hh

private lemma cell_9_2 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/3 - 11/6)*h0 + (-4/3)*hf
  norm_num at hh

private lemma cell_9_3 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h2 : (16*t^8 + t^7*(64 - 128*z) + t^6*(2112*z - 1024) + t^5*(6080 - 17536*z) + t^4*(81856*z - 27488) + t^3*(73408 - 207744*z) + t^2*(260800*z - 94848) + t*(42816 - 116608*z) - 15552*z + 5328:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(63/1280 - 67*z/7680) + t^6*(541/7680 - 47*z/3840) + t^5*(1099*z/7680 - 3181/3840) + t^4*(541*z/3840 - 4909/7680) + t^3*(5781/1280 - 2331*z/2560) + t^2*(33*z/256 + 4159/7680) + t*(8353*z/7680 - 28151/3840) - 543*z/1280 + 6659/2560)*h0 + (t*(67*z/61440 - 63/10240) - 25*z/6144 + 1411/61440)*h2 + (67*t^8/480 - 2711*t^7/960 + 1663*t^6/60 - 154193*t^5/960 + 33577*t^4/60 - 216905*t^3/192 + 142603*t^2/120 - 439219*t/960 - 2025/32)*hf
  norm_num at hh

private lemma cell_9_4 (z t : ℝ) (_hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/6)*h0
  norm_num at hh

private lemma cell_9_5 (z t : ℝ) (_hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/8)*h0
  norm_num at hh

private lemma cell_9_6 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/12 - 5/12)*h0 + (-1/3)*hf
  norm_num at hh

private lemma cell_9_7 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t:ℝ)=0) (h1 : (16*t^8 - 64*t^7 + t^6*(64 - 64*z) + 256*t^5*z - 256*t^4 + t^3*(1024 - 1024*z) + t^2*(1024*z - 1024):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(z/4608 - 1/4608) + t^4*(1/1152 - z/288) + t^3*(z/288 - 1/288) + t^2*(z/96 - 1/96) + t*(-z/72 - 1/36) - 1/8)*h0 + (1/36864 - z/36864)*h1 + (-t^6/576 + t^5/144 - t^3/36 + t^2/36)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_9_8 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/3 - 11/6)*h0 + (-4/3)*hf
  norm_num at hh

private lemma cell_9_9 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/12 - 5/12)*h0 + (-1/3)*hf
  norm_num at hh

private lemma cell_9_10 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (8*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (3/8 - z/16)*h0 + (1/2)*hf
  norm_num at hh

private lemma cell_9_11 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 4*z + 4:ℝ)=0) (h1 : (16*t^8 - 64*t^7 + t^6*(320*z - 320) + t^5*(1152 - 896*z) + t^4*(9216*z - 2560) + t^3*(1792 - 13312*z) + t^2*(129280*z - 46336) + t*(29184 - 75264*z) + 595968*z - 211200:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(463/55296 - 41*z/27648) + t^6*(79*z/18432 - 223/9216) + t^5*(641*z/27648 - 3617/27648) + t^4*(2015/6912 - 1427*z/27648) + t^3*(321/512 - 85*z/768) + t^2*(2161*z/13824 - 6065/6912) + t*(149*z/768 - 821/768) - 77*z/2304 + 137/576)*h0 + (t*(41*z/221184 - 463/442368) - 79*z/147456 + 223/73728)*h1 + (-41*t^7/768 + 4429*t^6/13824 - 15767*t^5/6912 + 17537*t^4/2304 - 52969*t^3/1728 + 285425*t^2/3456 - 87305*t/576 + 183989/576)*hf
  norm_num at hh

private lemma cell_9_12 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h2 : (16*t^8 - 192*t^7 + t^6*(64*z + 768) + t^5*(-512*z - 1088) + t^4*(1472*z - 352) + t^3*(2496 - 1024*z) + t^2*(-5440*z - 896) + t*(15872*z - 4800) - 23232*z + 8400:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(17/1536 - z/512) + t^6*(35*z/1536 - 33/256) + t^5*(775/1536 - 137*z/1536) + t^4*(197*z/1536 - 557/768) + t^3*(23*z/1536 - 133/1536) + t^2*(365/256 - 383*z/1536) + t*(413*z/1536 - 2363/1536) - 11*z/512 + 27/256)*h0 + (t*(z/4096 - 17/12288) - 11*z/12288 + 31/6144)*h2 + (-t^7/64 + 35*t^6/192 - 157*t^5/192 + 301*t^4/192 + 79*t^3/192 - 1679*t^2/192 + 3817*t/192 - 1331/64)*hf
  norm_num at hh

private lemma cell_9_13 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t:ℝ)=0) (h1 : (16*t^8 - 64*t^7 + t^6*(64 - 64*z) + 256*t^5*z - 256*t^4 + t^3*(1024 - 1024*z) + t^2*(1024*z - 1024):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(z/4608 - 1/4608) + t^4*(1/1152 - z/288) + t^3*(z/288 - 1/288) + t^2*(z/96 - 1/96) + t*(-z/72 - 1/36) - 1/8)*h0 + (1/36864 - z/36864)*h1 + (-t^6/576 + t^5/144 - t^3/36 + t^2/36)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_9_14 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 4*z + 4:ℝ)=0) (h1 : (16*t^8 - 64*t^7 + t^6*(320*z - 320) + t^5*(1152 - 896*z) + t^4*(9216*z - 2560) + t^3*(1792 - 13312*z) + t^2*(129280*z - 46336) + t*(29184 - 75264*z) + 595968*z - 211200:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(463/55296 - 41*z/27648) + t^6*(79*z/18432 - 223/9216) + t^5*(641*z/27648 - 3617/27648) + t^4*(2015/6912 - 1427*z/27648) + t^3*(321/512 - 85*z/768) + t^2*(2161*z/13824 - 6065/6912) + t*(149*z/768 - 821/768) - 77*z/2304 + 137/576)*h0 + (t*(41*z/221184 - 463/442368) - 79*z/147456 + 223/73728)*h1 + (-41*t^7/768 + 4429*t^6/13824 - 15767*t^5/6912 + 17537*t^4/2304 - 52969*t^3/1728 + 285425*t^2/3456 - 87305*t/576 + 183989/576)*hf
  norm_num at hh

private lemma cell_9_15 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*t^2 - 16*t + 8:ℝ)=0) (h1 : (256*t^8 - 512*t^7 + t^6*(-512*z - 1536) + t^5*(1024*z + 3072) + t^4*(3072*z + 2048) + t^3*(-6144*z - 4096) - 4096*t^2*z + 8192*t*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(23/448 - z/112) + t^6*(11*z/896 - 65/896) + t^5*(29*z/448 - 173/448) + t^4*(103/224 - 33*z/448) + t^3*(25/28 - 31*z/224) + t^2*(11*z/112 - 81/112) + t*(5*z/56 - 5/7) + 1/8)*h0 + (t*(z/7168 - 23/28672) - 27*z/57344 + 157/57344)*h1 + (t^7/14 - 43*t^6/112 + 3*t^5/56 + 129*t^4/56 - 65*t^3/28 - 43*t^2/14 + 27*t/7)*hf
  norm_num at hh

private lemma cell_9_16 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h1 : (8192*t*z:ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (3/8192 - z/16384)*h1 + (t/2)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_9_17 (z t : ℝ) (_hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/6)*h0
  norm_num at hh

private lemma cell_9_18 (z t : ℝ) (_hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/6)*h0
  norm_num at hh

private lemma cell_9_19 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 12*t + 10:ℝ)=0) (h1 : (16*t^8 - 192*t^7 + t^6*(640 - 64*z) + t^5*(640*z + 64) + t^4*(-1216*z - 3040) + t^3*(2496 - 3328*z) + t^2*(6720*z + 2048) + t*(6784*z - 2368) - 1344*z + 336:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(7/9216 - 5*z/36864) + t^6*(53*z/36864 - 19/2304) + t^5*(187/9216 - 125*z/36864) + t^4*(79/2304 - 203*z/36864) + t^3*(227*z/12288 - 385/3072) + t^2*(215*z/36864 - 151/2304) + t*(395/3072 - 47*z/4096) + 7*z/4096 + 27/256)*h0 + (t*(5*z/294912 - 7/73728) - 23*z/294912 + 17/36864)*h1 + (5*t^7/4608 - 73*t^6/4608 + 325*t^5/4608 - 59*t^4/1536 - 1721*t^3/4608 + 1885*t^2/4608 + 2543*t/4608 - 161/1536)*hf
  norm_num at hh

private lemma cell_9_20 (z t : ℝ) (_hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/6)*h0
  norm_num at hh

private lemma cell_9_21 (z t : ℝ) (_hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (-12:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/12)*h0
  norm_num at hh

private lemma cell_9_22 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h2 : (8192*t*z:ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (3/8192 - z/16384)*h2 + (t/2)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_9_23 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 12*t + 4:ℝ)=0) (h2 : (16*t^8 + t^7*(-128*z - 64) + t^6*(3008*z - 1088) + t^5*(12672 - 32512*z) + t^4*(200192*z - 71680) + t^3*(252672 - 722944*z) + t^2*(1477376*z - 521472) + t*(546304 - 1533952*z) + 595968*z - 211200:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(289/184320 - 77*z/276480) + t^6*(203*z/110592 - 469/46080) + t^5*(127*z/276480 - 103/18432) + t^4*(15149/138240 - 1409*z/92160) + t^3*(-139*z/13824 - 4109/138240) + t^2*(11639*z/138240 - 12349/34560) + t*(55*z/13824 + 3679/69120) - 2521*z/23040 + 3563/11520)*h0 + (t*(77*z/2211840 - 289/1474560) - 289*z/1474560 + 2449/2211840)*h2 + (77*t^8/17280 - 2243*t^7/17280 + 118981*t^6/69120 - 230537*t^5/17280 + 111289*t^4/1728 - 1668571*t^3/8640 + 1185245*t^2/3456 - 25711*t/80 + 28033/240)*hf
  norm_num at hh

private lemma cell_9_24 (z t : ℝ) (_hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/6)*h0
  norm_num at hh

private lemma cell_9_25 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h2 : (t*(8192 - 20480*z) + 135168*z - 49152:ℝ)=0) : (t - z - 1:ℝ)=0 := by
  have hh : (t - z - 1:ℝ)=0 := by linear_combination (7/6144 - 5*z/24576)*h2 + (55/2 - 25*t/6)*hf
  exact hh

private lemma cell_9_26 (z t : ℝ) (_hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (12:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (1/12)*h0
  norm_num at hh

private lemma cell_9_27 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 12*t + 16:ℝ)=0) (h1 : (16*t^8 - 192*t^7 + t^6*(192*z + 576) + t^5*(640 - 1664*z) + t^4*(7424*z - 5632) + t^3*(8704 - 18944*z) + t^2*(36864*z - 10240) + t*(12288 - 36864*z):ℝ)=0) (h2 : (16*t^8 + t^7*(-128*z - 64) + t^6*(3136*z - 960) + t^5*(13824 - 38272*z) + t^4*(286976*z - 102400) + t^3*(485376 - 1368064*z) + t^2*(4034560*z - 1429504) + t*(2367488 - 6684672*z) + 4718592*z - 1671168:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(175*z/14155776 - 247/3538944) + t^12*(223/294912 - 79*z/589824) + t^11*(365*z/1179648 - 515/294912) + t^10*(1405*z/1769472 - 1987/442368) + t^9*(1807/110592 - 1273*z/442368) + t^8*(419/110592 - 353*z/442368) + t^7*(719*z/110592 - 3587/110592) + t^6*(157/18432 - 31*z/6144) + t^5*(361*z/27648 + 5/27648) + t^4*(-265*z/6912 - 29/6912) + t^3*(809*z/6912 - 167/1728) + t^2*(605/3456 - 463*z/1728) + t*(47*z/96 - 7/72) - 7*z/12 + 11/48)*h0 + (t^7*(247/28311552 - 175*z/113246208) + t^6*(47*z/6291456 - 199/4718592) + t^5*(5*z/14155776 - 29/14155776) + t^4*(499/3538944 - 11*z/442368) + t^3*(73*z/3538944 - 427/3538944) + t^2*(95/589824 - 5*z/196608) + t*(161/884736 - 35*z/884736) - z/442368 + 25/442368)*h1 + (65/36864 - 23*z/73728)*h2 + (175*t^13/589824 - 443*t^12/110592 + 659*t^11/27648 - 1463*t^10/18432 + 5549*t^9/36864 - 11*t^8/108 - 3017*t^7/6912 + 8371*t^6/3456 - 15907*t^5/1152 + 8687*t^4/96 - 368323*t^3/864 + 90521*t^2/72 - 25025*t/12 + 1472)*hf
  norm_num at hh

private lemma cell_9_28 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 12*t + 10:ℝ)=0) (h1 : (16*t^8 - 192*t^7 + t^6*(640 - 64*z) + t^5*(640*z + 64) + t^4*(-1216*z - 3040) + t^3*(2496 - 3328*z) + t^2*(6720*z + 2048) + t*(6784*z - 2368) - 1344*z + 336:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(7/9216 - 5*z/36864) + t^6*(53*z/36864 - 19/2304) + t^5*(187/9216 - 125*z/36864) + t^4*(79/2304 - 203*z/36864) + t^3*(227*z/12288 - 385/3072) + t^2*(215*z/36864 - 151/2304) + t*(395/3072 - 47*z/4096) + 7*z/4096 + 27/256)*h0 + (t*(5*z/294912 - 7/73728) - 23*z/294912 + 17/36864)*h1 + (5*t^7/4608 - 73*t^6/4608 + 325*t^5/4608 - 59*t^4/1536 - 1721*t^3/4608 + 1885*t^2/4608 + 2543*t/4608 - 161/1536)*hf
  norm_num at hh

private lemma cell_9_29 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 12*t + 4:ℝ)=0) (h2 : (16*t^8 - 320*t^7 + t^6*(64*z + 2496) + t^5*(-896*z - 9856) + t^4*(4864*z + 20992) + t^3*(-12288*z - 22784) + t^2*(10496*z + 9984) + t*(14848*z - 4608) - 33792*z + 9984:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(11*z/36864 - 7/4096) + t^6*(155/4608 - 217*z/36864) + t^5*(13*z/288 - 1585/6144) + t^4*(3071/3072 - 3217*z/18432) + t^3*(3335*z/9216 - 19199/9216) + t^2*(313/144 - 3449*z/9216) + t*(139*z/1152 - 1081/1536) + 61*z/1536 - 253/768)*h0 + (t*(7/32768 - 11*z/294912) + 7*z/32768 - 179/147456)*h2 + (11*t^7/4608 - 217*t^6/4608 + 859*t^5/2304 - 575*t^4/384 + 3475*t^3/1152 - 1945*t^2/1152 - 851*t/192 + 231/32)*hf
  norm_num at hh

private lemma cell_9_30 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 12*t + 16:ℝ)=0) (h1 : (16*t^8 - 192*t^7 + t^6*(192*z + 576) + t^5*(640 - 1664*z) + t^4*(7424*z - 5632) + t^3*(8704 - 18944*z) + t^2*(36864*z - 10240) + t*(12288 - 36864*z):ℝ)=0) (h2 : (16*t^8 - 320*t^7 + t^6*(2368 - 64*z) + t^5*(1024*z - 7936) + t^4*(11008 - 5120*z) + t^3*(7168*z - 1024) + t^2*(5120*z - 9216) + t*(4096 - 4096*z):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(73*z/56623104 - 103/14155776) + t^12*(103/589824 - 73*z/2359296) + t^11*(1307*z/4718592 - 461/294912) + t^10*(21103/3538944 - 7481*z/7077888) + t^9*(3055*z/3538944 - 8591/1769472) + t^8*(8311*z/1769472 - 1469/55296) + t^7*(11303/221184 - 8003*z/884736) + t^6*(1879/73728 - 659*z/147456) + t^5*(407*z/55296 - 4627/110592) + t^4*(2045*z/110592 - 361/3456) + t^3*(281/13824 - 187*z/27648) + t^2*(233/3456 - 119*z/13824) + t*(5*z/1152 + 7/288) + 1/16)*h0 + (t^7*(103/113246208 - 73*z/452984832) + t^6*(73*z/25165824 - 103/6291456) + t^5*(5695/56623104 - 1009*z/56623104) + t^4*(575*z/14155776 - 6493/28311552) + t^3*(905/14155776 - 319*z/28311552) + t^2*(505/2359296 - 179*z/4718592) + t*(13/1769472 - 5*z/3538944) - 13*z/442368 + 73/442368)*h1 + (3/16384 - z/32768)*h2 + (73*t^13/2359296 - 365*t^12/442368 + 2089*t^11/221184 - 2287*t^10/36864 + 1077*t^9/4096 - 42217*t^8/55296 + 85937*t^7/55296 - 7205*t^6/3456 + 10939*t^5/9216 + 391*t^4/384 - 5821*t^3/3456 + 19*t^2/16 - 29*t/24)*hf
  norm_num at hh

private lemma cell_9_31 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*t^2 - 24*t + 20:ℝ)=0) (h1 : (256*t^8 - 2560*t^7 + t^6*(8704 - 512*z) + t^5*(4096*z - 9728) + t^4*(-8704*z - 5120) + t^3*(14848 - 2048*z) + t^2*(14848*z - 4608) + t*(2048*z - 2560) - 1536*z + 768:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(425/72576 - 71*z/72576) + t^6*(1277*z/145152 - 1913/36288) + t^5*(10345/72576 - 253*z/10368) + t^4*(1829*z/145152 - 443/9072) + t^3*(2341*z/72576 - 16873/72576) + t^2*(473/5184 - 503*z/20736) + t*(87/896 - 55*z/8064) + 47*z/16128 + 89/2016)*h0 + (t*(71*z/4644864 - 425/4644864) - 709*z/9289728 + 1063/2322432)*h1 + (71*t^7/9072 - 205*t^6/2016 + 4043*t^5/9072 - 11485*t^4/18144 - 1159*t^3/3024 + 19993*t^2/18144 + 233*t/1296 - 709/6048)*hf
  norm_num at hh

private lemma cell_9_32 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (16*z - 8:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/12 - 11/24)*h0 + (-4/3)*hf
  norm_num at hh

private lemma cell_9_33 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (12*z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/9 - 11/18)*h0 + (-4/3)*hf
  norm_num at hh

private lemma cell_9_34 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/3 - 11/6)*h0 + (-4/3)*hf
  norm_num at hh

private lemma cell_9_35 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 20*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(64 - 128*z) + t^6*(2240*z - 896) + t^5*(8000 - 22528*z) + t^4*(142144*z - 50144) + t^3*(201920 - 569984*z) + t^2*(1405760*z - 498176) + t*(678848 - 1918208*z) + 1075392*z - 380592:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(655/36864 - 29*z/9216) + t^6*(889/36864 - 79*z/18432) + t^5*(91*z/4608 - 4069/36864) + t^4*(-17*z/18432 - 115/36864) + t^3*(2783/12288 - 103*z/3072) + t^2*(553/12288 - 155*z/6144) + t*(53*z/768 - 3053/12288) + 297*z/2048 - 3641/4096)*h0 + (t*(29*z/73728 - 655/294912) - 73*z/73728 + 1649/294912)*h1 + (29*t^8/768 - 4433*t^7/4608 + 51811*t^6/4608 - 362257*t^5/4608 + 560365*t^4/1536 - 571763*t^3/512 + 3298043*t^2/1536 - 10704659*t/4608 + 543679/512)*hf
  norm_num at hh

private lemma cell_9_36 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (12*z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/9 - 11/18)*h0 + (-4/3)*hf
  norm_num at hh

private lemma cell_9_37 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (8*z - 4:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/6 - 11/12)*h0 + (-4/3)*hf
  norm_num at hh

private lemma cell_9_38 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h2 : (t*(8192 - 20480*z) + 135168*z - 49152:ℝ)=0) : (t - z - 1:ℝ)=0 := by
  have hh : (t - z - 1:ℝ)=0 := by linear_combination (7/6144 - 5*z/24576)*h2 + (55/2 - 25*t/6)*hf
  exact hh

private lemma cell_9_39 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 16*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(64 - 128*z) + t^6*(2112*z - 576) + t^5*(7424 - 20224*z) + t^4*(112768*z - 38912) + t^3*(137472 - 382464*z) + t^2*(747776*z - 262400) + t*(267264 - 746496*z) + 262656*z - 94464:ℝ)=0) (h2 : (16*t^8 + t^7*(192 - 256*z) + t^6*(8000*z - 2624) + t^5*(55168 - 154752*z) + t^4*(1846528*z - 653312) + t^3*(4964096 - 14010368*z) + t^2*(65940736*z - 23359744) + t*(62305792 - 175886848*z) + 203326464*z - 72028416:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(5*z/14155776 - 7/3538944) + t^12*(z/294912 - 49/2359296) + t^11*(7*z/196608 - 25/196608) + t^10*(-245*z/884736 - 49/110592) + t^9*(953*z/131072 - 175/36864) + t^8*(13321/589824 - 1403*z/16384) + t^7*(11069*z/13824 - 68287/221184) + t^6*(66409/36864 - 194255*z/36864) + t^5*(2491511*z/98304 - 671113/73728) + t^4*(1487231/49152 - 1584919*z/18432) + t^3*(7352395*z/36864 - 290631/4096) + t^2*(960469/9216 - 5434871*z/18432) + t*(2030371*z/8192 - 89783/1024) - 97393*z/1024 + 139627/4096)*h0 + (t^7*(7/28311552 - 5*z/113246208) + t^6*(31/18874368 - 5*z/18874368) + t^5*(13/3145728 - 29*z/18874368) + t^4*(191*z/14155776 + 43/28311552) + t^3*(161/2359296 - 481*z/3145728) + t^2*(4327*z/4718592 - 1445/4718592) + t*(291/262144 - 14761*z/4718592) + 5369*z/1179648 - 1289/786432)*h1 + (5*z/24576 - 7/6144)*h2 + (-5*t^14/1179648 + 119*t^13/1769472 - 391*t^12/884736 + 215*t^11/73728 - 28879*t^10/884736 + 158939*t^9/442368 - 17207*t^8/6144 + 211009*t^7/13824 - 13684993*t^6/221184 + 7460131*t^5/36864 - 13182481*t^4/18432 + 15135013*t^3/4608 - 252260459*t^2/18432 + 109539805*t/3072 - 10506381/256)*hf
  norm_num at hh

private lemma cell_9_40 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/3 - 11/6)*h0 + (-4/3)*hf
  norm_num at hh

private lemma cell_9_41 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h2 : (t*(278528 - 819200*z) + 10911744*z - 3833856:ℝ)=0) : (t - 2*z - 2:ℝ)=0 := by
  have hh : (t - 2*z - 2:ℝ)=0 := by linear_combination (25*z/1548288 - 283/3096576)*h2 + (2500*t/189 - 3700/21)*hf
  exact hh

private lemma cell_9_42 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4 - 8*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (11/12 - z/6)*h0 + (-4/3)*hf
  norm_num at hh

private lemma cell_9_43 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 8*z:ℝ)=0) (h2 : (16*t^8 + t^7*(192 - 256*z) + t^6*(7872*z - 2752) + t^5*(50944 - 145152*z) + t^4*(1621504*z - 574208) + t^3*(3976192 - 11222016*z) + t^2*(47010816*z - 16655360) + t*(38629376 - 109043712*z) + 107323392*z - 38019072:ℝ)=0) : (t - 2*z:ℝ)=0 := by
  have hh : (t - 2*z:ℝ)=0 := by linear_combination (t^6*(61*z/258048 - 43/32256) + t^5*(13*z/6144 - 37/3072) + t^4*(209*z/32256 - 137/4032) + t^3*(-5*z/8064 - 523/16128) + t^2*(341*z/5376 - 221/2688) + t*(-1469*z/8064 - 115/1008) + 101*z/224 - 93/224)*h0 + (43/258048 - 61*z/2064384)*h2 + (-61*t^7/9216 + 7715*t^6/32256 - 69029*t^5/16128 + 24121*t^4/504 - 1335955*t^3/4032 + 2797957*t^2/2016 - 3244597*t/1008 + 9503/3)*hf
  exact hh

private lemma cell_9_44 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 20*z - 6:ℝ)=0) (h1 : (16*t^8 + t^7*(64 - 128*z) + t^6*(2240*z - 896) + t^5*(8000 - 22528*z) + t^4*(142144*z - 50144) + t^3*(201920 - 569984*z) + t^2*(1405760*z - 498176) + t*(678848 - 1918208*z) + 1075392*z - 380592:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(655/36864 - 29*z/9216) + t^6*(889/36864 - 79*z/18432) + t^5*(91*z/4608 - 4069/36864) + t^4*(-17*z/18432 - 115/36864) + t^3*(2783/12288 - 103*z/3072) + t^2*(553/12288 - 155*z/6144) + t*(53*z/768 - 3053/12288) + 297*z/2048 - 3641/4096)*h0 + (t*(29*z/73728 - 655/294912) - 73*z/73728 + 1649/294912)*h1 + (29*t^8/768 - 4433*t^7/4608 + 51811*t^6/4608 - 362257*t^5/4608 + 560365*t^4/1536 - 571763*t^3/512 + 3298043*t^2/1536 - 10704659*t/4608 + 543679/512)*hf
  norm_num at hh

private lemma cell_9_45 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 16*z - 4:ℝ)=0) (h1 : (16*t^8 + t^7*(64 - 128*z) + t^6*(2112*z - 576) + t^5*(7424 - 20224*z) + t^4*(112768*z - 38912) + t^3*(137472 - 382464*z) + t^2*(747776*z - 262400) + t*(267264 - 746496*z) + 262656*z - 94464:ℝ)=0) (h2 : (16*t^8 + t^7*(-128*z - 64) + t^6*(3520*z - 576) + t^5*(17280 - 55552*z) + t^4*(584192*z - 199168) + t^3*(1487616 - 4243456*z) + t^2*(20962048*z - 7394560) + t*(22932992 - 64819200*z) + 100263936*z - 35483904:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^13*(541/8026324992 - 383*z/32105299968) + t^12*(61*z/2006581248 - 2815/16052649984) + t^11*(9421/4013162496 - 1577*z/4013162496) + t^10*(5*z/286654464 - 841/286654464) + t^9*(5857*z/2675441664 + 10541/334430208) + t^8*(6395/191102976 - 283*z/2985984) + t^7*(54617*z/71663616 + 1931/71663616) + t^6*(516541/250822656 - 1351517*z/250822656) + t^5*(51649699*z/2006581248 - 2875499/501645312) + t^4*(30437291/1003290624 - 11832563*z/125411328) + t^3*(921433*z/3981312 - 190445/3981312) + t^2*(1280753/13934592 - 5228101*z/13934592) + t*(5928851*z/18579456 + 31139/1161216) - 22219*z/193536 - 320251/3096576)*h0 + (t^7*(383*z/256842399744 - 541/64210599936) + t^6*(7009/128421199872 - 1235*z/128421199872) + t^5*(7445*z/128421199872 - 21419/64210599936) + t^4*(73163/64210599936 - 5993*z/32105299968) + t^3*(32503*z/64210599936 - 58427/16052649984) + t^2*(211921/32105299968 - 10487*z/32105299968) + t*(-32267*z/32105299968 - 204751/16052649984) + 13259*z/2675441664 + 42673/5350883328)*h1 + (541/13934592 - 383*z/55738368)*h2 + (383*t^14/2675441664 - 16325*t^13/4013162496 + 37343*t^12/668860416 - 252139*t^11/501645312 + 244859*t^10/74317824 - 2383655*t^9/143327232 + 1398139*t^8/20901888 - 6830951*t^7/31352832 + 100060249*t^6/167215104 - 405184363*t^5/250822656 + 28693547*t^4/4644864 - 1006176737*t^3/31352832 + 6142961669*t^2/41803776 - 115347301*t/258048 + 400322077/580608)*hf
  norm_num at hh

private lemma cell_9_46 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 8*z:ℝ)=0) (h2 : (16*t^8 + t^7*(-128*z - 64) + t^6*(3136*z - 960) + t^5*(13824 - 38272*z) + t^4*(286976*z - 102400) + t^3*(485376 - 1368064*z) + t^2*(4034560*z - 1429504) + t*(2367488 - 6684672*z) + 4718592*z - 1671168:ℝ)=0) : (t - 2*z:ℝ)=0 := by
  have hh : (t - 2*z:ℝ)=0 := by linear_combination (t^6*(5*z/1536 - 7/384) + t^5*(29/384 - 11*z/768) + t^4*(z/192 + 5/96) + t^3*(-z/12 - 5/24) + t^2*(29*z/48 - 7/48) + t*(7/24 - 19*z/12) + 2*z - 5/4)*h0 + (7/3072 - 5*z/12288)*h2 + (-5*t^7/128 + 229*t^6/192 - 247*t^5/16 + 5587*t^4/48 - 6643*t^3/12 + 3261*t^2/2 - 8098*t/3 + 1904)*hf
  exact hh

private lemma cell_9_47 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*t^2 + t*(-8*z - 8) + 24*z - 4:ℝ)=0) (h1 : (256*t^8 + t^7*(1536 - 2048*z) + t^6*(31232*z - 11776) + t^5*(95744 - 277504*z) + t^4*(1473024*z - 520192) + t^3*(1673728 - 4720640*z) + t^2*(8898048*z - 3154432) + t*(3185152 - 8987648*z) + 3700224*z - 1310976:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(4679/10368 - 103*z/1296) + t^6*(17279/10368 - 6463*z/20736) + t^5*(427*z/1296 - 5165/10368) + t^4*(-23521*z/20736 - 41791/10368) + t^3*(43427*z/5184 - 26515/10368) + t^2*(102385/10368 - 426293*z/20736) + t*(42731*z/1728 - 38965/3456) - 8881*z/768 + 1877/384)*h0 + (t*(103*z/82944 - 4679/663552) - 3541*z/1327104 + 10265/663552)*h1 + (103*t^8/54 - 38737*t^7/864 + 567719*t^6/1296 - 2234845*t^5/864 + 533881*t^4/54 - 20745343*t^3/864 + 46129841*t^2/1296 - 75846913*t/2592 + 365419/36)*hf
  norm_num at hh

private lemma cell_9_48 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (h0 : (4*t^2 - 8*t:ℝ)=0) (h1 : (256*t^8 - 4608*t^7 + t^6*(33280 - 512*z) + t^5*(7168*z - 123904) + t^4*(253952 - 35840*z) + t^3*(75776*z - 282624) + t^2*(155648 - 61440*z) + t*(16384*z - 32768):ℝ)=0) : False := by
  have hh : ((t-((0:ℝ))))*(1:ℝ)=0 := by linear_combination (t^6*(z/256 - 3/128) + t^5*(3/8 - z/16) + t^4*(49*z/128 - 73/32) + t^3*(105/16 - 9*z/8) + t^2*(13*z/8 - 289/32) + t*(11/2 - 17*z/16) + z/4 - 11/8)*h0 + (3/8192 - z/16384)*h1 + (-t^6/32 + 7*t^5/16 - 35*t^4/16 + 37*t^3/8 - 15*t^2/4 + t)*hf
  have hv := (mul_eq_zero.mp hh).resolve_left hn3
  norm_num at hv

private lemma cell_9_49 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*t^2 - 12*t + 2:ℝ)=0) (h1 : (256*t^8 - 5632*t^7 + t^6*(51200 - 512*z) + t^5*(8704*z - 250112) + t^4*(714112 - 55552*z) + t^3*(165888*z - 1211776) + t^2*(1183232 - 237696*z) + t*(156800*z - 603200) - 37440*z + 121680:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(z/756 - 25/3024) + t^6*(79/504 - 25*z/1008) + t^5*(79*z/432 - 7055/6048) + t^4*(26275/6048 - 4111*z/6048) + t^3*(1375*z/1008 - 34555/4032) + t^2*(52961/6048 - 2557*z/1728) + t*(9745*z/12096 - 98279/24192) - 65*z/384 + 1019/2688)*h0 + (t*(25/193536 - z/48384) - z/193536 + 1/193536)*h1 + (-2*t^7/189 + 67*t^6/378 - 139*t^5/126 + 2375*t^4/756 - 73*t^3/18 + 3043*t^2/1512 + 55*t/1512 - 65/336)*hf
  norm_num at hh

private lemma cell_9_50 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*t^2 + t*(-4*z - 4) + 8*z - 2:ℝ)=0) (h1 : (256*t^8 + t^7*(-1024*z - 3584) + t^6*(23552*z + 15360) + t^5*(14592 - 238080*z) + t^4*(1374464*z - 384128) + t^3*(1662080 - 4880640*z) + t^2*(10580736*z - 3738880) + t*(4549184 - 12823680*z) + 6609984*z - 2343216:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(5*z/144 - 29/144) + t^6*(3 - z/2) + t^5*(745*z/288 - 4921/288) + t^4*(13211/288 - 341*z/72) + t^3*(-1097*z/192 - 10615/192) + t^2*(355*z/9 + 1033/72) + t*(27695/1152 - 76151*z/1152) + 3925*z/96 - 7031/384)*h0 + (t*(29/9216 - 5*z/9216) + z/2304 - 25/9216)*h1 + (-5*t^8/12 + 197*t^7/18 - 3001*t^6/24 + 14569*t^5/18 - 51671*t^4/16 + 580481*t^3/72 - 388147*t^2/32 + 708793*t/72 - 3196)*hf
  norm_num at hh

private lemma cell_9_51 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h2 : (16*t^8 - 192*t^7 + t^6*(64*z + 768) + t^5*(-512*z - 1088) + t^4*(1472*z - 352) + t^3*(2496 - 1024*z) + t^2*(-5440*z - 896) + t*(15872*z - 4800) - 23232*z + 8400:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(17/1536 - z/512) + t^6*(35*z/1536 - 33/256) + t^5*(775/1536 - 137*z/1536) + t^4*(197*z/1536 - 557/768) + t^3*(23*z/1536 - 133/1536) + t^2*(365/256 - 383*z/1536) + t*(413*z/1536 - 2363/1536) - 11*z/512 + 27/256)*h0 + (t*(z/4096 - 17/12288) - 11*z/12288 + 31/6144)*h2 + (-t^7/64 + 35*t^6/192 - 157*t^5/192 + 301*t^4/192 + 79*t^3/192 - 1679*t^2/192 + 3817*t/192 - 1331/64)*hf
  norm_num at hh

private lemma cell_9_52 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*t^2 - 12*t + 2:ℝ)=0) (h1 : (256*t^8 - 5632*t^7 + t^6*(51200 - 512*z) + t^5*(8704*z - 250112) + t^4*(714112 - 55552*z) + t^3*(165888*z - 1211776) + t^2*(1183232 - 237696*z) + t*(156800*z - 603200) - 37440*z + 121680:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(z/756 - 25/3024) + t^6*(79/504 - 25*z/1008) + t^5*(79*z/432 - 7055/6048) + t^4*(26275/6048 - 4111*z/6048) + t^3*(1375*z/1008 - 34555/4032) + t^2*(52961/6048 - 2557*z/1728) + t*(9745*z/12096 - 98279/24192) - 65*z/384 + 1019/2688)*h0 + (t*(25/193536 - z/48384) - z/193536 + 1/193536)*h1 + (-2*t^7/189 + 67*t^6/378 - 139*t^5/126 + 2375*t^4/756 - 73*t^3/18 + 3043*t^2/1512 + 55*t/1512 - 65/336)*hf
  norm_num at hh

private lemma cell_9_53 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*t^2 - 16*t + 4:ℝ)=0) (h1 : (256*t^8 - 6656*t^7 + t^6*(72192 - 512*z) + t^5*(10240*z - 425472) + t^4*(1485824 - 78336*z) + t^3*(288768*z - 3139072) + t^2*(3909120 - 534016*z) + t*(475136*z - 2621952) - 161280*z + 725760:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(5*z/2304 - 29/2304) + t^6*(215/768 - 37*z/768) + t^5*(985*z/2304 - 5731/2304) + t^4*(2911/256 - 1501*z/768) + t^3*(11419*z/2304 - 66283/2304) + t^2*(31001/768 - 5371*z/768) + t*(11783*z/2304 - 67253/2304) - 385*z/256 + 2129/256)*h0 + (t*(29/147456 - 5*z/147456) + z/147456 - 7/147456)*h1 + (-5*t^7/288 + 101*t^6/288 - 785*t^5/288 + 991*t^4/96 - 5779*t^3/288 + 5683*t^2/288 - 2503*t/288 + 35/32)*hf
  norm_num at hh

private lemma cell_9_54 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*t^2 + t*(-4*z - 8) + 8*z:ℝ)=0) (h2 : (256*t^8 - 4608*t^7 + t^6*(33280 - 512*z) + t^5*(7168*z - 123904) + t^4*(253952 - 35840*z) + t^3*(75776*z - 282624) + t^2*(155648 - 61440*z) + t*(16384*z - 32768):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(7*z/768 - 79/1536) + t^6*(43/48 - 61*z/384) + t^5*(279*z/256 - 1573/256) + t^4*(337/16 - 239*z/64) + t^3*(855*z/128 - 1207/32) + t^2*(3217/96 - 569*z/96) + t*(209*z/96 - 295/24) - z/16 + 3/8)*h0 + (t*(79/98304 - 7*z/49152) + 25*z/98304 - 35/24576)*h2 + (7*t^8/192 - 25*t^7/32 + 217*t^6/32 - 367*t^5/12 + 153*t^4/2 - 631*t^3/6 + 889*t^2/12 - 131*t/6 + 1/2)*hf
  norm_num at hh

private lemma cell_9_55 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 12*t + 4:ℝ)=0) (h2 : (16*t^8 - 320*t^7 + t^6*(64*z + 2496) + t^5*(-896*z - 9856) + t^4*(4864*z + 20992) + t^3*(-12288*z - 22784) + t^2*(10496*z + 9984) + t*(14848*z - 4608) - 33792*z + 9984:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(11*z/36864 - 7/4096) + t^6*(155/4608 - 217*z/36864) + t^5*(13*z/288 - 1585/6144) + t^4*(3071/3072 - 3217*z/18432) + t^3*(3335*z/9216 - 19199/9216) + t^2*(313/144 - 3449*z/9216) + t*(139*z/1152 - 1081/1536) + 61*z/1536 - 253/768)*h0 + (t*(7/32768 - 11*z/294912) + 7*z/32768 - 179/147456)*h2 + (11*t^7/4608 - 217*t^6/4608 + 859*t^5/2304 - 575*t^4/384 + 3475*t^3/1152 - 1945*t^2/1152 - 851*t/192 + 231/32)*hf
  norm_num at hh

private lemma cell_9_56 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*t^2 + t*(-4*z - 4) + 8*z - 2:ℝ)=0) (h1 : (256*t^8 + t^7*(-1024*z - 3584) + t^6*(23552*z + 15360) + t^5*(14592 - 238080*z) + t^4*(1374464*z - 384128) + t^3*(1662080 - 4880640*z) + t^2*(10580736*z - 3738880) + t*(4549184 - 12823680*z) + 6609984*z - 2343216:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(5*z/144 - 29/144) + t^6*(3 - z/2) + t^5*(745*z/288 - 4921/288) + t^4*(13211/288 - 341*z/72) + t^3*(-1097*z/192 - 10615/192) + t^2*(355*z/9 + 1033/72) + t*(27695/1152 - 76151*z/1152) + 3925*z/96 - 7031/384)*h0 + (t*(29/9216 - 5*z/9216) + z/2304 - 25/9216)*h1 + (-5*t^8/12 + 197*t^7/18 - 3001*t^6/24 + 14569*t^5/18 - 51671*t^4/16 + 580481*t^3/72 - 388147*t^2/32 + 708793*t/72 - 3196)*hf
  norm_num at hh

private lemma cell_9_57 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*t^2 + t*(-4*z - 8) + 8*z:ℝ)=0) (h2 : (256*t^8 - 4608*t^7 + t^6*(1536*z + 35328) + t^5*(-20480*z - 151552) + t^4*(130048*z + 392192) + t^3*(-481280*z - 600064) + t^2*(1112064*z + 444416) + t*(24576 - 1511424*z) + 995328*z - 221184:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(10351*z/870912 - 58409/870912) + t^6*(233095/217728 - 165233*z/870912) + t^5*(556697*z/435456 - 1570427/217728) + t^4*(5845291/217728 - 518185*z/108864) + t^3*(2306347*z/217728 - 12999269/217728) + t^2*(2142839/27216 - 3046115*z/217728) + t*(363011*z/36288 - 127159/2268) - 2885*z/1008 + 31877/2016)*h0 + (t*(58409/55738368 - 10351*z/55738368) + 1657*z/27869184 - 9269/27869184)*h2 + (10351*t^8/217728 - 123829*t^7/217728 + 3547*t^6/1296 - 106105*t^5/27216 - 906761*t^4/54432 + 1713319*t^3/18144 - 331462*t^2/1701 + 103889*t/567 - 9143/252)*hf
  norm_num at hh

private lemma cell_9_58 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4*t^2 - 8*t*z + 16*z - 4:ℝ)=0) (h1 : (256*t^8 + t^7*(-2048*z - 2560) + t^6*(59904*z - 5632) + t^5*(257536 - 818176*z) + t^4*(6574592*z - 2306048) + t^3*(11594240 - 32704512*z) + t^2*(98854400*z - 35031552) + t*(58864128 - 166159360*z) + 118967808*z - 42144000:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(25*z/4608 - 71/2304) + t^6*(101/256 - 35*z/512) + t^5*(1373*z/4608 - 4255/2304) + t^4*(2759/768 - 517*z/1536) + t^3*(-7105*z/4608 - 3181/2304) + t^2*(10705*z/1536 - 1145/256) + t*(13627/2304 - 57749*z/4608) + 14333*z/1536 - 2051/768)*h0 + (t*(71/147456 - 25*z/294912) + 17*z/294912 - 49/147456)*h1 + (-25*t^8/192 + 73*t^7/16 - 208*t^6/3 + 171947*t^5/288 - 9475*t^4/3 + 496591*t^3/48 - 59987*t^2/3 + 5742241*t/288 - 1345367/192)*hf
  norm_num at hh

private lemma cell_9_59 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 8*z:ℝ)=0) (h2 : (16*t^8 + t^7*(-128*z - 64) + t^6*(3136*z - 960) + t^5*(13824 - 38272*z) + t^4*(286976*z - 102400) + t^3*(485376 - 1368064*z) + t^2*(4034560*z - 1429504) + t*(2367488 - 6684672*z) + 4718592*z - 1671168:ℝ)=0) : (t - 2*z:ℝ)=0 := by
  have hh : (t - 2*z:ℝ)=0 := by linear_combination (t^6*(5*z/1536 - 7/384) + t^5*(29/384 - 11*z/768) + t^4*(z/192 + 5/96) + t^3*(-z/12 - 5/24) + t^2*(29*z/48 - 7/48) + t*(7/24 - 19*z/12) + 2*z - 5/4)*h0 + (7/3072 - 5*z/12288)*h2 + (-5*t^7/128 + 229*t^6/192 - 247*t^5/16 + 5587*t^4/48 - 6643*t^3/12 + 3261*t^2/2 - 8098*t/3 + 1904)*hf
  exact hh

private lemma cell_9_60 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 8*t + 2:ℝ)=0) (h2 : (16*t^8 + t^7*(128*z - 448) + t^6*(4096 - 448*z) + t^5*(4224*z - 20544) + t^4*(50848 - 8768*z) + t^3*(9088*z - 62272) + t^2*(36224 - 15168*z) + t*(-3200*z - 1216) + 1344*z - 2352:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(49*z/72192 - 161/36096) + t^6*(7531/72192 - 737*z/36096) + t^5*(3533*z/24064 - 10749/12032) + t^4*(89399/24064 - 8231*z/12032) + t^3*(31897*z/24064 - 91161/12032) + t^2*(525881/72192 - 43999*z/36096) + t*(59029*z/72192 - 93077/36096) + 3815*z/12032 - 12587/24064)*h0 + (t*(161/288768 - 49*z/577536) + 37*z/288768 - 587/577536)*h2 + (49*t^8/4512 - 491*t^7/9024 + 469*t^6/1128 - 11597*t^5/9024 + 2137*t^4/1128 - 22121*t^3/9024 + 943*t^2/564 + 4729*t/9024 - 259/1504)*hf
  norm_num at hh

private lemma cell_9_61 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 - 12*t + 4:ℝ)=0) (h2 : (16*t^8 + t^7*(128*z - 576) + t^6*(7616 - 1344*z) + t^5*(9216*z - 53888) + t^4*(219136 - 38912*z) + t^3*(92160*z - 517376) + t^2*(692992 - 125184*z) + t*(89088*z - 481792) - 24576*z + 132864:ℝ)=0) : (t + z - 6:ℝ)=0 := by
  have hh : (t + z - 6:ℝ)=0 := by linear_combination (t^6*(409/248832 - 145*z/497664) + t^5*(1967*z/248832 - 5555/124416) + t^4*(19171/41472 - 6793*z/82944) + t^3*(2861*z/6912 - 4039/1728) + t^2*(382319/62208 - 135497*z/124416) + t*(90661*z/62208 - 256417/31104) - 6079*z/6912 + 16855/3456)*h0 + (145*z/3981312 - 409/1990656)*h2 + (-145*t^7/31104 + 1015*t^6/20736 - 145*t^5/432 + 2755*t^4/1944 - 725*t^3/216 + 23635*t^2/5184 - 4205*t/1296 + 145/162)*hf
  exact hh

private lemma cell_9_62 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (2*t^2 + t*(-4*z - 4) + 8*z:ℝ)=0) (h2 : (16*t^8 - 320*t^7 + t^6*(2368 - 64*z) + t^5*(1024*z - 7936) + t^4*(11008 - 5120*z) + t^3*(7168*z - 1024) + t^2*(5120*z - 9216) + t*(4096 - 4096*z):ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(39161*z/2285568 - 13817/142848) + t^6*(532681/285696 - 377437*z/1142784) + t^5*(649327*z/285696 - 3665701/285696) + t^4*(5218133/142848 - 115531*z/17856) + t^3*(741847*z/142848 - 2094827/71424) + t^2*(42237*z/7936 - 119215/3968) + t*(103187/4464 - 73049*z/17856) - z/16 + 3/8)*h0 + (t*(13817/1142784 - 39161*z/18284544) + 19441*z/4571136 - 109699/4571136)*h2 + (39161*t^8/571392 - 455759*t^7/285696 + 676087*t^6/47616 - 2120713*t^5/35712 + 3916237*t^4/35712 - 710257*t^3/17856 - 8591*t^2/96 + 111373*t/2232 + 1/2)*hf
  norm_num at hh

private lemma cell_9_63 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (4 - 8*t:ℝ)=0) (h2 : (t*(5632*z - 2560) - 18432*z + 6912:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/8 - 3/4)*h0 + (43/4032 - 61*z/32256)*h2 + (671*t/63 - 244/7)*hf
  norm_num at hh

private lemma pair_9_25_38 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z - 1:ℝ)=0) (h2 : (t*(278528 - 819200*z) + 10911744*z - 3833856:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7/9 - z/9)*h0 + (209/3096576 - 37*z/3096576)*h2 + (8207/63 - 1850*t/189)*hf
  norm_num at hh

private lemma pair_9_25_41 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z - 1:ℝ)=0) (h1 : (t - 2*z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7/9 - z/9)*h0 + (z/9 - 7/9)*h1 + (1/9)*hf
  norm_num at hh

private lemma pair_9_25_43 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z - 1:ℝ)=0) (h1 : (t - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/3 - 5/3)*h0 + (5/3 - z/3)*h1 + (-1/3)*hf
  norm_num at hh

private lemma pair_9_25_46 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z - 1:ℝ)=0) (h1 : (t - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/3 - 5/3)*h0 + (5/3 - z/3)*h1 + (-1/3)*hf
  norm_num at hh

private lemma pair_9_25_59 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z - 1:ℝ)=0) (h1 : (t - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/3 - 5/3)*h0 + (5/3 - z/3)*h1 + (-1/3)*hf
  norm_num at hh

private lemma pair_9_25_61 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z - 1:ℝ)=0) (h1 : (t + z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7/27 - 2*z/27)*h0 + (2*z/27 - 7/27)*h1 + (-4/27)*hf
  norm_num at hh

private lemma pair_9_38_41 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z - 1:ℝ)=0) (h1 : (t - 2*z - 2:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7/9 - z/9)*h0 + (z/9 - 7/9)*h1 + (1/9)*hf
  norm_num at hh

private lemma pair_9_38_43 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z - 1:ℝ)=0) (h1 : (t - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/3 - 5/3)*h0 + (5/3 - z/3)*h1 + (-1/3)*hf
  norm_num at hh

private lemma pair_9_38_46 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z - 1:ℝ)=0) (h1 : (t - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/3 - 5/3)*h0 + (5/3 - z/3)*h1 + (-1/3)*hf
  norm_num at hh

private lemma pair_9_38_59 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z - 1:ℝ)=0) (h1 : (t - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (z/3 - 5/3)*h0 + (5/3 - z/3)*h1 + (-1/3)*hf
  norm_num at hh

private lemma pair_9_38_61 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - z - 1:ℝ)=0) (h1 : (t + z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7/27 - 2*z/27)*h0 + (2*z/27 - 7/27)*h1 + (-4/27)*hf
  norm_num at hh

private lemma pair_9_41_43 (z t : ℝ) (_hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z - 2:ℝ)=0) (h1 : (t - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/2)*h0 + (1/2)*h1
  norm_num at hh

private lemma pair_9_41_46 (z t : ℝ) (_hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z - 2:ℝ)=0) (h1 : (t - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/2)*h0 + (1/2)*h1
  norm_num at hh

private lemma pair_9_41_59 (z t : ℝ) (_hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z - 2:ℝ)=0) (h1 : (t - 2*z:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (-1/2)*h0 + (1/2)*h1
  norm_num at hh

private lemma pair_9_41_61 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z - 2:ℝ)=0) (h1 : (t + z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (7/19 - 3*z/38)*h0 + (3*z/38 - 7/19)*h1 + (-9/38)*hf
  norm_num at hh

private lemma pair_9_43_46 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z:ℝ)=0) (h2 : (256*t^8 + t^7*(-2048*z - 512) + t^6*(45568*z - 15872) + t^5*(184320 - 504832*z) + t^4*(3355648*z - 1192960) + t^3*(4872192 - 13772800*z) + t^2*(34023424*z - 12048384) + t*(16375808 - 46219264*z) + 26431488*z - 9363456:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(209*z/6048 - 295/1512) + t^6*(1217/1512 - 431*z/3024) + t^5*(551/1512 - 197*z/3024) + t^4*(529*z/756 - 1483/378) + t^3*(341/756 - 155*z/1512) + t^2*(115/21 - 229*z/252) + t*(227/378 - 149*z/756) + z/3 - 5/3)*h0 + (295/387072 - 209*z/1548288)*h2 + (-209*t^7/1008 + 657*t^6/112 - 51617*t^5/756 + 229003*t^4/504 - 117140*t^3/63 + 3470743*t^2/756 - 2358505*t/378 + 149881/42)*hf
  norm_num at hh

private lemma pair_9_43_59 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z:ℝ)=0) (h2 : (256*t^8 + t^7*(-2048*z - 512) + t^6*(45568*z - 15872) + t^5*(184320 - 504832*z) + t^4*(3355648*z - 1192960) + t^3*(4872192 - 13772800*z) + t^2*(34023424*z - 12048384) + t*(16375808 - 46219264*z) + 26431488*z - 9363456:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(209*z/6048 - 295/1512) + t^6*(1217/1512 - 431*z/3024) + t^5*(551/1512 - 197*z/3024) + t^4*(529*z/756 - 1483/378) + t^3*(341/756 - 155*z/1512) + t^2*(115/21 - 229*z/252) + t*(227/378 - 149*z/756) + z/3 - 5/3)*h0 + (295/387072 - 209*z/1548288)*h2 + (-209*t^7/1008 + 657*t^6/112 - 51617*t^5/756 + 229003*t^4/504 - 117140*t^3/63 + 3470743*t^2/756 - 2358505*t/378 + 149881/42)*hf
  norm_num at hh

private lemma pair_9_43_61 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z:ℝ)=0) (h1 : (t + z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2/9 - z/18)*h0 + (z/18 - 2/9)*h1 + (-1/6)*hf
  norm_num at hh

private lemma pair_9_46_59 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z:ℝ)=0) (h2 : (4096*t^8 + t^7*(-32768*z - 4096) + t^6*(708608*z - 241664) + t^5*(2838528 - 7942144*z) + t^4*(54505472*z - 19333120) + t^3*(83386368 - 235417600*z) + t^2*(624680960*z - 221282304) + t*(329826304 - 931053568*z) + 596901888*z - 211451904:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (t^7*(1307*z/1512 - 7379/1512) + t^6*(23063/1512 - 4085*z/1512) + t^5*(23*z/378 - 521/1512) + t^4*(1007*z/189 - 45469/1512) + t^3*(6079/756 - 2165*z/1512) + t^2*(317/18 - 223*z/72) + t*(86/189 - 89*z/756) + z/3 - 11/6)*h0 + (7379/6193152 - 1307*z/6193152)*h2 + (-1307*t^7/252 + 72647*t^6/504 - 2534089*t^5/1512 + 5802787*t^4/504 - 25041385*t^3/504 + 49830301*t^2/378 - 37136489*t/189 + 881794/7)*hf
  norm_num at hh

private lemma pair_9_46_61 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z:ℝ)=0) (h1 : (t + z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2/9 - z/18)*h0 + (z/18 - 2/9)*h1 + (-1/6)*hf
  norm_num at hh

private lemma pair_9_59_61 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (_hn0 : t-(1)≠0) (_hn1 : t-(2)≠0) (_hn2 : t-(z)≠0) (_hn3 : t-((0:ℝ))≠0) (h0 : (t - 2*z:ℝ)=0) (h1 : (t + z - 6:ℝ)=0) : False := by
  have hh : (1:ℝ)=0 := by linear_combination (2/9 - z/18)*h0 + (z/18 - 2/9)*h1 + (-1/6)*hf
  norm_num at hh

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_0 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 0) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_0 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_1 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 1) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_1 z t hf hn0 hn1 hn2 hn3
  · have hr : (-6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_2 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 2) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_2 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_3 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 3) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_3 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z + 64*t^7 + 448*t^6*z^2 - 576*t^6*z - 128*t^6 - 896*t^5*z^3 + 2112*t^5*z^2 + 256*t^5*z - 448*t^5 + 1120*t^4*z^4 - 4160*t^4*z^3 + 896*t^4*z^2 + 2880*t^4*z + 544*t^4 - 896*t^3*z^5 + 4800*t^3*z^4 - 3584*t^3*z^3 - 6016*t^3*z^2 - 128*t^3*z + 704*t^3 + 448*t^2*z^6 - 3264*t^2*z^5 + 4736*t^2*z^4 + 5248*t^2*z^3 - 4416*t^2*z^2 - 4032*t^2*z - 768*t^2 - 128*t*z^7 + 1216*t*z^6 - 2816*t*z^5 - 1728*t*z^4 + 7040*t*z^3 + 832*t*z^2 + 4096*t*z - 320*t + 16*z^8 - 192*z^7 + 640*z^6 + 64*z^5 - 3040*z^4 + 2496*z^3 + 2048*z^2 - 2368*z + 336:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 3264*t^5 - 1120*t^4*z^2 - 2560*t^4*z - 14016*t^4 + 896*t^3*z^3 + 576*t^3*z^2 + 5248*t^3*z + 36352*t^3 - 448*t^2*z^4 + 576*t^2*z^3 - 384*t^2*z^2 - 8704*t^2*z - 47040*t^2 + 128*t*z^5 - 448*t*z^4 - 128*t*z^3 + 1856*t*z^2 + 4352*t*z + 21568*t - 16*z^6 + 96*z^5 - 32*z^4 - 448*z^3 + 416*z^2 + 896*z + 2496)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_4 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 4) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_4 z t hf hn0 hn1 hn2 hn3
  · have hr : (-6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_5 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 5) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_5 z t hf hn0 hn1 hn2 hn3
  · have hr : (-8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_6 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 6) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_6 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_7 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 7) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_7 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7 - 64*t^6*z + 64*t^6 + 256*t^5*z - 256*t^4 - 1024*t^3*z + 1024*t^3 + 1024*t^2*z - 1024*t^2:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_8 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 8) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_8 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_9 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 9) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_9 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_10 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 10) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_10 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*z^2 - 16*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_11 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 11) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_11 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2*z^2 - 8*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 64*t^7 + 64*t^6*z^2 - 64*t^6*z - 192*t^6 - 192*t^5*z^2 + 256*t^5*z + 768*t^5 + 96*t^4*z^4 - 192*t^4*z^3 - 576*t^4*z^2 + 768*t^4*z + 512*t^4 - 192*t^3*z^4 + 512*t^3*z^3 + 1536*t^3*z^2 - 3072*t^3*z - 2048*t^3 + 64*t^2*z^6 - 192*t^2*z^5 - 576*t^2*z^4 + 1536*t^2*z^3 + 1024*t^2*z^2 - 2048*t^2*z - 64*t*z^6 + 256*t*z^5 + 768*t*z^4 - 3072*t*z^3 - 2048*t*z^2 + 8192*t*z + 16*z^8 - 64*z^7 - 192*z^6 + 768*z^5 + 512*z^4 - 2048*z^3:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-64*t^6 + 192*t^5 - 96*t^4*z^2 - 384*t^4*z - 1536*t^4 + 192*t^3*z^2 + 640*t^3*z + 1920*t^3 - 64*t^2*z^4 - 192*t^2*z^3 - 448*t^2*z^2 - 3840*t^2*z - 23168*t^2 + 64*t*z^4 + 128*t*z^3 - 128*t*z^2 + 2048*t*z + 14592*t - 16*z^6 - 32*z^5 + 32*z^4 - 512*z^3 - 3648*z^2 - 18816*z - 105600)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_12 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 12) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_12 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 192*t^7 + 64*t^6*z^2 - 320*t^6*z + 896*t^6 - 576*t^5*z^2 + 2944*t^5*z - 2240*t^5 + 96*t^4*z^4 - 960*t^4*z^3 + 4224*t^4*z^2 - 9664*t^4*z + 3104*t^4 - 576*t^3*z^4 + 5888*t^3*z^3 - 17536*t^3*z^2 + 14592*t^3*z - 1088*t^3 + 64*t^2*z^6 - 960*t^2*z^5 + 5760*t^2*z^4 - 18560*t^2*z^3 + 29504*t^2*z^2 - 8384*t^2*z - 2816*t^2 - 192*t*z^6 + 2944*t*z^5 - 15296*t*z^4 + 30464*t*z^3 - 15680*t*z^2 - 5248*t*z + 3520*t + 16*z^8 - 320*z^7 + 2432*z^6 - 8896*z^5 + 15904*z^4 - 10688*z^3 - 4096*z^2 + 6080*z - 1200:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-64*t^6 + 576*t^5 - 96*t^4*z^2 + 384*t^4*z - 1728*t^4 + 576*t^3*z^2 - 2432*t^3*z + 1792*t^3 - 64*t^2*z^4 + 576*t^2*z^3 - 2176*t^2*z^2 + 4352*t^2*z + 960*t^2 + 192*t*z^4 - 1792*t*z^3 + 4160*t*z^2 - 1920*t*z - 4160*t - 16*z^6 + 224*z^5 - 1056*z^4 + 2112*z^3 - 1120*z^2 - 256*z + 4800)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_13 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 13) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_13 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 64*t^7 - 64*t^6*z + 64*t^6 + 256*t^5*z - 256*t^4 - 1024*t^3*z + 1024*t^3 + 1024*t^2*z - 1024*t^2:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_14 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 14) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_14 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2*z^2 - 8*z + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 64*t^7 + 64*t^6*z^2 - 64*t^6*z - 192*t^6 - 192*t^5*z^2 + 256*t^5*z + 768*t^5 + 96*t^4*z^4 - 192*t^4*z^3 - 576*t^4*z^2 + 768*t^4*z + 512*t^4 - 192*t^3*z^4 + 512*t^3*z^3 + 1536*t^3*z^2 - 3072*t^3*z - 2048*t^3 + 64*t^2*z^6 - 192*t^2*z^5 - 576*t^2*z^4 + 1536*t^2*z^3 + 1024*t^2*z^2 - 2048*t^2*z - 64*t*z^6 + 256*t*z^5 + 768*t*z^4 - 3072*t*z^3 - 2048*t*z^2 + 8192*t*z + 16*z^8 - 64*z^7 - 192*z^6 + 768*z^5 + 512*z^4 - 2048*z^3:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-64*t^6 + 192*t^5 - 96*t^4*z^2 - 384*t^4*z - 1536*t^4 + 192*t^3*z^2 + 640*t^3*z + 1920*t^3 - 64*t^2*z^4 - 192*t^2*z^3 - 448*t^2*z^2 - 3840*t^2*z - 23168*t^2 + 64*t*z^4 + 128*t*z^3 - 128*t*z^2 + 2048*t*z + 14592*t - 16*z^6 - 32*z^5 + 32*z^4 - 512*z^3 - 3648*z^2 - 18816*z - 105600)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_15 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 15) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_15 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*t^2 - 16*t + 8:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (256*t^8 - 512*t^7 - 512*t^6*z - 1536*t^6 + 1024*t^5*z + 3072*t^5 + 3072*t^4*z + 2048*t^4 - 6144*t^3*z - 4096*t^3 - 4096*t^2*z + 8192*t*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_16 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 16) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_16 z t hf hn0 hn1 hn2 hn3
  · have hr : (8192*t*z:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_17 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 17) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_17 z t hf hn0 hn1 hn2 hn3
  · have hr : (-6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_18 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 18) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_18 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 12*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_19 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 19) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_19 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 12*t + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 192*t^7 - 64*t^6*z + 640*t^6 + 640*t^5*z + 64*t^5 - 1216*t^4*z - 3040*t^4 - 3328*t^3*z + 2496*t^3 + 6720*t^2*z + 2048*t^2 + 6784*t*z - 2368*t - 1344*z + 336:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_20 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 20) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_20 z t hf hn0 hn1 hn2 hn3
  · have hr : (-6:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_21 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 21) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_21 z t hf hn0 hn1 hn2 hn3
  · have hr : (-12:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] 
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_22 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 22) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_22 z t hf hn0 hn1 hn2 hn3
  · have hr : (8192*t*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_23 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 23) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_23 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 12*t + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 128*t^7*z - 64*t^7 + 448*t^6*z^2 + 320*t^6*z - 192*t^6 - 896*t^5*z^3 - 576*t^5*z^2 + 1408*t^5*z + 768*t^5 + 1120*t^4*z^4 + 320*t^4*z^3 - 3904*t^4*z^2 - 2304*t^4*z + 512*t^4 - 896*t^3*z^5 + 320*t^3*z^4 + 5376*t^3*z^3 + 1536*t^3*z^2 - 5120*t^3*z - 2048*t^3 + 448*t^2*z^6 - 576*t^2*z^5 - 3904*t^2*z^4 + 1536*t^2*z^3 + 9216*t^2*z^2 + 2048*t^2*z - 128*t*z^7 + 320*t*z^6 + 1408*t*z^5 - 2304*t*z^4 - 5120*t*z^3 + 2048*t*z^2 + 8192*t*z + 16*z^8 - 64*z^7 - 192*z^6 + 768*z^5 + 512*z^4 - 2048*z^3:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 + 896*t^5*z + 5952*t^5 - 1120*t^4*z^2 - 7040*t^4*z - 36096*t^4 + 896*t^3*z^3 + 5056*t^3*z^2 + 23168*t^3*z + 127360*t^3 - 448*t^2*z^4 - 2112*t^2*z^3 - 7872*t^2*z^2 - 44544*t^2*z - 260736*t^2 + 128*t*z^5 + 448*t*z^4 + 1024*t*z^3 + 7552*t*z^2 + 48384*t*z + 273152*t - 16*z^6 - 32*z^5 + 32*z^4 - 512*z^3 - 3648*z^2 - 18816*z - 105600)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_24 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 24) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_24 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 12*z + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_25 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 25) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : (t - z - 1:ℝ)=0 := by
  apply cell_9_25 z t hf hn0 hn1 hn2 hn3
  · have hr : (-512*t*z^6 + 7168*t*z^5 - 35840*t*z^4 + 75776*t*z^3 - 61440*t*z^2 + 16384*t*z + 256*z^8 - 4608*z^7 + 33280*z^6 - 123904*z^5 + 253952*z^4 - 282624*z^3 + 155648*z^2 - 32768*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(512*t*z^4 - 4096*t*z^3 + 10240*t*z^2 - 6144*t*z + 4096*t - 256*z^6 + 3072*z^5 - 14336*z^4 + 31744*z^3 - 34816*z^2 + 10240*z - 24576)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_26 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 26) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_26 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*z^2 - 24*z + 20:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_27 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 27) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_27 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 12*t + 2*z^2 - 12*z + 20:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 192*t^7 + 64*t^6*z^2 - 192*t^6*z + 704*t^6 - 576*t^5*z^2 + 1792*t^5*z - 512*t^5 + 96*t^4*z^4 - 576*t^4*z^3 + 2112*t^4*z^2 - 4096*t^4*z - 1792*t^4 - 576*t^3*z^4 + 3584*t^3*z^3 - 4608*t^3*z^2 - 2560*t^3*z + 3328*t^3 + 64*t^2*z^6 - 576*t^2*z^5 + 2112*t^2*z^4 - 4608*t^2*z^3 + 1536*t^2*z^2 + 11520*t^2*z - 1280*t^2 - 192*t*z^6 + 1792*t*z^5 - 4096*t*z^4 - 2560*t*z^3 + 11520*t*z^2 - 2048*t + 16*z^8 - 192*z^7 + 704*z^6 - 512*z^5 - 1792*z^4 + 3328*z^3 - 1280*z^2 - 2048*z + 768:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-64*t^6 + 576*t^5 - 96*t^4*z^2 - 1920*t^4 + 576*t^3*z^2 - 128*t^3*z + 2688*t^3 - 64*t^2*z^4 + 192*t^2*z^3 - 832*t^2*z^2 - 768*t^2*z - 4480*t^2 + 192*t*z^4 - 640*t*z^3 - 128*t*z^2 + 3072*t*z + 7168*t - 16*z^6 + 96*z^5 - 96*z^4 - 256*z^3 + 448*z^2 - 128*z - 384)*hf
  · have hr : (16*t^8 - 128*t^7*z - 64*t^7 + 512*t^6*z^2 + 64*t^6*z + 64*t^6 - 1280*t^5*z^3 + 768*t^5*z^2 + 640*t^5*z + 2176*t^4*z^4 - 3712*t^4*z^3 - 640*t^4*z^2 - 768*t^4*z - 256*t^4 - 2560*t^3*z^5 + 7936*t^3*z^4 - 3072*t^3*z^3 - 2048*t^3*z^2 + 1024*t^3 + 2048*t^2*z^6 - 9984*t^2*z^5 + 12544*t^2*z^4 - 3072*t^2*z^3 + 3072*t^2*z^2 + 1024*t^2*z - 1024*t^2 - 1024*t*z^7 + 7168*t*z^6 - 15872*t*z^5 + 10240*t*z^4 + 2048*t*z^3 - 2048*t*z + 256*z^8 - 2560*z^7 + 9728*z^6 - 17408*z^5 + 13312*z^4 + 2048*z^3 - 10240*z^2 + 4096*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-512*t^6 + 1280*t^5*z + 6912*t^5 - 2176*t^4*z^2 - 9344*t^4*z - 51072*t^4 + 2560*t^3*z^3 + 7424*t^3*z^2 + 42496*t^3*z + 242176*t^3 - 2048*t^2*z^4 - 2304*t^2*z^3 - 22272*t^2*z^2 - 125952*t^2*z - 714240*t^2 + 1024*t*z^5 - 1024*t*z^4 + 7680*t*z^3 + 37888*t*z^2 + 209920*t*z + 1183744*t - 256*z^6 + 1024*z^5 - 3072*z^4 - 3072*z^3 - 25600*z^2 - 149504*z - 835584)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_28 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 28) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_28 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 12*t + 10:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 192*t^7 - 64*t^6*z + 640*t^6 + 640*t^5*z + 64*t^5 - 1216*t^4*z - 3040*t^4 - 3328*t^3*z + 2496*t^3 + 6720*t^2*z + 2048*t^2 + 6784*t*z - 2368*t - 1344*z + 336:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_29 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 29) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_29 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 12*t + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 320*t^7 + 64*t^6*z^2 - 320*t^6*z + 2624*t^6 - 960*t^5*z^2 + 4864*t^5*z - 11776*t^5 + 96*t^4*z^4 - 960*t^4*z^3 + 7872*t^4*z^2 - 28160*t^4*z + 31744*t^4 - 960*t^3*z^4 + 9728*t^3*z^3 - 39936*t^3*z^2 + 80896*t^3*z - 51200*t^3 + 64*t^2*z^6 - 960*t^2*z^5 + 7872*t^2*z^4 - 39936*t^2*z^3 + 104448*t^2*z^2 - 120832*t^2*z + 45056*t^2 - 320*t*z^6 + 4864*t*z^5 - 28160*t*z^4 + 80896*t*z^3 - 120832*t*z^2 + 81920*t*z - 16384*t + 16*z^8 - 320*z^7 + 2624*z^6 - 11776*z^5 + 31744*z^4 - 51200*z^3 + 45056*z^2 - 16384*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-64*t^6 + 960*t^5 - 96*t^4*z^2 + 384*t^4*z - 5376*t^4 + 960*t^3*z^2 - 3968*t^3*z + 14208*t^3 - 64*t^2*z^4 + 576*t^2*z^3 - 4288*t^2*z^2 + 13056*t^2*z - 17536*t^2 + 320*t*z^4 - 2944*t*z^3 + 9856*t*z^2 - 15872*t*z + 5888*t - 16*z^6 + 224*z^5 - 1248*z^4 + 3840*z^3 - 6208*z^2 + 6272*z + 4992)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_30 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 30) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_30 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 12*t + 2*z^2 - 12*z + 20:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 192*t^7 + 64*t^6*z^2 - 192*t^6*z + 704*t^6 - 576*t^5*z^2 + 1792*t^5*z - 512*t^5 + 96*t^4*z^4 - 576*t^4*z^3 + 2112*t^4*z^2 - 4096*t^4*z - 1792*t^4 - 576*t^3*z^4 + 3584*t^3*z^3 - 4608*t^3*z^2 - 2560*t^3*z + 3328*t^3 + 64*t^2*z^6 - 576*t^2*z^5 + 2112*t^2*z^4 - 4608*t^2*z^3 + 1536*t^2*z^2 + 11520*t^2*z - 1280*t^2 - 192*t*z^6 + 1792*t*z^5 - 4096*t*z^4 - 2560*t*z^3 + 11520*t*z^2 - 2048*t + 16*z^8 - 192*z^7 + 704*z^6 - 512*z^5 - 1792*z^4 + 3328*z^3 - 1280*z^2 - 2048*z + 768:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-64*t^6 + 576*t^5 - 96*t^4*z^2 - 1920*t^4 + 576*t^3*z^2 - 128*t^3*z + 2688*t^3 - 64*t^2*z^4 + 192*t^2*z^3 - 832*t^2*z^2 - 768*t^2*z - 4480*t^2 + 192*t*z^4 - 640*t*z^3 - 128*t*z^2 + 3072*t*z + 7168*t - 16*z^6 + 96*z^5 - 96*z^4 - 256*z^3 + 448*z^2 - 128*z - 384)*hf
  · have hr : (16*t^8 - 320*t^7 - 64*t^6*z + 2368*t^6 + 1024*t^5*z - 7936*t^5 - 5120*t^4*z + 11008*t^4 + 7168*t^3*z - 1024*t^3 + 5120*t^2*z - 9216*t^2 - 4096*t*z + 4096*t:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_31 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 31) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_31 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*t^2 - 24*t + 20:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (256*t^8 - 2560*t^7 - 512*t^6*z + 8704*t^6 + 4096*t^5*z - 9728*t^5 - 8704*t^4*z - 5120*t^4 - 2048*t^3*z + 14848*t^3 + 14848*t^2*z - 4608*t^2 + 2048*t*z - 2560*t - 1536*z + 768:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_32 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 32) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_32 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*z^2 - 8*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_33 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 33) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_33 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*z^2 - 12*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_34 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 34) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_34 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_35 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 35) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_35 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 4*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4)*hf
  · have hr : (16*t^8 - 128*t^7*z + 64*t^7 + 512*t^6*z^2 - 832*t^6*z + 128*t^6 - 1280*t^5*z^3 + 3840*t^5*z^2 - 2048*t^5*z + 320*t^5 + 2176*t^4*z^4 - 10112*t^4*z^3 + 12032*t^4*z^2 - 4032*t^4*z + 544*t^4 - 2560*t^3*z^5 + 16640*t^3*z^4 - 32768*t^3*z^3 + 22016*t^3*z^2 - 7808*t^3*z + 1216*t^3 + 2048*t^2*z^6 - 17664*t^2*z^5 + 51712*t^2*z^4 - 61696*t^2*z^3 + 32768*t^2*z^2 - 7872*t^2*z + 512*t^2 - 1024*t*z^7 + 11264*t*z^6 - 45056*t*z^5 + 80640*t*z^4 - 67328*t*z^3 + 29440*t*z^2 - 2304*t*z - 1600*t + 256*z^8 - 3584*z^7 + 19456*z^6 - 51456*z^5 + 66944*z^4 - 33664*z^3 - 6400*z^2 + 8640*z - 1200:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-512*t^6 + 1280*t^5*z + 3840*t^5 - 2176*t^4*z^2 - 2944*t^4*z - 25344*t^4 + 2560*t^3*z^3 - 1280*t^3*z^2 + 19968*t^3*z + 100352*t^3 - 2048*t^2*z^4 + 5376*t^2*z^3 - 15360*t^2*z^2 - 41216*t^2*z - 249344*t^2 + 1024*t*z^5 - 5120*t*z^4 + 12288*t*z^3 + 3328*t*z^2 + 62720*t*z + 340224*t - 256*z^6 + 2048*z^5 - 6656*z^4 + 7424*z^3 - 9088*z^2 - 35712*z - 189696)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_36 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 36) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_36 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*z^2 - 12*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_37 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 37) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_37 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*z^2 - 16*z + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_38 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 38) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : (t - z - 1:ℝ)=0 := by
  apply cell_9_38 z t hf hn0 hn1 hn2 hn3
  · have hr : (-512*t*z^6 + 7168*t*z^5 - 35840*t*z^4 + 75776*t*z^3 - 61440*t*z^2 + 16384*t*z + 256*z^8 - 4608*z^7 + 33280*z^6 - 123904*z^5 + 253952*z^4 - 282624*z^3 + 155648*z^2 - 32768*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(512*t*z^4 - 4096*t*z^3 + 10240*t*z^2 - 6144*t*z + 4096*t - 256*z^6 + 3072*z^5 - 14336*z^4 + 31744*z^3 - 34816*z^2 + 10240*z - 24576)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_39 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 39) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_39 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 4*z^2 - 8*z + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4)*hf
  · have hr : (16*t^8 - 128*t^7*z + 64*t^7 + 512*t^6*z^2 - 960*t^6*z + 448*t^6 - 1280*t^5*z^3 + 4608*t^5*z^2 - 4352*t^5*z + 1280*t^5 + 2176*t^4*z^4 - 12416*t^4*z^3 + 22400*t^4*z^2 - 17280*t^4*z + 4864*t^4 - 2560*t^3*z^5 + 20736*t^3*z^4 - 58368*t^3*z^3 + 73216*t^3*z^2 - 43520*t^3*z + 10496*t^3 + 2048*t^2*z^6 - 22272*t^2*z^5 + 90880*t^2*z^4 - 180736*t^2*z^3 + 193024*t^2*z^2 - 105216*t^2*z + 22272*t^2 - 1024*t*z^7 + 14336*t*z^6 - 78848*t*z^5 + 220160*t*z^4 - 338944*t*z^3 + 292864*t*z^2 - 134144*t*z + 25600*t + 256*z^8 - 4608*z^7 + 34304*z^6 - 137728*z^5 + 324608*z^4 - 454144*z^3 + 358912*z^2 - 140800*z + 19200:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-512*t^6 + 1280*t^5*z + 3072*t^5 - 2176*t^4*z^2 - 640*t^4*z - 21888*t^4 + 2560*t^3*z^3 - 5376*t^3*z^2 + 20992*t^3*z + 63488*t^3 - 2048*t^2*z^4 + 9984*t^2*z^3 - 26880*t^2*z^2 - 512*t^2*z - 142336*t^2 + 1024*t*z^5 - 8192*t*z^4 + 27648*t*z^3 - 37888*t*z^2 + 56320*t*z + 120832*t - 256*z^6 + 3072*z^5 - 15360*z^4 + 39424*z^3 - 57344*z^2 + 31232*z - 56832)*hf
  · have hr : (16*t^8 - 256*t^7*z + 192*t^7 + 1856*t^6*z^2 - 3136*t^6*z + 1088*t^6 - 7936*t^5*z^3 + 22080*t^5*z^2 - 17408*t^5*z + 4096*t^5 + 21856*t^4*z^4 - 87744*t^4*z^3 + 115648*t^4*z^2 - 60416*t^4*z + 11264*t^4 - 39680*t^3*z^5 + 213568*t^3*z^4 - 411648*t^3*z^3 + 356352*t^3*z^2 - 144384*t^3*z + 22528*t^3 + 46400*t^2*z^6 - 319680*t^2*z^5 + 836288*t^2*z^4 - 1058816*t^2*z^3 + 694272*t^2*z^2 - 227328*t^2*z + 28672*t^2 - 32000*t*z^7 + 273600*t*z^6 - 926720*t*z^5 + 1597440*t*z^4 - 1508352*t*z^3 + 780288*t*z^2 - 196608*t*z + 16384*t + 10000*z^8 - 104000*z^7 + 443200*z^6 - 998400*z^5 + 1276928*z^4 - 919552*z^3 + 339968*z^2 - 49152*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1856*t^6 + 7936*t^5*z + 25536*t^5 - 21856*t^4*z^2 - 43392*t^4*z - 332288*t^4 + 39680*t^3*z^3 + 24512*t^3*z^2 + 479360*t^3*z + 2470784*t^3 - 46400*t^2*z^4 + 41280*t^2*z^3 - 495808*t^2*z^2 - 1998592*t^2*z - 11694208*t^2 + 32000*t*z^5 - 81600*t*z^4 + 373120*t*z^3 + 804480*t*z^2 + 5588992*t*z + 31144704*t - 10000*z^6 + 44000*z^5 - 159200*z^4 - 44800*z^3 - 1227328*z^2 - 6354816*z - 36014208)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_40 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 40) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_40 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*z^2 - 8*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_41 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 41) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : (t - 2*z - 2:ℝ)=0 := by
  apply cell_9_41 z t hf hn0 hn1 hn2 hn3
  · have hr : (-4096*t*z^6 + 53248*t*z^5 - 266240*t*z^4 + 643072*t*z^3 - 778240*t*z^2 + 450560*t*z - 98304*t + 4096*z^8 - 69632*z^7 + 495616*z^6 - 1921024*z^5 + 4415488*z^4 - 6135808*z^3 + 5013504*z^2 - 2195456*z + 393216:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(4096*t*z^4 - 28672*t*z^3 + 86016*t*z^2 - 69632*t*z + 188416*t - 4096*z^6 + 45056*z^5 - 217088*z^4 + 528384*z^3 - 811008*z^2 + 212992*z - 2113536)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_42 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 42) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_42 z t hf hn0 hn1 hn2 hn3
  · have hr : (4 - 8*z:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_43 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 43) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : (t - 2*z:ℝ)=0 := by
  apply cell_9_43 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 4*z + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 256*t^7*z + 192*t^7 + 1792*t^6*z^2 - 2880*t^6*z + 832*t^6 - 7168*t^5*z^3 + 18432*t^5*z^2 - 12032*t^5*z + 1792*t^5 + 17920*t^4*z^4 - 65280*t^4*z^3 + 70912*t^4*z^2 - 25088*t^4*z + 2816*t^4 - 28672*t^3*z^5 + 138240*t^3*z^4 - 219136*t^3*z^3 + 133120*t^3*z^2 - 31744*t^3*z + 3072*t^3 + 28672*t^2*z^6 - 175104*t^2*z^5 + 375808*t^2*z^4 - 339968*t^2*z^3 + 129024*t^2*z^2 - 19456*t^2*z - 1024*t^2 - 16384*t*z^7 + 122880*t*z^6 - 339968*t*z^5 + 421888*t*z^4 - 225280*t*z^3 + 32768*t*z^2 + 16384*t*z - 4096*t + 4096*z^8 - 36864*z^7 + 126976*z^6 - 204800*z^5 + 143360*z^4 - 12288*z^3 - 28672*z^2 + 8192*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1792*t^6 + 7168*t^5*z + 24576*t^5 - 17920*t^4*z^2 - 42240*t^4*z - 288512*t^4 + 28672*t^3*z^3 + 33792*t^3*z^2 + 364544*t^3*z + 1986560*t^3 - 28672*t^2*z^4 + 3072*t^2*z^3 - 300032*t^2*z^2 - 1466368*t^2*z - 8327168*t^2 + 16384*t*z^5 - 24576*t*z^4 + 159744*t*z^3 + 585728*t*z^2 + 3420160*t*z + 19316736*t - 4096*z^6 + 12288*z^5 - 45056*z^4 - 90112*z^3 - 593920*z^2 - 3371008*z - 19009536)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_44 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 44) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_44 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 4*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4)*hf
  · have hr : (16*t^8 - 128*t^7*z + 64*t^7 + 512*t^6*z^2 - 832*t^6*z + 128*t^6 - 1280*t^5*z^3 + 3840*t^5*z^2 - 2048*t^5*z + 320*t^5 + 2176*t^4*z^4 - 10112*t^4*z^3 + 12032*t^4*z^2 - 4032*t^4*z + 544*t^4 - 2560*t^3*z^5 + 16640*t^3*z^4 - 32768*t^3*z^3 + 22016*t^3*z^2 - 7808*t^3*z + 1216*t^3 + 2048*t^2*z^6 - 17664*t^2*z^5 + 51712*t^2*z^4 - 61696*t^2*z^3 + 32768*t^2*z^2 - 7872*t^2*z + 512*t^2 - 1024*t*z^7 + 11264*t*z^6 - 45056*t*z^5 + 80640*t*z^4 - 67328*t*z^3 + 29440*t*z^2 - 2304*t*z - 1600*t + 256*z^8 - 3584*z^7 + 19456*z^6 - 51456*z^5 + 66944*z^4 - 33664*z^3 - 6400*z^2 + 8640*z - 1200:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-512*t^6 + 1280*t^5*z + 3840*t^5 - 2176*t^4*z^2 - 2944*t^4*z - 25344*t^4 + 2560*t^3*z^3 - 1280*t^3*z^2 + 19968*t^3*z + 100352*t^3 - 2048*t^2*z^4 + 5376*t^2*z^3 - 15360*t^2*z^2 - 41216*t^2*z - 249344*t^2 + 1024*t*z^5 - 5120*t*z^4 + 12288*t*z^3 + 3328*t*z^2 + 62720*t*z + 340224*t - 256*z^6 + 2048*z^5 - 6656*z^4 + 7424*z^3 - 9088*z^2 - 35712*z - 189696)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_45 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 45) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_45 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 4*z^2 - 8*z + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4)*hf
  · have hr : (16*t^8 - 128*t^7*z + 64*t^7 + 512*t^6*z^2 - 960*t^6*z + 448*t^6 - 1280*t^5*z^3 + 4608*t^5*z^2 - 4352*t^5*z + 1280*t^5 + 2176*t^4*z^4 - 12416*t^4*z^3 + 22400*t^4*z^2 - 17280*t^4*z + 4864*t^4 - 2560*t^3*z^5 + 20736*t^3*z^4 - 58368*t^3*z^3 + 73216*t^3*z^2 - 43520*t^3*z + 10496*t^3 + 2048*t^2*z^6 - 22272*t^2*z^5 + 90880*t^2*z^4 - 180736*t^2*z^3 + 193024*t^2*z^2 - 105216*t^2*z + 22272*t^2 - 1024*t*z^7 + 14336*t*z^6 - 78848*t*z^5 + 220160*t*z^4 - 338944*t*z^3 + 292864*t*z^2 - 134144*t*z + 25600*t + 256*z^8 - 4608*z^7 + 34304*z^6 - 137728*z^5 + 324608*z^4 - 454144*z^3 + 358912*z^2 - 140800*z + 19200:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-512*t^6 + 1280*t^5*z + 3072*t^5 - 2176*t^4*z^2 - 640*t^4*z - 21888*t^4 + 2560*t^3*z^3 - 5376*t^3*z^2 + 20992*t^3*z + 63488*t^3 - 2048*t^2*z^4 + 9984*t^2*z^3 - 26880*t^2*z^2 - 512*t^2*z - 142336*t^2 + 1024*t*z^5 - 8192*t*z^4 + 27648*t*z^3 - 37888*t*z^2 + 56320*t*z + 120832*t - 256*z^6 + 3072*z^5 - 15360*z^4 + 39424*z^3 - 57344*z^2 + 31232*z - 56832)*hf
  · have hr : (16*t^8 - 128*t^7*z - 64*t^7 + 704*t^6*z^2 - 704*t^6*z + 832*t^6 - 2432*t^5*z^3 + 4800*t^5*z^2 - 1664*t^5*z - 2304*t^5 + 6496*t^4*z^4 - 25024*t^4*z^3 + 36800*t^4*z^2 - 33024*t^4*z + 15872*t^4 - 12160*t^3*z^5 + 65344*t^3*z^4 - 120576*t^3*z^3 + 79360*t^3*z^2 + 15360*t^3*z - 26624*t^3 + 17600*t^2*z^6 - 137280*t^2*z^5 + 432832*t^2*z^4 - 741888*t^2*z^3 + 777216*t^2*z^2 - 481280*t^2*z + 131072*t^2 - 16000*t*z^7 + 155200*t*z^6 - 594560*t*z^5 + 1123072*t*z^4 - 1020928*t*z^3 + 264192*t*z^2 + 188416*t*z - 98304*t + 10000*z^8 - 136000*z^7 + 795200*z^6 - 2612480*z^5 + 5271040*z^4 - 6670336*z^3 + 5144576*z^2 - 2195456*z + 393216:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-704*t^6 + 2432*t^5*z + 9792*t^5 - 6496*t^4*z^2 - 13952*t^4*z - 107520*t^4 + 12160*t^3*z^3 + 7616*t^3*z^2 + 141952*t^3*z + 757120*t^3 - 17600*t^2*z^4 + 31680*t^2*z^3 - 207552*t^2*z^2 - 566784*t^2*z - 3762816*t^2 + 16000*t*z^5 - 59200*t*z^4 + 207360*t*z^3 + 239488*t*z^2 + 2043136*t*z + 11515648*t - 10000*z^6 + 76000*z^5 - 319200*z^4 + 545280*z^3 - 1360960*z^2 - 2585984*z - 17938560)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_46 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 46) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : (t - 2*z:ℝ)=0 := by
  apply cell_9_46 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 4*z + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 128*t^7*z - 64*t^7 + 512*t^6*z^2 + 64*t^6*z + 64*t^6 - 1280*t^5*z^3 + 768*t^5*z^2 + 640*t^5*z + 2176*t^4*z^4 - 3712*t^4*z^3 - 640*t^4*z^2 - 768*t^4*z - 256*t^4 - 2560*t^3*z^5 + 7936*t^3*z^4 - 3072*t^3*z^3 - 2048*t^3*z^2 + 1024*t^3 + 2048*t^2*z^6 - 9984*t^2*z^5 + 12544*t^2*z^4 - 3072*t^2*z^3 + 3072*t^2*z^2 + 1024*t^2*z - 1024*t^2 - 1024*t*z^7 + 7168*t*z^6 - 15872*t*z^5 + 10240*t*z^4 + 2048*t*z^3 - 2048*t*z + 256*z^8 - 2560*z^7 + 9728*z^6 - 17408*z^5 + 13312*z^4 + 2048*z^3 - 10240*z^2 + 4096*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-512*t^6 + 1280*t^5*z + 6912*t^5 - 2176*t^4*z^2 - 9344*t^4*z - 51072*t^4 + 2560*t^3*z^3 + 7424*t^3*z^2 + 42496*t^3*z + 242176*t^3 - 2048*t^2*z^4 - 2304*t^2*z^3 - 22272*t^2*z^2 - 125952*t^2*z - 714240*t^2 + 1024*t*z^5 - 1024*t*z^4 + 7680*t*z^3 + 37888*t*z^2 + 209920*t*z + 1183744*t - 256*z^6 + 1024*z^5 - 3072*z^4 - 3072*z^3 - 25600*z^2 - 149504*z - 835584)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_47 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 47) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_47 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*t^2 - 8*t*z - 8*t + 4*z^2 + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4)*hf
  · have hr : (256*t^8 - 2048*t^7*z + 1536*t^7 + 7168*t^6*z^2 - 11776*t^6*z + 2560*t^6 - 14336*t^5*z^3 + 38400*t^5*z^2 - 20480*t^5*z + 512*t^5 + 17920*t^4*z^4 - 69120*t^4*z^3 + 65024*t^4*z^2 - 7680*t^4*z - 1024*t^4 - 14336*t^3*z^5 + 74240*t^3*z^4 - 106496*t^3*z^3 + 29696*t^3*z^2 + 8192*t^3*z - 1536*t^3 + 7168*t^2*z^6 - 47616*t^2*z^5 + 95744*t^2*z^4 - 48128*t^2*z^3 - 18432*t^2*z^2 + 9728*t^2*z - 2560*t^2 - 2048*t*z^7 + 16896*t*z^6 - 45056*t*z^5 + 35328*t*z^4 + 16384*t*z^3 - 23040*t*z^2 + 10240*t*z - 512*t + 256*z^8 - 2560*z^7 + 8704*z^6 - 9728*z^5 - 5120*z^4 + 14848*z^3 - 4608*z^2 - 2560*z + 768:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-7168*t^6 + 14336*t^5*z + 47616*t^5 - 17920*t^4*z^2 - 38400*t^4*z - 259584*t^4 + 14336*t^3*z^3 + 11776*t^3*z^2 + 148480*t^3*z + 837632*t^3 - 7168*t^2*z^4 + 4608*t^2*z^3 - 53760*t^2*z^2 - 283648*t^2*z - 1575936*t^2 + 2048*t*z^5 - 4608*t*z^4 + 13312*t*z^3 + 53760*t*z^2 + 279552*t*z + 1592832*t - 256*z^6 + 1024*z^5 - 2048*z^4 - 4608*z^3 - 18432*z^2 - 116224*z - 655872)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_48 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 48) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_48 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*t^2 - 8*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (256*t^8 - 4608*t^7 - 512*t^6*z + 33280*t^6 + 7168*t^5*z - 123904*t^5 - 35840*t^4*z + 253952*t^4 + 75776*t^3*z - 282624*t^3 - 61440*t^2*z + 155648*t^2 + 16384*t*z - 32768*t:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_49 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 49) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_49 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*t^2 - 12*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (256*t^8 - 5632*t^7 - 512*t^6*z + 51200*t^6 + 8704*t^5*z - 250112*t^5 - 55552*t^4*z + 714112*t^4 + 165888*t^3*z - 1211776*t^3 - 237696*t^2*z + 1183232*t^2 + 156800*t*z - 603200*t - 37440*z + 121680:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_50 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 50) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_50 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*t^2 - 4*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (256*t^8 - 1024*t^7*z - 3584*t^7 + 2048*t^6*z^2 + 11264*t^6*z + 19456*t^6 - 2560*t^5*z^3 - 17664*t^5*z^2 - 45056*t^5*z - 51456*t^5 + 2176*t^4*z^4 + 16640*t^4*z^3 + 51712*t^4*z^2 + 80640*t^4*z + 66944*t^4 - 1280*t^3*z^5 - 10112*t^3*z^4 - 32768*t^3*z^3 - 61696*t^3*z^2 - 67328*t^3*z - 33664*t^3 + 512*t^2*z^6 + 3840*t^2*z^5 + 12032*t^2*z^4 + 22016*t^2*z^3 + 32768*t^2*z^2 + 29440*t^2*z - 6400*t^2 - 128*t*z^7 - 832*t*z^6 - 2048*t*z^5 - 4032*t*z^4 - 7808*t*z^3 - 7872*t*z^2 - 2304*t*z + 8640*t + 16*z^8 + 64*z^7 + 128*z^6 + 320*z^5 + 544*z^4 + 1216*z^3 + 512*z^2 - 1600*z - 1200:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2048*t^6 + 2560*t^5*z + 33024*t^5 - 2176*t^4*z^2 - 29696*t^4*z - 225536*t^4 + 1280*t^3*z^3 + 17792*t^3*z^2 + 136960*t^3*z + 847872*t^3 - 512*t^2*z^4 - 6912*t^2*z^3 - 52480*t^2*z^2 - 323072*t^2*z - 1866240*t^2 + 128*t*z^5 + 1600*t*z^4 + 11392*t*z^3 + 69184*t*z^2 + 400128*t*z + 2270272*t - 16*z^6 - 160*z^5 - 1056*z^4 - 6336*z^3 - 36448*z^2 - 207232*z - 1171008)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_51 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 51) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_51 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 192*t^7 + 64*t^6*z^2 - 320*t^6*z + 896*t^6 - 576*t^5*z^2 + 2944*t^5*z - 2240*t^5 + 96*t^4*z^4 - 960*t^4*z^3 + 4224*t^4*z^2 - 9664*t^4*z + 3104*t^4 - 576*t^3*z^4 + 5888*t^3*z^3 - 17536*t^3*z^2 + 14592*t^3*z - 1088*t^3 + 64*t^2*z^6 - 960*t^2*z^5 + 5760*t^2*z^4 - 18560*t^2*z^3 + 29504*t^2*z^2 - 8384*t^2*z - 2816*t^2 - 192*t*z^6 + 2944*t*z^5 - 15296*t*z^4 + 30464*t*z^3 - 15680*t*z^2 - 5248*t*z + 3520*t + 16*z^8 - 320*z^7 + 2432*z^6 - 8896*z^5 + 15904*z^4 - 10688*z^3 - 4096*z^2 + 6080*z - 1200:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-64*t^6 + 576*t^5 - 96*t^4*z^2 + 384*t^4*z - 1728*t^4 + 576*t^3*z^2 - 2432*t^3*z + 1792*t^3 - 64*t^2*z^4 + 576*t^2*z^3 - 2176*t^2*z^2 + 4352*t^2*z + 960*t^2 + 192*t*z^4 - 1792*t*z^3 + 4160*t*z^2 - 1920*t*z - 4160*t - 16*z^6 + 224*z^5 - 1056*z^4 + 2112*z^3 - 1120*z^2 - 256*z + 4800)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_52 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 52) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_52 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*t^2 - 12*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (256*t^8 - 5632*t^7 - 512*t^6*z + 51200*t^6 + 8704*t^5*z - 250112*t^5 - 55552*t^4*z + 714112*t^4 + 165888*t^3*z - 1211776*t^3 - 237696*t^2*z + 1183232*t^2 + 156800*t*z - 603200*t - 37440*z + 121680:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_53 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 53) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_53 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*t^2 - 16*t + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (256*t^8 - 6656*t^7 - 512*t^6*z + 72192*t^6 + 10240*t^5*z - 425472*t^5 - 78336*t^4*z + 1485824*t^4 + 288768*t^3*z - 3139072*t^3 - 534016*t^2*z + 3909120*t^2 + 475136*t*z - 2621952*t - 161280*z + 725760:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_54 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 54) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_54 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*t^2 - 4*t*z - 8*t + 2*z^2 - 4*z + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (256*t^8 - 4608*t^7 - 512*t^6*z + 33280*t^6 + 7168*t^5*z - 123904*t^5 - 35840*t^4*z + 253952*t^4 + 75776*t^3*z - 282624*t^3 - 61440*t^2*z + 155648*t^2 + 16384*t*z - 32768*t:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_55 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 55) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_55 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 12*t + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 - 320*t^7 + 64*t^6*z^2 - 320*t^6*z + 2624*t^6 - 960*t^5*z^2 + 4864*t^5*z - 11776*t^5 + 96*t^4*z^4 - 960*t^4*z^3 + 7872*t^4*z^2 - 28160*t^4*z + 31744*t^4 - 960*t^3*z^4 + 9728*t^3*z^3 - 39936*t^3*z^2 + 80896*t^3*z - 51200*t^3 + 64*t^2*z^6 - 960*t^2*z^5 + 7872*t^2*z^4 - 39936*t^2*z^3 + 104448*t^2*z^2 - 120832*t^2*z + 45056*t^2 - 320*t*z^6 + 4864*t*z^5 - 28160*t*z^4 + 80896*t*z^3 - 120832*t*z^2 + 81920*t*z - 16384*t + 16*z^8 - 320*z^7 + 2624*z^6 - 11776*z^5 + 31744*z^4 - 51200*z^3 + 45056*z^2 - 16384*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-64*t^6 + 960*t^5 - 96*t^4*z^2 + 384*t^4*z - 5376*t^4 + 960*t^3*z^2 - 3968*t^3*z + 14208*t^3 - 64*t^2*z^4 + 576*t^2*z^3 - 4288*t^2*z^2 + 13056*t^2*z - 17536*t^2 + 320*t*z^4 - 2944*t*z^3 + 9856*t*z^2 - 15872*t*z + 5888*t - 16*z^6 + 224*z^5 - 1248*z^4 + 3840*z^3 - 6208*z^2 + 6272*z + 4992)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_56 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 56) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_56 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*t^2 - 4*t*z - 4*t + 2*z^2 - 4*z + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (256*t^8 - 1024*t^7*z - 3584*t^7 + 2048*t^6*z^2 + 11264*t^6*z + 19456*t^6 - 2560*t^5*z^3 - 17664*t^5*z^2 - 45056*t^5*z - 51456*t^5 + 2176*t^4*z^4 + 16640*t^4*z^3 + 51712*t^4*z^2 + 80640*t^4*z + 66944*t^4 - 1280*t^3*z^5 - 10112*t^3*z^4 - 32768*t^3*z^3 - 61696*t^3*z^2 - 67328*t^3*z - 33664*t^3 + 512*t^2*z^6 + 3840*t^2*z^5 + 12032*t^2*z^4 + 22016*t^2*z^3 + 32768*t^2*z^2 + 29440*t^2*z - 6400*t^2 - 128*t*z^7 - 832*t*z^6 - 2048*t*z^5 - 4032*t*z^4 - 7808*t*z^3 - 7872*t*z^2 - 2304*t*z + 8640*t + 16*z^8 + 64*z^7 + 128*z^6 + 320*z^5 + 544*z^4 + 1216*z^3 + 512*z^2 - 1600*z - 1200:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2048*t^6 + 2560*t^5*z + 33024*t^5 - 2176*t^4*z^2 - 29696*t^4*z - 225536*t^4 + 1280*t^3*z^3 + 17792*t^3*z^2 + 136960*t^3*z + 847872*t^3 - 512*t^2*z^4 - 6912*t^2*z^3 - 52480*t^2*z^2 - 323072*t^2*z - 1866240*t^2 + 128*t*z^5 + 1600*t*z^4 + 11392*t*z^3 + 69184*t*z^2 + 400128*t*z + 2270272*t - 16*z^6 - 160*z^5 - 1056*z^4 - 6336*z^3 - 36448*z^2 - 207232*z - 1171008)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_57 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 57) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_57 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*t^2 - 4*t*z - 8*t + 2*z^2 - 4*z + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (256*t^8 - 4608*t^7 + 1024*t^6*z^2 - 4608*t^6*z + 37376*t^6 - 13824*t^5*z^2 + 62464*t^5*z - 179200*t^5 + 1536*t^4*z^4 - 13824*t^4*z^3 + 112128*t^4*z^2 - 367616*t^4*z + 555008*t^4 - 13824*t^3*z^4 + 124928*t^3*z^3 - 546816*t^3*z^2 + 1206272*t^3*z - 1134592*t^3 + 1024*t^2*z^6 - 13824*t^2*z^5 + 112128*t^2*z^4 - 546816*t^2*z^3 + 1536000*t^2*z^2 - 2322432*t^2*z + 1490944*t^2 - 4608*t*z^6 + 62464*t*z^5 - 367616*t*z^4 + 1206272*t*z^3 - 2322432*t*z^2 + 2482176*t*z - 1146880*t + 256*z^8 - 4608*z^7 + 37376*z^6 - 179200*z^5 + 555008*z^4 - 1134592*z^3 + 1490944*z^2 - 1146880*z + 393216:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-1024*t^6 + 13824*t^5 - 1536*t^4*z^2 + 4608*t^4*z - 81408*t^4 + 13824*t^3*z^2 - 41984*t^3*z + 267264*t^3 - 1024*t^2*z^4 + 7680*t^2*z^3 - 64000*t^2*z^2 + 147456*t^2*z - 523264*t^2 + 4608*t*z^4 - 34816*t*z^3 + 149504*t*z^2 - 239616*t*z + 585728*t - 256*z^6 + 3072*z^5 - 18432*z^4 + 62464*z^3 - 143360*z^2 + 149504*z - 307200)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_58 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 58) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_58 z t hf hn0 hn1 hn2 hn3
  · have hr : (4*t^2 - 8*t*z + 4*z^2 - 8*z + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-4)*hf
  · have hr : (256*t^8 - 2048*t^7*z - 2560*t^7 + 7168*t^6*z^2 + 16896*t^6*z + 8704*t^6 - 14336*t^5*z^3 - 47616*t^5*z^2 - 45056*t^5*z - 9728*t^5 + 17920*t^4*z^4 + 74240*t^4*z^3 + 95744*t^4*z^2 + 35328*t^4*z - 5120*t^4 - 14336*t^3*z^5 - 69120*t^3*z^4 - 106496*t^3*z^3 - 48128*t^3*z^2 + 16384*t^3*z + 14848*t^3 + 7168*t^2*z^6 + 38400*t^2*z^5 + 65024*t^2*z^4 + 29696*t^2*z^3 - 18432*t^2*z^2 - 23040*t^2*z - 4608*t^2 - 2048*t*z^7 - 11776*t*z^6 - 20480*t*z^5 - 7680*t*z^4 + 8192*t*z^3 + 9728*t*z^2 + 10240*t*z - 2560*t + 256*z^8 + 1536*z^7 + 2560*z^6 + 512*z^5 - 1024*z^4 - 1536*z^3 - 2560*z^2 - 512*z + 768:ℝ)=0 := by
      convert hc.2.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-7168*t^6 + 14336*t^5*z + 133632*t^5 - 17920*t^4*z^2 - 181760*t^4*z - 1150464*t^4 + 14336*t^3*z^3 + 155136*t^3*z^2 + 1008640*t^3*z + 5789696*t^3 - 7168*t^2*z^4 - 81408*t^2*z^3 - 539136*t^2*z^2 - 3101696*t^2*z - 17513472*t^2 + 2048*t*z^5 + 24064*t*z^4 + 160768*t*z^3 + 924160*t*z^2 + 5215232*t*z + 29433344*t - 256*z^6 - 3072*z^5 - 20480*z^4 - 117248*z^3 - 661504*z^2 - 3732992*z - 21072384)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_59 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 59) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : (t - 2*z:ℝ)=0 := by
  apply cell_9_59 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 4*z + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 128*t^7*z - 64*t^7 + 512*t^6*z^2 + 64*t^6*z + 64*t^6 - 1280*t^5*z^3 + 768*t^5*z^2 + 640*t^5*z + 2176*t^4*z^4 - 3712*t^4*z^3 - 640*t^4*z^2 - 768*t^4*z - 256*t^4 - 2560*t^3*z^5 + 7936*t^3*z^4 - 3072*t^3*z^3 - 2048*t^3*z^2 + 1024*t^3 + 2048*t^2*z^6 - 9984*t^2*z^5 + 12544*t^2*z^4 - 3072*t^2*z^3 + 3072*t^2*z^2 + 1024*t^2*z - 1024*t^2 - 1024*t*z^7 + 7168*t*z^6 - 15872*t*z^5 + 10240*t*z^4 + 2048*t*z^3 - 2048*t*z + 256*z^8 - 2560*z^7 + 9728*z^6 - 17408*z^5 + 13312*z^4 + 2048*z^3 - 10240*z^2 + 4096*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-512*t^6 + 1280*t^5*z + 6912*t^5 - 2176*t^4*z^2 - 9344*t^4*z - 51072*t^4 + 2560*t^3*z^3 + 7424*t^3*z^2 + 42496*t^3*z + 242176*t^3 - 2048*t^2*z^4 - 2304*t^2*z^3 - 22272*t^2*z^2 - 125952*t^2*z - 714240*t^2 + 1024*t*z^5 - 1024*t*z^4 + 7680*t*z^3 + 37888*t*z^2 + 209920*t*z + 1183744*t - 256*z^6 + 1024*z^5 - 3072*z^4 - 3072*z^3 - 25600*z^2 - 149504*z - 835584)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_60 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 60) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_60 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 8*t + 2:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z - 448*t^7 + 448*t^6*z^2 - 3136*t^6*z + 4992*t^6 + 896*t^5*z^3 - 9408*t^5*z^2 + 30208*t^5*z - 28608*t^5 + 1120*t^4*z^4 - 15680*t^4*z^3 + 75904*t^4*z^2 - 146112*t^4*z + 90656*t^4 + 896*t^3*z^5 - 15680*t^3*z^4 + 101376*t^3*z^3 - 295296*t^3*z^2 + 373376*t^3*z - 158528*t^3 + 448*t^2*z^6 - 9408*t^2*z^5 + 75904*t^2*z^4 - 295296*t^2*z^3 + 565440*t^2*z^2 - 484800*t^2*z + 143616*t^2 + 128*t*z^7 - 3136*t*z^6 + 30208*t*z^5 - 146112*t*z^4 + 373376*t*z^3 - 484800*t*z^2 + 288512*t*z - 58176*t + 16*z^8 - 448*z^7 + 4992*z^6 - 28608*z^5 + 90656*z^4 - 158528*z^3 + 143616*z^2 - 58176*z + 6480:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 - 896*t^5*z + 4032*t^5 - 1120*t^4*z^2 + 8960*t^4*z - 19904*t^4 - 896*t^3*z^3 + 10304*t^3*z^2 - 37760*t^3*z + 48128*t^3 - 448*t^2*z^4 + 6720*t^2*z^3 - 34688*t^2*z^2 + 73728*t^2*z - 53696*t^2 - 128*t*z^5 + 2368*t*z^4 - 15744*t*z^3 + 46912*t*z^2 - 60416*t*z + 28480*t - 16*z^6 + 352*z^5 - 2848*z^4 + 10816*z^3 - 20064*z^2 + 16512*z - 4416)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_61 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 61) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : (t + z - 6:ℝ)=0 := by
  apply cell_9_61 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 12*t + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (16*t^8 + 128*t^7*z - 576*t^7 + 448*t^6*z^2 - 4032*t^6*z + 8512*t^6 + 896*t^5*z^3 - 12096*t^5*z^2 + 51328*t^5*z - 67328*t^5 + 1120*t^4*z^4 - 20160*t^4*z^3 + 128704*t^4*z^2 - 340736*t^4*z + 310784*t^4 + 896*t^3*z^5 - 20160*t^3*z^4 + 171776*t^3*z^3 - 685568*t^3*z^2 + 1264640*t^3*z - 854016*t^3 + 448*t^2*z^6 - 12096*t^2*z^5 + 128704*t^2*z^4 - 685568*t^2*z^3 + 1907712*t^2*z^2 - 2603008*t^2*z + 1359872*t^2 + 128*t*z^7 - 4032*t*z^6 + 51328*t*z^5 - 340736*t*z^4 + 1264640*t*z^3 - 2603008*t*z^2 + 2744320*t*z - 1146880*t + 16*z^8 - 576*z^7 + 8512*z^6 - 67328*z^5 + 310784*z^4 - 854016*z^3 + 1359872*z^2 - 1146880*z + 393216:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-448*t^6 - 896*t^5*z + 6720*t^5 - 1120*t^4*z^2 + 13440*t^4*z - 45824*t^4 - 896*t^3*z^3 + 14784*t^3*z^2 - 81280*t^3*z + 168320*t^3 - 448*t^2*z^4 + 9408*t^2*z^3 - 71360*t^2*z^2 + 238592*t^2*z - 333440*t^2 - 128*t*z^5 + 3264*t*z^4 - 31488*t*z^3 + 145280*t*z^2 - 329984*t*z + 332544*t - 16*z^6 + 480*z^5 - 5600*z^4 + 32768*z^3 - 102976*z^2 + 170624*z - 130176)*hf

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_62 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 62) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_62 z t hf hn0 hn1 hn2 hn3
  · have hr : (2*t^2 - 4*t*z - 4*t + 2*z^2 - 4*z + 4:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(-2)*hf
  · have hr : (16*t^8 - 320*t^7 - 64*t^6*z + 2368*t^6 + 1024*t^5*z - 7936*t^5 - 5120*t^4*z + 11008*t^4 + 7168*t^3*z - 1024*t^3 + 5120*t^2*z - 9216*t^2 - 4096*t*z + 4096*t:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma row_9_63 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hc : cell (1) (1) (2) (profile4 (2) (z) t 63) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : False := by
  apply cell_9_63 z t hf hn0 hn1 hn2 hn3
  · have hr : (4 - 8*t:ℝ)=0 := by
      convert hc.1 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr
  · have hr : (-64*t*z^6 + 1024*t*z^5 - 5120*t*z^4 + 7168*t*z^3 + 5120*t*z^2 - 4096*t*z + 16*z^8 - 320*z^7 + 2368*z^6 - 7936*z^5 + 11008*z^4 - 1024*z^3 - 9216*z^2 + 4096*z:ℝ)=0 := by
      convert hc.2.2 using 1 ; norm_num [profile4,palette4,locus,gram,edge4,sep4,area] ; ring
    linear_combination hr+(64*t*z^4 - 640*t*z^3 + 1152*t*z^2 + 1024*t*z - 1280*t - 16*z^6 + 224*z^5 - 992*z^4 + 1536*z^3 + 192*z^2 - 896*z + 3456)*hf


private def limit9 (z t : ℝ) : Fin 64→Prop := ![False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,False,((t - z - 1:ℝ)=0),False,False,False,False,False,False,False,False,False,False,False,False,((t - z - 1:ℝ)=0),False,False,((t - 2*z - 2:ℝ)=0),False,((t - 2*z:ℝ)=0),False,False,((t - 2*z:ℝ)=0),False,False,False,False,False,False,False,False,False,False,False,False,((t - 2*z:ℝ)=0),False,((t + z - 6:ℝ)=0),False,False]

private def hue9 : Fin 64→Fin 4 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_25_38 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 25) (_hj : limit9 z t 38) (he : edge4 (1) (1) (2) (profile4 (2) (z) t 25) (profile4 (2) (z) t 38) (2) (z) t=0) : False := by
  apply pair_9_25_38 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (-4096*t*z^6 + 53248*t*z^5 - 266240*t*z^4 + 643072*t*z^3 - 778240*t*z^2 + 450560*t*z - 98304*t + 4096*z^8 - 69632*z^7 + 495616*z^6 - 1921024*z^5 + 4415488*z^4 - 6135808*z^3 + 5013504*z^2 - 2195456*z + 393216:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(4096*t*z^4 - 28672*t*z^3 + 86016*t*z^2 - 69632*t*z + 188416*t - 4096*z^6 + 45056*z^5 - 217088*z^4 + 528384*z^3 - 811008*z^2 + 212992*z - 2113536)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_25_41 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 25) (hj : limit9 z t 41) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 25) (profile4 (2) (z) t 41) (2) (z) t=0) : False := by
  apply pair_9_25_41 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_25_43 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 25) (hj : limit9 z t 43) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 25) (profile4 (2) (z) t 43) (2) (z) t=0) : False := by
  apply pair_9_25_43 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_25_46 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 25) (hj : limit9 z t 46) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 25) (profile4 (2) (z) t 46) (2) (z) t=0) : False := by
  apply pair_9_25_46 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_25_59 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 25) (hj : limit9 z t 59) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 25) (profile4 (2) (z) t 59) (2) (z) t=0) : False := by
  apply pair_9_25_59 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_25_61 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 25) (hj : limit9 z t 61) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 25) (profile4 (2) (z) t 61) (2) (z) t=0) : False := by
  apply pair_9_25_61 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_38_41 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 38) (hj : limit9 z t 41) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 38) (profile4 (2) (z) t 41) (2) (z) t=0) : False := by
  apply pair_9_38_41 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_38_43 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 38) (hj : limit9 z t 43) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 38) (profile4 (2) (z) t 43) (2) (z) t=0) : False := by
  apply pair_9_38_43 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_38_46 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 38) (hj : limit9 z t 46) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 38) (profile4 (2) (z) t 46) (2) (z) t=0) : False := by
  apply pair_9_38_46 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_38_59 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 38) (hj : limit9 z t 59) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 38) (profile4 (2) (z) t 59) (2) (z) t=0) : False := by
  apply pair_9_38_59 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_38_61 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 38) (hj : limit9 z t 61) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 38) (profile4 (2) (z) t 61) (2) (z) t=0) : False := by
  apply pair_9_38_61 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_41_43 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 41) (hj : limit9 z t 43) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 41) (profile4 (2) (z) t 43) (2) (z) t=0) : False := by
  apply pair_9_41_43 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_41_46 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 41) (hj : limit9 z t 46) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 41) (profile4 (2) (z) t 46) (2) (z) t=0) : False := by
  apply pair_9_41_46 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_41_59 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 41) (hj : limit9 z t 59) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 41) (profile4 (2) (z) t 59) (2) (z) t=0) : False := by
  apply pair_9_41_59 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_41_61 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 41) (hj : limit9 z t 61) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 41) (profile4 (2) (z) t 61) (2) (z) t=0) : False := by
  apply pair_9_41_61 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_43_46 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 43) (_hj : limit9 z t 46) (he : edge4 (1) (1) (2) (profile4 (2) (z) t 43) (profile4 (2) (z) t 46) (2) (z) t=0) : False := by
  apply pair_9_43_46 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (256*t^8 - 2048*t^7*z - 512*t^7 + 7168*t^6*z^2 + 2560*t^6*z - 1536*t^6 - 14336*t^5*z^3 - 4608*t^5*z^2 + 10240*t^5*z + 3072*t^5 + 17920*t^4*z^4 + 2560*t^4*z^3 - 27136*t^4*z^2 - 9216*t^4*z + 2048*t^4 - 14336*t^3*z^5 + 2560*t^3*z^4 + 36864*t^3*z^3 + 6144*t^3*z^2 - 14336*t^3*z - 4096*t^3 + 7168*t^2*z^6 - 4608*t^2*z^5 - 27136*t^2*z^4 + 6144*t^2*z^3 + 24576*t^2*z^2 + 4096*t^2*z - 2048*t*z^7 + 2560*t*z^6 + 10240*t*z^5 - 9216*t*z^4 - 14336*t*z^3 + 4096*t*z^2 + 8192*t*z + 256*z^8 - 512*z^7 - 1536*z^6 + 3072*z^5 + 2048*z^4 - 4096*z^3:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-7168*t^6 + 14336*t^5*z + 90624*t^5 - 17920*t^4*z^2 - 110080*t^4*z - 597504*t^4 + 14336*t^3*z^3 + 83456*t^3*z^2 + 435200*t^3*z + 2438144*t^3 - 7168*t^2*z^4 - 38400*t^2*z^3 - 188928*t^2*z^2 - 1062912*t^2*z - 6024192*t^2 + 2048*t*z^5 + 9728*t*z^4 + 44032*t*z^3 + 253952*t*z^2 + 1449984*t*z + 8187904*t - 256*z^6 - 1024*z^5 - 4096*z^4 - 25600*z^3 - 147456*z^2 - 829440*z - 4681728)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_43_59 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 43) (_hj : limit9 z t 59) (he : edge4 (1) (1) (2) (profile4 (2) (z) t 43) (profile4 (2) (z) t 59) (2) (z) t=0) : False := by
  apply pair_9_43_59 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (256*t^8 - 2048*t^7*z - 512*t^7 + 7168*t^6*z^2 + 2560*t^6*z - 1536*t^6 - 14336*t^5*z^3 - 4608*t^5*z^2 + 10240*t^5*z + 3072*t^5 + 17920*t^4*z^4 + 2560*t^4*z^3 - 27136*t^4*z^2 - 9216*t^4*z + 2048*t^4 - 14336*t^3*z^5 + 2560*t^3*z^4 + 36864*t^3*z^3 + 6144*t^3*z^2 - 14336*t^3*z - 4096*t^3 + 7168*t^2*z^6 - 4608*t^2*z^5 - 27136*t^2*z^4 + 6144*t^2*z^3 + 24576*t^2*z^2 + 4096*t^2*z - 2048*t*z^7 + 2560*t*z^6 + 10240*t*z^5 - 9216*t*z^4 - 14336*t*z^3 + 4096*t*z^2 + 8192*t*z + 256*z^8 - 512*z^7 - 1536*z^6 + 3072*z^5 + 2048*z^4 - 4096*z^3:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-7168*t^6 + 14336*t^5*z + 90624*t^5 - 17920*t^4*z^2 - 110080*t^4*z - 597504*t^4 + 14336*t^3*z^3 + 83456*t^3*z^2 + 435200*t^3*z + 2438144*t^3 - 7168*t^2*z^4 - 38400*t^2*z^3 - 188928*t^2*z^2 - 1062912*t^2*z - 6024192*t^2 + 2048*t*z^5 + 9728*t*z^4 + 44032*t*z^3 + 253952*t*z^2 + 1449984*t*z + 8187904*t - 256*z^6 - 1024*z^5 - 4096*z^4 - 25600*z^3 - 147456*z^2 - 829440*z - 4681728)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_43_61 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 43) (hj : limit9 z t 61) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 43) (profile4 (2) (z) t 61) (2) (z) t=0) : False := by
  apply pair_9_43_61 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_46_59 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 46) (_hj : limit9 z t 59) (he : edge4 (1) (1) (2) (profile4 (2) (z) t 46) (profile4 (2) (z) t 59) (2) (z) t=0) : False := by
  apply pair_9_46_59 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · have hraw : (4096*t^8 - 32768*t^7*z - 4096*t^7 + 114688*t^6*z^2 + 20480*t^6*z - 12288*t^6 - 229376*t^5*z^3 - 36864*t^5*z^2 + 77824*t^5*z + 12288*t^5 + 286720*t^4*z^4 + 20480*t^4*z^3 - 200704*t^4*z^2 - 36864*t^4*z + 8192*t^4 - 229376*t^3*z^5 + 20480*t^3*z^4 + 270336*t^3*z^3 + 24576*t^3*z^2 - 45056*t^3*z - 8192*t^3 + 114688*t^2*z^6 - 36864*t^2*z^5 - 200704*t^2*z^4 + 24576*t^2*z^3 + 73728*t^2*z^2 + 8192*t^2*z - 32768*t*z^7 + 20480*t*z^6 + 77824*t*z^5 - 36864*t*z^4 - 45056*t*z^3 + 8192*t*z^2 + 8192*t*z + 4096*z^8 - 4096*z^7 - 12288*z^6 + 12288*z^5 + 8192*z^4 - 8192*z^3:ℝ)=0 := by
      convert he using 1 ; norm_num [profile4,palette4,edge4,sep4,area] ; ring
    linear_combination hraw+(-114688*t^6 + 229376*t^5*z + 1413120*t^5 - 286720*t^4*z^2 - 1740800*t^4*z - 9670656*t^4 + 229376*t^3*z^3 + 1355776*t^3*z^2 + 7405568*t^3*z + 41697280*t^3 - 114688*t^2*z^4 - 651264*t^2*z^3 - 3477504*t^2*z^2 - 19587072*t^2*z - 110641152*t^2 + 32768*t*z^5 + 176128*t*z^4 + 913408*t*z^3 + 5165056*t*z^2 + 29208576*t*z + 164913152*t - 4096*z^6 - 20480*z^5 - 102400*z^4 - 585728*z^3 - 3317760*z^2 - 18726912*z - 105725952)*hf


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_46_61 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 46) (hj : limit9 z t 61) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 46) (profile4 (2) (z) t 61) (2) (z) t=0) : False := by
  apply pair_9_46_61 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma rowpair_9_59_61 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (hi : limit9 z t 59) (hj : limit9 z t 61) (_he : edge4 (1) (1) (2) (profile4 (2) (z) t 59) (profile4 (2) (z) t 61) (2) (z) t=0) : False := by
  apply pair_9_59_61 z t hf hn0 hn1 hn2 hn3
  · exact hi
  · exact hj


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
private lemma exclude_field_9 (z t : ℝ) (hf : z^2 - 6*z + 2=0) (hn0 : t-(1)≠0) (hn1 : t-(2)≠0) (hn2 : t-(z)≠0) (hn3 : t-((0:ℝ))≠0) (g : Fin 5→Fin 64) (hinj : Function.Injective g)
    (hc : ∀ i, cell (1) (1) (2) (profile4 (2) (z) t (g i)) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t)
    (he : ∀ i j : Fin 5, i≠j → edge4 (1) (1) (2) (profile4 (2) (z) t (g i)) (profile4 (2) (z) t (g j)) (2) (z) t=0) : False := by
  have row (k : Fin 64) (hh : cell (1) (1) (2) (profile4 (2) (z) t k) ((2),(1),(1)) ((2),(2),(z)) (2) (z) t) : limit9 z t k := by
    fin_cases k
    · exact row_9_0 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_1 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_2 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_3 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_4 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_5 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_6 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_7 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_8 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_9 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_10 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_11 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_12 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_13 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_14 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_15 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_16 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_17 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_18 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_19 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_20 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_21 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_22 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_23 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_24 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_25 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_26 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_27 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_28 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_29 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_30 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_31 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_32 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_33 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_34 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_35 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_36 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_37 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_38 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_39 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_40 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_41 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_42 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_43 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_44 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_45 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_46 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_47 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_48 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_49 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_50 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_51 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_52 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_53 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_54 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_55 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_56 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_57 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_58 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_59 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_60 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_61 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_62 z t hf hn0 hn1 hn2 hn3 hh
    · exact row_9_63 z t hf hn0 hn1 hn2 hn3 hh
  have allowed (k : Fin 64) (hh : limit9 z t k) : k∈([25,38,41,43,46,59,61]:List (Fin 64)) := by
    fin_cases k <;> first | decide | exact False.elim hh
  have cert : ∀ i j : Fin 64, i∈([25,38,41,43,46,59,61]:List (Fin 64)) → j∈([25,38,41,43,46,59,61]:List (Fin 64)) → i<j → hue9 i=hue9 j → (i,j)∈([(25,38),(25,41),(25,43),(25,46),(25,59),(25,61),(38,41),(38,43),(38,46),(38,59),(38,61),(41,43),(41,46),(41,59),(41,61),(43,46),(43,59),(43,61),(46,59),(46,61),(59,61)]:List (Fin 64×Fin 64)) := by decide
  have bad (i j : Fin 64) (hi : limit9 z t i) (hj : limit9 z t j) (hlt : i<j) (hc : hue9 i=hue9 j) (hb : edge4 (1) (1) (2) (profile4 (2) (z) t i) (profile4 (2) (z) t j) (2) (z) t=0) : False := by
    have h := cert i j (allowed i hi) (allowed j hj) hlt hc
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact rowpair_9_25_38 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_25_41 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_25_43 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_25_46 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_25_59 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_25_61 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_38_41 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_38_43 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_38_46 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_38_59 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_38_61 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_41_43 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_41_46 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_41_59 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_41_61 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_43_46 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_43_59 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_43_61 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_46_59 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_46_61 z t hf hn0 hn1 hn2 hn3 hi hj hb
    · exact rowpair_9_59_61 z t hf hn0 hn1 hn2 hn3 hi hj hb
  have hi : Function.Injective (fun i : Fin 5 => hue9 (g i)) := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne (show g i≠g j from fun e => hne (hinj e)) with hl|hl
    · exact bad _ _ (row _ (hc i)) (row _ (hc j)) hl h (he i j hne)
    · exact bad _ _ (row _ (hc j)) (row _ (hc i)) hl h.symm (he j i (Ne.symm hne))
  have hh := Fintype.card_le_of_injective _ hi
  norm_num at hh

private lemma no_0001011121 (x y t : ℝ) (H : admissible ![0,0,0,1,0,1,1,1,2,1] x y) (E : hasExtension ![0,0,0,1,0,1,1,1,2,1] x y t)
    (t1 : t-1≠0) (tx : t-x≠0) (ty : t-y≠0) (t0 : t≠0) : False := by
  obtain ⟨h0,h1⟩ := shape_0001011121 x y H
  by_cases G0 : y^2 - 8*y + 4=0
  · have ex : x=y/2 := by linear_combination (1)*h0
    obtain ⟨u,hu,hc,he⟩ := E
    change ∀ i, cell (1) (1) (1) (profile4 x y t (u i)) ((1),(x),(x)) ((x),(x),(y)) x y t at hc
    change ∀ i j, i≠j → edge4 (1) (1) (1) (profile4 x y t (u i)) (profile4 x y t (u j)) x y t=0 at he
    simp only [ex] at hc he tx ty
    apply exclude_field_6 y t (by linear_combination (1)*G0) t1 tx ty (by simpa using t0) u hu hc he
  apply G0
  linear_combination (1)*h1

private lemma no_0011101022 (x y t : ℝ) (H : admissible ![0,0,1,1,1,0,1,0,2,2] x y) (E : hasExtension ![0,0,1,1,1,0,1,0,2,2] x y t)
    (t1 : t-1≠0) (tx : t-x≠0) (ty : t-y≠0) (t0 : t≠0) : False := by
  obtain ⟨h0,h1⟩ := shape_0011101022 x y H
  by_cases G0 : y^2 - 6*y + 2=0
  · have ex : x=2 := by linear_combination (1)*h0
    obtain ⟨u,hu,hc,he⟩ := E
    change ∀ i, cell (1) (1) (x) (profile4 x y t (u i)) ((x),(1),(1)) ((x),(x),(y)) x y t at hc
    change ∀ i j, i≠j → edge4 (1) (1) (x) (profile4 x y t (u i)) (profile4 x y t (u j)) x y t=0 at he
    simp only [ex] at hc he tx ty
    apply exclude_field_9 y t (by linear_combination (1)*G0) t1 tx ty (by simpa using t0) u hu hc he
  apply G0
  linear_combination (1)*h1

private lemma no_0011102200 (x y t : ℝ) (H : admissible ![0,0,1,1,1,0,2,2,0,0] x y) (E : hasExtension ![0,0,1,1,1,0,2,2,0,0] x y t)
    (t1 : t-1≠0) (tx : t-x≠0) (ty : t-y≠0) (t0 : t≠0) : False := by
  obtain ⟨h0,h1⟩ := shape_0011102200 x y H
  by_cases G0 : 2*y - 3=0
  · have ex : x=1/4 := by linear_combination (1)*h0 + (92*y^3/9075 - 588*y^2/3025 + 18187*y/18150 - 5009/12100)*G0
    have ey : y=3/2 := by linear_combination (1/2)*G0
    apply H.2.1 0 3 4 (by decide) (by decide)
    change area (x) (x) (1)=0
    simp only [ex,ey,area]
    ring
  by_cases G1 : y - 9=0
  · have ex : x=4 := by linear_combination (1)*h0 + (184*y^3/9075 - 716*y^2/3025 + 377*y/825 + 843/3025)*G1
    have ey : y=9 := by linear_combination (1)*G1
    apply H.2.1 0 1 2 (by decide) (by decide)
    change area (1) (1) (x)=0
    simp only [ex,ey,area]
    ring
  by_cases G2 : y^2 - 3*y + 1=0
  · have ex : x=y := by linear_combination (1)*h0 + (184*y^2/9075 - 1084*y/3025 + 4513/3025)*G2
    apply H.1.2.2.2.2
    rw [ex]
    ring
  apply (mul_ne_zero (mul_ne_zero G0 (pow_ne_zero 2 G1)) G2)
  linear_combination (2)*h1

end Erdos1082Ten

open Erdos1082Ten EuclideanGeometry

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H4_R1.H2 := by
  intro A hn hA hd M hm B hBA hB hf hthree p r c hc hh
  obtain ⟨x,y,t,H,E,t1,tx,ty,t0⟩ := given_extension A B M hm hBA hA hB hd hthree hn hf p r c hc
  change colorCode c∈([853,3194,3231]:List ℕ) at hh
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with eq|eq|eq
  · have cc : c=![0,0,0,1,0,1,1,1,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact no_0001011121 x y t H E t1 tx ty t0
  · have cc : c=![0,0,1,1,1,0,1,0,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact no_0011101022 x y t H E t1 tx ty t0
  · have cc : c=![0,0,1,1,1,0,2,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact no_0011102200 x y t H E t1 tx ty t0
