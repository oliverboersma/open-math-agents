import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H1_R1

/-!
# Impossible five-point three-distance patterns, part 2

The three fixed anchors and the last two points give three Gram identities. Noncollinearity makes every triangle area factor nonzero. The displayed polynomial combinations eliminate the listed patterns.
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
private lemma base_0001011210 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : -4*x - y + (4:ℝ)=0) (g2 : 2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x + y/4 - (1:ℝ)=0 := by linear_combination (-1/4)*g1
  have h3 : x - 1/(3:ℝ)=0 := by linear_combination (-1/6)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (3/4)*h1 + (-3*y - 1)*h2 + (-3*x/4 + 15*y/4 + 9/4)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0001011212 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : -4*x + 2*y + (1:ℝ)=0) (g2 : 2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : 4*x*y - y^2≠0) (_n14 : -x^2 + 4*x*y≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x - y/2 - 1/(4:ℝ)=0 := by linear_combination (-1/4)*g1
  have h3 : x - 1/(3:ℝ)=0 := by linear_combination (-1/6)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (12)*h1 + (24*y - 52)*h2 + (-12*x - 12*y + 72)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma shape_0001011210 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,1,2,1,0] x y) : False := by
  apply base_0001011210 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x x x 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x x x x x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
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
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001011212 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,1,2,1,2] x y) : False := by
  apply base_0001011212 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x x x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x x x x x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
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
  · have hn : area 1 x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring

private lemma base_0001011220 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : x^2 - 3*x*y - 2*x + 2*y^2 - 3*y + (4:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h3 : (1:ℝ)=0 := by linear_combination (x^2/9 + x/9 - y^2/9 + y/3 - 8/9)*h1 + (x^2/9 + x*y/9 - 2*x/9 - y/9 + 4/9)*g1 + (-2*x^2/9 - x*y/9 + x/9 + y^2/9 - 2*y/9 + 1/9)*h2
  have h4 : (1:ℝ)=0 := by linear_combination (1)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  norm_num at h3



private lemma base_0001011221 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : x^2 - 3*x*y + x + 2*y^2 - 3*y + (1:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 3*x^2≠0) (_n14 : -x^2 + 4*x*y≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h3 : (1:ℝ)=0 := by linear_combination (-4*x*y^2/27 + 4*x*y/9 - x/3 + 4*y^3/27 - 8*y^2/27 + 5*y/3 - 11/3)*h1 + (-4*x*y^2/27 + 4*x*y/9 - x/3 - 8*y^2/27 + 8*y/9 + 2/3)*g1 + (8*x*y^2/27 - 8*x*y/9 + 2*x/3 - 4*y^3/27 + 28*y^2/27 - 35*y/9 + 4)*h2
  have h4 : (1:ℝ)=0 := by linear_combination (1)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  norm_num at h3



private lemma base_0001011222 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : x^2 - 3*x*y - 2*x + 2*y^2 + (1:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 4*x*y - y^2≠0) (n14 : 3*y^2≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h3 : x^2 - 2*x - 3*y + (1:ℝ)=0 := by linear_combination (1)*h1 + (-1)*g1 + (1)*h2
  have h4 : x*y - y=0 := by linear_combination (1)*h1 + (-1)*h2
  have h5 : y^2=0 := by linear_combination (1)*h1 + (1)*g1 + (-2)*h2
  have h6 : x^2 - 2*x - 3*y + (1:ℝ)=0 := by linear_combination (1)*h3
  have h8 : y≠0 := by
    intro he
    apply n14
    linear_combination (3*y)*he
  have h9 : x - (1:ℝ)≠0 := by
    intro he
    apply n2
    linear_combination (1)*he
  have h10 : ((y) * (x - 1))*(1)=0 := by linear_combination (1)*h4
  have h7 := (mul_eq_zero.mp h10).resolve_left (mul_ne_zero h8 h9)
  have h12 : ((y) * (y))*(1)=0 := by linear_combination (1)*h5
  have h11 := (mul_eq_zero.mp h12).resolve_left (mul_ne_zero h8 h8)
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h11
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h13
  have h15 : (1:ℝ)=0 := by linear_combination (1)*h14
  norm_num at h13



private lemma base_0001012120 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : -2*x^2 + 2*x*y - x - 4*y + (4:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 2*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : 4*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y + x/2 + 2*y - (2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h3 : x^2 - 2*x*y - x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-2*x*y^2/27 + 4*x*y/9 - x/2 + 2*y^3/27 - 23*y^2/27 + 22*y/9 - 2/3)*h1 + (4*x*y^2/27 - 8*x*y/9 + x - 2*y^3/27 + 7*y^2/27 + 2*y/3 - 4/3)*h2 + (-2*x*y^2/27 + 4*x*y/9 - x/2 + 4*y^2/27 - 4*y/9 - 1)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0001012121 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : -2*x^2 + 2*x*y + 2*x - 4*y + (1:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 2*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : 4*y - (1:ℝ)≠0) (_n13 : 4*x*y - y^2≠0) (_n14 : 4*x*y - y^2≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y - x + 2*y - 1/(2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h3 : x^2 - 2*x*y - x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-28*x*y^2/27 + 80*x*y/9 - 12*x + 28*y^3/27 - 352*y^2/27 + 358*y/9)*h1 + (56*x*y^2/27 - 160*x*y/9 + 24*x - 28*y^3/27 + 212*y^2/27 - 74/3)*h2 + (-28*x*y^2/27 + 80*x*y/9 - 12*x + 56*y^2/27 - 118*y/9 - 34/3)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0001012122 (x y : ℝ) (g0 : 2*x^2 - 8*x + (2:ℝ)=0) (g1 : -2*x^2 + 2*x*y - x - y + (1:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 2*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : 4*y - (1:ℝ)≠0) (_n13 : -x^2 + 4*x*y≠0) (_n14 : -x^2 + 4*x*y≠0) : False := by
  have h1 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y + x/2 + y/2 - 1/(2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h3 : x^2 - 2*x*y - x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-7*x*y^2/27 + 29*x*y/18 - 5*x/3 + 7*y^3/27 - 143*y^2/54 + 97*y/18 - 2)*h1 + (14*x*y^2/27 - 29*x*y/9 + 10*x/3 - 7*y^3/27 + 26*y^2/27 + 44*y/9 - 22/3)*h2 + (-7*x*y^2/27 + 29*x*y/18 - 5*x/3 + 7*y^2/54 - 11*y/18 - 2/3)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0001012200 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : -x^2 + x*y - x - y^2 - y + (2:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -y^2 + 4*y≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n14 : -y^2 + 4*y≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y + x + y^2 + y - (2:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x + y - (1:ℝ)=0 := by linear_combination (1/3)*h2 + (-1/3)*h3
  have h5 : y^2 - y=0 := by linear_combination (-x/9 + 2*y/9 + 1/9)*h2 + (x/9 - 2*y/9 + 2/9)*h3
  have h6 : x + y - (1:ℝ)=0 := by linear_combination (1)*h4
  have h8 : y - (1:ℝ)≠0 := by
    intro he
    apply n3
    linear_combination (1)*he
  have h9 : y≠0 := by
    intro he
    apply n14
    linear_combination (4 - y)*he
  have h10 : ((y - 1) * (y))*(1)=0 := by linear_combination (1)*h5
  have h7 := (mul_eq_zero.mp h10).resolve_left (mul_ne_zero h8 h9)
  have h11 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h12 : (1:ℝ)=0 := by linear_combination (1)*h11
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h12
  norm_num at h11



private lemma base_0001012201 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : -x^2 + x*y + 2*x - y^2 - y - (1:ℝ)=0) (g2 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -y^2 + 4*y≠0) (n13 : 4*x*y - y^2≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - x*y - 2*x + y^2 + y + (1:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x^2 - 2*x + (1:ℝ)=0 := by linear_combination (x/3 - y/3 + 2/3)*h2 + (-x/3 + y/3 + 1/3)*h3
  have h5 : y=0 := by linear_combination (1/3)*h2 + (-1/3)*h3
  have h7 : x - (1:ℝ)≠0 := by
    intro he
    apply n2
    linear_combination (1)*he
  have h8 : ((x - 1) * (x - 1))*(1)=0 := by linear_combination (1)*h4
  have h6 := (mul_eq_zero.mp h8).resolve_left (mul_ne_zero h7 h7)
  have h10 : y≠0 := by
    intro he
    apply n13
    linear_combination (4*x - y)*he
  have h11 : ((y))*(1)=0 := by linear_combination (1)*h5
  have h9 := (mul_eq_zero.mp h11).resolve_left h10
  have h12 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h12
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h13
  norm_num at h12



private lemma base_0001012210 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : -2*x^2 + 3*x*y - 2*x - y^2 - 3*y + (4:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 3*x*y/2 + x + y^2/2 + 3*y/2 - (2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h3 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x - (1:ℝ)=0 := by linear_combination (x*y^2/324 - x*y/36 + x/18 - y^3/324 + 5*y^2/81 - 19*y/36 + 13/9)*h1 + (-x*y^2/162 + x*y/18 - x/9 + 7*y^2/162 - 5*y/18 + 4/9)*h2 + (x*y^2/324 - x*y/36 + x/18 + y^3/324 - 7*y^2/81 + 23*y/36 - 14/9)*h3
  have h5 : y=0 := by linear_combination (x*y/54 - x/18 - y^2/54 + 7*y/27 - 29/18)*h1 + (-x*y/27 + x/9 + 7*y/27 - 1/9)*h2 + (x*y/54 - x/18 + y^2/54 - 11*y/27 + 25/18)*h3
  have h7 : x - (1:ℝ)≠0 := by
    intro he
    apply n2
    linear_combination (1)*he
  have h8 : ((x - 1))*(1)=0 := by linear_combination (1)*h4
  have h6 := (mul_eq_zero.mp h8).resolve_left h7
  have h10 : y≠0 := by
    intro he
    apply n8
    linear_combination (4 - y)*he
  have h11 : ((y))*(1)=0 := by linear_combination (1)*h5
  have h9 := (mul_eq_zero.mp h11).resolve_left h10
  have h12 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h12
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h13
  norm_num at h12



private lemma base_0001012211 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : -2*x^2 + 3*x*y + x - y^2 - 3*y + (1:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 4*x*y - y^2≠0) (n14 : 4*x*y - y^2≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 3*x*y/2 - x/2 + y^2/2 + 3*y/2 - 1/(2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h3 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x - (1:ℝ)=0 := by linear_combination (x*y^2/81 - x*y/9 + 2*x/9 - y^3/81 + 17*y^2/81 - 4*y/3 + 25/9)*h1 + (-2*x*y^2/81 + 2*x*y/9 - 4*x/9 + 8*y^2/81 - 2*y/3 + 10/9)*h2 + (x*y^2/81 - x*y/9 + 2*x/9 + y^3/81 - 22*y^2/81 + 5*y/3 - 29/9)*h3
  have h5 : y=0 := by linear_combination (x*y/27 - x/9 - y^2/27 + 11*y/27 - 14/9)*h1 + (-2*x*y/27 + 2*x/9 + 8*y/27 - 2/9)*h2 + (x*y/27 - x/9 + y^2/27 - 16*y/27 + 13/9)*h3
  have h7 : x - (1:ℝ)≠0 := by
    intro he
    apply n2
    linear_combination (1)*he
  have h8 : ((x - 1))*(1)=0 := by linear_combination (1)*h4
  have h6 := (mul_eq_zero.mp h8).resolve_left h7
  have h10 : y≠0 := by
    intro he
    apply n14
    linear_combination (4*x - y)*he
  have h11 : ((y))*(1)=0 := by linear_combination (1)*h5
  have h9 := (mul_eq_zero.mp h11).resolve_left h10
  have h12 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h12
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h13
  norm_num at h12



private lemma base_0001012212 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : -2*x^2 + 3*x*y - 2*x - y^2 + (1:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 4*x*y≠0) (_n14 : -x^2 + 4*x*y≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 3*x*y/2 + x + y^2/2 - 1/(2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h3 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-11*x*y^2/54 + 11*x*y/18 + 2*x/3 + 11*y^3/54 - 121*y^2/54 + 197*y/18 - 67/6)*h1 + (11*x*y^2/27 - 11*x*y/9 - 4*x/3 - 77*y^2/27 + 77*y/9 + 2)*h2 + (-11*x*y^2/54 + 11*x*y/18 + 2*x/3 - 11*y^3/54 + 209*y^2/54 - 95*y/6 + 79/6)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0001012220 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : -x^2 + y^2 - 5*y + (4:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 2*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : 4*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - y^2 + 5*y - (4:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - 2*x*y - x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x=0 := by linear_combination (8*x*y^2/81 - 16*x*y/81 - 10*x/81 - 8*y^3/81 + 16*y^2/27 - 2*y/3 - 94/81)*h1 + (-4*x*y^2/81 + 8*x*y/81 + 5*x/81 + 2*y^2/27 - y/27 - 1/27)*h2 + (-4*x*y^2/81 + 8*x*y/81 + 5*x/81 + 8*y^3/81 - 14*y^2/27 + 11*y/27 + 82/81)*h3
  have h5 : y - (1:ℝ)=0 := by linear_combination (4*x*y/27 + 2*x/27 - 4*y^2/27 + 14*y/27 + 8/27)*h1 + (-2*x*y/27 - x/27 + y/9 + 2/9)*h2 + (-2*x*y/27 - x/27 + 4*y^2/27 - 11*y/27 - 11/27)*h3
  have h7 : x≠0 := by
    intro he
    apply n10
    linear_combination (4 - x)*he
  have h8 : ((x))*(1)=0 := by linear_combination (1)*h4
  have h6 := (mul_eq_zero.mp h8).resolve_left h7
  have h10 : y - (1:ℝ)≠0 := by
    intro he
    apply n3
    linear_combination (1)*he
  have h11 : ((y - 1))*(1)=0 := by linear_combination (1)*h5
  have h9 := (mul_eq_zero.mp h11).resolve_left h10
  have h12 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h12
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h13
  norm_num at h12



private lemma base_0001012221 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : -x^2 + 3*x + y^2 - 5*y + (1:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 2*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : 4*y - (1:ℝ)≠0) (_n13 : 4*x*y - y^2≠0) (_n14 : -x^2 + 4*x*y≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 3*x - y^2 + 5*y - (1:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - 2*x*y - x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-4*x^2*y/9 + 14*x^2/9 + 2*x*y/3 - 7*x/3 + 4*y^3/9 - 40*y^2/9 + 119*y/9 - 89/9)*h1 + (2*x^2*y/9 - 7*x^2/9 + 2*x*y^2/9 - 5*x*y/3 + 28*x/9 - y/3 + 2/3)*h2 + (2*x^2*y/9 - 7*x^2/9 - 2*x*y^2/9 + x*y - 7*x/9 - 4*y^3/9 + 40*y^2/9 - 122*y/9 + 104/9)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  norm_num at h4



private lemma base_0001012222 (x y : ℝ) (g0 : 2*x^2 - 2*x*y - 4*x + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : -x^2 + y^2 - 2*y + (1:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 2*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : 4*y - (1:ℝ)≠0) (n13 : -x^2 + 4*x*y≠0) (_n14 : 3*y^2≠0) : False := by
  have h1 : x^2 - x*y - 2*x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - y^2 + 2*y - (1:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - 2*x*y - x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x=0 := by linear_combination (-4*x/9 + 4*y/9 - 10/9)*h1 + (2*x/9 - 1/3)*h2 + (2*x/9 - 4*y/9 + 7/9)*h3
  have h5 : y^2 - 2*y + (1:ℝ)=0 := by linear_combination (-2*x/3 + 2*y/3 - 2/3)*h1 + (x/3 - 1)*h2 + (x/3 - 2*y/3 + 2/3)*h3
  have h7 : x≠0 := by
    intro he
    apply n13
    linear_combination (-x + 4*y)*he
  have h8 : ((x))*(1)=0 := by linear_combination (1)*h4
  have h6 := (mul_eq_zero.mp h8).resolve_left h7
  have h10 : y - (1:ℝ)≠0 := by
    intro he
    apply n3
    linear_combination (1)*he
  have h11 : ((y - 1) * (y - 1))*(1)=0 := by linear_combination (1)*h5
  have h9 := (mul_eq_zero.mp h11).resolve_left (mul_ne_zero h10 h10)
  have h12 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h12
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h13
  norm_num at h12



private lemma base_0001020210 (x y : ℝ) (g0 : 2*y^2 - 8*y + (2:ℝ)=0) (g1 : -x*y - x - y + (2:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*y - (1:ℝ)≠0) (_n12 : -x^2 + 4*x≠0) (_n13 : -y^2 + 4*y≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h1 : y^2 - 4*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x*y + x + y - (2:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-x^2*y/27 + 2*x^2/27 + x*y/27 - 2*x/27 + 2*y/27 - 13/27)*h1 + (x*y^2/27 - 7*x*y/27 + 10*x/27 - 2*y^2/27 + 17*y/27 - 26/27)*h2 + (2*y/9 - 4/9)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  norm_num at h4



private lemma base_0001020211 (x y : ℝ) (g0 : 2*y^2 - 8*y + (2:ℝ)=0) (g1 : -x*y + 2*x - y - (1:ℝ)=0) (g2 : 2*x^2 - 8*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : 4*y - (1:ℝ)≠0) (_n12 : -x^2 + 4*x≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : 4*x*y - y^2≠0) : False := by
  have h1 : y^2 - 4*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x*y - 2*x + y + (1:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - 4*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (2*x^2*y/27 - 7*x^2/27 - 8*x*y/27 + 28*x/27 - 10*y/27 - 1/27)*h1 + (-2*x*y^2/27 + 11*x*y/27 - 14*x/27 + 10*y^2/27 - 49*y/27 + 49/27)*h2 + (2*y/9 - 7/9)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  norm_num at h4



private lemma base_0001021210 (x y : ℝ) (g0 : 2*y^2 - 8*y + (2:ℝ)=0) (g1 : -3*x - 2*y + (4:ℝ)=0) (g2 : 2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*y - (1:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h1 : y^2 - 4*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x + 2*y/3 - 4/(3:ℝ)=0 := by linear_combination (-1/3)*g1
  have h3 : x - 1/(3:ℝ)=0 := by linear_combination (-1/6)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-4/11)*h1 + (6*y/11 - 15/11)*h2 + (15/11 - 6*y/11)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0001021212 (x y : ℝ) (g0 : 2*y^2 - 8*y + (2:ℝ)=0) (g1 : -3*x + y + (1:ℝ)=0) (g2 : 2 - 6*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : 4*y - (1:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : -x^2 + 4*x*y≠0) (_n14 : -x^2 + 4*x*y≠0) : False := by
  have h1 : y^2 - 4*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x - y/3 - 1/(3:ℝ)=0 := by linear_combination (-1/3)*g1
  have h3 : x - 1/(3:ℝ)=0 := by linear_combination (-1/6)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (1)*h1 + (3*y - 12)*h2 + (12 - 3*y)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma shape_0001011220 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,1,2,2,0] x y) : False := by
  apply base_0001011220 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x x y 1=0 := ha.2.2.2.1
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
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001011221 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,1,2,2,1] x y) : False := by
  apply base_0001011221 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x x y x=0 := ha.2.2.2.1
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
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001011222 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,1,2,2,2] x y) : False := by
  apply base_0001011222 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x x y y=0 := ha.2.2.2.1
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001012120 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,2,1,2,0] x y) : False := by
  apply base_0001012120 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x x y y 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y y x y y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001012121 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,2,1,2,1] x y) : False := by
  apply base_0001012121 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x x y y x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y y x y y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area 1 y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001012122 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,2,1,2,2] x y) : False := by
  apply base_0001012122 x y
  · have hg : gram 1 1 1 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x x x y y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y y x y y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001012200 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,2,2,0,0] x y) : False := by
  apply base_0001012200 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x y 1 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y 1 x y 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
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
  · have hn : area 1 y 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001012201 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,2,2,0,1] x y) : False := by
  apply base_0001012201 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x y 1 x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y 1 x y 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
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
  · have hn : area 1 y 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001012210 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,2,2,1,0] x y) : False := by
  apply base_0001012210 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x y x 1=0 := ha.2.2.2.1
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
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
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


private lemma shape_0001012211 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,2,2,1,1] x y) : False := by
  apply base_0001012211 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x y x x=0 := ha.2.2.2.1
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
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
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


private lemma shape_0001012212 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,2,2,1,2] x y) : False := by
  apply base_0001012212 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x y x y=0 := ha.2.2.2.1
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
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
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


private lemma shape_0001012220 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,2,2,2,0] x y) : False := by
  apply base_0001012220 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x y y 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y y x y y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area 1 y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001012221 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,2,2,2,1] x y) : False := by
  apply base_0001012221 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x y y x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y y x y y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area 1 y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001012222 (x y : ℝ) (ha : admissible ![0,0,0,1,0,1,2,2,2,2] x y) : False := by
  apply base_0001012222 x y
  · have hg : gram 1 1 1 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 x y x y y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y y x y y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001020210 (x y : ℝ) (ha : admissible ![0,0,0,1,0,2,0,2,1,0] x y) : False := by
  apply base_0001020210 x y
  · have hg : gram 1 1 1 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 y y x 1 x 1=0 := ha.2.2.2.1
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
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
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001020211 (x y : ℝ) (ha : admissible ![0,0,0,1,0,2,0,2,1,1] x y) : False := by
  apply base_0001020211 x y
  · have hg : gram 1 1 1 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 y y x 1 x x=0 := ha.2.2.2.1
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
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
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001021210 (x y : ℝ) (ha : admissible ![0,0,0,1,0,2,1,2,1,0] x y) : False := by
  apply base_0001021210 x y
  · have hg : gram 1 1 1 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 y y x x x 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x x x x x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001021212 (x y : ℝ) (ha : admissible ![0,0,0,1,0,2,1,2,1,2] x y) : False := by
  apply base_0001021212 x y
  · have hg : gram 1 1 1 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 y y x x x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x x x x x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
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
  · have hn : area 1 y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring

private lemma base_0001021220 (x y : ℝ) (g0 : 2*y^2 - 8*y + (2:ℝ)=0) (g1 : -x*y - x + y^2 - 4*y + (4:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h1 : y^2 - 4*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x*y + x - y^2 + 4*y - (4:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (x^2*y/9 - 4*x^2/9 - x*y^2/9 + 4*x*y/3 - 32*x/9 - y^2/3 + 2*y - 5/3)*h1 + (-x*y^2/9 + x*y - 20*x/9 - y^2/3 + 4*y/3)*h2 + (8/3 - 2*y/3)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  norm_num at h4



private lemma base_0001021221 (x y : ℝ) (g0 : 2*y^2 - 8*y + (2:ℝ)=0) (g1 : -x*y + 2*x + y^2 - 4*y + (1:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : 4*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 4*x*y - y^2≠0) (_n14 : -x^2 + 4*x*y≠0) : False := by
  have h1 : y^2 - 4*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x*y - 2*x - y^2 + 4*y - (1:ℝ)=0 := by linear_combination (-1)*g1
  have h3 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-x^2*y/9 + 4*x^2/9 + x*y^2/9 - 16*x/9 - 2*y^2/3 + 11*y/3 - 3)*h1 + (x*y^2/9 - 2*x*y/3 + 8*x/9 - 2*y^2/3 + 10*y/3 - 8/3)*h2 + (4/3 - y/3)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  norm_num at h4



private lemma base_0001022220 (x y : ℝ) (g0 : 2*y^2 - 8*y + (2:ℝ)=0) (g1 : -2*x*y + x + 2*y^2 - 6*y + (4:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 2*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*y - (1:ℝ)≠0) (_n12 : 4*y - (1:ℝ)≠0) (_n13 : 4*y - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h1 : y^2 - 4*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x*y - x/2 - y^2 + 3*y - (2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h3 : x^2 - 2*x*y - x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-4*x^2*y/27 + 2*x^2/27 + 4*x*y^2/27 + 16*x*y/27 - x/3 - 28*y^2/27 + 29*y/9 - 145/54)*h1 + (4*x*y^2/27 - 16*x*y/27 + 7*x/27 - 28*y^2/27 + 112*y/27 - 49/27)*h2 + (1/18 - y/9)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0001022221 (x y : ℝ) (g0 : 2*y^2 - 8*y + (2:ℝ)=0) (g1 : -2*x*y + 4*x + 2*y^2 - 6*y + (1:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 2*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : 4*y - (1:ℝ)≠0) (_n12 : 4*y - (1:ℝ)≠0) (_n13 : -x^2 + 4*x*y≠0) (_n14 : -x^2 + 4*x*y≠0) : False := by
  have h1 : y^2 - 4*y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x*y - 2*x - y^2 + 3*y - 1/(2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h3 : x^2 - 2*x*y - x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-8*x^2*y/27 + 28*x^2/27 + 8*x*y^2/27 - 4*x*y/27 - 28*x/9 - 32*y^2/27 + 44*y/9 - 106/27)*h1 + (8*x*y^2/27 - 44*x*y/27 + 56*x/27 - 32*y^2/27 + 140*y/27 - 98/27)*h2 + (28/9 - 8*y/9)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0001110100 (x y : ℝ) (g0 : 2*x^3 - 6*x^2=0) (g1 : -x^3=0) (g2 : 4*x^3 - 8*x^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 3*x^2≠0) (_n12 : -x^2 + 4*x≠0) (_n13 : -x^2 + 4*x≠0) (n14 : -x^2 + 4*x≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (4 - x)*he
  have h3 : ((x) * (x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 h2)
  have h5 : ((x) * (x) * (x))*(1)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left (mul_ne_zero (mul_ne_zero h2 h2) h2)
  have h7 : ((x) * (x))*(x - 2)=0 := by linear_combination (1/4)*g2
  have h6 := (mul_eq_zero.mp h7).resolve_left (mul_ne_zero h2 h2)
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0001110102 (x y : ℝ) (g0 : 2*x^3 - 6*x^2=0) (g1 : -x^3 - x^2*y + x^2 + 4*x*y - 4*x=0) (g2 : 4*x^3 - 8*x^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : 3*x^2≠0) (n12 : -x^2 + 4*x≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n12
    linear_combination (4 - x)*he
  have h3 : ((x) * (x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 h2)
  have h5 : ((x))*(x^2 + x*y - x - 4*y + 4)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h7 : ((x) * (x))*(x - 2)=0 := by linear_combination (1/4)*g2
  have h6 := (mul_eq_zero.mp h7).resolve_left (mul_ne_zero h2 h2)
  have h8 : (1:ℝ)=0 := by linear_combination (-1)*h1 + (1)*h6
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0001110122 (x y : ℝ) (g0 : 2*x^3 - 6*x^2=0) (g1 : -x^3 + 2*x*y - 2*x=0) (g2 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : 3*x^2≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n14 : -x^2 + 4*x*y≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (-x + 4*y)*he
  have h3 : ((x) * (x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 h2)
  have h5 : ((x))*(x^2 - 2*y + 2)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (8*x^2/9 - 2*x*y/9 + x/9 - 2*y/3 + 1/3)*h1 + (11/9 - 2*y/9)*h4 + (-8/9)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0001110200 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : -x^2*y=0) (g2 : 4*x^3 - 8*x^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*x*y - y^2≠0) (_n12 : -x^2 + 4*x≠0) (n13 : -x^2 + 4*x≠0) (n14 : -y^2 + 4*y≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n14
    linear_combination (4 - y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : x≠0 := by
    intro he
    apply n13
    linear_combination (4 - x)*he
  have h6 : ((y) * (x) * (x))*(1)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h6).resolve_left (mul_ne_zero (mul_ne_zero h2 h5) h5)
  have h8 : ((x) * (x))*(x - 2)=0 := by linear_combination (1/4)*g2
  have h7 := (mul_eq_zero.mp h8).resolve_left (mul_ne_zero h5 h5)
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h11 : (1:ℝ)=0 := by linear_combination (1)*h10
  norm_num at h9



private lemma base_0001110201 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : -x^3 - x^2*y + 5*x^2 - 4*x=0) (g2 : 4*x^3 - 8*x^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : 4*x - (1:ℝ)≠0) (n11 : 4*x*y - y^2≠0) (n12 : -x^2 + 4*x≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n11
    linear_combination (4*x - y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : x≠0 := by
    intro he
    apply n12
    linear_combination (4 - x)*he
  have h6 : ((x))*(x^2 + x*y - 5*x + 4)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h6).resolve_left h5
  have h8 : ((x) * (x))*(x - 2)=0 := by linear_combination (1/4)*g2
  have h7 := (mul_eq_zero.mp h8).resolve_left (mul_ne_zero h5 h5)
  have h9 : (1:ℝ)=0 := by linear_combination (-1/3)*h1 + (1/6)*h4 + (x/6 - y/6 - 1/6)*h7
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h11 : (1:ℝ)=0 := by linear_combination (1)*h10
  norm_num at h9



private lemma base_0001110202 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : -2*x^2*y + x^2 + 4*x*y - 4*x=0) (g2 : 4*x^3 - 8*x^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n11 : 4*x*y - y^2≠0) (n12 : -x^2 + 4*x≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n11
    linear_combination (4*x - y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : x≠0 := by
    intro he
    apply n12
    linear_combination (4 - x)*he
  have h6 : ((x))*(x*y - x/2 - 2*y + 2)=0 := by linear_combination (-1/2)*g1
  have h4 := (mul_eq_zero.mp h6).resolve_left h5
  have h8 : ((x) * (x))*(x - 2)=0 := by linear_combination (1/4)*g2
  have h7 := (mul_eq_zero.mp h8).resolve_left (mul_ne_zero h5 h5)
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h4 + (1/2 - y)*h7
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h11 : (1:ℝ)=0 := by linear_combination (1)*h10
  have h12 : (1:ℝ)=0 := by linear_combination (1)*h11
  norm_num at h10



private lemma base_0001110211 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : -x^2*y + 2*x*y - 2*y=0) (g2 : 2*x^3 - 4*x^2 - 4*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : 4*x*y - y^2≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : 4*x - (1:ℝ)≠0) (n14 : 4*x*y - y^2≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n14
    linear_combination (4*x - y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((y))*(x^2 - 2*x + 2)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^3 - 2*x^2 - 2*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (8*x/25 - 2/25)*h1 + (-2*x*y/25 + 3*x/25 + 18/25)*h4 + (2*y/25 - 11/25)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0001110212 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : x^3 - 2*x^2*y - 4*x^2 + 6*x*y - 2*y=0) (g2 : 2*x^3 - 4*x^2 - 4*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n11 : 4*x*y - y^2≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 4*x*y≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n11
    linear_combination (4*x - y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x^3 - 2*x^2 - 2*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h5 : (1:ℝ)=0 := by linear_combination (272*x^2*y^2/2025 - 82*x^2*y/225 + 4*x^2/25 - 272*x*y^2/675 + 4798*x*y/2025 + 35*x/27 + 272*y^2/2025 - 518*y/675 - 14/25)*h1 + (136*x*y^2/2025 - 41*x*y/225 + 2*x/25 + 272*y^2/2025 - 466*y/2025 - 1226/675)*g1 + (-136*x*y^2/675 + 41*x*y/75 - 6*x/25 + 272*y^3/2025 + 622*y^2/2025 - 2074*y/675 + 1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0001110222 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : -x^2*y + 2*y^2 - 2*y=0) (g2 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : 4*x*y - y^2≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n14 : 3*y^2≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n14
    linear_combination (3*y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((y))*(x^2 - 2*y + 2)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (-88*x*y/81 + 412*x/81 + 11*y^2/27 - 149*y/81 + 197/81)*h1 + (-110*x*y/81 + 394*x/81 + 22*y^2/27 - 103*y/27 + 242/81)*h4 + (22*y/9 - 806/81)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0001111202 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : -x^2*y + x^2 + x*y - 4*x + 2*y=0) (g2 : 2*x^3 - 4*x^2 - 4*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : 4*x*y - y^2≠0) (_n12 : 4*x - (1:ℝ)≠0) (n13 : 4*x*y - y^2≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n13
    linear_combination (4*x - y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x^2*y - x^2 - x*y + 4*x - 2*y=0 := by linear_combination (-1)*g1
  have h5 : x^3 - 2*x^2 - 2*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h6 : (1:ℝ)=0 := by linear_combination (-2*x^2*y^2/75 - 11*x^2*y/100 + 6*x^2/25 + 4*x*y^2/225 - x*y/30 - 3*x/5 + 2*y^2/45 + 109*y/900 - 119/100)*h1 + (2*x*y^2/225 + 11*x*y/300 - 2*x/25 + 4*y^2/225 + y/90 - 63/100)*h4 + (2*x*y^2/75 + 11*x*y/100 - 6*x/25 - 2*y^3/225 - 89*y^2/900 - 7*y/100 + 1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  norm_num at h6



private lemma base_0001111222 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : -3*x*y + 2*y^2=0) (g2 : 2*x^3 - 4*x^2 - 6*x*y + 2*x + 2*y^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : 4*x*y - y^2≠0) (_n12 : 4*x*y - y^2≠0) (_n13 : 4*x*y - y^2≠0) (n14 : 3*y^2≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n14
    linear_combination (3*y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((y))*(x - 2*y/3)=0 := by linear_combination (-1/3)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^3 - 2*x^2 - 3*x*y + x + y^2=0 := by linear_combination (1/2)*g2
  have h7 : x=0 := by linear_combination (16*y/81 - 14/27)*h1 + (8*x^2/27 - 2*x/27 - 4*y/27 - 7/9)*h4 + (-8/27)*h6
  have h8 : y=0 := by linear_combination (8*y/27 - 7/9)*h1 + (4*x^2/9 - x/9 - 2*y/9 - 8/3)*h4 + (-4/9)*h6
  have h10 : x≠0 := by
    intro he
    apply n6
    linear_combination (4 - x)*he
  have h11 : ((x))*(1)=0 := by linear_combination (1)*h7
  have h9 := (mul_eq_zero.mp h11).resolve_left h10
  have h13 : ((y))*(1)=0 := by linear_combination (1)*h8
  have h12 := (mul_eq_zero.mp h13).resolve_left h2
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h15 : (1:ℝ)=0 := by linear_combination (1)*h14
  have h16 : (1:ℝ)=0 := by linear_combination (1)*h15
  norm_num at h14



private lemma base_0001112122 (x y : ℝ) (g0 : 2*x^3 - 6*x^2=0) (g1 : -x^3 + x^2*y - x^2=0) (g2 : 4*x^3 - 4*x^2*y - 4*x^2 + 2*x*y^2 - 4*x*y + 2*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : 3*x^2≠0) (_n12 : -x^2 + 4*x*y≠0) (_n13 : -x^2 + 4*x*y≠0) (n14 : -x^2 + 4*x*y≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (-x + 4*y)*he
  have h3 : ((x) * (x))*(x - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 h2)
  have h5 : ((x) * (x))*(x - y + 1)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left (mul_ne_zero h2 h2)
  have h7 : ((x))*(x^2 - x*y - x + y^2/2 - y + 1/2)=0 := by linear_combination (1/4)*g2
  have h6 := (mul_eq_zero.mp h7).resolve_left h2
  have h8 : (1:ℝ)=0 := by linear_combination (y/3 - 2/3)*h1 + (2*x/3 - y/3 - 2/3)*h4 + (-2/3)*h6
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h11 : (1:ℝ)=0 := by linear_combination (1)*h10
  norm_num at h9



private lemma base_0001112200 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : -x^2*y + x*y^2 - x*y - 2*y^2 + 2*y=0) (g2 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : 4*x*y - y^2≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n14 : -y^2 + 4*y≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n14
    linear_combination (4 - y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((y))*(x^2 - x*y + x + 2*y - 2)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (-41*x*y/81 + 365*x/81 + 41*y^3/243 - 190*y^2/81 + 1948*y/243 - 392/81)*h1 + (82*x*y^2/243 - 853*x*y/243 + 1915*x/243 + 287*y/243 - 874/243)*h4 + (-82*y^2/243 + 976*y/243 - 3010/243)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0001112201 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : -x^3 - x^2*y + 5*x^2 + x*y^2 - x*y - 4*x - 2*y^2 + 2*y=0) (g2 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : 4*x*y - y^2≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n13 : 4*x*y - y^2≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n13
    linear_combination (4*x - y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x^3 + x^2*y - 5*x^2 - x*y^2 + x*y + 4*x + 2*y^2 - 2*y=0 := by linear_combination (-1)*g1
  have h5 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g2
  have h6 : (1:ℝ)=0 := by linear_combination (-361*x^2*y^4/810 + 5867*x^2*y^3/972 - 13849*x^2*y^2/540 + 8290*x^2*y/243 + 220*x^2/81 + 361*x*y^5/1620 - 20671*x*y^4/9720 + 44123*x*y^3/9720 + 31897*x*y^2/9720 - 273137*x*y/9720 - 3899*x/324 - 361*y^5/540 + 25003*y^4/3240 - 237623*y^3/9720 + 31673*y^2/1944 - 66863*y/9720 + 2911/324)*h1 + (-361*x*y^3/270 + 2377*x*y^2/180 - 770*x*y/27 - 20*x/9 + 361*y^4/810 - 10877*y^3/2430 + 108917*y^2/9720 - 21601*y/3240 + 977/108)*h4 + (361*x*y^4/810 - 22837*x*y^3/4860 + 3359*x*y^2/270 - 1360*x*y/243 - 40*x/81 - 361*y^4/810 + 16339*y^3/4860 - 32383*y^2/4860 + 3599*y/162 + 2)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma shape_0001021220 (x y : ℝ) (ha : admissible ![0,0,0,1,0,2,1,2,2,0] x y) : False := by
  apply base_0001021220 x y
  · have hg : gram 1 1 1 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 y y x x y 1=0 := ha.2.2.2.1
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area 1 y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001021221 (x y : ℝ) (ha : admissible ![0,0,0,1,0,2,1,2,2,1] x y) : False := by
  apply base_0001021221 x y
  · have hg : gram 1 1 1 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 y y x x y x=0 := ha.2.2.2.1
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area 1 y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001022220 (x y : ℝ) (ha : admissible ![0,0,0,1,0,2,2,2,2,0] x y) : False := by
  apply base_0001022220 x y
  · have hg : gram 1 1 1 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 y y x y y 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y y x y y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area 1 y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001022221 (x y : ℝ) (ha : admissible ![0,0,0,1,0,2,2,2,2,1] x y) : False := by
  apply base_0001022221 x y
  · have hg : gram 1 1 1 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 1 y y x y y x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y y x y y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area 1 y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001110100 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,0,1,0,0] x y) : False := by
  apply base_0001110100 x y
  · have hg : gram 1 1 x 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x x x 1 1 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 1 x 1 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001110102 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,0,1,0,2] x y) : False := by
  apply base_0001110102 x y
  · have hg : gram 1 1 x 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x x x 1 1 y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 1 x 1 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 x≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001110122 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,0,1,2,2] x y) : False := by
  apply base_0001110122 x y
  · have hg : gram 1 1 x 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x x x 1 y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 y x 1 y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001110200 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,0,2,0,0] x y) : False := by
  apply base_0001110200 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y x 1 1 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 1 x 1 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001110201 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,0,2,0,1] x y) : False := by
  apply base_0001110201 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y x 1 1 x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 1 x 1 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001110202 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,0,2,0,2] x y) : False := by
  apply base_0001110202 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y x 1 1 y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 1 x 1 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001110211 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,0,2,1,1] x y) : False := by
  apply base_0001110211 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y x 1 x x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 x x 1 x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001110212 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,0,2,1,2] x y) : False := by
  apply base_0001110212 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y x 1 x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 x x 1 x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
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
  · have hn : area x x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001110222 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,0,2,2,2] x y) : False := by
  apply base_0001110222 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y x 1 y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 y x 1 y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001111202 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,1,2,0,2] x y) : False := by
  apply base_0001111202 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y x x 1 y=0 := ha.2.2.2.1
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
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001111222 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,1,2,2,2] x y) : False := by
  apply base_0001111222 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y x x y y=0 := ha.2.2.2.1
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
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001112122 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,2,1,2,2] x y) : False := by
  apply base_0001112122 x y
  · have hg : gram 1 1 x 1 x x 1 x x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x x x y y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x y y x y y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x x≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001112200 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,2,2,0,0] x y) : False := by
  apply base_0001112200 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y x y 1 1=0 := ha.2.2.2.1
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
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001112201 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,2,2,0,1] x y) : False := by
  apply base_0001112201 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y x y 1 x=0 := ha.2.2.2.1
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
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring

private lemma base_0001112202 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : -2*x^2*y + x^2 + x*y^2 + 3*x*y - 4*x - 2*y^2 + 2*y=0) (g2 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n11 : 4*x*y - y^2≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 4*x*y≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n11
    linear_combination (4*x - y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x^2*y - x^2/2 - x*y^2/2 - 3*x*y/2 + 2*x + y^2 - y=0 := by linear_combination (-1/2)*g1
  have h5 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g2
  have h6 : (1:ℝ)=0 := by linear_combination (1084*x^2*y^4/4725 - 4376*x^2*y^3/2025 + 18223*x^2*y^2/2835 - 1147*x^2*y/189 + 40*x^2/81 - 542*x*y^5/4725 + 562*x*y^4/2025 + 1873*x*y^3/630 - 167978*x*y^2/14175 + 27157*x*y/1890 - 134*x/81 + 2168*y^5/4725 - 56386*y^4/14175 + 52112*y^3/4725 - 73739*y^2/5670 + 247046*y/14175 - 61991/5670)*h1 + (2168*x*y^3/1575 - 16808*x*y^2/1575 + 2182*x*y/105 - 16*x/9 - 2168*y^4/4725 + 51508*y^3/14175 - 20338*y^2/2025 + 79019*y/4725 - 761/35)*h4 + (-1084*x*y^4/4725 + 4376*x*y^3/2025 - 18223*x*y^2/2835 + 1147*x*y/189 - 40*x/81 - 1084*y^3/4725 + 9796*y^2/2025 - 49951*y/2835 + 2)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0001112211 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : -x^2*y + x*y^2 + x*y - 2*y^2=0) (g2 : 2*x^3 - 4*x^2 - 6*x*y + 2*x + 2*y^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : 4*x*y - y^2≠0) (_n12 : 4*x*y - y^2≠0) (_n13 : 4*x*y - y^2≠0) (n14 : 4*x*y - y^2≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n14
    linear_combination (4*x - y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((y))*(x^2 - x*y - x + 2*y)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^3 - 2*x^2 - 3*x*y + x + y^2=0 := by linear_combination (1/2)*g2
  have h7 : x=0 := by linear_combination (-x/3 - y^3/18 + 11*y^2/18 - 4*y/3)*h1 + (-x*y^2/18 + x*y/2 - 2*x/3 - y^2/18 + y/6)*h4 + (y^2/18 - y/2 + 1)*h6
  have h8 : y=0 := by linear_combination (y^2/6 - 5*y/6)*h1 + (x*y/6 - x/2 + y/6 + 1/2)*h4 + (1/2 - y/6)*h6
  have h10 : x≠0 := by
    intro he
    apply n6
    linear_combination (4 - x)*he
  have h11 : ((x))*(1)=0 := by linear_combination (1)*h7
  have h9 := (mul_eq_zero.mp h11).resolve_left h10
  have h13 : ((y))*(1)=0 := by linear_combination (1)*h8
  have h12 := (mul_eq_zero.mp h13).resolve_left h2
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h15 : (1:ℝ)=0 := by linear_combination (1)*h14
  have h16 : (1:ℝ)=0 := by linear_combination (1)*h15
  norm_num at h14



private lemma base_0001112212 (x y : ℝ) (g0 : 2*x^2*y - 8*x*y + 2*y^2=0) (g1 : x^3 - 2*x^2*y - 4*x^2 + x*y^2 + 5*x*y - 2*y^2=0) (g2 : 2*x^3 - 4*x^2 - 6*x*y + 2*x + 2*y^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : 4*x*y - y^2≠0) (n12 : 4*x*y - y^2≠0) (_n13 : -x^2 + 4*x*y≠0) (n14 : -x^2 + 4*x*y≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n12
    linear_combination (4*x - y)*he
  have h3 : ((y))*(x^2 - 4*x + y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h4 : x^3 - 2*x^2 - 3*x*y + x + y^2=0 := by linear_combination (1/2)*g2
  have h5 : x=0 := by linear_combination (-32*x^2*y^5/5103 + 1360*x^2*y^4/35721 - 1726*x^2*y^3/35721 - 4876*x^2*y^2/35721 + 1607*x^2*y/3969 - 2*x^2/7 + 32*x*y^5/729 - 1744*x*y^4/5103 + 38986*x*y^3/35721 - 63566*x*y^2/35721 + 2591*x*y/1701 - 185*x/567 - 64*y^6/5103 + 3616*y^5/35721 - 116*y^4/441 + 338*y^3/35721 + 4630*y^2/5103 - 827*y/567)*h1 + (128*x*y^4/5103 - 7456*x*y^3/35721 + 23680*x*y^2/35721 - 33776*x*y/35721 + 32*x/63 - 32*y^5/5103 + 1808*y^4/35721 - 718*y^3/3969 + 11320*y^2/35721 - 1159*y/5103 - 130/567)*g1 + (32*x*y^5/5103 - 752*x*y^4/11907 + 9182*x*y^3/35721 - 6268*x*y^2/11907 + 2759*x*y/5103 - 2*x/9 - 8*y^3/81 + 118*y^2/189 - 772*y/567 + 1)*h4
  have h6 : y=0 := by linear_combination (-8*x^2*y^3/81 + 130*x^2*y^2/567 + 4*x^2*y/9 - 9*x^2/7 + 56*x*y^3/81 - 226*x*y^2/81 + 814*x*y/189 - 19*x/9 - 16*y^4/81 + 484*y^3/567 - 142*y^2/567 - 34*y/9 + 1)*h1 + (32*x*y^2/81 - 1024*x*y/567 + 16*x/7 - 8*y^3/81 + 242*y^2/567 - 512*y/567 + 1/9)*g1 + (8*x*y^3/81 - 118*x*y^2/189 + 772*x*y/567 - x - 14*y/9 + 4)*h4
  have h8 : x≠0 := by
    intro he
    apply n14
    linear_combination (-x + 4*y)*he
  have h9 : ((x))*(1)=0 := by linear_combination (1)*h5
  have h7 := (mul_eq_zero.mp h9).resolve_left h8
  have h11 : ((y))*(1)=0 := by linear_combination (1)*h6
  have h10 := (mul_eq_zero.mp h11).resolve_left h2
  have h12 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h12
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h13
  norm_num at h12



private lemma base_0001120200 (x y : ℝ) (g0 : 2*x^2 + 2*x*y^2 - 8*x*y=0) (g1 : x^3 - 2*x^2*y=0) (g2 : 4*x^3 - 8*x^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 4*x*y≠0) (n12 : -x^2 + 4*x≠0) (_n13 : -y^2 + 4*y≠0) (_n14 : -y^2 + 4*y≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n12
    linear_combination (4 - x)*he
  have h3 : ((x))*(x + y^2 - 4*y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x) * (x))*(x - 2*y)=0 := by linear_combination (1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left (mul_ne_zero h2 h2)
  have h7 : ((x) * (x))*(x - 2)=0 := by linear_combination (1/4)*g2
  have h6 := (mul_eq_zero.mp h7).resolve_left (mul_ne_zero h2 h2)
  have h8 : (1:ℝ)=0 := by linear_combination (-1)*h1 + (3/2 - y/2)*h4 + (y/2 - 1/2)*h6
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0001120201 (x y : ℝ) (g0 : 2*x^2 + 2*x*y^2 - 8*x*y=0) (g1 : -2*x^2*y + 5*x^2 - 4*x=0) (g2 : 4*x^3 - 8*x^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 4*x*y≠0) (n12 : -x^2 + 4*x≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n12
    linear_combination (4 - x)*he
  have h3 : ((x))*(x + y^2 - 4*y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x*y - 5*x/2 + 2)=0 := by linear_combination (-1/2)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h7 : ((x) * (x))*(x - 2)=0 := by linear_combination (1/4)*g2
  have h6 := (mul_eq_zero.mp h7).resolve_left (mul_ne_zero h2 h2)
  have h8 : (1:ℝ)=0 := by linear_combination (-4/7)*h1 + (2*y/7 - 5/7)*h4 + (-2*y^2/7 + 10*y/7 - 17/14)*h6
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h11 : (1:ℝ)=0 := by linear_combination (1)*h10
  norm_num at h9



private lemma base_0001120210 (x y : ℝ) (g0 : 2*x^2 + 2*x*y^2 - 8*x*y=0) (g1 : x^3 - x^2*y - 2*x^2 - x*y + 2*x=0) (g2 : 2*x^3 - 4*x^2 - 4*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (n11 : -x^2 + 4*x*y≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : -y^2 + 4*y≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n11
    linear_combination (-x + 4*y)*he
  have h3 : ((x))*(x + y^2 - 4*y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x^2 - x*y - 2*x - y + 2)=0 := by linear_combination (1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^3 - 2*x^2 - 2*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (-x*y^2/25 - 8*x*y/25 - 16*x/25 - y^2/25 - 3*y/25 + 4/25)*h1 + (-x*y^2/25 - 2*x*y/25 + 7*x/25 - y^3/25 - y^2/25 + 3*y/5 + 16/25)*h4 + (y^2/25 + 2*y/25 - 7/25)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0001120212 (x y : ℝ) (g0 : 2*x^2 + 2*x*y^2 - 8*x*y=0) (g1 : x^3 - 2*x^2*y - x^2 + 3*x*y - 2*x=0) (g2 : 2*x^3 - 4*x^2 - 4*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : -x^2 + 4*x*y≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : 4*y - (1:ℝ)≠0) (n14 : -x^2 + 4*x*y≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (-x + 4*y)*he
  have h3 : ((x))*(x + y^2 - 4*y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x^2 - 2*x*y - x + 3*y - 2)=0 := by linear_combination (1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^3 - 2*x^2 - 2*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (16*x*y^3/25 - 56*x*y^2/25 + 9*x*y/25 + 6*x/25 - 24*y^3/25 + 94*y^2/25 - 51*y/25 - 19/25)*h1 + (4*x*y^3/25 - 19*x*y^2/25 + 3*x*y/5 + 13*x/25 + 8*y^4/25 - 58*y^3/25 + 21*y^2/5 + 2*y/25 - 19/25)*h4 + (-4*y^3/25 + 19*y^2/25 - 3*y/5 - 13/25)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0001120220 (x y : ℝ) (g0 : 2*x^2 + 2*x*y^2 - 8*x*y=0) (g1 : x^3 - 2*x^2*y + x*y^2 - 3*x*y + 2*x=0) (g2 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (n11 : -x^2 + 4*x*y≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -y^2 + 4*y≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n11
    linear_combination (-x + 4*y)*he
  have h3 : ((x))*(x + y^2 - 4*y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x^2 - 2*x*y + y^2 - 3*y + 2)=0 := by linear_combination (1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (-104*x*y^3/1323 + 74*x*y^2/441 + 295*x*y/1323 - 122*x/189 + 26*y^4/441 - 73*y^3/189 + 1156*y^2/1323 - 944*y/1323 - 220/1323)*h1 + (-52*x*y^3/1323 + 254*x*y^2/1323 - 382*x*y/1323 + 110*x/1323 - 26*y^4/441 + 563*y^3/1323 - 8*y^2/9 + 443*y/1323 + 689/1323)*h4 + (52*y^3/1323 - 254*y^2/1323 + 382*y/1323 - 110/1323)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0001120221 (x y : ℝ) (g0 : 2*x^2 + 2*x*y^2 - 8*x*y=0) (g1 : -2*x^2*y + 5*x^2 + x*y^2 - 3*x*y - 2*x=0) (g2 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 4*x*y≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n14 : -x^2 + 4*x*y≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (-x + 4*y)*he
  have h3 : ((x))*(x + y^2 - 4*y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x*y - 5*x/2 - y^2/2 + 3*y/2 + 1)=0 := by linear_combination (-1/2)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (-444*x^2*y^2/343 + 2560*x^2*y/343 - 3358*x^2/343 + 222*x*y^3/343 - 2279*x*y^2/343 + 7439*x*y/343 - 15111*x/686 + 444*y^3/343 - 6341*y^2/686 + 10093*y/686 + 1697/343)*h1 + (444*x*y^3/343 - 3226*x*y^2/343 + 7198*x*y/343 - 5037*x/343 + 888*y^3/343 - 6785*y^2/343 + 13430*y/343 - 1336/343)*h4 + (444*y^2/343 - 2560*y/343 + 3358/343)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0001121220 (x y : ℝ) (g0 : 2*x^2 + 2*x*y^2 - 8*x*y=0) (g1 : x^3 - x^2*y - 2*x^2 + x*y^2 - 4*x*y + 4*x=0) (g2 : 2*x^3 - 4*x^2 - 6*x*y + 2*x + 2*y^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (n11 : -x^2 + 4*x*y≠0) (_n12 : 4*x*y - y^2≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n11
    linear_combination (-x + 4*y)*he
  have h3 : ((x))*(x + y^2 - 4*y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x^2 - x*y - 2*x + y^2 - 4*y + 4)=0 := by linear_combination (1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h6 : x^3 - 2*x^2 - 3*x*y + x + y^2=0 := by linear_combination (1/2)*g2
  have h7 : (1:ℝ)=0 := by linear_combination (x*y^2/4 - x*y - x/4 - y^4/16 + 7*y^3/16 - 5*y^2/8 - 7*y/16 + 11/16)*h1 + (x*y^3/16 - 3*x*y^2/8 + x*y/2 - x/16 + y^4/16 - 3*y^3/8 + y^2/4 + 15*y/16 + 1/4)*h4 + (-y^3/16 + 3*y^2/8 - y/2 + 1/16)*h6
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  norm_num at h7



private lemma base_0001122220 (x y : ℝ) (g0 : 2*x^2 + 2*x*y^2 - 8*x*y=0) (g1 : x^3 - 2*x^2*y + 2*x*y^2 - 6*x*y + 4*x=0) (g2 : 4*x^3 - 4*x^2*y - 4*x^2 + 2*x*y^2 - 4*x*y + 2*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 4*x≠0) (_n11 : -x^2 + 4*x*y≠0) (n12 : -x^2 + 4*x*y≠0) (_n13 : 4*y - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n12
    linear_combination (-x + 4*y)*he
  have h3 : ((x))*(x + y^2 - 4*y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x^2 - 2*x*y + 2*y^2 - 6*y + 4)=0 := by linear_combination (1)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h7 : ((x))*(x^2 - x*y - x + y^2/2 - y + 1/2)=0 := by linear_combination (1/4)*g2
  have h6 := (mul_eq_zero.mp h7).resolve_left h2
  have h8 : (1:ℝ)=0 := by linear_combination (28*x*y^2/243 - 4*x*y/27 - 73*x/243 - 14*y^3/81 + 187*y^2/243 - 80*y/81 + 14/243)*h1 + (28*y^3/243 - 134*y^2/243 + 116*y/243 + 59/243)*h4 + (-28*y^3/243 + 106*y^2/243 - 80*y/243 + 14/243)*h6
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h11 : (1:ℝ)=0 := by linear_combination (1)*h10
  norm_num at h9



private lemma base_0001122221 (x y : ℝ) (g0 : 2*x^2 + 2*x*y^2 - 8*x*y=0) (g1 : -2*x^2*y + 5*x^2 + 2*x*y^2 - 6*x*y=0) (g2 : 4*x^3 - 4*x^2*y - 4*x^2 + 2*x*y^2 - 4*x*y + 2*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 4*x*y≠0) (_n12 : -x^2 + 4*x*y≠0) (_n13 : -x^2 + 4*x*y≠0) (n14 : -x^2 + 4*x*y≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n14
    linear_combination (-x + 4*y)*he
  have h3 : ((x))*(x + y^2 - 4*y)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x*y - 5*x/2 - y^2 + 3*y)=0 := by linear_combination (-1/2)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h7 : ((x))*(x^2 - x*y - x + y^2/2 - y + 1/2)=0 := by linear_combination (1/4)*g2
  have h6 := (mul_eq_zero.mp h7).resolve_left h2
  have h8 : (1:ℝ)=0 := by linear_combination (-8*x*y^2/81 + 88*x*y/81 - 2*x + 8*y^3/81 - 32*y^2/27 + 248*y/81 - 143/81)*h1 + (8*y^3/81 - 100*y^2/81 + 280*y/81 - 122/81)*h4 + (8*y^2/81 - 88*y/81 + 2)*h6
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h11 : (1:ℝ)=0 := by linear_combination (1)*h10
  norm_num at h9



private lemma base_0001220200 (x y : ℝ) (g0 : 2*y^3 - 6*y^2=0) (g1 : -x*y^2=0) (g2 : 2*x^2*y + 2*x*y^2 - 8*x*y=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -y^2 + 4*y≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (_n9 : -x^2 + 4*x≠0) (n10 : -x^2 + 4*x≠0) (_n11 : 3*y^2≠0) (_n12 : -y^2 + 4*y≠0) (_n13 : -y^2 + 4*y≠0) (n14 : -y^2 + 4*y≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n14
    linear_combination (4 - y)*he
  have h3 : ((y) * (y))*(y - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 h2)
  have h5 : x≠0 := by
    intro he
    apply n10
    linear_combination (4 - x)*he
  have h6 : ((y) * (y) * (x))*(1)=0 := by linear_combination (-1)*g1
  have h4 := (mul_eq_zero.mp h6).resolve_left (mul_ne_zero (mul_ne_zero h2 h2) h5)
  have h8 : ((y) * (x))*(x + y - 4)=0 := by linear_combination (1/2)*g2
  have h7 := (mul_eq_zero.mp h8).resolve_left (mul_ne_zero h2 h5)
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h11 : (1:ℝ)=0 := by linear_combination (1)*h10
  norm_num at h9



private lemma base_0001220201 (x y : ℝ) (g0 : 2*y^3 - 6*y^2=0) (g1 : -2*x*y^2 + 4*x*y + y^2 - 4*y=0) (g2 : 2*x^2*y + 2*x*y^2 - 8*x*y=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -y^2 + 4*y≠0) (_n6 : -y^2 + 4*y≠0) (_n7 : -x^2 + 4*x≠0) (_n8 : -y^2 + 4*y≠0) (n9 : -x^2 + 4*x≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : 3*y^2≠0) (n12 : -y^2 + 4*y≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n12
    linear_combination (4 - y)*he
  have h3 : ((y) * (y))*(y - 3)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 h2)
  have h5 : ((y))*(x*y - 2*x - y/2 + 2)=0 := by linear_combination (-1/2)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h7 : x≠0 := by
    intro he
    apply n9
    linear_combination (4 - x)*he
  have h8 : ((y) * (x))*(x + y - 4)=0 := by linear_combination (1/2)*g2
  have h6 := (mul_eq_zero.mp h8).resolve_left (mul_ne_zero h2 h7)
  have h9 : (1:ℝ)=0 := by linear_combination (1 - 2*x/3)*h1 + (2/3)*h4 + (-2/3)*h6
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  have h11 : (1:ℝ)=0 := by linear_combination (1)*h10
  have h12 : (1:ℝ)=0 := by linear_combination (1)*h11
  norm_num at h10



private lemma base_0011011220 (x y : ℝ) (g0 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (g1 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (5:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : 4*x - (1:ℝ)≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 4*x - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h1 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 2*x*y - 2*x + y^2 - y + 5/(2:ℝ)=0 := by linear_combination (1/2)*g1
  have h3 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (2/3)*h2 + (-2/3)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0011011222 (x y : ℝ) (g0 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (g1 : 2*x^2 - 4*x*y - 4*x + 2*y^2 + y + (2:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : 4*x - (1:ℝ)≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x*y - y^2≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : 4*x*y - y^2≠0) (n14 : 3*y^2≠0) : False := by
  have h1 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 2*x*y - 2*x + y^2 + y/2 + (1:ℝ)=0 := by linear_combination (1/2)*g1
  have h3 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x^2 - 2*x + (1:ℝ)=0 := by linear_combination (4*x/3 - 2*y/3 + 2/3)*h2 + (-4*x/3 + 2*y/3 + 1/3)*h3
  have h5 : y=0 := by linear_combination (2/3)*h2 + (-2/3)*h3
  have h7 : x - (1:ℝ)≠0 := by
    intro he
    apply n2
    linear_combination (1)*he
  have h8 : ((x - 1) * (x - 1))*(1)=0 := by linear_combination (1)*h4
  have h6 := (mul_eq_zero.mp h8).resolve_left (mul_ne_zero h7 h7)
  have h10 : y≠0 := by
    intro he
    apply n14
    linear_combination (3*y)*he
  have h11 : ((y))*(1)=0 := by linear_combination (1)*h5
  have h9 := (mul_eq_zero.mp h11).resolve_left h10
  have h12 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h12
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h13
  norm_num at h12



private lemma shape_0001112202 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,2,2,0,2] x y) : False := by
  apply base_0001112202 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y x y 1 y=0 := ha.2.2.2.1
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
  · have hn : area 1 1 x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001112211 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,2,2,1,1] x y) : False := by
  apply base_0001112211 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y x y x x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x y x x y x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
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
  · have hn : area x y x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001112212 (x y : ℝ) (ha : admissible ![0,0,0,1,1,1,2,2,1,2] x y) : False := by
  apply base_0001112212 x y
  · have hg : gram 1 1 x 1 x y 1 x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 x y x y x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x y x x y x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 1 y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
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


private lemma shape_0001120200 (x y : ℝ) (ha : admissible ![0,0,0,1,1,2,0,2,0,0] x y) : False := by
  apply base_0001120200 x y
  · have hg : gram 1 1 x 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 y y x 1 1 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 1 x 1 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001120201 (x y : ℝ) (ha : admissible ![0,0,0,1,1,2,0,2,0,1] x y) : False := by
  apply base_0001120201 x y
  · have hg : gram 1 1 x 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 y y x 1 1 x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 1 x 1 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001120210 (x y : ℝ) (ha : admissible ![0,0,0,1,1,2,0,2,1,0] x y) : False := by
  apply base_0001120210 x y
  · have hg : gram 1 1 x 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 y y x 1 x 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 x x 1 x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
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
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001120212 (x y : ℝ) (ha : admissible ![0,0,0,1,1,2,0,2,1,2] x y) : False := by
  apply base_0001120212 x y
  · have hg : gram 1 1 x 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 y y x 1 x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 x x 1 x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
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
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001120220 (x y : ℝ) (ha : admissible ![0,0,0,1,1,2,0,2,2,0] x y) : False := by
  apply base_0001120220 x y
  · have hg : gram 1 1 x 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 y y x 1 y 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 y x 1 y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
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
  · have hn : area x y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001120221 (x y : ℝ) (ha : admissible ![0,0,0,1,1,2,0,2,2,1] x y) : False := by
  apply base_0001120221 x y
  · have hg : gram 1 1 x 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 y y x 1 y x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 y x 1 y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
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
  · have hn : area x y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001121220 (x y : ℝ) (ha : admissible ![0,0,0,1,1,2,1,2,2,0] x y) : False := by
  apply base_0001121220 x y
  · have hg : gram 1 1 x 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 y y x x y 1=0 := ha.2.2.2.1
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area x y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001122220 (x y : ℝ) (ha : admissible ![0,0,0,1,1,2,2,2,2,0] x y) : False := by
  apply base_0001122220 x y
  · have hg : gram 1 1 x 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 y y x y y 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x y y x y y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area x y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001122221 (x y : ℝ) (ha : admissible ![0,0,0,1,1,2,2,2,2,1] x y) : False := by
  apply base_0001122221 x y
  · have hg : gram 1 1 x 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x 1 y y x y y x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x y y x y y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
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
  · have hn : area x y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001220200 (x y : ℝ) (ha : admissible ![0,0,0,1,2,2,0,2,0,0] x y) : False := by
  apply base_0001220200 x y
  · have hg : gram 1 1 y 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 y 1 y y x 1 1 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 y x 1 1 x 1 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0001220201 (x y : ℝ) (ha : admissible ![0,0,0,1,2,2,0,2,0,1] x y) : False := by
  apply base_0001220201 x y
  · have hg : gram 1 1 y 1 y y 1 y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 y 1 y y x 1 1 x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 y x 1 1 x 1 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 1 y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
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
  · have hn : area 1 x 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0011011220 (x y : ℝ) (ha : admissible ![0,0,1,1,0,1,1,2,2,0] x y) : False := by
  apply base_0011011220 x y
  · have hg : gram 1 1 1 x x y x x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x y x x y 1=0 := ha.2.2.2.1
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
  · have hn : area 1 x x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
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
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0011011222 (x y : ℝ) (ha : admissible ![0,0,1,1,0,1,1,2,2,2] x y) : False := by
  apply base_0011011222 x y
  · have hg : gram 1 1 1 x x y x x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x y x x y y=0 := ha.2.2.2.1
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
  · have hn : area 1 x x≠0 := ha.2.1 0 1 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x x≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
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
  · have hn : area 1 x y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma base_0011012220 (x y : ℝ) (g0 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (g1 : x^2 - 2*x*y - 3*x + y^2 - 3*y + (5:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 2*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : 4*x - (1:ℝ)≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : 4*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h1 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 2*x*y - x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h3 : (1:ℝ)=0 := by linear_combination (-5*x/9 + 2*y/9 + 1/9)*h1 + (x/9 - y/9 + 1/3)*g1 + (4*x/9 - y/9 - 7/9)*h2
  have h4 : (1:ℝ)=0 := by linear_combination (1)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  norm_num at h3



private lemma base_0011101100 (x y : ℝ) (g0 : 2*x^3 - 4*x^2 - 4*x + (2:ℝ)=0) (g1 : 3*x^3 - 11*x^2 + 9*x - (2:ℝ)=0) (g2 : 2*x^3 - 4*x^2 - 4*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : 4*x - (1:ℝ)≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : 4*x - (1:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : -x^2 + 4*x≠0) (_n14 : -x^2 + 4*x≠0) : (x^2 - 3*x + (1:ℝ)=0) := by
  have h1 : x^3 - 2*x^2 - 2*x + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^3 - 11*x^2/3 + 3*x - 2/(3:ℝ)=0 := by linear_combination (1/3)*g1
  have h3 : x^3 - 2*x^2 - 2*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x^2 - 3*x + (1:ℝ)=0 := by linear_combination (-3/5)*h2 + (3/5)*h3
  have h5 : x^2 - 3*x + (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : x^2 - 3*x + (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : x^2 - 3*x + (1:ℝ)=0 := by linear_combination (1)*h6
  exact h5



private lemma base_0011101202 (x y : ℝ) (g0 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : 3*x^3 - x^2*y - 7*x^2 + x*y + 3*x + 2*y - (2:ℝ)=0) (g2 : 2*x^3 - 4*x^2 - 4*x + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n9 : -x^2 + 4*x≠0) (_n10 : 4*x*y - y^2≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : 4*x - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h1 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g0
  have h2 : x^3 - x^2*y/3 - 7*x^2/3 + x*y/3 + x + 2*y/3 - 2/(3:ℝ)=0 := by linear_combination (1/3)*g1
  have h3 : x^3 - 2*x^2 - 2*x + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-2*x^2*y^5/265 + 49*x^2*y^4/3975 + 2414*x^2*y^3/11925 - 617*x^2*y^2/2385 + 5914*x^2*y/11925 - 7264*x^2/3975 + 2*x*y^5/265 + 131*x*y^4/3975 - 4736*x*y^3/11925 + 3733*x*y^2/11925 - 49034*x*y/11925 + 13866*x/1325 + 4*y^5/265 - 368*y^4/3975 + 361*y^3/2385 - 12547*y^2/11925 + 18814*y/3975 - 43178/3975)*h1 + (3*x^2*y^5/265 - 49*x^2*y^4/2650 - 1207*x^2*y^3/3975 + 617*x^2*y^2/1590 - 2957*x^2*y/3975 + 3632*x^2/1325 - 6*x*y^5/265 + 229*x*y^4/1325 - 2068*x*y^3/3975 + 4961*x*y^2/3975 + 3533*x*y/1325 - 12173*x/1325 - 3*y^6/265 + 199*y^5/2650 - 1201*y^4/7950 + 7189*y^3/7950 - 5737*y^2/1590 + 8772*y/1325 - 3798/1325)*h2 + (-x^2*y^5/265 + 49*x^2*y^4/7950 + 1207*x^2*y^3/11925 - 617*x^2*y^2/4770 + 2957*x^2*y/11925 - 3632*x^2/3975 + 6*x*y^5/265 - 289*x*y^4/1325 + 2842*x*y^3/3975 - 5177*x*y^2/3975 + 11323*x*y/11925 + 437*x/795 + y^6/265 - 199*y^5/7950 + 481*y^4/23850 - 11593*y^3/23850 + 10259*y^2/2650 - 5489*y/795 + 17968/3975)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0011102210 (x y : ℝ) (g0 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : 3*x^3 - 2*x^2*y - 6*x^2 + x*y^2 + 3*x - 2*y^2 + 2*y=0) (g2 : 2*x^3 - 4*x^2 - 6*x*y + 2*x + 2*y^2=0) (_n0 : x≠0) (_n1 : y≠0) (n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : 4*x*y - y^2≠0) (n13 : -y^2 + 4*y≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h1 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g0
  have h2 : x^3 - 2*x^2*y/3 - 2*x^2 + x*y^2/3 + x - 2*y^2/3 + 2*y/(3:ℝ)=0 := by linear_combination (1/3)*g1
  have h3 : x^3 - 2*x^2 - 3*x*y + x + y^2=0 := by linear_combination (1/2)*g2
  have h4 : x^2 - 2*x + (1:ℝ)=0 := by linear_combination (-2*x^3*y^5/39 + 29*x^3*y^4/39 - 128*x^3*y^3/39 + 112*x^3*y^2/39 + 106*x^3*y/13 - 123*x^3/13 + x^2*y^6/39 + x^2*y^5/26 - 166*x^2*y^4/39 + 333*x^2*y^3/13 - 536*x^2*y^2/13 - 569*x^2*y/78 + 379*x^2/13 - 8*x*y^6/39 + 28*x*y^5/13 - 34*x*y^4/13 - 1138*x*y^3/39 + 2824*x*y^2/39 - 258*x*y/13 - 266*x/13 + 5*y^6/13 - 137*y^5/26 + 303*y^4/13 - 919*y^3/26 + 189*y^2/13 - 28*y/13 + 2)*h1 + (x^3*y^5/26 - 29*x^3*y^4/52 + 32*x^3*y^3/13 - 28*x^3*y^2/13 - 159*x^3*y/26 + 369*x^3/52 - 9*x^2*y^5/26 + 263*x^2*y^4/52 - 1247*x^2*y^3/52 + 1913*x^2*y^2/52 + 35*x^2*y/52 - 39*x^2/2 + x*y^6/26 + 9*x*y^5/52 - 31*x*y^4/4 + 1153*x*y^3/26 - 1034*x*y^2/13 + 1757*x*y/52 + 393*x/52 - 3*y^6/26 + 75*y^5/52 - 129*y^4/26 + 6*y^3/13 + 207*y^2/13 - 855*y/52 + 60/13)*h2 + (x^3*y^5/78 - 29*x^3*y^4/156 + 32*x^3*y^3/39 - 28*x^3*y^2/39 - 53*x^3*y/26 + 123*x^3/52 - x^2*y^6/39 + x^2*y^5/3 - 61*x^2*y^4/52 + x^2*y^3/156 + 469*x^2*y^2/156 + 397*x^2*y/156 - 64*x^2/13 + x*y^6/6 - 129*x*y^5/52 + 1949*x*y^4/156 - 943*x*y^3/39 + 1253*x*y^2/78 - 253*x*y/156 - 87*x/52 - 7*y^6/26 + 211*y^5/52 - 278*y^4/13 + 614*y^3/13 - 1143*y^2/26 + 609*y/52 + 47/13)*h3
  have h5 : y=0 := by linear_combination (-4*x^2*y^4/39 + 46*x^2*y^3/39 - 118*x^2*y^2/39 - 10*x^2*y/3 + 82*x^2/13 + 2*x*y^5/39 - x*y^4/13 - 179*x*y^3/39 + 277*x*y^2/13 - 135*x*y/13 - 266*x/39 - 10*y^5/39 + 3*y^4 - 124*y^3/13 + 175*y^2/39 - 28*y/39)*h1 + (x^2*y^4/13 - 23*x^2*y^3/26 + 59*x^2*y^2/26 + 5*x^2*y/2 - 123*x^2/26 - 6*x*y^4/13 + 73*x*y^3/13 - 19*x*y^2 + 136*x*y/13 + 46*x/13 + y^5/13 - 21*y^4/26 + 22*y^3/13 + 40*y^2/13 - 58*y/13 + 53/26)*h2 + (x^2*y^4/39 - 23*x^2*y^3/78 + 59*x^2*y^2/78 + 5*x^2*y/6 - 41*x^2/26 - 2*x*y^5/39 + 23*x*y^4/39 - 21*x*y^3/13 - 31*x*y^2/39 + 62*x*y/39 + 5*x/39 + 7*y^5/39 - 61*y^4/26 + 373*y^3/39 - 482*y^2/39 + 179*y/39 + 107/78)*h3
  have h7 : x - (1:ℝ)≠0 := by
    intro he
    apply n2
    linear_combination (1)*he
  have h8 : ((x - 1) * (x - 1))*(1)=0 := by linear_combination (1)*h4
  have h6 := (mul_eq_zero.mp h8).resolve_left (mul_ne_zero h7 h7)
  have h10 : y≠0 := by
    intro he
    apply n13
    linear_combination (4 - y)*he
  have h11 : ((y))*(1)=0 := by linear_combination (1)*h5
  have h9 := (mul_eq_zero.mp h11).resolve_left h10
  have h12 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h12
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h13
  norm_num at h12



private lemma base_0011102212 (x y : ℝ) (g0 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : 3*x^3 - 3*x^2*y - 5*x^2 + x*y^2 + 4*x*y - x - 2*y^2 + 2*y=0) (g2 : 2*x^3 - 4*x^2 - 6*x*y + 2*x + 2*y^2=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n9 : 4*x - (1:ℝ)≠0) (_n10 : 4*x*y - y^2≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : 4*x*y - y^2≠0) (_n13 : 4*y - (1:ℝ)≠0) (_n14 : -x^2 + 4*x*y≠0) : False := by
  have h1 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g0
  have h2 : x^3 - x^2*y - 5*x^2/3 + x*y^2/3 + 4*x*y/3 - x/3 - 2*y^2/3 + 2*y/(3:ℝ)=0 := by linear_combination (1/3)*g1
  have h3 : x^3 - 2*x^2 - 3*x*y + x + y^2=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (329*x^2*y^7/759 - 23137*x^2*y^6/2277 + 20775*x^2*y^5/253 - 548590*x^2*y^4/2277 + 10139*x^2*y^3/207 + 922807*x^2*y^2/2277 + 37453*x^2*y/759 - 13038*x^2/253 - 329*x*y^8/2277 + 9319*x*y^7/6831 + 146813*x*y^6/6831 - 772732*x*y^5/2277 + 9819415*x*y^4/6831 - 10824493*x*y^3/6831 - 3350449*x*y^2/6831 - 208166*x*y/6831 + 21640*x/253 + 1645*y^8/2277 - 10786*y^7/621 + 337723*y^6/2277 - 3479537*y^5/6831 + 3368432*y^4/6831 + 154961*y^3/759 - 132724*y^2/6831 - 64060*y/2277 + 2)*h1 + (-329*x^2*y^7/1518 + 23137*x^2*y^6/4554 - 20775*x^2*y^5/506 + 274295*x^2*y^4/2277 - 10139*x^2*y^3/414 - 922807*x^2*y^2/4554 - 37453*x^2*y/1518 + 6519*x^2/253 + 329*x*y^7/253 - 23795*x*y^6/759 + 611147*x*y^5/2277 - 2102398*x*y^4/2277 + 184655*x*y^3/207 + 828038*x*y^2/2277 + 4478*x*y/2277 - 38608*x/759 - 329*y^8/1518 + 11075*y^7/2277 - 81919*y^6/2277 + 357667*y^5/4554 + 505921*y^4/4554 - 63128*y^3/207 - 307745*y^2/2277 + 214367*y/4554 + 18292/759)*h2 + (-329*x^2*y^7/1518 + 23137*x^2*y^6/4554 - 20775*x^2*y^5/506 + 274295*x^2*y^4/2277 - 10139*x^2*y^3/414 - 922807*x^2*y^2/4554 - 37453*x^2*y/1518 + 6519*x^2/253 + 329*x*y^8/2277 - 19189*x*y^7/6831 + 90479*x*y^6/6831 + 99260*x*y^5/2277 - 89807*x*y^4/207 + 171087*x*y^3/253 - 18824*x*y^2/2277 + 82373*x*y/6831 - 13274*x/759 - 2303*y^8/4554 + 7945*y^7/621 - 813686*y^6/6831 + 6667531*y^5/13662 - 3681389*y^4/4554 + 279571*y^3/759 + 50011*y^2/621 + 8339*y/594 - 79088/2277)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0011102220 (x y : ℝ) (g0 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : 4*x^3 - 3*x^2*y - 6*x^2 + x*y^2 - 2*x*y + 5*x=0) (g2 : 4*x^3 - 4*x^2*y - 4*x^2 + 2*x*y^2 - 4*x*y + 2*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (n12 : -x^2 + 4*x*y≠0) (_n13 : -y^2 + 4*y≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h1 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g0
  have h3 : x≠0 := by
    intro he
    apply n12
    linear_combination (-x + 4*y)*he
  have h4 : ((x))*(x^2 - 3*x*y/4 - 3*x/2 + y^2/4 - y/2 + 5/4)=0 := by linear_combination (1/4)*g1
  have h2 := (mul_eq_zero.mp h4).resolve_left h3
  have h6 : ((x))*(x^2 - x*y - x + y^2/2 - y + 1/2)=0 := by linear_combination (1/4)*g2
  have h5 := (mul_eq_zero.mp h6).resolve_left h3
  have h7 : (1:ℝ)=0 := by linear_combination (-3*y^3/112 + 29*y^2/336 + 25*y/84 - 29/168)*h1 + (3*x*y^3/56 - x*y^2/3 - 103*x*y/168 + 39*x/28 + 3*y^3/56 - 11*y^2/168 - 5*y/168 + 25/24)*h2 + (-3*x*y^3/112 + 83*x*y^2/336 + 53*x*y/168 - 205*x/168 - 3*y^2/56 - 131*y/336 - 145/336)*h5
  have h8 : (1:ℝ)=0 := by linear_combination (1)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0011122220 (x y : ℝ) (g0 : 4*x^3 - 4*x^2*y - 4*x^2 + 2*x*y^2 - 4*x*y + 2*x=0) (g1 : 4*x^3 - 4*x^2*y - 5*x^2 + 2*x*y^2 - 4*x*y + 6*x=0) (g2 : 4*x^3 - 4*x^2*y - 4*x^2 + 2*x*y^2 - 4*x*y + 2*x=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (n5 : -x^2 + 4*x≠0) (_n6 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n7 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n8 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x - (1:ℝ)≠0) (_n11 : -x^2 + 4*x*y≠0) (n12 : -x^2 + 4*x*y≠0) (_n13 : 4*y - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h2 : x≠0 := by
    intro he
    apply n12
    linear_combination (-x + 4*y)*he
  have h3 : ((x))*(x^2 - x*y - x + y^2/2 - y + 1/2)=0 := by linear_combination (1/4)*g0
  have h1 := (mul_eq_zero.mp h3).resolve_left h2
  have h5 : ((x))*(x^2 - x*y - 5*x/4 + y^2/2 - y + 3/2)=0 := by linear_combination (1/4)*g1
  have h4 := (mul_eq_zero.mp h5).resolve_left h2
  have h7 : ((x))*(x^2 - x*y - x + y^2/2 - y + 1/2)=0 := by linear_combination (1/4)*g2
  have h6 := (mul_eq_zero.mp h7).resolve_left h2
  have h8 : x - (4:ℝ)=0 := by linear_combination (-4)*h4 + (4)*h6
  have h9 : y^2 - 10*y + (25:ℝ)=0 := by linear_combination (8*x - 8*y + 24)*h4 + (-8*x + 8*y - 22)*h6
  have h11 : x - (4:ℝ)≠0 := by
    intro he
    apply n5
    linear_combination (-x)*he
  have h12 : ((x - 4))*(1)=0 := by linear_combination (1)*h8
  have h10 := (mul_eq_zero.mp h12).resolve_left h11
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h10
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h13
  have h15 : (1:ℝ)=0 := by linear_combination (1)*h14
  norm_num at h13



private lemma base_0011201022 (x y : ℝ) (g0 : 2*x^2*y + 2*x*y^2 - 8*x*y=0) (g1 : x^2*y + x*y^2 - 6*x*y - y^3 + 4*y^2=0) (g2 : 2*x^2 + 2*x*y^2 - 10*x*y + 2*y=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -y^2 + 4*y≠0) (_n6 : -x^2 + 4*x≠0) (_n7 : 4*x - (1:ℝ)≠0) (_n8 : -x^2 + 4*x≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : 4*x*y - y^2≠0) (n11 : -y^2 + 4*y≠0) (n12 : -x^2 + 4*x*y≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : 4*y - (1:ℝ)≠0) : False := by
  have h2 : y≠0 := by
    intro he
    apply n11
    linear_combination (4 - y)*he
  have h3 : x≠0 := by
    intro he
    apply n12
    linear_combination (-x + 4*y)*he
  have h4 : ((y) * (x))*(x + y - 4)=0 := by linear_combination (1/2)*g0
  have h1 := (mul_eq_zero.mp h4).resolve_left (mul_ne_zero h2 h3)
  have h6 : ((y))*(x^2 + x*y - 6*x - y^2 + 4*y)=0 := by linear_combination (1)*g1
  have h5 := (mul_eq_zero.mp h6).resolve_left h2
  have h7 : x^2 + x*y^2 - 5*x*y + y=0 := by linear_combination (1/2)*g2
  have h8 : (1:ℝ)=0 := by linear_combination (5*x*y^2/24 - 13*x*y/8 + 15*x/8 - 5*y^3/24 + 17*y^2/12 - 3*y/2 - 1/4)*h1 + (-5*y^2/24 + 17*y/12 - 31/24)*h5 + (5*y/24 - 7/12)*h7
  have h9 : (1:ℝ)=0 := by linear_combination (1)*h8
  have h10 : (1:ℝ)=0 := by linear_combination (1)*h9
  norm_num at h8



private lemma base_0012012210 (x y : ℝ) (g0 : 2*x^2 - 4*x*y - 4*x + 2*y^2 - 2*y + (2:ℝ)=0) (g1 : -2*x^2 + 4*x*y - 3*x - 2*y^2 - 3*y + (5:ℝ)=0) (g2 : 2*x^2 - 4*x*y - 2*x + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (_n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : (3:ℝ)≠0) (_n6 : 4*x - (1:ℝ)≠0) (_n7 : 4*y - (1:ℝ)≠0) (_n8 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n9 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n10 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h1 : x^2 - 2*x*y - 2*x + y^2 - y + (1:ℝ)=0 := by linear_combination (1/2)*g0
  have h2 : x^2 - 2*x*y + 3*x/2 + y^2 + 3*y/2 - 5/(2:ℝ)=0 := by linear_combination (-1/2)*g1
  have h3 : x^2 - 2*x*y - x + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : (1:ℝ)=0 := by linear_combination (-17*x/9 + 5*y/9 + 4/9)*h1 + (-2*x/9 + 2*y/9 - 2/3)*h2 + (19*x/9 - 7*y/9 - 10/9)*h3
  have h5 : (1:ℝ)=0 := by linear_combination (1)*h4
  have h6 : (1:ℝ)=0 := by linear_combination (1)*h5
  have h7 : (1:ℝ)=0 := by linear_combination (1)*h6
  norm_num at h5



private lemma base_0012102201 (x y : ℝ) (g0 : 4*x^3 - 2*x^2*y - 6*x^2 + 2*y^2 - 4*y + (2:ℝ)=0) (g1 : 2*x^2*y + x^2 - 5*x*y + x - 2*y^2 + 4*y - (2:ℝ)=0) (g2 : 2*x^2*y - 6*x*y + 2*y^2 - 4*y + (2:ℝ)=0) (_n0 : x≠0) (_n1 : y≠0) (_n2 : x - (1:ℝ)≠0) (n3 : y - (1:ℝ)≠0) (_n4 : x - y≠0) (_n5 : -x^2 + 4*x≠0) (n6 : -x^2 + 4*x≠0) (_n7 : 4*y - (1:ℝ)≠0) (_n8 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n9 : -y^2 + 4*y≠0) (_n10 : 4*x*y - y^2≠0) (_n11 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n12 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n13 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) (_n14 : -x^2 + 2*x*y + 2*x - y^2 + 2*y - (1:ℝ)≠0) : False := by
  have h1 : x^3 - x^2*y/2 - 3*x^2/2 + y^2/2 - y + 1/(2:ℝ)=0 := by linear_combination (1/4)*g0
  have h2 : x^2*y + x^2/2 - 5*x*y/2 + x/2 - y^2 + 2*y - (1:ℝ)=0 := by linear_combination (1/2)*g1
  have h3 : x^2*y - 3*x*y + y^2 - 2*y + (1:ℝ)=0 := by linear_combination (1/2)*g2
  have h4 : x=0 := by linear_combination (1294336*x*y^5/128207625 + 13739008*x*y^4/128207625 + 7667456*x*y^3/128207625 - 3119552*x*y^2/2513875 - 65068624*x*y/42735875 - 249056*x/580125 - 5177344*y^6/128207625 - 1937408*y^5/9862125 + 23379968*y^4/18315375 + 3261952*y^3/9862125 - 283862272*y^2/128207625 - 25420744*y/9862125 - 24198478/25641525)*h1 + (-2588672*x^2*y^5/128207625 - 27478016*x^2*y^4/128207625 - 15334912*x^2*y^3/128207625 + 6239104*x^2*y^2/2513875 + 130137248*x^2*y/42735875 + 498112*x^2/580125 + 14237696*x*y^5/128207625 + 123904*x*y^4/146523 - 65201408*x*y^3/42735875 - 59737152*x*y^2/8547175 - 548206432*x*y/128207625 - 1328884*x/5128305 - 5177344*y^6/128207625 - 1445888*y^5/6105125 + 139767808*y^4/128207625 + 11421184*y^3/7541625 - 4320704*y^2/1408875 - 69769064*y/42735875 + 36858646/42735875)*h2 + (2588672*x^2*y^5/128207625 + 27478016*x^2*y^4/128207625 + 15334912*x^2*y^3/128207625 - 6239104*x^2*y^2/2513875 - 130137248*x^2*y/42735875 - 498112*x^2/580125 - 7118848*x*y^5/128207625 - 22168064*x*y^4/42735875 + 23585152*x*y^3/128207625 + 731976928*x*y^2/128207625 + 84220808*x*y/18315375 + 67218244*x/128207625 - 2588672*y^6/128207625 - 17770496*y^5/128207625 + 3862528*y^4/8547175 + 11530496*y^3/8547175 - 4926528*y^2/2513875 - 44072356*y/128207625 + 171072133/128207625)*h3
  have h5 : y^2 - 2*y + (1:ℝ)=0 := by linear_combination (-10112*x*y^3/580125 - 132616*x*y^2/580125 - 418618*x*y/580125 - 724*x/2625 + 40448*y^4/580125 + 99296*y^3/193375 - 425168*y^2/580125 - 593638*y/580125 - 81812/116025)*h1 + (20224*x^2*y^3/580125 + 265232*x^2*y^2/580125 + 837236*x^2*y/580125 + 1448*x^2/2625 - 111232*x*y^3/580125 - 225016*x*y^2/116025 - 40602*x*y/14875 + 724*x/23205 + 40448*y^4/580125 + 338336*y^3/580125 - 137392*y^2/580125 - 317026*y/193375 + 11584/193375)*h2 + (-20224*x^2*y^3/580125 - 265232*x^2*y^2/580125 - 837236*x^2*y/580125 - 1448*x^2/2625 + 55616*x*y^3/580125 + 658604*x*y^2/580125 + 94807*x*y/34125 + 80726*x/580125 + 20224*y^4/580125 + 27056*y^3/82875 + 1928*y^2/14875 - 654259*y/580125 + 819407/580125)*h3
  have h7 : x≠0 := by
    intro he
    apply n6
    linear_combination (4 - x)*he
  have h8 : ((x))*(1)=0 := by linear_combination (1)*h4
  have h6 := (mul_eq_zero.mp h8).resolve_left h7
  have h10 : y - (1:ℝ)≠0 := by
    intro he
    apply n3
    linear_combination (1)*he
  have h11 : ((y - 1) * (y - 1))*(1)=0 := by linear_combination (1)*h5
  have h9 := (mul_eq_zero.mp h11).resolve_left (mul_ne_zero h10 h10)
  have h12 : (1:ℝ)=0 := by linear_combination (1)*h6
  have h13 : (1:ℝ)=0 := by linear_combination (1)*h12
  have h14 : (1:ℝ)=0 := by linear_combination (1)*h13
  norm_num at h12


private lemma shape_0011012220 (x y : ℝ) (ha : admissible ![0,0,1,1,0,1,2,2,2,0] x y) : False := by
  apply base_0011012220 x y
  · have hg : gram 1 1 1 x x y x x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x y x y y 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x y y x y y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
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
  · have hn : area 1 y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0011101100 (x y : ℝ) (ha : admissible ![0,0,1,1,1,0,1,1,0,0] x y) : (x^2 - 3*x + 1=0) := by
  apply base_0011101100 x y
  · have hg : gram 1 1 x x 1 x x 1 x 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 x x x 1 1=0 := ha.2.2.2.1
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
  · have hn : area x x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
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
  · have hn : area 1 x 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x 1 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0011101202 (x y : ℝ) (ha : admissible ![0,0,1,1,1,0,1,2,0,2] x y) : False := by
  apply base_0011101202 x y
  · have hg : gram 1 1 x x 1 y x 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 y x x 1 y=0 := ha.2.2.2.1
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
  · have hn : area x x 1≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0011102210 (x y : ℝ) (ha : admissible ![0,0,1,1,1,0,2,2,1,0] x y) : False := by
  apply base_0011102210 x y
  · have hg : gram 1 1 x x 1 y x 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 y x y x 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x y x x y x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
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
  · have hn : area x y x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0011102212 (x y : ℝ) (ha : admissible ![0,0,1,1,1,0,2,2,1,2] x y) : False := by
  apply base_0011102212 x y
  · have hg : gram 1 1 x x 1 y x 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 y x y x y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x y x x y x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
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
  · have hn : area x y x≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y y≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x y≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0011102220 (x y : ℝ) (ha : admissible ![0,0,1,1,1,0,2,2,2,0] x y) : False := by
  apply base_0011102220 x y
  · have hg : gram 1 1 x x 1 y x 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 y x y y 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x y y x y y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
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
  · have hn : area x y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0011122220 (x y : ℝ) (ha : admissible ![0,0,1,1,1,2,2,2,2,0] x y) : False := by
  apply base_0011122220 x y
  · have hg : gram 1 1 x x y y x y y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x y y x y y 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x y y x y y 0=0 := ha.2.2.2.2
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
  · have hn : area 1 x y≠0 := ha.2.1 0 1 3 (by decide) (by decide)
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
  · have hn : area 1 x y≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x x 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y y 1≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring


private lemma shape_0011201022 (x y : ℝ) (ha : admissible ![0,0,1,1,2,0,1,0,2,2] x y) : False := by
  apply base_0011201022 x y
  · have hg : gram 1 1 y x 1 1 x 1 1 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 y x 1 1 x x y y=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 y x x y x x y 0=0 := ha.2.2.2.2
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
  · have hn : area y 1 1≠0 := ha.2.1 1 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y x y≠0 := ha.2.1 1 2 4 (by decide) (by decide)
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


private lemma shape_0012012210 (x y : ℝ) (ha : admissible ![0,0,1,2,0,1,2,2,1,0] x y) : False := by
  apply base_0012012210 x y
  · have hg : gram 1 1 1 x x y x x y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 x x y y y x 1=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 1 y y x y y x 0=0 := ha.2.2.2.2
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
  · have hn : area 1 y y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y x≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y 1≠0 := ha.2.1 0 3 4 (by decide) (by decide)
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


private lemma shape_0012102201 (x y : ℝ) (ha : admissible ![0,0,1,2,1,0,2,2,0,1] x y) : False := by
  apply base_0012102201 x y
  · have hg : gram 1 1 x x 1 y x 1 y 0=0 := ha.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x x 1 y y y 1 x=0 := ha.2.2.2.1
    convert hg using 1 ; unfold gram area ; ring
  · have hg : gram 1 1 x y y 1 y y 1 0=0 := ha.2.2.2.2
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
  · have hn : area 1 y y≠0 := ha.2.1 0 1 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 x y≠0 := ha.2.1 0 2 3 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area 1 y 1≠0 := ha.2.1 0 2 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area x y x≠0 := ha.2.1 0 3 4 (by decide) (by decide)
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
  · have hn : area 1 y x≠0 := ha.2.1 1 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
  · have hn : area y 1 x≠0 := ha.2.1 2 3 4 (by decide) (by decide)
    intro h
    apply hn
    convert h using 1 ; unfold area ; ring
lemma all_used {B : Finset ℝ²} (p : Fin 5≃B) (r : Fin 3≃distanceSet B) (c : Fin 10→Fin 3)
    (h : ∀ k, dist (p (edges5 k).1).1 (p (edges5 k).2).1=(r (c k)).1) (d : Fin 3) :
    ∃ i j : Fin 5, i≠j ∧ c (slot i j)=d := by
  have hh := (r d).2
  obtain ⟨⟨u,v⟩,hm,he⟩ := Finset.mem_image.mp hh
  obtain ⟨hu,hv,hne⟩ := Finset.mem_offDiag.mp hm
  obtain ⟨i,hi⟩ := p.surjective (⟨u,hu⟩:B)
  obtain ⟨j,hj⟩ := p.surjective (⟨v,hv⟩:B)
  have eu : (p i).1=u := congrArg Subtype.val hi
  have ev : (p j).1=v := congrArg Subtype.val hj
  have hij : i≠j := by rintro rfl; exact hne (eu.symm.trans ev)
  refine ⟨i,j,hij,r.injective (Subtype.ext ?_)⟩
  rw [match_edges p r c h i j hij,eu,ev]
  exact he

end Erdos1082Ten

open Erdos1082Ten EuclideanGeometry

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H1_R1.H3 := by
  intro B hn _ _ p r c hc hh
  obtain ⟨s,x,y,_,H,_,_⟩ := given_colors B hn p r c hc
  change colorCode c∈([858,860,861,862,863,879,880,881,882,883,885,886,887,888,889,890,912,913,939,941,942,943,969,970,1062,1064,1070,1071,1072,1073,1075,1076,1079,1100,1106,1124,1125,1126,1127,1129,1130,1152,1153,1155,1157,1158,1159,1185,1212,1213,1395,1396,3048,3050,3075,3195,3206,3234,3236,3237,3399,3437,3801,3961]:List ℕ) at hh
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq|eq
  · have cc : c=![0,0,0,1,0,1,1,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001011210 x y H
  · have cc : c=![0,0,0,1,0,1,1,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001011212 x y H
  · have cc : c=![0,0,0,1,0,1,1,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001011220 x y H
  · have cc : c=![0,0,0,1,0,1,1,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001011221 x y H
  · have cc : c=![0,0,0,1,0,1,1,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001011222 x y H
  · have cc : c=![0,0,0,1,0,1,2,1,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001012120 x y H
  · have cc : c=![0,0,0,1,0,1,2,1,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001012121 x y H
  · have cc : c=![0,0,0,1,0,1,2,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001012122 x y H
  · have cc : c=![0,0,0,1,0,1,2,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001012200 x y H
  · have cc : c=![0,0,0,1,0,1,2,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001012201 x y H
  · have cc : c=![0,0,0,1,0,1,2,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001012210 x y H
  · have cc : c=![0,0,0,1,0,1,2,2,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001012211 x y H
  · have cc : c=![0,0,0,1,0,1,2,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001012212 x y H
  · have cc : c=![0,0,0,1,0,1,2,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001012220 x y H
  · have cc : c=![0,0,0,1,0,1,2,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001012221 x y H
  · have cc : c=![0,0,0,1,0,1,2,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001012222 x y H
  · have cc : c=![0,0,0,1,0,2,0,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001020210 x y H
  · have cc : c=![0,0,0,1,0,2,0,2,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001020211 x y H
  · have cc : c=![0,0,0,1,0,2,1,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001021210 x y H
  · have cc : c=![0,0,0,1,0,2,1,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001021212 x y H
  · have cc : c=![0,0,0,1,0,2,1,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001021220 x y H
  · have cc : c=![0,0,0,1,0,2,1,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001021221 x y H
  · have cc : c=![0,0,0,1,0,2,2,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001022220 x y H
  · have cc : c=![0,0,0,1,0,2,2,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001022221 x y H
  · have cc : c=![0,0,0,1,1,1,0,1,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001110100 x y H
  · have cc : c=![0,0,0,1,1,1,0,1,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001110102 x y H
  · have cc : c=![0,0,0,1,1,1,0,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001110122 x y H
  · have cc : c=![0,0,0,1,1,1,0,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001110200 x y H
  · have cc : c=![0,0,0,1,1,1,0,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001110201 x y H
  · have cc : c=![0,0,0,1,1,1,0,2,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001110202 x y H
  · have cc : c=![0,0,0,1,1,1,0,2,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001110211 x y H
  · have cc : c=![0,0,0,1,1,1,0,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001110212 x y H
  · have cc : c=![0,0,0,1,1,1,0,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001110222 x y H
  · have cc : c=![0,0,0,1,1,1,1,2,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001111202 x y H
  · have cc : c=![0,0,0,1,1,1,1,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001111222 x y H
  · have cc : c=![0,0,0,1,1,1,2,1,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001112122 x y H
  · have cc : c=![0,0,0,1,1,1,2,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001112200 x y H
  · have cc : c=![0,0,0,1,1,1,2,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001112201 x y H
  · have cc : c=![0,0,0,1,1,1,2,2,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001112202 x y H
  · have cc : c=![0,0,0,1,1,1,2,2,1,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001112211 x y H
  · have cc : c=![0,0,0,1,1,1,2,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001112212 x y H
  · have cc : c=![0,0,0,1,1,2,0,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001120200 x y H
  · have cc : c=![0,0,0,1,1,2,0,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001120201 x y H
  · have cc : c=![0,0,0,1,1,2,0,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001120210 x y H
  · have cc : c=![0,0,0,1,1,2,0,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001120212 x y H
  · have cc : c=![0,0,0,1,1,2,0,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001120220 x y H
  · have cc : c=![0,0,0,1,1,2,0,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001120221 x y H
  · have cc : c=![0,0,0,1,1,2,1,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001121220 x y H
  · have cc : c=![0,0,0,1,1,2,2,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001122220 x y H
  · have cc : c=![0,0,0,1,1,2,2,2,2,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001122221 x y H
  · have cc : c=![0,0,0,1,2,2,0,2,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001220200 x y H
  · have cc : c=![0,0,0,1,2,2,0,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0001220201 x y H
  · have cc : c=![0,0,1,1,0,1,1,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0011011220 x y H
  · have cc : c=![0,0,1,1,0,1,1,2,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0011011222 x y H
  · have cc : c=![0,0,1,1,0,1,2,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0011012220 x y H
  · have cc : c=![0,0,1,1,1,0,1,1,0,0] := injective_colorCode (eq.trans (by decide))
    subst c
    have no : ¬ ∃ i j : Fin 5, i≠j ∧ (![0,0,1,1,1,0,1,1,0,0] : Fin 10→Fin 3) (slot i j)=2 := by decide
    exact no (all_used p r _ hc 2)
  · have cc : c=![0,0,1,1,1,0,1,2,0,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0011101202 x y H
  · have cc : c=![0,0,1,1,1,0,2,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0011102210 x y H
  · have cc : c=![0,0,1,1,1,0,2,2,1,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0011102212 x y H
  · have cc : c=![0,0,1,1,1,0,2,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0011102220 x y H
  · have cc : c=![0,0,1,1,1,2,2,2,2,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0011122220 x y H
  · have cc : c=![0,0,1,1,2,0,1,0,2,2] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0011201022 x y H
  · have cc : c=![0,0,1,2,0,1,2,2,1,0] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0012012210 x y H
  · have cc : c=![0,0,1,2,1,0,2,2,0,1] := injective_colorCode (eq.trans (by decide))
    subst c
    exact shape_0012102201 x y H
