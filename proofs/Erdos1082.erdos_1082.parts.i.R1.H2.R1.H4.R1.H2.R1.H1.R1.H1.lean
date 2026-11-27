import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H1_R1

/-!
# The 142 three-color base patterns

Minimize the base-three encoding over permutations of vertices and colors. For a partial assignment whose code is not minimal, a specified pair of permutations already gives a smaller code. The other branches end in one of 142 representatives.
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
private lemma orbit_0000000000 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=0 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000000001 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000000002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000000000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000000000 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000001 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000002 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000000010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000000011 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=4 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000000012 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=5 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000000010 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000011 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000012 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000000002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00000000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000000000 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000001 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000002 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_000000010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000000110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000000111 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=13 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000000112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=14 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000000110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000000120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000000121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000000122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000000012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000000120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000000122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00000001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000000010 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000011 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000012 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_00000002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0000000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00000000 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000001 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000002 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000000100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000001010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001011 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=31 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000001012 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=32 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001010 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001011 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001012 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000001020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000000102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001020 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001021 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001022 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00000010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000000100 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000101 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000102 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0000001100 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=36 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000001101 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=37 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000001102 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=38 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001100 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001101 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001102 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000001110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001111 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=40 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000001112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=41 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000001120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=44 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00000011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000000110 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000111 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000112 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0000001200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=45 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000001201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=46 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000001202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000000120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000001210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001211 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=49 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000001212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=50 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000001220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000001222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=53 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000000122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000001220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000001222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00000012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000000120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000000122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0000001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00000010 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000011 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000012 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_0000002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_000000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000000 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000001 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000002 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_0000010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00000110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000001110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000011110 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=120 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000011111 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=121 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000011112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=122 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000001111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000011110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000011111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000011112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000011120 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=123 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000011121 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=124 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000011122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=125 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000001112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000011120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000011121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000011122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00000111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000001110 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001111 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001112 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_000001120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000001121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000011220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=132 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000011221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=133 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000011222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000001122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000011220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000011221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000011222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00000112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000001120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0000011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00000110 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000111 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000112 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00000120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000001210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000001211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000012120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000012121 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=151 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000012122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000001212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000012120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000012121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000012122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00000121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000001210 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001211 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001212 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_000001220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000012210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=156 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000012211 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=157 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000012212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000001221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000012210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000012211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000012212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000001222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00000122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000001220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000001222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0000012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00000120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00000122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000010 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000011 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000012 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_000002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_00000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=0) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_000000 c h h0 h1 h2 h3 h4 e
  · exact orbit_000001 c h h0 h1 h2 h3 h4 e
  · exact orbit_000002 c h h0 h1 h2 h3 h4 e

private lemma orbit_000010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_0000110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00001110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000011110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000111110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000111111 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=364 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000111112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=365 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000011111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000111110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000111111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000111112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0000111120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000111121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000111122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=368 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000011112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000111120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000111121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000111122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00001111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000011110 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011111 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011112 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_000011120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000011121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000111220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000111221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000111222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=377 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000011122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000111220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000111221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000111222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00001112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000011120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0000111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00001110 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00001111 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00001112 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00001120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000011210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000011211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000112120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000112121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000112122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,4,1,2,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000011212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000112120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000112121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000112122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00001121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000011210 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011211 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011212 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_000011220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0000112210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0000112211 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=400 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0000112212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=401 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000011221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000112210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000112211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0000112212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000011222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![0,2,4,3,1]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00001122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000011220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000011222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0000112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00001120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00001121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00001122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000110 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000111 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000112 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_0000120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0000121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0000122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_000012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000120 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000121 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0000122 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=1) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_000010 c h h0 h1 h2 h3 h4 e
  · exact orbit_000011 c h h0 h1 h2 h3 h4 e
  · exact orbit_000012 c h h0 h1 h2 h3 h4 e

private lemma orbit_00002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) (h4 : c 4=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4] at hh ; omega

private lemma orbit_0000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=0) : colorCode c∈baseCodes := by
  have he : c 4=0 ∨ c 4=1 ∨ c 4=2 := by have hv := (c 4).isLt; omega
  rcases he with e|e|e
  · exact orbit_00000 c h h0 h1 h2 h3 e
  · exact orbit_00001 c h h0 h1 h2 h3 e
  · exact orbit_00002 c h h0 h1 h2 h3 e

private lemma orbit_0001000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_000100100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001001010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001012 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=761 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001010 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001011 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001012 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001001020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001022 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=764 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001020 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001021 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001022 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000100100 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100101 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100102 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001001100 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=765 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001001101 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=766 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001001102 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=767 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001100 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001101 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001102 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001001110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=770 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001001120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=773 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000100110 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100111 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100112 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001001200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=774 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001001201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=775 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001001202 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=776 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001001210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=779 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001001220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001001222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=782 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001001220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001001222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000100120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010010 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010011 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010012 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000100200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000100201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000100202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00010020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000100200 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100201 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100202 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001002100 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=792 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001002101 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=793 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001002102 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=794 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001002100 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001002101 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001002102 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001002110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001002111 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=796 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001002112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=797 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001002110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001002111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001002112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001002120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001002121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001002122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=800 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000100212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001002120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001002121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001002122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000100210 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100211 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000100212 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_00010022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0001002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010020 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010021 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010022 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001000 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001001 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001002 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00010100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000101010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001010110 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=822 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001010111 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=823 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001010112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=824 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001010110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001010111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001010112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001010120 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=825 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001010121 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=826 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001010122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=827 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001010120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001010121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001010122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000101010 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101011 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101012 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_000101020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000101021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001010220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=834 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001010221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=835 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001010222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=836 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001010220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001010221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001010222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000101020 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101021 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101022 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010100 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010101 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010102 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00010110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000101110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001011110 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=849 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001011111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![3,1,4,2,0]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001011112 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=851 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001011110 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011111 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011112 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001011120 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=852 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001011121 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=853 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001011122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=854 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001011120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000101110 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101111 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101112 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001011200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=855 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001011201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,1,3,0,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001011202 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=857 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001011200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001011210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=858 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001011211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001011212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=860 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001011210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001011220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=861 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001011221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=862 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001011222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=863 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001011220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001011222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000101120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010110 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010111 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010112 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00010120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000101210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000101211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001012120 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=879 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012121 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=880 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=881 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001012120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000101210 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101211 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101212 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001012200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=882 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=883 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![2,1,0,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000101220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001012200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001012210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=885 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012211 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=886 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=887 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001012210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001012220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=888 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=889 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001012222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=890 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000101222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001012220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001012222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000101220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000101222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001010 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001011 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001012 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00010200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00010201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000102020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001020210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=912 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001020211 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=913 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001020212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000102021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001020210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001020211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001020212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000102022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00010202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000102020 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000102021 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000102022 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010200 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010201 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010202 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00010210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00010211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000102120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001021210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=939 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001021211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001021212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=941 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000102121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001021210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001021211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001021212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001021220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=942 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001021221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=943 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001021222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,2,4,1,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000102122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001021220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001021221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001021222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000102120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000102121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000102122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010210 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010211 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010212 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00010220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00010221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000102220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000102221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001022220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=969 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001022221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=970 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001022222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,1,4,2,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000102222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001022220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001022221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001022222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00010222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000102220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000102221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000102222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010220 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010221 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00010222 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001020 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001021 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001022 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=0) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_000100 c h h0 h1 h2 h3 h4 e
  · exact orbit_000101 c h h0 h1 h2 h3 h4 e
  · exact orbit_000102 c h h0 h1 h2 h3 h4 e

private lemma orbit_000110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_00011100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0001110100 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1062 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001110101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![3,1,2,4,0]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001110102 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1064 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001110100 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110101 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110102 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000111011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![2,1,3,4,0]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001110120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001110121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001110122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1070 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001110120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000111010 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111011 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111012 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001110200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1071 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001110201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1072 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001110202 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1073 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001110200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001110210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001110211 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1075 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001110212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1076 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001110210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001110220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001110221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001110222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1079 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001110220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001110222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000111020 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111021 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111022 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00011100 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011101 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011102 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00011110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00011111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,4,0]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0001111200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![1,4,2,3,0]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001111201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![1,3,4,2,0]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001111202 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1100 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001111200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001111201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001111202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000111121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,4,3,0]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001111220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001111221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001111222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1106 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001111220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001111221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001111222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000111120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00011110 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011111 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011112 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00011120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000111210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000111211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001112120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001112121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001112122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1124 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001112120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000111210 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111211 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111212 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001112200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1125 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001112201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1126 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001112202 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1127 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001112200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001112210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001112211 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1129 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001112212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1130 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000111221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001112210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001112220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001112221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001112222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![4,1,2,3,0]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000111222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001112220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001112222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000111220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000111222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00011120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001110 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001111 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001112 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00011200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00011201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0001120200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1152 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001120201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1153 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001120202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,4,1,2,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000112020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001120200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001120201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001120202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001120210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1155 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001120211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,2,3,1]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001120212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=1157 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_000112021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001120210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001120211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001120212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001120220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1158 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001120221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1159 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001120222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,2,4,1,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000112022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001120220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001120221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001120222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000112020 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000112021 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000112022 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00011200 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011201 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011202 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00011210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00011211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000112120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001121210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001121211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001121212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![4,1,2,0,3]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000112121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001121210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001121211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001121212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001121220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1185 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001121221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,1,3,0,2]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001121222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,2,4,1,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000112122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001121220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001121221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001121222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000112120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000112121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000112122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00011210 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011211 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011212 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00011220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00011221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000112220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_000112221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001122220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1212 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001122221 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1213 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001122222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,1,4,2,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000112222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001122220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001122221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001122222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00011222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000112220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000112221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000112222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00011220 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011221 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00011222 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_000112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001120 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001121 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001122 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=1) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_000110 c h h0 h1 h2 h3 h4 e
  · exact orbit_000111 c h h0 h1 h2 h3 h4 e
  · exact orbit_000112 c h h0 h1 h2 h3 h4 e

private lemma orbit_000120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_000121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_00012200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00012201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0001220200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=1395 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001220201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=1396 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0001220202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,1,2,4,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000122020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001220200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001220201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001220202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0001220210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001220211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,2,3,1]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001220212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,1,2,4,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000122021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001220210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001220211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001220212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000122022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![2,1,3,4,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00012202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000122020 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000122021 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000122022 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00012200 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00012201 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00012202 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00012210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00012211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_000122120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0001221210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001221211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0001221212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,1,2,4,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_000122121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001221210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001221211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0001221212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_000122122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![2,1,3,4,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00012212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_000122120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000122121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_000122122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0001221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00012210 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00012211 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00012212 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_0001222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,4,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_000122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0001220 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001221 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0001222 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) (h4 : c 4=2) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_000120 c h h0 h1 h2 h3 h4 e
  · exact orbit_000121 c h h0 h1 h2 h3 h4 e
  · exact orbit_000122 c h h0 h1 h2 h3 h4 e

private lemma orbit_0001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=1) : colorCode c∈baseCodes := by
  have he : c 4=0 ∨ c 4=1 ∨ c 4=2 := by have hv := (c 4).isLt; omega
  rcases he with e|e|e
  · exact orbit_00010 c h h0 h1 h2 h3 e
  · exact orbit_00011 c h h0 h1 h2 h3 e
  · exact orbit_00012 c h h0 h1 h2 h3 e

private lemma orbit_0002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) (h3 : c 3=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3] at hh ; omega

private lemma orbit_000 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=0) : colorCode c∈baseCodes := by
  have he : c 3=0 ∨ c 3=1 ∨ c 3=2 := by have hv := (c 3).isLt; omega
  rcases he with e|e|e
  · exact orbit_0000 c h h0 h1 h2 e
  · exact orbit_0001 c h h0 h1 h2 e
  · exact orbit_0002 c h h0 h1 h2 e

private lemma orbit_0010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3] at hh ; omega

private lemma orbit_001100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_0011010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00110110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00110111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![3,0,1,2,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_001101120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001101121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011011220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3048 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011011221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011011222 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3050 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001101122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011011220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011011221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011011222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00110112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001101120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001101121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001101122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00110110 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00110111 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00110112 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00110120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00110121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![3,0,1,2,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_001101220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011012210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3072 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011012211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011012212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3074 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001101221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011012210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011012211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011012212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0011012220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3075 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011012221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011012222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![2,1,0,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001101222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011012220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011012221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011012222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00110122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001101220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001101221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001101222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00110120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00110121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00110122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011010 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011011 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011012 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_0011020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0011021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00110220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00110221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00110222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0011022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00110220 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00110221 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00110222 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011020 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011021 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011022 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=0) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_001100 c h h0 h1 h2 h3 h4 e
  · exact orbit_001101 c h h0 h1 h2 h3 h4 e
  · exact orbit_001102 c h h0 h1 h2 h3 h4 e

private lemma orbit_0011100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_001110100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001110101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,4,0,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011101020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101022 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3194 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001110102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011101020 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101021 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101022 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001110100 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110101 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110102 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011101100 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3195 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011101101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101102 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3197 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001110110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011101100 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101101 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101102 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_001110111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,4,0,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011101120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101122 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3203 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001110112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011101120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001110110 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110111 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110112 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011101200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,4,3,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101202 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3206 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001110120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011101200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_001110121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,4,0,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011101220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011101222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![4,2,3,0,1]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001110122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011101220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011101222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001110120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00111010 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111011 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111012 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001110200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001110201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011102020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![3,1,2,0,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011102021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011102022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![4,1,2,0,3]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001110202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011102020 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102021 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102022 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001110200 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110201 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110202 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_001110210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001110211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![2,1,3,0,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011102120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,2,1]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011102121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011102122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![4,1,2,0,3]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001110212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011102120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001110210 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110211 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110212 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011102200 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3231 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011102201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011102202 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3233 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001110220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011102200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0011102210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3234 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011102211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011102212 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3236 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001110221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011102210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0011102220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3237 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011102221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011102222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![4,1,2,0,3]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001110222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011102220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011102222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001110220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001110222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00111020 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111021 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111022 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011100 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011101 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011102 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_0011110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0011111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,0,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00111120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00111121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![3,0,1,2,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_001111220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011112210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011112211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011112212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,2,4,1,0]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001111221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011112210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011112211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011112212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0011112220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011112221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011112222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,2,4,0,1]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001111222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011112220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011112221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011112222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001111220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001111221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001111222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00111120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011110 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011111 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011112 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_0011120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0011121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00111220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00111221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_001112220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001112221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011122220 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3399 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0011122221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011122222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,1,2,0,4]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001112222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011122220 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011122221 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011122222 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00111222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001112220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001112221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001112222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00111220 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111221 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00111222 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011120 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011121 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011122 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=1) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_001110 c h h0 h1 h2 h3 h4 e
  · exact orbit_001111 c h h0 h1 h2 h3 h4 e
  · exact orbit_001112 c h h0 h1 h2 h3 h4 e

private lemma orbit_0011200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_001120100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001120101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,4,3,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011201020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011201021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011201022 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3437 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001120102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011201020 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011201021 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011201022 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00112010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001120100 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120101 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120102 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011201100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011201101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011201102 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have e : colorCode c=3440 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_001120110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011201100 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011201101 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011201102 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_001120111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,2,1]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0011201120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011201121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0011201122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![4,2,3,0,1]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001120112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011201120 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011201121 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0011201122 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_00112011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001120110 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120111 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120112 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_001120120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,4,3,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001120121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,4,3,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001120122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![2,1,3,0,4]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00112012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001120120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0011201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00112010 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00112011 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00112012 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001120200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001120201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001120202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![1,2,4,0,3]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00112020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001120200 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120201 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001120202 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_00112021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,2,1]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00112022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0011202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00112020 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00112021 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00112022 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011200 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011201 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011202 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_001121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have hh := h (![0,3,4,1,2]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_0011220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0011221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0011222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,0,4]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_001122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0011220 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011221 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0011222 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) (h4 : c 4=2) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_001120 c h h0 h1 h2 h3 h4 e
  · exact orbit_001121 c h h0 h1 h2 h3 h4 e
  · exact orbit_001122 c h h0 h1 h2 h3 h4 e

private lemma orbit_0011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=1) : colorCode c∈baseCodes := by
  have he : c 4=0 ∨ c 4=1 ∨ c 4=2 := by have hv := (c 4).isLt; omega
  rcases he with e|e|e
  · exact orbit_00110 c h h0 h1 h2 h3 e
  · exact orbit_00111 c h h0 h1 h2 h3 e
  · exact orbit_00112 c h h0 h1 h2 h3 e

private lemma orbit_001200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5] at hh ; omega

private lemma orbit_0012010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0012011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00120120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00120121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![3,0,1,2,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_001201220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_0012012210 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have e : colorCode c=3801 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0012012211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![3,0,1,2,4]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012012212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001201221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012012210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012012211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012012212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_001201222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00120122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001201220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001201221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001201222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0012012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00120120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00120121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00120122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012010 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012011 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012012 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_0012020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00120210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00120211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00120212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0012021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00120210 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00120211 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00120212 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_0012022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_001202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012020 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012021 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012022 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=0) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_001200 c h h0 h1 h2 h3 h4 e
  · exact orbit_001201 c h h0 h1 h2 h3 h4 e
  · exact orbit_001202 c h h0 h1 h2 h3 h4 e

private lemma orbit_0012100 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0012101 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_001210200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001210201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001210202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00121020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001210200 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001210201 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001210202 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_001210210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![2,0,4,1,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001210211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![2,1,3,0,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001210212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00121021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001210210 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001210211 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001210212 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0012102200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![2,4,0,3,1]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012102201 (c : Fin 10→Fin 3) (_h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have e : colorCode c=3961 := by simp [colorCode,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  rw [e]
  decide

private lemma orbit_0012102202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,4,2,1,0]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001210220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012102200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012102201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012102202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_0012102210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012102211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![2,4,1,3,0]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012102212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![3,4,2,0,1]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001210221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012102210 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012102211 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012102212 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_001210222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![4,0,1,2,3]) (![1,2,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00121022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001210220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001210221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001210222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0012102 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00121020 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121021 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121022 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=0) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012100 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012101 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012102 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_0012110 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,4,2,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_0012111 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,0,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6] at hh ; omega

private lemma orbit_00121120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00121121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,0,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0012112200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![2,4,0,3,1]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012112201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![1,3,2,4,0]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012112202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![1,3,2,4,0]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001211220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012112200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012112201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012112202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_001211221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,4,0]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001211222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![1,2,3,4,0]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00121122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001211220 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001211221 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001211222 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0012112 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00121120 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121121 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121122 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=1) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012110 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012111 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012112 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00121200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00121201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0012120200 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=0) : colorCode c∈baseCodes := by
  have hh := h (![1,0,4,3,2]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012120201 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=1) : colorCode c∈baseCodes := by
  have hh := h (![3,0,4,1,2]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_0012120202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) (h9 : c 9=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,4,3,2]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9] at hh 

private lemma orbit_001212020 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have he : c 9=0 ∨ c 9=1 ∨ c 9=2 := by have hv := (c 9).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012120200 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012120201 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e
  · exact orbit_0012120202 c h h0 h1 h2 h3 h4 h5 h6 h7 h8 e

private lemma orbit_001212021 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![2,1,4,0,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001212022 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![1,0,4,3,2]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00121202 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001212020 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001212021 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001212022 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0012120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=0) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00121200 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121201 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121202 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00121210 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00121211 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_001212120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001212121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=1) : colorCode c∈baseCodes := by
  have hh := h (![1,2,4,0,3]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_001212122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) (h8 : c 8=2) : colorCode c∈baseCodes := by
  have hh := h (![1,2,4,3,0]) (![2,0,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hh ; omega

private lemma orbit_00121212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have he : c 8=0 ∨ c 8=1 ∨ c 8=2 := by have hv := (c 8).isLt; omega
  rcases he with e|e|e
  · exact orbit_001212120 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001212121 c h h0 h1 h2 h3 h4 h5 h6 h7 e
  · exact orbit_001212122 c h h0 h1 h2 h3 h4 h5 h6 h7 e

private lemma orbit_0012121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=1) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00121210 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121211 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121212 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_00121220 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=0) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00121221 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_00121222 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) (h7 : c 7=2) : colorCode c∈baseCodes := by
  have hh := h (![3,1,2,0,4]) (![2,1,0]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4,h5,h6,h7] at hh ; omega

private lemma orbit_0012122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) (h6 : c 6=2) : colorCode c∈baseCodes := by
  have he : c 7=0 ∨ c 7=1 ∨ c 7=2 := by have hv := (c 7).isLt; omega
  rcases he with e|e|e
  · exact orbit_00121220 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121221 c h h0 h1 h2 h3 h4 h5 h6 e
  · exact orbit_00121222 c h h0 h1 h2 h3 h4 h5 h6 e

private lemma orbit_001212 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) (h5 : c 5=2) : colorCode c∈baseCodes := by
  have he : c 6=0 ∨ c 6=1 ∨ c 6=2 := by have hv := (c 6).isLt; omega
  rcases he with e|e|e
  · exact orbit_0012120 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012121 c h h0 h1 h2 h3 h4 h5 e
  · exact orbit_0012122 c h h0 h1 h2 h3 h4 h5 e

private lemma orbit_00121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=1) : colorCode c∈baseCodes := by
  have he : c 5=0 ∨ c 5=1 ∨ c 5=2 := by have hv := (c 5).isLt; omega
  rcases he with e|e|e
  · exact orbit_001210 c h h0 h1 h2 h3 h4 e
  · exact orbit_001211 c h h0 h1 h2 h3 h4 e
  · exact orbit_001212 c h h0 h1 h2 h3 h4 e

private lemma orbit_00122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) (h4 : c 4=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3,h4] at hh ; omega

private lemma orbit_0012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) (h3 : c 3=2) : colorCode c∈baseCodes := by
  have he : c 4=0 ∨ c 4=1 ∨ c 4=2 := by have hv := (c 4).isLt; omega
  rcases he with e|e|e
  · exact orbit_00120 c h h0 h1 h2 h3 e
  · exact orbit_00121 c h h0 h1 h2 h3 e
  · exact orbit_00122 c h h0 h1 h2 h3 e

private lemma orbit_001 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=1) : colorCode c∈baseCodes := by
  have he : c 3=0 ∨ c 3=1 ∨ c 3=2 := by have hv := (c 3).isLt; omega
  rcases he with e|e|e
  · exact orbit_0010 c h h0 h1 h2 e
  · exact orbit_0011 c h h0 h1 h2 e
  · exact orbit_0012 c h h0 h1 h2 e

private lemma orbit_002 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) (h2 : c 2=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2] at hh ; omega

private lemma orbit_00 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=0) : colorCode c∈baseCodes := by
  have he : c 2=0 ∨ c 2=1 ∨ c 2=2 := by have hv := (c 2).isLt; omega
  rcases he with e|e|e
  · exact orbit_000 c h h0 h1 e
  · exact orbit_001 c h h0 h1 e
  · exact orbit_002 c h h0 h1 e

private lemma orbit_010 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=1) (h2 : c 2=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2] at hh ; omega

private lemma orbit_011 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=1) (h2 : c 2=1) : colorCode c∈baseCodes := by
  have hh := h (![0,2,1,3,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2] at hh ; omega

private lemma orbit_0120 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=1) (h2 : c 2=2) (h3 : c 3=0) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3] at hh ; omega

private lemma orbit_0121 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=1) (h2 : c 2=2) (h3 : c 3=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,4,3]) (![0,1,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3] at hh ; omega

private lemma orbit_0122 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=1) (h2 : c 2=2) (h3 : c 3=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,3,2,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1,h2,h3] at hh ; omega

private lemma orbit_012 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=1) (h2 : c 2=2) : colorCode c∈baseCodes := by
  have he : c 3=0 ∨ c 3=1 ∨ c 3=2 := by have hv := (c 3).isLt; omega
  rcases he with e|e|e
  · exact orbit_0120 c h h0 h1 h2 e
  · exact orbit_0121 c h h0 h1 h2 e
  · exact orbit_0122 c h h0 h1 h2 e

private lemma orbit_01 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=1) : colorCode c∈baseCodes := by
  have he : c 2=0 ∨ c 2=1 ∨ c 2=2 := by have hv := (c 2).isLt; omega
  rcases he with e|e|e
  · exact orbit_010 c h h0 h1 e
  · exact orbit_011 c h h0 h1 e
  · exact orbit_012 c h h0 h1 e

private lemma orbit_02 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) (h1 : c 1=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0,h1] at hh ; omega

private lemma orbit_0 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=0) : colorCode c∈baseCodes := by
  have he : c 1=0 ∨ c 1=1 ∨ c 1=2 := by have hv := (c 1).isLt; omega
  rcases he with e|e|e
  · exact orbit_00 c h h0 e
  · exact orbit_01 c h h0 e
  · exact orbit_02 c h h0 e

private lemma orbit_1 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=1) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![1,0,2]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0] at hh ; omega

private lemma orbit_2 (c : Fin 10→Fin 3) (h : minimalColor c) (h0 : c 0=2) : colorCode c∈baseCodes := by
  have hh := h (![0,1,2,3,4]) (![0,2,1]) (by decide) (by decide)
  simp [colorCode,permColors,slot,h0] at hh ; omega

private lemma orbit_empty (c : Fin 10→Fin 3) (h : minimalColor c)  : colorCode c∈baseCodes := by
  have he : c 0=0 ∨ c 0=1 ∨ c 0=2 := by have hv := (c 0).isLt; omega
  rcases he with e|e|e
  · exact orbit_0 c h  e
  · exact orbit_1 c h  e
  · exact orbit_2 c h  e


end Erdos1082Ten

open Erdos1082Ten EuclideanGeometry

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H1_R1.H1 := by
  classical
  intro B _ hB hD
  have hg (x : ℝ²) (hx : x∈B) (y : ℝ²) (hy : y∈B) (hne : x≠y) : dist x y∈distanceSet B :=
    OMA.R_Erdos1082_erdos_1082_parts_i_R1.dist_mem hx hy hne
  obtain ⟨c,⟨p,r,hc⟩,hm⟩ := minimal_realization B (distanceSet B) hB hD hg
  refine ⟨p,r,c,unmatch_edges p r c hc,?_⟩
  have hh := orbit_empty c hm
  have same : baseCodes.toFinset=([3440,3197,3233,3074,835,3072,3203,157,123,401,824,834,853,3194,3231,0,1,4,5,13,14,31,32,36,37,38,40,41,44,45,46,49,50,53,120,121,122,124,125,132,133,151,156,364,365,368,377,400,761,764,765,766,767,770,773,774,775,776,779,782,792,793,794,796,797,800,822,823,825,826,827,836,849,851,852,854,855,857,858,860,861,862,863,879,880,881,882,883,885,886,887,888,889,890,912,913,939,941,942,943,969,970,1062,1064,1070,1071,1072,1073,1075,1076,1079,1100,1106,1124,1125,1126,1127,1129,1130,1152,1153,1155,1157,1158,1159,1185,1212,1213,1395,1396,3048,3050,3075,3195,3206,3234,3236,3237,3399,3437,3801,3961]:List ℕ).toFinset := by set_option maxRecDepth 12000 in decide
  exact List.mem_toFinset.mp (same ▸ List.mem_toFinset.mpr hh)
