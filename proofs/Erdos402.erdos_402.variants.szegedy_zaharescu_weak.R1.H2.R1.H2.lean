import OMAReductions.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1_H2_R1
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-! Normalized divisor collisions for complementary factors. Each collision forces close factors at m or p−m. Six elementary boxes enumerate the feasible factor triples in a window of width O(n^(3/4)); the divisor count absorbs their multiplicity. All estimates and their Lean proofs are written for this reduction. -/

namespace OMA.FactorCount402
open Finset

private lemma component_ratio {u v a b n : ℕ} (up : 0<u) (vp : 0<v)
    (uv : u.Coprime v) (ab : a.Coprime b) (support : u∣a*b)
    (bound : a*u/(a*u).gcd (b*v) ≤ n) : a*(u.gcd a) ≤ n*(v.gcd a) := by
  have first : (a*u).gcd b ∣ u.gcd b := by
    have h : b.gcd (a*u) ∣ b.gcd a*b.gcd u := gcd_mul_dvd_mul_gcd b a u
    simpa only [Nat.gcd_comm b a,ab.gcd_eq_one,one_mul,Nat.gcd_comm b (a*u),Nat.gcd_comm b u] using h
  have second : (a*u).gcd v ∣ v.gcd a := by
    have h : v.gcd (a*u) ∣ v.gcd a*v.gcd u := gcd_mul_dvd_mul_gcd v a u
    simpa only [Nat.gcd_comm v u,uv.gcd_eq_one,mul_one,Nat.gcd_comm v (a*u)] using h
  have dg := (show (a*u).gcd (b*v) ∣ (a*u).gcd b*(a*u).gcd v from gcd_mul_dvd_mul_gcd _ _ _).trans
    (Nat.mul_dvd_mul first second)
  have split := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime ab).mpr support
  have ubp := Nat.gcd_pos_of_pos_left b up
  refine Nat.le_of_mul_le_mul_right ?_ ubp
  calc
    a*u.gcd a*u.gcd b = a*u := by rw [mul_assoc,split]
    _ = (a*u/(a*u).gcd (b*v))*(a*u).gcd (b*v) := (Nat.div_mul_cancel (Nat.gcd_dvd_left ..)).symm
    _ ≤ n*(u.gcd b*v.gcd a) := Nat.mul_le_mul bound (Nat.le_of_dvd
      (Nat.mul_pos ubp (Nat.gcd_pos_of_pos_left _ vp)) dg)
    _ = _ := by ring

/-- A feasible normalized collision gives two distinct close factors on one side.
This leaves only an ordinary count of integers with near-equal factors. -/
theorem near_factors {u v a b n : ℕ} (up : 0<u) (lt : u<v) (uv : u.Coprime v)
    (ab : a.Coprime b) (support : u*v∣a*b)
    (h₁ : a*u/(a*u).gcd (b*v)≤n) (h₂ : a*v/(a*v).gcd (b*u)≤n)
    (h₃ : b*u/(b*u).gcd (a*v)≤n) (h₄ : b*v/(b*v).gcd (a*u)≤n) :
    ∃ w : ℕ, (w=a ∨ w=b) ∧ ∃ x y : ℕ, 0<x ∧ x<y ∧ x*y∣w ∧ w*y≤n*x := by
  have vp := up.trans lt
  have ua := (dvd_mul_right u v).trans support
  have va := (dvd_mul_left v u).trans support
  have ub : u∣b*a := Nat.mul_comm a b ▸ ua
  have vb : v∣b*a := Nat.mul_comm a b ▸ va
  have front := component_ratio up vp uv ab ua h₁
  have front' := component_ratio vp up uv.symm ab va h₂
  have back := component_ratio up vp uv ab.symm ub h₃
  have back' := component_ratio vp up uv.symm ab.symm vb h₄
  have pick (w : ℕ) (ne : u.gcd w ≠ v.gcd w)
      (one : w*u.gcd w≤n*v.gcd w) (two : w*v.gcd w≤n*u.gcd w) :
      ∃ x y : ℕ, 0<x ∧ x<y ∧ x*y∣w ∧ w*y≤n*x := by
    have cop : (u.gcd w).Coprime (v.gcd w) := uv.of_dvd (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_left ..)
    have dv := cop.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right u w) (Nat.gcd_dvd_right v w)
    rcases lt_or_gt_of_ne ne with le|ge
    · exact ⟨_,_,Nat.gcd_pos_of_pos_left _ up,le,dv,two⟩
    · exact ⟨_,_,Nat.gcd_pos_of_pos_left _ vp,ge,Nat.mul_comm .. ▸ dv,one⟩
  by_cases ne : u.gcd a ≠ v.gcd a
  · exact ⟨a,Or.inl rfl,pick a ne front front'⟩
  · have diff : u.gcd b ≠ v.gcd b := by
      intro eq
      have one := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime ab).mpr ua
      have two := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime ab).mpr va
      rw [not_not.mp ne,eq,two] at one
      omega
    exact ⟨b,Or.inr rfl,pick b diff back back'⟩

private lemma exponential_majorant (k : ℕ) :
    ∃ C : ℕ, 0<C ∧ ∀ e : ℕ, (e+1)^k ≤ C*2^e := by
  have lim := tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1:ℝ)<2)
  obtain ⟨N,tail⟩ := Filter.eventually_atTop.mp
    (lim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)))
  refine ⟨max 2 ((N+1)^k),by positivity,?_⟩
  intro e
  by_cases early : e<N
  · calc
      _ ≤ (N+1)^k := Nat.pow_le_pow_left (by omega) _
      _ ≤ max 2 ((N+1)^k) := le_max_right ..
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by positivity)
  · have frac := tail (e+1) (by omega)
    change ((e+1:ℕ):ℝ)^k/(2:ℝ)^(e+1)<1 at frac
    have small : (e+1)^k ≤ (2:ℕ)^(e+1) := by
      exact_mod_cast ((div_lt_one (by positivity)).mp frac).le
    rw [pow_succ,mul_comm] at small
    exact small.trans (Nat.mul_le_mul_right _ (le_max_left ..))

/-- Elementary divisor bound: any fixed power of the divisor count grows at most
linearly. Splitting primes at 2^k pays a constant only for a fixed finite set. -/
theorem divisor_subpower (k : ℕ) : ∃ C : ℕ, 0<C ∧ ∀ t : ℕ, 0<t →
    t.divisors.card^k ≤ C*t := by
  obtain ⟨B,bp,exp⟩ := exponential_majorant k
  refine ⟨B^(2^k),pow_pos bp _,?_⟩
  intro t tp
  have fac (p : ℕ) (hp:p∈t.primeFactors) : (t.factorization p+1)^k ≤
      (if p<2^k then B else 1)*p^(t.factorization p) := by
    let e := t.factorization p
    have pp := (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with small
    · exact (exp e).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left pp e))
    · rw [one_mul]
      calc
        (e+1)^k ≤ (2^e)^k := Nat.pow_le_pow_left (show e<2^e from Nat.lt_two_pow_self) _
        _ = (2^k)^e := by rw [←pow_mul,←pow_mul,Nat.mul_comm e k]
        _ ≤ p^e := Nat.pow_le_pow_left (by omega) _
  calc
    _ = ∏ p ∈ t.primeFactors, (t.factorization p+1)^k := by
      rw [Nat.card_divisors tp.ne',prod_pow]
    _ ≤ ∏ p ∈ t.primeFactors, ((if p<2^k then B else 1)*p^(t.factorization p)) :=
      prod_le_prod' fac
    _ = B^(t.primeFactors.filter (·<2^k)).card*t := by
      rw [prod_mul_distrib,←Nat.prod_primeFactors_pow_factorization tp.ne']
      congr 1
      rw [←prod_const]
      exact (prod_filter _ _).symm
    _ ≤ _ := by
      apply Nat.mul_le_mul_right t
      apply Nat.pow_le_pow_right bp
      exact (card_le_card (t:=range (2^k)) (fun p hp => mem_range.mpr (mem_filter.mp hp).2)).trans_eq
        (card_range _)

end OMA.FactorCount402
namespace OMA.NearFactors402
open Finset

private lemma image_range {α : Type*} (s : Finset α) (f : α→ℕ) (D : ℕ)
    (diam : ∀ a∈s, ∀ b∈s, f a ≤ f b + D) : (s.image f).card ≤ D+1 := by
  by_cases ne : (s.image f).Nonempty
  · let l := (s.image f).min' ne
    obtain ⟨a,ha,ea⟩ := mem_image.mp (min'_mem (s.image f) ne)
    have sub : s.image f ⊆ Icc l (l+D) := by
      intro x hx
      refine mem_Icc.mpr ⟨min'_le _ x hx,?_⟩
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hx
      change f b ≤ (s.image f).min' ne+D
      rw [←ea]
      exact diam b hb a ha
    exact (card_le_card sub).trans (by simp [Nat.card_Icc]; omega)
  · simp [not_nonempty_iff_eq_empty.mp ne]

private lemma box {α : Type*} (s : Finset α) (f g h : α→ℕ) (X Y Z : ℕ)
    (dx : ∀ a∈s, ∀ b∈s, f a ≤ f b+X)
    (dy : ∀ a∈s, ∀ b∈s, f a=f b → g a ≤ g b+Y)
    (dz : ∀ a∈s, ∀ b∈s, f a=f b → g a=g b → h a ≤ h b+Z)
    (inj : ∀ a∈s,∀ b∈s,f a=f b → g a=g b → h a=h b → a=b) :
    s.card ≤ (X+1)*(Y+1)*(Z+1) := by
  classical
  have fib (x : ℕ) : (s.filter (f · = x)).card ≤ (Z+1)*(Y+1) := by
    let T := s.filter (f · = x)
    have gt : (T.image g).card ≤ Y+1 := image_range T g Y fun a ha b hb =>
      dy a (mem_filter.mp ha).1 b (mem_filter.mp hb).1
        ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
    have last (y : ℕ) : (T.filter (g · = y)).card ≤ Z+1 := by
      let V := T.filter (g · = y)
      have data (a) (ha:a∈V) : a∈s ∧ f a=x ∧ g a=y := by
        have ⟨u,v⟩ := mem_filter.mp ha
        exact ⟨(mem_filter.mp u).1,(mem_filter.mp u).2,v⟩
      have hi : Set.InjOn h (V:Set α) := by
        intro a ha b hb eq
        have da := data a ha
        have db := data b hb
        exact inj a da.1 b db.1 (da.2.1.trans db.2.1.symm) (da.2.2.trans db.2.2.symm) eq
      change V.card≤Z+1
      rw [←card_image_of_injOn hi]
      apply image_range
      intro a ha b hb
      have da := data a ha
      have db := data b hb
      exact dz a da.1 b db.1 (da.2.1.trans db.2.1.symm) (da.2.2.trans db.2.2.symm)
    exact (card_le_mul_card_image (f:=g) T (Z+1) (fun y _ => last y)).trans (Nat.mul_le_mul_left _ gt)
  calc
    _ ≤ ((Z+1)*(Y+1))*(s.image f).card := card_le_mul_card_image s _ (fun x _ => fib x)
    _ ≤ ((Z+1)*(Y+1))*(X+1) := Nat.mul_le_mul_left _ (image_range s f X dx)
    _ = _ := by ring

private lemma geom {w n W q x h : ℕ} (xp : 0<x)
    (lo : n≤w+W) (hi : w≤n) (fac : w=q*x*(x+h)) (close : w*(x+h)≤n*x) :
    q*x^2≤n ∧ n≤q*x^2+2*W ∧ q*x*h≤W ∧ w*h≤W*x := by
  have hlow := Nat.mul_le_mul_right x lo
  have hh : w*h≤W*x := by nlinarith
  have qh : q*x*h≤W := by
    apply Nat.le_of_mul_le_mul_right _ xp
    calc
      q*x*h*x ≤ q*x*(x+h)*h := by
        rw [mul_right_comm (q*x) h x]
        gcongr
        omega
      _ ≤ W*x := fac ▸ hh
  have eq : w=q*x^2+q*x*h := by rw [fac]; ring
  exact ⟨by omega,by omega,qh,hh⟩

private lemma small_box (s : Finset (ℕ×ℕ×ℕ)) {n W X Y Z A D : ℕ}
    (np : 0<n) (ap : 0<A) (wide : 2*W≤n)
    (gaps : 2*W*X≤n*Y) (scales : W*D^2≤A^2*Z)
    (pr : ∀ t∈s, let x:=t.2.1; let h:=t.2.2; let w:=t.1*x*(x+h);
      0<x ∧ x≤X ∧ A≤D*x ∧ w≤n ∧ n≤w+W ∧ w*h≤W*x) :
    s.card≤(X+1)*(Y+1)*(Z+1) := by
  apply box s (·.2.1) (·.2.2) (·.1)
  · intro a ha b _
    have := (pr a ha).2.1
    omega
  · rintro ⟨q,x,h⟩ ha b _ _
    obtain ⟨_,xu,_,_,lo,hh⟩ := pr _ ha
    dsimp at xu lo hh
    have lb : n≤2*(q*x*(x+h)) := by omega
    have mul_bound : n*h≤n*Y := by
      calc
        n*h ≤ (2*(q*x*(x+h)))*h := Nat.mul_le_mul_right _ lb
        _ = 2*(q*x*(x+h)*h) := by ring
        _ ≤ 2*(W*x) := Nat.mul_le_mul_left _ hh
        _ ≤ 2*W*X := by rw [←mul_assoc]; gcongr
        _ ≤ _ := gaps
    have hsmall := Nat.le_of_mul_le_mul_left mul_bound np
    change h≤_+Y
    omega
  · rintro ⟨q,x,h⟩ ha ⟨Q,y,j⟩ hb eq₁ eq₂
    change x=y at eq₁
    change h=j at eq₂
    subst y j
    obtain ⟨_,_,lower,hi,_,_⟩ := pr _ ha
    obtain ⟨_,_,_,_,lo,_⟩ := pr _ hb
    dsimp at lower hi lo
    change q≤Q+Z
    by_contra! big
    have qq : Q+(Z+1)≤q := by omega
    have add := Nat.mul_le_mul_right (x*(x+h)) qq
    have cap : (Z+1)*x^2 ≤ W := by nlinarith [Nat.zero_le ((Z+1)*x*h)]
    have left := Nat.mul_le_mul_left (Z+1) (Nat.pow_le_pow_left lower 2)
    have right := Nat.mul_le_mul_right (D^2) cap
    have contra : (Z+1)*A^2≤A^2*Z := by
      calc
        _ ≤ (Z+1)*(D*x)^2 := left
        _ = ((Z+1)*x^2)*D^2 := by ring
        _ ≤ W*D^2 := right
        _ ≤ _ := scales
    nlinarith [Nat.one_le_pow 2 A ap]
  · rintro ⟨q,x,h⟩ _ ⟨Q,y,j⟩ _ e₁ e₂ e₃
    exact Prod.ext e₃ (Prod.ext e₁ e₂)

private lemma large_box (s : Finset (ℕ×ℕ×ℕ)) {n W R L Q D : ℕ}
    (rp : 0<R) (lp : 0<L) (square : R^2≤n) (wide : 4*W≤n)
    (width : 4*W≤R*L*D)
    (pr : ∀ t∈s, let q:=t.1; let x:=t.2.1; let h:=t.2.2;
      q≤Q ∧ L^2≤q ∧ q*x^2≤n ∧ n≤q*x^2+2*W ∧ q*x*h≤W) :
    s.card≤(Q+1)*(D+1)*(D+1) := by
  have scale {q x h : ℕ} (ht : (q,x,h)∈s) : R*L≤2*(q*x) := by
    obtain ⟨_,low,_,near,_⟩ := pr _ ht
    dsimp at low near
    have large : n≤2*(q*x^2) := by omega
    have sq : (R*L)^2 ≤ 2*(q*x)^2 := by
      calc
        (R*L)^2 = R^2*L^2 := by ring
        _ ≤ (2*(q*x^2))*q := Nat.mul_le_mul (square.trans large) low
        _ = _ := by ring
    by_contra! bad
    have := Nat.pow_lt_pow_left bad (by decide : 2≠0)
    nlinarith
  have cancel {q x h d : ℕ} (ht : (q,x,h)∈s) (small : (q*x)*d≤2*W) : d≤D := by
    apply Nat.le_of_mul_le_mul_left _ (Nat.mul_pos rp lp)
    calc
      R*L*d ≤ (2*(q*x))*d := Nat.mul_le_mul_right _ (scale ht)
      _ ≤ 4*W := by nlinarith
      _ ≤ _ := width
  apply box s (·.1) (·.2.1) (·.2.2)
  · intro a ha b _
    have := (pr a ha).1
    omega
  · rintro ⟨q,x,h⟩ ha ⟨q',y,j⟩ hb eq
    change q=q' at eq
    subst q'
    change x≤y+D
    rcases le_total x y with le|le
    · omega
    · obtain ⟨z,rfl⟩ := Nat.exists_eq_add_of_le le
      have hi := (pr _ ha).2.2.1
      have lo := (pr _ hb).2.2.2.1
      dsimp at hi lo
      have small : q*y*z≤2*W := by
        nlinarith [Nat.zero_le (q*z^2),Nat.zero_le (q*y*z)]
      have := cancel hb small
      omega
  · rintro ⟨q,x,h⟩ ha b _ _ _
    have hh := (pr _ ha).2.2.2.2
    dsimp at hh
    have := cancel ha (show q*x*h≤2*W by omega)
    change h≤_+D
    omega
  · rintro ⟨q,x,h⟩ _ ⟨Q,y,j⟩ _ e₁ e₂ e₃
    exact Prod.ext e₁ (Prod.ext e₂ e₃)

private lemma cube_budget (r K a b c : ℕ) (rp : 0<r) (sum : a+b+c=14) :
    (K*r^a+1)*(K*r^b+1)*(K*r^c+1) ≤ (K+1)^3*r^14 := by
  have h (j : ℕ) : K*r^j+1≤(K+1)*r^j := by
    have := pow_pos rp j
    nlinarith
  calc
    _ ≤ ((K+1)*r^a)*((K+1)*r^b)*((K+1)*r^c) := Nat.mul_le_mul (Nat.mul_le_mul (h _) (h _)) (h _)
    _ = (K+1)^3*(r^a*r^b*r^c) := by ring
    _ = _ := by rw [←pow_add,←pow_add,sum]

/-- A sixth-power subdivision in the sizes of the two small factors and the
complementary factor. The resulting exponent 14/24 leaves room below 5/8. -/
theorem count_triples (s : Finset (ℕ×ℕ×ℕ)) (n W C r : ℕ) (cp : 0<C) (rp : 0<r)
    (base : r^24≤n) (top : n≤C*r^24) (window : W≤C*r^18) (wide : 4*W≤n)
    (pr : ∀ t∈s, let x:=t.2.1; let h:=t.2.2; let w:=t.1*x*(x+h);
      0<x ∧ 0<h ∧ w≤n ∧ n≤w+W ∧ w*(x+h)≤n*x) :
    s.card ≤ 6*(16*(C+1)^3+1)^3*r^14 := by
  classical
  let K := 16*(C+1)^3
  have ck : C≤K := by dsimp [K]; nlinarith [Nat.zero_le (C^3),Nat.zero_le (C^2)]
  have larger : 4*C≤K := by dsimp [K]; nlinarith [Nat.zero_le (C^3),Nat.zero_le (C^2)]
  have cub : C*(2*C)^2≤K := by dsimp [K]; nlinarith
  have np := (pow_pos rp 24).trans_le base
  have scaleW := (Nat.mul_le_mul_right (r^18) larger)
  have wK : 4*W≤K*r^18 := (Nat.mul_le_mul_left 4 window).trans (by simpa [mul_assoc] using scaleW)
  have xlower {q x h : ℕ} (ht : (q,x,h)∈s) : r^6 ≤ 2*C*x := by
    obtain ⟨xp,hp,hi,lo,cl⟩ := pr _ ht
    dsimp at xp hp hi lo cl
    have ⟨_,_,_,bounds⟩ := geom xp lo hi rfl cl
    have wle : q*x*(x+h) ≤ W*x := (Nat.le_mul_of_pos_right _ hp).trans bounds
    have nx : n≤2*(W*x) := by nlinarith [Nat.le_mul_of_pos_right W xp]
    apply Nat.le_of_mul_le_mul_right _ (pow_pos rp 18)
    calc
      r^6*r^18 = r^24 := by ring
      _ ≤ 2*(W*x) := base.trans nx
      _ ≤ 2*((C*r^18)*x) := by gcongr
      _ = _ := by ring
  have qmax {q x h : ℕ} (ht : (q,x,h)∈s) (big : r^8≤x) : q≤C*r^8 := by
    obtain ⟨xp,_,hi,lo,cl⟩ := pr _ ht
    dsimp at xp hi lo cl
    have qx := (geom xp lo hi rfl cl).1
    apply Nat.le_of_mul_le_mul_right _ (pow_pos rp 16)
    calc
      q*r^16 = q*(r^8)^2 := by ring
      _ ≤ q*x^2 := by gcongr
      _ ≤ C*r^24 := qx.trans top
      _ = _ := by ring
  have small (T : Finset (ℕ×ℕ×ℕ)) (sub : T⊆s) (a b c : ℕ) (sum : a+b+c=14)
      (A D : ℕ) (ap : 0<A) (xl : ∀ t∈T,A≤D*t.2.1) (xu : ∀ t∈T,t.2.1≤r^a)
      (gap : 2*W*r^a ≤ n*(K*r^b)) (scale : W*D^2 ≤ A^2*(K*r^c)) :
      T.card≤(K+1)^3*r^14 := by
    apply le_trans (small_box T np ap (by omega) gap scale ?_)
    · exact le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
        (Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (cp.trans_le ck)) 1))) (cube_budget r K a b c rp sum)
    · rintro ⟨q,x,h⟩ ht
      obtain ⟨xp,_,hi,lo,cl⟩ := pr _ (sub ht)
      exact ⟨xp,xu _ ht,xl _ ht,hi,lo,(geom xp lo hi rfl cl).2.2.2⟩
  have large (T : Finset (ℕ×ℕ×ℕ)) (sub : T⊆s) (a b i : ℕ) (sum : a+b+b=14) (add : i+b=6)
      (ql : ∀ t∈T,(r^i)^2≤t.1) (qu : ∀ t∈T,t.1≤K*r^a) : T.card≤(K+1)^3*r^14 := by
    apply le_trans (large_box T (R:=r^12) (L:=r^i) (Q:=K*r^a) (D:=K*r^b)
      (pow_pos rp _) (pow_pos rp _) (by convert base using 1; ring) wide ?_ ?_) (cube_budget r K a b b rp sum)
    · calc
        _ ≤ K*r^18 := wK
        _ = (r^12*r^i)*(K*r^b) := by
          have eq : 12+i+b=18 := by omega
          rw [show r^12*r^i*(K*r^b)=K*(r^12*r^i*r^b) by ring,←pow_add,←pow_add,eq]
    · rintro ⟨q,x,h⟩ ht
      obtain ⟨xp,_,hi,lo,cl⟩ := pr _ (sub ht)
      obtain ⟨one,two,three,_⟩ := geom xp lo hi rfl cl
      exact ⟨qu _ ht,ql _ ht,one,two,three⟩
  let label (t : ℕ×ℕ×ℕ) : ℕ :=
    if t.2.1≤r^7 then 0 else if t.2.1≤r^8 then 1 else if t.1≤r^2 then 2
    else if t.1≤r^4 then 3 else if t.1≤r^6 then 4 else 5
  have last : s.card≤((K+1)^3*r^14)*(range 6).card := by
    apply card_le_mul_card_image_of_maps_to (f:=label)
    · intro t _
      apply mem_range.mpr
      unfold label
      split_ifs <;> decide
    · intro i hi
      have il : i<6 := mem_range.mp hi
      let T := s.filter (label · = i)
      have sub : T⊆s := filter_subset ..
      have lab (t) (ht:t∈T) : label t=i := (mem_filter.mp ht).2
      change T.card≤_
      interval_cases i
      · refine small T sub 7 1 6 (by decide) (r^6) (2*C) (pow_pos rp _) ?_ ?_ ?_ ?_
        · rintro ⟨q,x,h⟩ ht; exact xlower (sub ht)
        · intro t ht; have eq := lab t ht; simp only [label] at eq; split_ifs at eq; omega
        · calc
            _ ≤ (K*r^18)*r^7 := Nat.mul_le_mul_right _ (by omega)
            _ = r^24*(K*r^1) := by ring
            _ ≤ _ := by gcongr
        · calc
            _ ≤ (C*r^18)*(2*C)^2 := by gcongr
            _ = r^18*(C*(2*C)^2) := by ring
            _ ≤ r^18*K := by gcongr
            _ = _ := by ring
      · refine small T sub 8 2 4 (by decide) (r^7) 1 (pow_pos rp _) ?_ ?_ ?_ ?_
        · intro t ht; have eq := lab t ht; simp only [label] at eq; simp only [one_mul]; split_ifs at eq <;> omega
        · intro t ht; have eq := lab t ht; simp only [label] at eq; split_ifs at eq <;> omega
        · calc
            _ ≤ (K*r^18)*r^8 := Nat.mul_le_mul_right _ (by omega)
            _ = r^24*(K*r^2) := by ring
            _ ≤ _ := by gcongr
        · calc
            _ ≤ K*r^18 := by simp only [one_pow,mul_one]; omega
            _ = _ := by ring
      · apply large T sub 2 6 0 (by decide) (by decide)
        · rintro ⟨q,x,h⟩ ht; have pq := pr _ (sub ht); dsimp at pq; simp only [pow_zero,one_pow]
          by_contra! zero; have : q=0 := by omega
          subst q; simp at pq; omega
        · intro t ht; have eq := lab t ht; simp only [label] at eq
          have := Nat.le_mul_of_pos_left (r^2) (cp.trans_le ck); split_ifs at eq <;> omega
      · apply large T sub 4 5 1 (by decide) (by decide)
        · intro t ht; have eq := lab t ht; simp only [label] at eq; simp only [pow_one]; split_ifs at eq <;> omega
        · intro t ht; have eq := lab t ht; simp only [label] at eq
          have := Nat.le_mul_of_pos_left (r^4) (cp.trans_le ck); split_ifs at eq <;> omega
      · apply large T sub 6 4 2 (by decide) (by decide)
        · intro t ht; have eq := lab t ht; simp only [label] at eq; rw [←pow_mul]; norm_num; split_ifs at eq <;> omega
        · intro t ht; have eq := lab t ht; simp only [label] at eq
          have := Nat.le_mul_of_pos_left (r^6) (cp.trans_le ck); split_ifs at eq <;> omega
      · apply large T sub 8 3 3 (by decide) (by decide)
        · intro t ht; have eq := lab t ht; simp only [label] at eq; rw [←pow_mul]; norm_num; split_ifs at eq <;> omega
        · rintro ⟨q,x,h⟩ ht; have eq := lab _ ht; simp only [label] at eq
          apply le_trans (qmax (sub ht) ?_) (Nat.mul_le_mul_right _ ck)
          split_ifs at eq <;> omega
  exact last.trans_eq (by rw [card_range]; dsimp [K]; ring)

theorem count_values (s : Finset ℕ) (n W C r : ℕ) (cp : 0<C) (rp : 0<r)
    (base : r^24≤n) (top : n≤C*r^24) (window : W≤C*r^18) (wide : 4*W≤n)
    (pr : ∀ w∈s, w≤n ∧ n≤w+W ∧ ∃ x y : ℕ, 0<x ∧ x<y ∧ x*y∣w ∧ w*y≤n*x) :
    s.card ≤ 6*(16*(C+1)^3+1)^3*r^14 := by
  classical
  have rep (w : s) : ∃ q x h : ℕ, w.val=q*x*(x+h) ∧ 0<x ∧ 0<h ∧ w.val*(x+h)≤n*x := by
    obtain ⟨_,_,x,y,xp,xy,⟨q,fac⟩,close⟩ := pr _ w.property
    obtain ⟨h,rfl⟩ := Nat.exists_eq_add_of_le xy.le
    exact ⟨q,x,h,by rw [fac]; ring,xp,by omega,close⟩
  choose q x h fac xp gap cl using rep
  let triple (w : s) := (q w,x w,h w)
  let T := (univ : Finset s).image triple
  have inj : Function.Injective triple := by
    intro i j eq
    apply Subtype.ext
    have := congrArg (fun t : ℕ×ℕ×ℕ => t.1*t.2.1*(t.2.1+t.2.2)) eq
    exact (fac i).trans (this.trans (fac j).symm)
  have card : T.card=s.card := by simp [T,card_image_of_injective _ inj]
  rw [←card]
  apply count_triples T n W C r cp rp base top window wide
  intro t ht
  obtain ⟨i,_,rfl⟩ := mem_image.mp ht
  have ⟨hi,lo,_⟩ := pr i i.property
  rw [fac i] at hi lo
  exact ⟨xp i,gap i,hi,lo,fac i ▸ cl i⟩

end OMA.NearFactors402
namespace OMA.GrahamDivisor402
open Finset Filter

private theorem index_count {n p C r W : ℕ} {S : Finset ℕ} (cp : 0<C) (rp : 0<r)
    (base : r^24≤n) (top : n≤C*r^24) (win : W≤C*r^18) (wide : 4*W≤n)
    (sub : S⊆Ioc (p/2) n) (np : n<p) (window : 2*n≤p+W)
    (witness : ∀ m∈S, ∃ w : ℕ, (w=m ∨ w=p-m) ∧
      ∃ x y : ℕ, 0<x ∧ x<y ∧ x*y∣w ∧ w*y≤n*x) :
    S.card ≤ (12*(16*(C+1)^3+1)^3)*r^14 := by
  classical
  let V := (Icc 0 n).filter (fun w => n≤w+W ∧
    ∃ x y : ℕ, 0<x ∧ x<y ∧ x*y∣w ∧ w*y≤n*x)
  have bound := OMA.NearFactors402.count_values V n W C r cp rp base top win wide
    (fun _ hw => ⟨(mem_Icc.mp (mem_filter.mp hw).1).2,(mem_filter.mp hw).2⟩)
  have cover : S ⊆ V ∪ V.image (p-·) := by
    intro m hm
    have ⟨lo,hi⟩ := mem_Ioc.mp (sub hm)
    obtain ⟨w,one|two,find⟩ := witness m hm
    · subst w
      exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hi⟩,by omega,find⟩)
    · subst w
      apply mem_union_right
      exact mem_image.mpr ⟨p-m,mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,by omega,find⟩,by omega⟩
  calc
    _ ≤ _ := card_le_card cover
    _ ≤ V.card+(V.image (p-·)).card := card_union_le ..
    _ ≤ 2*(6*(16*(C+1)^3+1)^3*r^14) := by have cap := card_image_le (s:=V) (f:=(p-·)); omega
    _ = _ := by ring

private theorem fiber_card {n m l : ℕ} {F : Finset (ℕ×ℕ)} (mp : 0 < m) (lp : 0 < l)
    (mn : m≤n) (ln : l≤n) (supp : ∀ z∈F,z.1*z.2∣m*l)
    {B C r : ℕ} (bp : 0<B) (cp : 0<C)
    (divisors : ∀ t : ℕ, 0<t → t.divisors.card^192 ≤ B*t) (scale : n≤C*r^24) :
    F.card^2 ≤ (B*C^2)*r := by
  let t := m*l
  have tp : 0<t := Nat.mul_pos mp lp
  have sub : F ⊆ t.divisors ×ˢ t.divisors := by
    intro z hz
    exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨(dvd_mul_right ..).trans (supp z hz),tp.ne'⟩,
      Nat.mem_divisors.mpr ⟨(dvd_mul_left ..).trans (supp z hz),tp.ne'⟩⟩
  have card : F.card≤t.divisors.card^2 := by simpa [pow_two] using card_le_card sub
  have tn : t≤(C*r^24)^2 := by
    simpa [t,pow_two] using Nat.mul_le_mul (mn.trans scale) (ln.trans scale)
  have H := divisors t tp
  have bpos := Nat.mul_pos bp (pow_pos cp 2)
  apply (Nat.pow_left_strictMono (by decide : 48≠0)).le_iff_le.mp
  calc
    (F.card^2)^48 = F.card^96 := by ring
    _ ≤ (t.divisors.card^2)^96 := Nat.pow_le_pow_left card _
    _ = t.divisors.card^192 := by ring
    _ ≤ B*(C*r^24)^2 := H.trans (Nat.mul_le_mul_left B tn)
    _ = (B*C^2)*r^48 := by ring
    _ ≤ (B*C^2)^48*r^48 := by
      gcongr
      exact Nat.le_self_pow (by decide) _
    _ = _ := by ring

end OMA.GrahamDivisor402

open Finset Filter in
theorem OMA.solution : OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1_H2_R1.H2 := by
  classical
  obtain ⟨B,bp,divisors⟩ := OMA.FactorCount402.divisor_subpower 192
  let C : ℕ := 2^24
  let K := 12*(16*(C+1)^3+1)^3
  let D := B*C^2
  let L := K^2*D + 4*C+1
  have cp : 0<C := by decide
  filter_upwards [eventually_ge_atTop (L^24)] with n starter
  intro _ p pp np window _ F bounds
  let r := Nat.nthRoot 24 n
  have deep : L≤r := (Nat.le_nthRoot_iff (by decide : 24≠0)).mpr starter
  have rp : 0<r := by dsimp [L] at deep; omega
  have base : r^24≤n := Nat.pow_nthRoot_le (Or.inl (by decide : 24≠0))
  have bound_n := Nat.lt_pow_nthRoot_add_one (by decide : 24≠0) n
  change n<(r+1)^24 at bound_n
  have upper : n≤(2*r)^24 := bound_n.le.trans (Nat.pow_le_pow_left (by omega) 24)
  have top : n≤C*r^24 := by simpa only [mul_pow,C] using upper
  let W := 2*(n.sqrt*n.sqrt.sqrt)
  have sqrt_one : n.sqrt≤(2*r)^12 := by
    apply (Nat.pow_left_strictMono (by decide : 2≠0)).le_iff_le.mp
    calc
      n.sqrt^2 ≤ n := Nat.sqrt_le' n
      _ ≤ (2*r)^24 := upper
      _ = ((2*r)^12)^2 := by ring
  have sqrt_two : n.sqrt.sqrt≤(2*r)^6 := by
    apply (Nat.pow_left_strictMono (by decide : 2≠0)).le_iff_le.mp
    calc
      n.sqrt.sqrt^2 ≤ n.sqrt := Nat.sqrt_le' _
      _ ≤ (2*r)^12 := sqrt_one
      _ = ((2*r)^6)^2 := by ring
  have win : W≤C*r^18 := by
    calc
      _ ≤ 2*((2*r)^12*(2*r)^6) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul sqrt_one sqrt_two)
      _ = 2^19*r^18 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by decide)
  have wide : 4*W≤n := by
    have big : 4*C≤r^6 := (show 4*C≤r by dsimp [L] at deep; omega).trans (Nat.le_self_pow (by decide) _)
    calc
      _ ≤ (4*C)*r^18 := by simpa [mul_assoc] using Nat.mul_le_mul_left 4 win
      _ ≤ r^6*r^18 := Nat.mul_le_mul_right _ big
      _ = r^24 := by ring
      _ ≤ _ := base
  let J := Ioc (p/2) n
  let S := J.filter (fun m => (F m).card≠0)
  have sj : S⊆J := filter_subset ..
  have info (m : ℕ) (hm:m∈J) : 0 < m ∧ 0 < p-m ∧ m≤n ∧ p-m≤n ∧ m.Coprime (p-m) := by
    have ⟨lo,hi⟩ := mem_Ioc.mp hm
    refine ⟨by omega,by omega,hi,by omega,?_⟩
    exact (Nat.coprime_sub_self_right (by omega)).mpr
      (pp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
  have ind : S.card≤K*r^14 := by
    apply OMA.GrahamDivisor402.index_count cp rp base top win wide sj np window
    intro m hm
    obtain ⟨z,hz⟩ := card_pos.mp (Nat.pos_of_ne_zero (mem_filter.mp hm).2)
    obtain ⟨zp,lt,co,supp,h₁,h₂,h₃,h₄⟩ := bounds m (sj hm) z hz
    exact OMA.FactorCount402.near_factors zp lt co (info m (sj hm)).2.2.2.2 supp h₁ h₂ h₃ h₄
  have fiber (m) (hm:m∈S) : (F m).card^2≤D*r := by
    have ⟨mp,lp,mn,ln,_⟩ := info _ (sj hm)
    exact OMA.GrahamDivisor402.fiber_card mp lp mn ln (fun z hz => (bounds m (sj hm) z hz).2.2.2.1)
      bp cp divisors top
  let M := S.sup (fun m => (F m).card)
  have cap : M^2≤D*r := by
    by_cases ne : S.Nonempty
    · obtain ⟨m,hm,eq⟩ := exists_mem_eq_sup S ne (fun m => (F m).card)
      change M=(F m).card at eq
      rw [eq]
      exact fiber m hm
    · simp [M,not_nonempty_iff_eq_empty.mp ne]
  let total := ∑ m∈S, (F m).card
  have total_le : total≤(K*r^14)*M := by
    calc
      total ≤ ∑ _m∈S, M := sum_le_sum fun m hm => le_sup (f:=fun a => (F a).card) hm
      _ = S.card*M := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ ind
  have strict : total<r^15 := by
    apply (Nat.pow_left_strictMono (by decide : 2≠0)).lt_iff_lt.mp
    calc
      total^2 ≤ ((K*r^14)*M)^2 := Nat.pow_le_pow_left total_le 2
      _ = (K^2*r^28)*M^2 := by ring
      _ ≤ (K^2*r^28)*(D*r) := Nat.mul_le_mul_left _ cap
      _ = (K^2*D)*r^29 := by ring
      _ < r*r^29 := Nat.mul_lt_mul_of_pos_right (by dsimp [L] at deep; omega) (pow_pos rp _)
      _ = (r^15)^2 := by ring
  have low₁ : r^12≤n.sqrt := Nat.le_sqrt'.mpr (by convert base using 1; ring)
  have low₂ : r^6≤n.sqrt.sqrt := Nat.le_sqrt'.mpr (by convert low₁ using 1; ring)
  have low₃ : r^3≤n.sqrt.sqrt.sqrt := Nat.le_sqrt'.mpr (by convert low₂ using 1; ring)
  have sum_eq : total = ∑ m∈J, (F m).card := sum_filter_ne_zero ..
  change (∑ m∈J, (F m).card) < _
  rw [←sum_eq]
  exact strict.trans_le (by simpa only [←pow_add] using Nat.mul_le_mul low₁ low₃)
