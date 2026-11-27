import OMAReductions.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1

/-! Graham equality families: a prime divisor exceeding half the size forces one of the two model families. Otherwise signed residues modulo a prime near twice the size yield more normalized divisor pairs than the analytic upper bound permits. The finite arguments are independently written following the ideas of Boyle and Balasubramanian–Soundararajan, On a conjecture of R. L. Graham, Acta Arith. 75 (1996), §§2, 4. -/

namespace OMA.Boyle402
open Finset

private theorem recover_card {A : Finset ℕ} {f : ℕ → ℕ} (hf : Set.InjOn f A)
    {b : ℕ} (bounds : ∀ x ∈ A, f x ∈ Icc 1 b) : A.card ≤ b := by
  calc
    A.card = (A.image f).card := (card_image_of_injOn hf).symm
    _ ≤ (Icc 1 b).card := card_le_card (image_subset_iff.mpr bounds)
    _ = b := by simp

private theorem partition_product {U V : Finset ℕ} {n : ℕ} (hU : U.Nonempty)
    (hV : V.Nonempty) (up : ∀ u ∈ U, 0 < u) (vp : ∀ v ∈ V, 0 < v)
    (cross : ∀ u ∈ U, ∀ v ∈ V, u ∣ v ∧ v / u ≤ n) : U.card * V.card ≤ n := by
  let d := U.lcm id
  have ud (u) (hu : u ∈ U) : u ∣ d := dvd_lcm (f := id) hu
  have dv (v) (hv : v ∈ V) : d ∣ v := lcm_dvd fun u hu => (cross u hu v hv).1
  have dp : 0 < d := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr fun u hu => (up u hu).ne')
  let l := U.min' hU
  let h := V.max' hV
  have hl : l ∈ U := min'_mem _ _
  have hh : h ∈ V := max'_mem _ _
  have Ubound : U.card ≤ d / l := by
    apply recover_card (f := (d / ·))
    · intro u hu v hv e
      change d / u = d / v at e
      rw [← Nat.div_div_self (ud u hu) dp.ne', e, Nat.div_div_self (ud v hv) dp.ne']
    · intro u hu
      exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd dp (ud _ hu)) (up _ hu),
        Nat.div_le_div_left (min'_le U u hu) (up _ hl)⟩
  have Vbound : V.card ≤ h / d := by
    apply recover_card (f := (· / d))
    · intro u hu v hv e
      change u / d = v / d at e
      rw [← Nat.div_mul_cancel (dv u hu), e, Nat.div_mul_cancel (dv v hv)]
    · intro v hv
      exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (vp _ hv) (dv _ hv)) dp,
        Nat.div_le_div_right (le_max' V v hv)⟩
  calc
    U.card * V.card ≤ (d / l) * (h / d) := Nat.mul_le_mul Ubound Vbound
    _ = h / l := by
      apply Nat.eq_of_mul_eq_mul_right (up _ hl)
      calc
        d / l * (h / d) * l = h / d * (d / l * l) := by ring
        _ = h := by rw [Nat.div_mul_cancel (ud _ hl), Nat.div_mul_cancel (dv _ hh)]
        _ = h / l * l := (Nat.div_mul_cancel (cross _ hl _ hh).1).symm
    _ ≤ n := (cross _ hl _ hh).2

private theorem cross_quotient {a b q n : ℕ} (ha : 0 < a) (hq : q.Prime)
    (hn : n < 2*q) (qa : q ∣ a) (qb : ¬ q ∣ b)
    (ab : a / a.gcd b ≤ n) (ba : b / b.gcd a ≤ n) :
    q ≤ n ∧ a / q ∣ b ∧ b / (a / q) ≤ n := by
  let g := a.gcd b
  have ag : a/g*g=a := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
  have qg : ¬ q ∣ g := fun t => qb (t.trans (Nat.gcd_dvd_right a b))
  have qt : q ∣ a/g := (hq.dvd_mul.mp (show q ∣ a/g*g by rw [ag]; exact qa)).resolve_right qg
  obtain ⟨k,hk⟩ := qt
  have pos : 0 < a/g := Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b))
    (Nat.gcd_pos_of_pos_left _ ha)
  have ub : a/g ≤ n := ab
  have ko : k=1 := by
    by_contra! h
    have kp : 0 < k := by
      apply Nat.pos_of_ne_zero
      rintro rfl
      simp only [Nat.mul_zero] at hk
      omega
    have := Nat.mul_le_mul_left q (show 2 ≤ k by omega)
    omega
  have aq : a/q = g := by
    have e : a=q*g := by simpa [hk,ko] using ag.symm
    rw [e,Nat.mul_div_cancel_left _ hq.pos]
  rw [aq]
  exact ⟨by simpa [hk, ko] using ub,Nat.gcd_dvd_right a b,
    by simpa [g,Nat.gcd_comm a b] using ba⟩

private theorem one_in_image {A : Finset ℕ} {n : ℕ} (card : A.card=n) (hn : 0<n)
    (f : ℕ → ℕ) (hf : Set.InjOn f A) (bounds : ∀ x ∈ A, f x ∈ Icc 1 n) :
    ∃ x ∈ A, f x = 1 := by
  have eq : A.image f = Icc 1 n := eq_of_subset_of_card_le (image_subset_iff.mpr bounds)
    (by simp [card_image_of_injOn hf,card])
  exact mem_image.mp (eq ▸ (mem_Icc.mpr ⟨by decide,hn⟩ : 1 ∈ Icc 1 n))

/-- A prime exceeding half the family size forces one of the two extremal elements. -/
theorem rigidity {A : Finset ℕ} {n q : ℕ} (card : A.card=n) (hn : 5≤n)
    (pos : ∀ a ∈ A, 0 < a) (primitive : A.gcd id=1)
    (bound : ∀ a∈A, ∀ b∈A, a/a.gcd b≤n)
    (hq : q.Prime) (large : n < 2*q) (occurs : ∃ a∈A, q∣a) :
    1∈A ∨ A.lcm id∈A := by
  classical
  let P := A.filter (q ∣ ·)
  let V := A.filter (fun b => ¬ q ∣ b)
  let U := P.image (·/q)
  obtain ⟨a,ha,hqa⟩ := occurs
  have haP : a∈P := mem_filter.mpr ⟨ha,hqa⟩
  have uNe : U.Nonempty := ⟨a/q,mem_image_of_mem _ haP⟩
  have vNe : V.Nonempty := by
    by_contra! h
    have qg : q ∣ A.gcd id := dvd_gcd fun b hb => by
      by_contra hq'
      have hin : b ∈ V := mem_filter.mpr ⟨hb,hq'⟩
      rw [h] at hin
      exact notMem_empty b hin
    exact hq.not_dvd_one (primitive ▸ qg)
  have un (u) (hu:u∈U) : ∃ x∈P, x/q=u := mem_image.mp hu
  have up (u) (hu:u∈U) : 0<u := by
    obtain ⟨x,hx,rfl⟩ := un u hu
    obtain ⟨inA,div⟩ := mem_filter.mp hx
    exact Nat.div_pos (Nat.le_of_dvd (pos _ inA) div) hq.pos
  have vp (v) (hv:v∈V) : 0<v := pos v (mem_filter.mp hv).1
  have cross (x) (hx:x∈P) (v) (hv:v∈V) :
      q ≤ n ∧ x/q ∣ v ∧ v/(x/q) ≤ n := by
    obtain ⟨xa,dx⟩ := mem_filter.mp hx
    obtain ⟨va,ndv⟩ := mem_filter.mp hv
    exact cross_quotient (pos _ xa) hq large dx ndv (bound _ xa _ va) (bound _ va _ xa)
  have uv : U.card*V.card≤n := partition_product uNe vNe up vp (by
    intro u hu v hv
    obtain ⟨x,hx,rfl⟩ := un u hu
    exact (cross _ hx _ hv).2)
  have inj : Set.InjOn (·/q) P := by
    intro x hx y hy e
    change x/q=y/q at e
    rw [← Nat.div_mul_cancel (mem_filter.mp hx).2,e,Nat.div_mul_cancel (mem_filter.mp hy).2]
  have sum : U.card+V.card=n := by
    change (P.image (·/q)).card + V.card=n
    rw [card_image_of_injOn inj, ←card]
    exact card_filter_add_card_filter_not ..
  have singleton : U.card=1 ∨ V.card=1 := by
    have := card_pos.mpr uNe
    have := card_pos.mpr vNe
    by_contra! neither
    have uu : 2≤U.card := by omega
    have vv : 2≤V.card := by omega
    have cu := Nat.sub_add_cancel uu
    have cv := Nat.sub_add_cancel vv
    nlinarith [Nat.zero_le ((U.card-2)*(V.card-2))]
  obtain ⟨v,hv⟩ := vNe
  have qle := (cross _ haP _ hv).1
  rcases singleton with sing|sing
  · left
    obtain ⟨u,su⟩ := card_eq_one.mp sing
    have only (x) (hx:x∈P) : x/q=u := mem_singleton.mp (su ▸ (mem_image_of_mem (·/q) hx : x/q∈U))
    have ug : u∣A.gcd id := dvd_gcd fun x hx => by
      by_cases dx : q∣x
      · rw [←only _ (mem_filter.mpr ⟨hx,dx⟩)]
        exact Nat.div_dvd_of_dvd dx
      · rw [←only _ haP]
        exact (cross _ haP _ (mem_filter.mpr ⟨hx,dx⟩)).2.1
    have uone : u=1 := Nat.dvd_one.mp (primitive ▸ ug)
    obtain ⟨z,hz,ez⟩ := one_in_image card (by omega) id Function.injective_id.injOn (by
      intro x hx
      refine mem_Icc.mpr ⟨pos _ hx,?_⟩
      by_cases dx : q∣x
      · have t := only _ (mem_filter.mpr ⟨hx,dx⟩)
        have e : x=q := by simpa [t,uone] using (Nat.div_mul_cancel dx).symm
        simpa [e] using qle
      · simpa [only _ haP,uone] using (cross _ haP _ (mem_filter.mpr ⟨hx,dx⟩)).2.2)
    exact ez ▸ hz
  · right
    have only (x) (hx:x∈V) : x=v := by
      obtain ⟨w,sw⟩ := card_eq_one.mp sing
      exact (mem_singleton.mp (sw ▸ hx)).trans (mem_singleton.mp (sw ▸ hv)).symm
    let T := q*v
    have tp : 0<T := Nat.mul_pos hq.pos (vp _ hv)
    have dxT (x) (hx:x∈A) : x∣T := by
      by_cases dx : q∣x
      · have udiv := (cross _ (mem_filter.mpr ⟨hx,dx⟩) _ hv).2.1
        have e := Nat.mul_dvd_mul_left q udiv
        rwa [Nat.mul_div_cancel' dx] at e
      · rw [only _ (mem_filter.mpr ⟨hx,dx⟩)]
        exact dvd_mul_left _ _
    have tinj : Set.InjOn (T/·) A := by
      intro x hx y hy e
      change T/x=T/y at e
      rw [←Nat.div_div_self (dxT _ hx) tp.ne',e,Nat.div_div_self (dxT _ hy) tp.ne']
    obtain ⟨z,hz,ez⟩ := one_in_image card (by omega) (T/·) tinj (by
      intro x hx
      refine mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd tp (dxT _ hx)) (pos _ hx),?_⟩
      by_cases dx : q∣x
      · have h := (cross _ (mem_filter.mpr ⟨hx,dx⟩) _ hv).2.2
        change q*v/x≤n
        conv_lhs => arg 2; rw [←Nat.mul_div_cancel' dx]
        simpa [Nat.mul_div_mul_left _ _ hq.pos] using h
      · change q*v/x≤n
        rw [only _ (mem_filter.mpr ⟨hx,dx⟩),Nat.mul_div_cancel _ (vp _ hv)]
        exact qle)
    have tz : T=z := by simpa [ez] using (Nat.div_mul_cancel (dxT _ hz)).symm
    have tm : T∈A := tz ▸ hz
    have e : A.lcm id=T := Nat.dvd_antisymm (lcm_dvd dxT) (dvd_lcm (f:=id) tm)
    exact e ▸ tm

end OMA.Boyle402
namespace OMA.Collision402
open Finset

private lemma no_large_prime {A : Finset ℕ} {p n : ℕ} (hp : p.Prime) (np : n<p)
    (positive : ∀ a∈A, 0<a) (primitive : A.gcd id=1)
    (bound : ∀ a∈A, ∀ b∈A, a/a.gcd b≤n) (a) (ha:a∈A) : ¬p∣a := by
  intro pa
  have all (b) (hb:b∈A) : p∣b := by
    let g := a.gcd b
    have d := Nat.gcd_dvd_left a b
    have e : a/g*g=a := Nat.div_mul_cancel d
    have hpg := hp.dvd_mul.mp (show p∣a/g*g by rwa [e])
    rcases hpg with ratio|pg
    · have pos : 0<a/g := Nat.div_pos (Nat.le_of_dvd (positive _ ha) d)
        (Nat.gcd_pos_of_pos_left _ (positive _ ha))
      exact False.elim (np.not_ge ((Nat.le_of_dvd pos ratio).trans (bound _ ha _ hb)))
    · exact pg.trans (Nat.gcd_dvd_right a b)
  exact hp.not_dvd_one (primitive ▸ (dvd_gcd (f:=id) all))

private lemma residues_inj {A : Finset ℕ} {p n : ℕ} (hp:p.Prime) (np:n<p)
    (unit : ∀ a∈A, ¬p∣a) (bound : ∀ a∈A, ∀ b∈A,a/a.gcd b≤n) :
    Set.InjOn (·%p) A := by
  intro a ha b hb h
  let g := a.gcd b
  have ag : a/g*g=a := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
  have bg : b/g*g=b := Nat.div_mul_cancel (Nat.gcd_dvd_right a b)
  have cop : p.Coprime g := hp.coprime_iff_not_dvd.mpr (fun h => unit _ ha (h.trans (Nat.gcd_dvd_left a b)))
  have rel : a/g*g ≡ b/g*g [MOD p] := by rw [ag,bg]; exact h
  have bb : b/g≤n := by simpa [g,Nat.gcd_comm a b] using bound _ hb _ ha
  have e := (Nat.ModEq.cancel_right_of_coprime cop rel).eq_of_lt_of_lt
    ((bound _ ha _ hb).trans_lt np) (bb.trans_lt np)
  rw [←ag,←bg,e]

/-- At a prime cardinality, an extremal family has a member divisible by that prime. -/
theorem prime_occurs {A : Finset ℕ} {p : ℕ} (hp:p.Prime) (card:A.card=p)
    (bound : ∀ a∈A, ∀ b∈A,a/a.gcd b≤p) : ∃ a∈A, p∣a := by
  classical
  by_contra! unit
  have positive := hp.pos
  have strict (a) (ha:a∈A) (b) (hb:b∈A) : a/a.gcd b≤p-1 := by
    have bd := bound _ ha _ hb
    have ne : a/a.gcd b ≠ p := by
      intro e
      have ag := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
      rw [e] at ag
      exact unit _ ha (ag ▸ dvd_mul_right _ _)
    omega
  have inj := residues_inj hp (show p-1<p by omega) unit strict
  have subset : A.image (·%p) ⊆ Ico 1 p := by
    apply image_subset_iff.mpr
    intro a ha
    exact mem_Ico.mpr ⟨Nat.pos_of_ne_zero fun e => unit _ ha (Nat.dvd_of_mod_eq_zero e),
      Nat.mod_lt _ positive⟩
  have := card_le_card subset
  rw [card_image_of_injOn inj,card,Nat.card_Ico] at this
  omega

private lemma paired_keys {E : Finset ℕ} {p n : ℕ} (card : E.card=n)
    (hp : 0<p) (bounds : E⊆Ico 1 p) :
    ∃ K : Finset ℕ, n ≤ K.card+p/2 ∧
      ∀ k∈K, 0<k ∧ k≤p/2 ∧ k∈E ∧ p-k∈E := by
  let L := E.filter (·≤p/2)
  let R := E.filter (fun v => ¬v≤p/2)
  let F := R.image (p-·)
  have pos (x) (hx:x∈E) := (mem_Ico.mp (bounds hx)).1
  have lt (x) (hx:x∈E) := (mem_Ico.mp (bounds hx)).2
  have total : L.card+R.card=n := (card_filter_add_card_filter_not ..).trans card
  have fc : F.card=R.card := by
    apply card_image_of_injOn
    intro x hx y hy e
    have := lt x (mem_filter.mp hx).1
    have := lt y (mem_filter.mp hy).1
    change p-x=p-y at e
    omega
  have union : L∪F⊆Icc 1 (p/2) := by
    intro x hx
    rcases mem_union.mp hx with l|r
    · exact mem_Icc.mpr ⟨pos _ (mem_filter.mp l).1,(mem_filter.mp l).2⟩
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp r
      have := lt y (mem_filter.mp hy).1
      have := (mem_filter.mp hy).2
      apply mem_Icc.mpr
      omega
  have cap := card_le_card union
  have cnt := card_union_add_card_inter L F
  simp only [Nat.card_Icc] at cap
  refine ⟨L∩F,by omega,?_⟩
  intro k hk
  obtain ⟨kl,kr⟩ := mem_inter.mp hk
  obtain ⟨y,hy,hy'⟩ := mem_image.mp kr
  have yl := lt y (mem_filter.mp hy).1
  have eq : p-k=y := by omega
  exact ⟨pos _ (mem_filter.mp kl).1,(mem_filter.mp kl).2,(mem_filter.mp kl).1,eq ▸ (mem_filter.mp hy).1⟩

private lemma opposite {A : Finset ℕ} {p n k a b : ℕ} (hp:p.Prime) (np:n<p) (odd : 2<p)
    (pos : ∀ a∈A, 0<a) (unit : ∀ a∈A, ¬p∣a)
    (bound : ∀ a∈A, ∀ b∈A,a/a.gcd b≤n)
    (ha:a∈A) (hb:b∈A) (ar:a%p=k) (br:b%p=p-k) (kl:k≤p/2) :
    ∃ m d : ℕ, p/2 < m ∧ m≤n ∧ m*d∈A ∧ (p-m)*d∈A ∧
      min ((m*d)%p) (((p-m)*d)%p)=k := by
  let g := a.gcd b
  let u := a/g
  let v := b/g
  have ag : u*g=a := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
  have bg : v*g=b := Nat.div_mul_cancel (Nat.gcd_dvd_right a b)
  have pu : 0<u := Nat.div_pos (Nat.le_of_dvd (pos _ ha) (Nat.gcd_dvd_left a b))
    (Nat.gcd_pos_of_pos_left _ (pos _ ha))
  have ub : u≤n := bound _ ha _ hb
  have vb : v≤n := by simpa [v,g,Nat.gcd_comm a b] using bound _ hb _ ha
  have qg : ¬p∣g := fun h => unit _ ha (h.trans (Nat.gcd_dvd_left a b))
  have e : p∣(u+v)*g := by
    rw [Nat.add_mul,ag,bg,Nat.dvd_iff_mod_eq_zero,Nat.add_mod,ar,br]
    rw [Nat.add_sub_of_le (by omega : k≤p),Nat.mod_self]
  have hsum := (hp.dvd_mul.mp e).resolve_right qg
  obtain ⟨w,hw⟩ := hsum
  have w1 : w=1 := by
    by_contra! h
    by_cases z:w=0
    · simp [z] at hw
      omega
    · have := Nat.mul_le_mul_left p (show 2≤w by omega)
      omega
  have s : u+v=p := by simpa [w1] using hw
  have uneven : u≠v := by
    intro uv
    obtain ⟨j,hj⟩ := hp.odd_of_ne_two odd.ne'
    omega
  rcases lt_or_gt_of_ne uneven with uv|vu
  · refine ⟨v,g,by omega,vb,bg ▸ hb,?_,?_⟩
    · simpa only [show p-v=u by omega,ag] using ha
    · simp only [show p-v=u by omega,ag,bg,ar,br]
      omega
  · refine ⟨u,g,by omega,ub,ag ▸ ha,?_,?_⟩
    · simpa only [show p-u=v by omega,bg] using hb
    · simp only [show p-u=v by omega,ag,bg,ar,br]
      omega

private lemma cross_gcd {m l d e : ℕ} (ml : m.Coprime l) (de : d.Coprime e) :
    (m*d).gcd (l*e) ∣ d.gcd l * e.gcd m := by
  have left : (m*d).gcd l ∣ d.gcd l := by
    have h : l.gcd (m*d) ∣ l.gcd m*l.gcd d := gcd_mul_dvd_mul_gcd l m d
    simpa only [Nat.gcd_comm l m,ml.gcd_eq_one,one_mul,Nat.gcd_comm l (m*d),Nat.gcd_comm l d] using h
  have right : (m*d).gcd e ∣ e.gcd m := by
    have h : e.gcd (m*d) ∣ e.gcd m*e.gcd d := gcd_mul_dvd_mul_gcd e m d
    simpa only [Nat.gcd_comm e d,de.gcd_eq_one,mul_one,Nat.gcd_comm e (m*d)] using h
  exact (show (m*d).gcd (l*e) ∣ (m*d).gcd l*(m*d).gcd e from gcd_mul_dvd_mul_gcd (m*d) l e).trans
    (Nat.mul_dvd_mul left right)

/-- The reduced dilation factors in an overlapping pair have no extra prime powers:
they divide the product of the two coefficients (Balasubramanian–Soundararajan, Lemma 2.3). -/
theorem supported {m l d e n : ℕ} (dp : 0 < d) (ep : 0 < e)
    (ml:m.Coprime l) (de:d.Coprime e) (close : n^2 < 2*m^2)
    (bd : m*d / (m*d).gcd (l*e) ≤ n) (be : m*e / (m*e).gcd (l*d) ≤ n) :
    d*e ∣ m*l := by
  have factor (w : ℕ) : w.gcd m*w.gcd l ∣ w :=
    (ml.gcd_both w w).mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_left ..)
  obtain ⟨z,dz⟩ := factor d
  obtain ⟨t,et⟩ := factor e
  have right (x y : ℕ) (xp:0<x) (yp:0<y) (cop:x.Coprime y)
      (h:m*x/(m*x).gcd (l*y)≤n) : m*x ≤ n*(x.gcd l*y.gcd m) := by
    have gs := cross_gcd ml cop
    have pos : 0 < x.gcd l*y.gcd m := Nat.mul_pos (Nat.gcd_pos_of_pos_left _ xp)
      (Nat.gcd_pos_of_pos_left _ yp)
    calc
      m*x = m*x/(m*x).gcd (l*y)*(m*x).gcd (l*y) := (Nat.div_mul_cancel (Nat.gcd_dvd_left ..)).symm
      _ ≤ n*(x.gcd l*y.gcd m) := Nat.mul_le_mul h (Nat.le_of_dvd pos gs)
  let t₀ := d.gcd m*d.gcd l*(e.gcd m*e.gcd l)
  have ht₀ : 0<t₀ := by
    dsimp [t₀]
    exact Nat.mul_pos (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ dp) (Nat.gcd_pos_of_pos_left _ dp))
      (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ ep) (Nat.gcd_pos_of_pos_left _ ep))
  have ctx : t₀*(m^2*(z*t)) ≤ t₀*n^2 := by
    calc
      t₀*(m^2*(z*t)) = (m*d)*(m*e) := by
        dsimp [t₀]
        calc
          _ = (m*(d.gcd m*d.gcd l*z))*(m*(e.gcd m*e.gcd l*t)) := by ring
          _ = _ := by rw [←dz,←et]
      _ ≤ (n*(d.gcd l*e.gcd m))*(n*(e.gcd l*d.gcd m)) :=
        Nat.mul_le_mul (right d e dp ep de bd) (right e d ep dp de.symm be)
      _ = t₀*n^2 := by dsimp [t₀]; ring
  have upper := Nat.le_of_mul_le_mul_left ctx ht₀
  have zpos : 0<z := Nat.pos_of_ne_zero fun ez => dp.ne' (by simpa only [ez,mul_zero] using dz)
  have tpos : 0<t := Nat.pos_of_ne_zero fun ez => ep.ne' (by simpa only [ez,mul_zero] using et)
  have zt : z*t=1 := by
    by_contra! h
    have := Nat.mul_pos zpos tpos
    have := Nat.mul_le_mul_left (m^2) (show 2≤z*t by omega)
    omega
  have ones : z=1 ∧ t=1 := ⟨Nat.dvd_one.mp (zt ▸ dvd_mul_right z t),
    Nat.dvd_one.mp (zt ▸ dvd_mul_left t z)⟩
  apply de.mul_dvd_of_dvd_of_dvd
  · apply (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime ml).mp
    simpa only [ones.1,mul_one] using dz.symm
  · apply (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime ml).mp
    simpa only [ones.2,mul_one] using et.symm

end OMA.Collision402
namespace OMA.Collision402
open Finset

private lemma reduced_cross {m l x y n : ℕ} (xp : 0<x)
    (h : m*x/(m*x).gcd (l*y) ≤ n) :
    m*(x/x.gcd y)/(m*(x/x.gcd y)).gcd (l*(y/x.gcd y)) ≤ n := by
  let g := x.gcd y
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ xp
  have h₁ : g*(m*(x/g))=m*x := by
    rw [mul_left_comm, Nat.mul_div_cancel' (Nat.gcd_dvd_left x y)]
  have h₂ : g*(l*(y/g))=l*y := by
    rw [mul_left_comm, Nat.mul_div_cancel' (Nat.gcd_dvd_right x y)]
  rw [←h₁,←h₂,Nat.gcd_mul_left,Nat.mul_div_mul_left _ _ gp] at h
  exact h

/-- In a nonempty fiber, hold its least dilation fixed. Each additional dilation
gives a different reduced pair supported on the two complementary coefficients. -/
private lemma normalized_fiber {A S : Finset ℕ} {m l n : ℕ} (pos : ∀ a∈A, 0<a)
    (bd : ∀ a∈A, ∀ b∈A, a/a.gcd b≤n) (cop : m.Coprime l) (close : n^2<2*m^2)
    (inside : ∀ d∈S, m*d∈A ∧ l*d∈A) :
    ∃ F : Finset (ℕ×ℕ), S.card≤F.card+1 ∧ ∀ z∈F, 0<z.1 ∧ z.1<z.2 ∧
      z.1.Coprime z.2 ∧ z.1*z.2∣m*l ∧
      m*z.1/(m*z.1).gcd (l*z.2)≤n ∧ m*z.2/(m*z.2).gcd (l*z.1)≤n ∧
      l*z.1/(l*z.1).gcd (m*z.2)≤n ∧ l*z.2/(l*z.2).gcd (m*z.1)≤n := by
  classical
  by_cases hs : S.Nonempty
  · let x := S.min' hs
    have hx : x∈S := min'_mem _ _
    have sp (y) (hy:y∈S) : 0<y := Nat.pos_of_mul_pos_left (pos _ (inside y hy).1)
    have xp := sp x hx
    let f (y : ℕ) := (x/x.gcd y,y/x.gcd y)
    have recur (y : ℕ) : (x/x.gcd y)*y=(y/x.gcd y)*x := by
      have a := Nat.div_mul_cancel (Nat.gcd_dvd_left x y)
      have b := Nat.div_mul_cancel (Nat.gcd_dvd_right x y)
      calc
        _ = (x/x.gcd y)*((y/x.gcd y)*x.gcd y) := by rw [b]
        _ = (y/x.gcd y)*((x/x.gcd y)*x.gcd y) := by ring
        _ = _ := by rw [a]
    have ip : Set.InjOn f ((S.erase x : Finset ℕ) : Set ℕ) := by
      intro y hy z hz eq
      have left := congrArg Prod.fst eq
      have right := congrArg Prod.snd eq
      change x/x.gcd y=x/x.gcd z at left
      change y/x.gcd y=z/x.gcd z at right
      have xy : 0<x/x.gcd y := Nat.div_pos (Nat.le_of_dvd xp (Nat.gcd_dvd_left ..))
        (Nat.gcd_pos_of_pos_left _ xp)
      exact Nat.eq_of_mul_eq_mul_left xy (by rw [recur,right,←recur,left])
    refine ⟨(S.erase x).image f,?_,?_⟩
    · rw [card_image_of_injOn ip,card_erase_of_mem hx]
      omega
    · intro u hu
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hu
      have ⟨yn,ys⟩ := mem_erase.mp hy
      have xy : x<y := lt_of_le_of_ne (min'_le S y ys) (Ne.symm yn)
      let g := x.gcd y
      let i := x/g
      let j := y/g
      have gp : 0<g := Nat.gcd_pos_of_pos_left _ xp
      have ipos : 0 < i := Nat.div_pos (Nat.le_of_dvd xp (Nat.gcd_dvd_left ..)) gp
      have ij : i < j := by
        have a : i*g=x := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
        have b : j*g=y := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
        exact Nat.lt_of_mul_lt_mul_right (a.symm ▸ b.symm ▸ xy)
      have co : i.Coprime j := Nat.coprime_div_gcd_div_gcd (by omega)
      have b₁ := reduced_cross xp (bd _ (inside x hx).1 _ (inside y ys).2)
      have b₂ := reduced_cross (sp y ys) (bd _ (inside y ys).1 _ (inside x hx).2)
      have b₃ := reduced_cross xp (bd _ (inside x hx).2 _ (inside y ys).1)
      have b₄ := reduced_cross (sp y ys) (bd _ (inside y ys).2 _ (inside x hx).1)
      rw [Nat.gcd_comm y x] at b₂ b₄
      exact ⟨ipos,ij,co,supported ipos (ipos.trans ij) cop co close b₁ b₂,b₁,b₂,b₃,b₄⟩
  · exact ⟨∅,by simp [not_nonempty_iff_eq_empty.mp hs],by simp⟩

/-- Count all complementary residue pairs, including their dilation multiplicities. -/
private lemma signed_count {A : Finset ℕ} {n p : ℕ} (card : A.card=n)
    (hp:p.Prime) (np:n<p) (odd : 2<p) (pos : ∀ a∈A, 0<a)
    (primitive : A.gcd id=1) (bound : ∀ a∈A, ∀ b∈A,a/a.gcd b≤n) :
    ∃ S : ℕ → Finset ℕ,
      (Ioc (p/2) n).card ≤ ∑ m∈Ioc (p/2) n, (S m).card ∧
      ∀ m∈Ioc (p/2) n, ∀ d∈S m, m*d∈A ∧ (p-m)*d∈A := by
  classical
  let E := A.image (·%p)
  have unit := no_large_prime hp np pos primitive bound
  have cE : E.card=n := (card_image_of_injOn (residues_inj hp np unit bound)).trans card
  have rE : E ⊆ Ico 1 p := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    exact mem_Ico.mpr ⟨Nat.pos_of_ne_zero fun e => unit _ ha (Nat.dvd_of_mod_eq_zero e),
      Nat.mod_lt a hp.pos⟩
  obtain ⟨K,ck,props⟩ := paired_keys cE hp.pos rE
  have pair (k : K) : ∃ m d : ℕ, p/2 < m ∧ m≤n ∧ m*d∈A ∧ (p-m)*d∈A ∧
      min ((m*d)%p) (((p-m)*d)%p)=k.val := by
    obtain ⟨_,hl,l,r⟩ := props _ k.property
    obtain ⟨a,ha,ar⟩ := mem_image.mp l
    obtain ⟨b,hb,br⟩ := mem_image.mp r
    exact opposite hp np odd pos unit bound ha hb ar br hl
  choose m d hlow hhigh hleft hright hkey using pair
  let U : Finset K := univ
  let V (t : ℕ) := U.filter (m · = t)
  let S (t : ℕ) := (V t).image d
  have sc (t : ℕ) : (S t).card = (V t).card := by
    apply card_image_of_injOn
    intro i hi j hj eq
    have mi : m i=t := (mem_filter.mp hi).2
    have mj : m j=t := (mem_filter.mp hj).2
    apply Subtype.ext
    rw [←hkey i,←hkey j,mi,mj,eq]
  have uc : U.card = ∑ t∈Ioc (p/2) n, (V t).card :=
    card_eq_sum_card_fiberwise (f:=m) (fun k _ => mem_Ioc.mpr ⟨hlow k,hhigh k⟩)
  refine ⟨S,?_,?_⟩
  · simp_rw [sc]
    rw [←uc,Nat.card_Ioc]
    have : U.card=K.card := by simp [U]
    omega
  · intro t _ z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    have mi : m i=t := (mem_filter.mp hi).2
    exact mi ▸ ⟨hleft i,hright i⟩

end OMA.Collision402

namespace OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1_H2_R1
open Finset Filter

/-- Prime distribution at power-scale intervals. For a composite n, pick p just
below 2n and retain a power-sized supply of primes between p/2 and n.
The interval width is asymptotic to n^(3/4), the requested count to n^(5/8). -/
def H1 : Prop := ∀ᶠ n : ℕ in atTop, ¬n.Prime →
  let g := n.sqrt * n.sqrt.sqrt
  ∃ p : ℕ, p.Prime ∧ n<p ∧ 2*n≤p+2*g ∧ p+g≤2*n ∧ 2*n^2<p^2 ∧
    n.sqrt*n.sqrt.sqrt.sqrt ≤ ((Ioc (p/2) n).filter Nat.Prime).card

/-- A divisor-pair estimate, independent of the family of integers in Graham's
problem. Count normalized pairs u<v supported on m(p−m) for which
the four directed cross quotients are at most n. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop, ¬n.Prime → ∀ p : ℕ, p.Prime → n<p →
  2*n≤p+2*(n.sqrt*n.sqrt.sqrt) → p+n.sqrt*n.sqrt.sqrt≤2*n →
  ∀ F : ℕ → Finset (ℕ×ℕ),
    (∀ m∈Ioc (p/2) n, ∀ z∈F m, 0<z.1 ∧ z.1<z.2 ∧ z.1.Coprime z.2 ∧
      z.1*z.2∣m*(p-m) ∧
      m*z.1/(m*z.1).gcd ((p-m)*z.2)≤n ∧ m*z.2/(m*z.2).gcd ((p-m)*z.1)≤n ∧
      (p-m)*z.1/((p-m)*z.1).gcd (m*z.2)≤n ∧ (p-m)*z.2/((p-m)*z.2).gcd (m*z.1)≤n) →
    (∑ m∈Ioc (p/2) n, (F m).card) < n.sqrt*n.sqrt.sqrt.sqrt

theorem main : H1 → H2 → OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1.H2 := by
  classical
  intro primes divisors
  filter_upwards [primes,divisors,eventually_ge_atTop 5] with n prime_est div_est large
  intro A card nz primitive bound _
  have pos (a) (ha:a∈A) : 0<a := Nat.pos_of_ne_zero fun e => nz (e ▸ ha)
  have finish (q) (hq:q.Prime) (nq:n<2*q) (found:∃ a∈A,q∣a) :=
    OMA.Boyle402.rigidity card large pos primitive bound hq nq found
  by_cases hn : n.Prime
  · exact finish n hn (by omega) (OMA.Collision402.prime_occurs hn card bound)
  by_contra notModel
  have missing (q) (hq:q.Prime) (nq:n<2*q) (a) (ha:a∈A) : ¬q∣a :=
    fun dv => notModel (finish q hq nq ⟨a,ha,dv⟩)
  obtain ⟨p,hp,np,pl,pu,close,prime_count⟩ := prime_est hn
  let J := Ioc (p/2) n
  obtain ⟨S,signed,inside⟩ := OMA.Collision402.signed_count card hp np (by omega) pos primitive bound
  let eligible (m : ℕ) (z : ℕ×ℕ) : Prop := 0<z.1 ∧ z.1<z.2 ∧ z.1.Coprime z.2 ∧
    z.1*z.2∣m*(p-m) ∧
    m*z.1/(m*z.1).gcd ((p-m)*z.2)≤n ∧ m*z.2/(m*z.2).gcd ((p-m)*z.1)≤n ∧
    (p-m)*z.1/((p-m)*z.1).gcd (m*z.2)≤n ∧ (p-m)*z.2/((p-m)*z.2).gcd (m*z.1)≤n
  have extract (m : ℕ) : ∃ F : Finset (ℕ×ℕ),
      ((S m).card≤F.card+(if m.Prime then 0 else 1) ∨ m∉J) ∧ ∀ z∈F, eligible m z := by
    by_cases hm : m∈J
    · have ⟨lo,hi⟩ := mem_Ioc.mp hm
      have lower : p<2*m := by omega
      by_cases prime : m.Prime
      · have empty : S m=∅ := eq_empty_iff_forall_notMem.mpr fun d hd =>
          missing m prime (by omega) _ (inside m hm d hd).1 (dvd_mul_right m d)
        exact ⟨∅,by simp [empty]⟩
      · have co : m.Coprime (p-m) :=
          (Nat.coprime_sub_self_right (by omega)).mpr
            (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
        have near : n^2<2*m^2 := by
          have := Nat.pow_lt_pow_left lower (by decide : 2≠0)
          nlinarith
        obtain ⟨F,fc,fe⟩ := OMA.Collision402.normalized_fiber pos bound co near (inside m hm)
        exact ⟨F,Or.inl (by simpa [prime] using fc),fe⟩
    · exact ⟨∅,Or.inr hm,by simp⟩
  choose F prop using extract
  have cap := div_est hn p hp np pl pu F (fun m _ => (prop m).2)
  have sum_le : (∑ m∈J, (S m).card) ≤ (∑ m∈J, (F m).card) +
      (J.filter (fun m => ¬m.Prime)).card := by
    calc
      _ ≤ ∑ m∈J, ((F m).card + if m.Prime then 0 else 1) :=
        sum_le_sum fun m hm => (prop m).1.resolve_right (not_not.mpr hm)
      _ = _ := by rw [sum_add_distrib]; congr 1; simp [card_filter]
  have part := card_filter_add_card_filter_not (s:=J) Nat.Prime
  change J.card ≤ ∑ m∈J, (S m).card at signed
  change (∑ m∈J, (F m).card) < n.sqrt*n.sqrt.sqrt.sqrt at cap
  change n.sqrt*n.sqrt.sqrt.sqrt ≤ (J.filter Nat.Prime).card at prime_count
  omega

end OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1_H2_R1
