import FormalConjectures.ErdosProblems.«1084»

/-! # Contacts in three-dimensional unit-sphere packings

We obtain explicit bounds 6n − 60 n^(2/3) and 6n − n^(2/3)/162. The lower construction is a face-centred cubic lattice. The upper bound counts columns of a half-unit grid: near the last covered site in each column one can add a direction to the contact sphere, so some packing point has fewer than twelve contacts.

The local bound of twelve uses Marek Wrzos’s Apache-2.0 formalization of Musin’s theorem, from KissingNumber/Basic.lean and KissingNumber/Musin.lean in https://github.com/Pendzoncymisio/kissing-number-lean/tree/2e403b0d1afe84f41a90cb77d926bc31666a8972. We combined and adapted these sources to the pinned Mathlib, scoped their resource options to individual declarations, and omitted the unused final energy corollary. The large sum-of-squares expansions are rechecked using an exact sparse integer polynomial verifier. A copy of the license follows the solution. The lattice, surface-deficit, counting and extremal-function arguments were formalized here. -/

/- # A separated face-centred cubic lattice with twelve contact directions -/

namespace OMA.Fcc1084
open Finset Filter Metric Erdos1084
open scoped EuclideanGeometry Classical

abbrev Lattice := Fin 3 → ℤ
abbrev Space := EuclideanSpace ℝ (Fin 3)

private def normForm (u : Lattice) : ℤ :=
  u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + (u 0 + u 1 + u 2) ^ 2

private noncomputable def point (u : Lattice) : Space :=
  WithLp.toLp 2 ![((u 0+u 1:ℤ):ℝ)/Real.sqrt 2, ((u 0+u 2:ℤ):ℝ)/Real.sqrt 2,
    ((u 1+u 2:ℤ):ℝ)/Real.sqrt 2]

private lemma dist_sq (a b : Lattice) :
    2 * dist (point a) (point b)^2 = (normForm (a-b) : ℝ) := by
  have h : 0 < Real.sqrt 2 := by positivity
  have hh := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp [Fin.sum_univ_succ,point,normForm,Real.dist_eq,sq_abs]
  field_simp
  linear_combination -(↑(a 0) ^ 2 + ↑(a 1) ^ 2 + ↑(a 2) ^ 2 + ↑(b 0) ^ 2 +
    ↑(b 1) ^ 2 + ↑(b 2) ^ 2 - 2*↑(a 0)*↑(b 0) - 2*↑(a 1)*↑(b 1) -
    2*↑(a 2)*↑(b 2) + (↑(a 0)+↑(a 1)+↑(a 2)-↑(b 0)-↑(b 1)-↑(b 2))^2) * hh

private lemma normForm_ge_two {u : Lattice} (hu : u ≠ 0) : 2 ≤ normForm u := by
  have ne : u 0 ≠ 0 ∨ u 1 ≠ 0 ∨ u 2 ≠ 0 := by
    by_contra! h
    exact hu (by funext i; fin_cases i <;> simp_all)
  have hsum : 0 < u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
    rcases ne with h|h|h <;> nlinarith [sq_pos_of_ne_zero h,sq_nonneg (u 0),
      sq_nonneg (u 1),sq_nonneg (u 2)]
  have hp : Even (normForm u) := by
    refine ⟨u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 0*u 1 + u 0*u 2 + u 1*u 2, ?_⟩
    unfold normForm; ring
  obtain ⟨t,ht⟩ := hp
  have h : 0 < normForm u := by unfold normForm; linarith [sq_nonneg (u 0+u 1+u 2)]
  omega

private lemma separated {a b : Lattice} (hne : a ≠ b) : 1 ≤ dist (point a) (point b) := by
  have h := normForm_ge_two (sub_ne_zero.mpr hne)
  have hr : (2:ℝ) ≤ normForm (a-b) := by exact_mod_cast h
  nlinarith [dist_sq a b, dist_nonneg (x:=point a) (y:=point b)]

private lemma point_injective : Function.Injective point := by
  intro a b h
  by_contra ne
  have hh := separated ne
  rw [h,dist_self] at hh
  linarith

private def dirs : Finset Lattice :=
  {![1,0,0],![-1,0,0],![0,1,0],![0,-1,0],![0,0,1],![0,0,-1],
   ![1,-1,0],![-1,1,0],![1,0,-1],![-1,0,1],![0,1,-1],![0,-1,1]}

private lemma card_dirs : dirs.card = 12 := by decide

private lemma good_dirs : ∀ d ∈ dirs, normForm d = 2 ∧ ∀ i, -1 ≤ d i ∧ d i ≤ 1 := by
  decide

private lemma contact (a d : Lattice) (hd : d ∈ dirs) :
    dist (point (a+d)) (point a) = 1 := by
  have h := dist_sq (a+d) a
  rw [add_sub_cancel_left, (good_dirs d hd).1] at h
  norm_num at h
  rcases h with h|h
  · exact h
  · linarith [dist_nonneg (x:=point (a+d)) (y:=point a)]

private lemma le_extremal (S : Finset Space) {n : ℕ}
    (hc : S.card=n) (hs : IsSeparated' 1 (S : Set Space)) :
    unitDistNum S ≤ f 3 n := by
  unfold f
  let F (T : Finset Space) := ⨆ (_ : T.card = n) (_ : IsSeparated' 1 (T : Set Space)), unitDistNum T
  have bnd (T : Finset Space) : F T ≤ n.choose 2 := by
    apply ciSup_le'
    intro ht
    apply ciSup_le'
    intro _
    simpa [ht] using unitDistNum_le_choose_two T
  apply le_ciSup_of_le (f:=F) ⟨_, Set.forall_mem_range.mpr bnd⟩ S
  apply le_ciSup_of_le (f:=fun _ : S.card=n => ⨆ _ : IsSeparated' 1 (S : Set Space), unitDistNum S)
    ⟨unitDistNum S, Set.forall_mem_range.mpr (fun _ => ciSup_le' fun _ => le_rfl)⟩ hc
  exact le_ciSup (f:=fun _ : IsSeparated' 1 (S : Set Space) => unitDistNum S)
    ⟨_, Set.forall_mem_range.mpr (fun _ => le_rfl)⟩ hs

private def box (lo hi : ℤ) : Finset Lattice :=
  Fintype.piFinset fun _ => Icc lo hi

private lemma card_box (lo hi : ℤ) :
    (box lo hi).card = (hi+1-lo).toNat ^ 3 := by
  simp [box, Int.card_Icc]

/-- A finite cube padded to exactly n points in the same lattice. The (k−2)³
    interior vertices retain all twelve contacts even before padding. -/
theorem grid_bound (k n : ℕ) (hkn : k^3 ≤ n) :
    6*(k-2)^3 ≤ f 3 n := by
  classical
  let B := box 0 ((k:ℤ)-1)
  let I := box 1 ((k:ℤ)-2)
  have cb : B.card = k^3 := by simp [B, card_box]
  have ci : I.card = (k-2)^3 := by
    rw [show I=box 1 ((k:ℤ)-2) from rfl, card_box]
    congr 1; omega
  obtain ⟨Q,sub,hq⟩ := Infinite.exists_superset_card_eq B n (cb.le.trans hkn)
  let S := Q.image point
  have sc : S.card = n := (card_image_of_injective Q point_injective).trans hq
  have sep : IsSeparated' 1 (S : Set Space) := by
    rintro _ hx _ hy hxy
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    obtain ⟨b,_,rfl⟩ := mem_image.mp hy
    have h := separated (a:=a) (b:=b) (fun he => hxy (congrArg point he))
    rw [edist_dist]
    exact_mod_cast (ENNReal.ofReal_le_ofReal h)
  let U := S.sym2.filter fun e => dist e.out.1 e.out.2 = 1
  let ord (e : Sym2 Space) : Finset (Space × Space) := {e.out,e.out.swap}
  let enc (p : Lattice × Lattice) := (point (p.1+p.2),point p.1)
  have inj : Function.Injective enc := by
    rintro ⟨a,d⟩ ⟨b,e⟩ h
    have h1 := point_injective (congrArg Prod.snd h)
    change a=b at h1; subst b
    have h2 : a+d=a+e := point_injective (congrArg Prod.fst h)
    exact Prod.ext rfl (add_left_cancel h2)
  have to_ord : ∀ p ∈ I ×ˢ dirs, enc p ∈ U.biUnion ord := by
    rintro ⟨a,d⟩ hp
    obtain ⟨ha,hd⟩ := mem_product.mp hp
    have hb (i) : 1 ≤ a i ∧ a i ≤ (k:ℤ)-2 := mem_Icc.mp (Fintype.mem_piFinset.mp ha i)
    have am : point a ∈ S := mem_image.mpr ⟨a,sub (Fintype.mem_piFinset.mpr fun i =>
      mem_Icc.mpr (by have := hb i; omega)),rfl⟩
    have dm : point (a+d) ∈ S := by
      refine mem_image.mpr ⟨a+d,sub (Fintype.mem_piFinset.mpr fun i => mem_Icc.mpr ?_),rfl⟩
      change 0 ≤ a i+d i ∧ a i+d i ≤ (k:ℤ)-1
      have := hb i
      have := (good_dirs d hd).2 i
      omega
    let e := Sym2.mk (point (a+d)) (point a)
    have he : Sym2.mk e.out.1 e.out.2 = Sym2.mk (point (a+d)) (point a) := e.out_eq
    have hl := contact a d hd
    apply mem_biUnion.mpr
    refine ⟨e,mem_filter.mpr ⟨mk_mem_sym2_iff.mpr ⟨dm,am⟩,?_⟩,?_⟩
    · rcases Sym2.eq_iff.mp he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> simp_all [dist_comm]
    · rcases Sym2.eq_iff.mp he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact (show e.out = enc (a,d) from Prod.ext h₁ h₂) ▸ mem_insert_self _ _
      · exact mem_insert_of_mem (mem_singleton.mpr (Prod.ext h₂.symm h₁.symm))
  have lb := card_le_card_of_injOn enc to_ord inj.injOn
  have ub : (U.biUnion ord).card ≤ U.card*2 := calc
    _ ≤ ∑ e ∈ U, (ord e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ U, 2 := sum_le_sum (fun _ _ => card_le_two)
    _ = _ := by simp
  rw [card_product,ci,card_dirs] at lb
  change (U.biUnion ord).card ≤ unitDistNum S * 2 at ub
  have := le_extremal S sc sep
  omega

theorem lower : ∀ᶠ n : ℕ in atTop,
    6*(n:ℝ) - 60*(n:ℝ)^(2/3:ℝ) ≤ f 3 n := by
  filter_upwards [eventually_ge_atTop 8] with n hn
  have large : ∃ m : ℕ, n < m^3 := ⟨n+1, by nlinarith [sq_nonneg (n:ℤ)]⟩
  let k := Nat.find large - 1
  have pos : 0 < Nat.find large := by
    by_contra! h
    have h0 := Nat.find_spec large
    rw [show Nat.find large = 0 by omega] at h0; simp at h0
  have heq : Nat.find large = k+1 := by dsimp [k]; omega
  have lo : k^3 ≤ n := le_of_not_gt (Nat.find_min large (by omega : k < Nat.find large))
  have hi : n < (k+1)^3 := heq ▸ Nat.find_spec large
  have hk : 2 ≤ k := by
    by_contra! h
    interval_cases k <;> omega
  have h2 : k-2+2 = k := by omega
  have loss : 6*n ≤ 6*(k-2)^3+60*k^2 := by
    generalize k-2 = j at h2 ⊢
    rw [← h2] at hi ⊢
    nlinarith
  have ksq : (k:ℝ)^2 ≤ (n:ℝ)^(2/3:ℝ) := calc
    (k:ℝ)^2 = ((k:ℝ)^3)^(2/3:ℝ) := by
      rw [← Real.rpow_natCast_mul (by positivity)]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast lo) (by norm_num)
  have lr : 6*(n:ℝ) ≤ 6*((k-2:ℕ):ℝ)^3+60*(k:ℝ)^2 := by exact_mod_cast loss
  have gr : 6*((k-2:ℕ):ℝ)^3 ≤ f 3 n := by exact_mod_cast grid_bound k n lo
  linarith

end OMA.Fcc1084

/- # The discrete three-dimensional projection inequality -/

namespace OMA.Projections1084
open Finset

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def xy (p : α × β × γ) := (p.1,p.2.1)
def xz (p : α × β × γ) := (p.1,p.2.2)

/-- The three pairwise projections of a finite set of triples satisfy the
    Loomis–Whitney bound. Two bounds on each x-slice feed Cauchy–Schwarz. -/
theorem three (S : Finset (α × β × γ)) :
    S.card^2 ≤ (S.image xy).card * (S.image xz).card * (S.image Prod.snd).card := by
  classical
  let X := S.image Prod.fst
  let Y := S.image xy
  let Z := S.image xz
  let W := S.image Prod.snd
  let A (x : α) := S.filter (fun p => p.1=x)
  let B (x : α) := Y.filter (fun p => p.1=x)
  let C (x : α) := Z.filter (fun p => p.1=x)
  have per (x : α) : (A x).card^2 ≤ (B x).card * ((C x).card*W.card) := by
    have yz : (A x).card ≤ W.card := by
      apply card_le_card_of_injOn Prod.snd
      · intro p hp
        exact mem_image_of_mem _ (mem_filter.mp hp).1
      · intro p hp q hq he
        exact Prod.ext ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm) he
    have yz' : (A x).card ≤ (B x).card * (C x).card := by
      rw [← card_product]
      apply card_le_card_of_injOn fun p => (xy p,xz p)
      · intro p hp
        obtain ⟨ps,px⟩ := mem_filter.mp hp
        exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_image_of_mem _ ps,px⟩,
          mem_filter.mpr ⟨mem_image_of_mem _ ps,px⟩⟩
      · rintro ⟨a,b,c⟩ _ ⟨d,e,f⟩ _ h
        simp [xy,xz] at h ⊢
        exact ⟨h.1.1,h.1.2,h.2.2⟩
    simpa only [sq,mul_assoc] using Nat.mul_le_mul yz' yz
  have sumA : S.card = ∑ x ∈ X,(A x).card := card_eq_sum_card_image Prod.fst S
  have sumB : Y.card = ∑ x ∈ X,(B x).card := by
    apply card_eq_sum_card_fiberwise (f:=Prod.fst)
    rintro _ hy
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hy
    exact mem_image_of_mem _ hp
  have sumC : Z.card = ∑ x ∈ X,(C x).card := by
    apply card_eq_sum_card_fiberwise (f:=Prod.fst)
    rintro _ hz
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hz
    exact mem_image_of_mem _ hp
  have bound := sum_sq_le_sum_mul_sum_of_sq_le_mul X
    (fun x _ => Nat.zero_le (B x).card) (fun x _ => Nat.zero_le ((C x).card*W.card))
    (fun x _ => per x)
  rwa [← sumA, ← sumB, ← sum_mul, ← sumC, ← mul_assoc] at bound

end OMA.Projections1084

/- # Exposed packing sites have at least one missing contact -/

namespace OMA.Boundary1084
open Finset Metric
open scoped EuclideanGeometry Classical RealInnerProductSpace

abbrev Space := EuclideanSpace ℝ (Fin 3)
def Hard (S : Finset Space) := ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ dist x y
noncomputable def neighbors (S : Finset Space) (z : Space) :=
  S.filter (fun x => dist x z = 1)
def Kissing := ∀ (V : Finset Space) (z : Space), (∀ x ∈ V, dist x z=1) →
  Hard V → V.card ≤ 12

lemma neighbor_bound (cap : Kissing) {S : Finset Space} (hs : Hard S) (z : Space) :
    (neighbors S z).card ≤ 12 := cap _ z (fun _ h => (mem_filter.mp h).2)
      (fun _ h _ h' => hs _ (mem_filter.mp h).1 _ (mem_filter.mp h').1)

private lemma unit_gap {u v : Space} (hu : ‖u‖=1) (hv : ‖v‖=1) {d : ℝ}
    (hd : 2 < d) (hd' : d ≤ 9/4) (gap : 2 < ‖d • u-v‖) : 1 ≤ ‖u-v‖ := by
  by_contra! near
  have h := norm_sub_sq_real u v
  rw [hu,hv] at h
  have inn : 1/2 < ⟪u,v⟫ := by
    nlinarith [mul_pos (by linarith : 0 < 1-‖u-v‖)
      (by linarith [norm_nonneg (u-v)] : 0 < 1+‖u-v‖)]
  have hw := norm_sub_sq_real (d • u) v
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith),hu,mul_one,
    real_inner_smul_left,hv] at hw
  nlinarith [mul_pos (by linarith : 0 < d) (by linarith : 0 < 2*⟪u,v⟫-1),
    mul_nonneg (by linarith : 0 ≤ 9/4-d) (by linarith : 0 ≤ d+9/4-1),
    mul_pos (by linarith : 0 < ‖d • u-v‖-2) (by linarith : 0 < ‖d • u-v‖+2)]

/-- An empty ball just beyond z gives one extra direction on z's unit sphere. -/
theorem exposed (cap : Kissing) {S : Finset Space} (hs : Hard S) {z q : Space}
    (hz : z ∈ S) (empty : ∀ y ∈ S, 2 < dist q y) (near : dist q z ≤ 9/4) :
    (neighbors S z).card < 12 := by
  let d := ‖q-z‖
  have hd : 2 < d := by simpa [d,dist_eq_norm] using empty z hz
  have hd' : d ≤ 9/4 := by simpa [d,dist_eq_norm] using near
  let u := d⁻¹ • (q-z)
  have hd0 : 0 < d := by linarith
  have hu : ‖u‖ = 1 := by
    simp [u,norm_smul,Real.norm_eq_abs,abs_of_pos hd0,
      show ‖q-z‖ = d from rfl,hd0.ne']
  have hdu : d • u = q-z := by simp [u,smul_smul,hd0.ne']
  let t := z+u
  have ht : dist t z = 1 := by simpa [t,dist_eq_norm] using hu
  have far (y) (hy : y ∈ neighbors S z) : 1 ≤ dist t y := by
    obtain ⟨ys,dy⟩ := mem_filter.mp hy
    have hh : 2 < ‖d • u-(y-z)‖ := by
      rw [hdu,sub_sub_sub_cancel_right]
      exact (dist_eq_norm q y) ▸ empty y ys
    have h := unit_gap hu (by simpa [dist_eq_norm] using dy) hd hd' hh
    rwa [dist_eq_norm, show t-y = u-(y-z) by dsimp [t]; abel]
  have fresh : t ∉ neighbors S z := by
    intro h
    have hf := far t h
    rw [dist_self] at hf
    linarith
  have hbound := cap (insert t (neighbors S z)) z (by
    intro x hx
    rcases mem_insert.mp hx with rfl|hn
    · exact ht
    · exact (mem_filter.mp hn).2) (by
    intro x hx y hy hxy
    rcases mem_insert.mp hx with rfl|hx <;> rcases mem_insert.mp hy with rfl|hy
    · exact (hxy rfl).elim
    · exact far y hy
    · simpa [dist_comm] using far x hx
    · exact hs x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 hxy)
  rw [card_insert_of_notMem fresh] at hbound
  omega

end OMA.Boundary1084

/- # Counting exposed packing sites by their coordinate projections -/

namespace OMA.ShellCount1084
open Finset OMA.Boundary1084 OMA.Projections1084
open scoped Classical

/-- A half-unit cell has diameter less than the minimum separation. -/
private noncomputable def bin (x : Space) (i : Fin 3) : ℤ := ⌊2*x i⌋

private noncomputable def code (x : Space) : ℤ × ℤ × ℤ :=
  (bin x 0,bin x 1,bin x 2)

private lemma distinct_codes {S : Finset Space} (hs : Hard S) : (S : Set Space).InjOn code := by
  intro x hx y hy eq
  by_contra ne
  have coord (i : Fin 3) : bin x i=bin y i := by
    have e : bin x 0=bin y 0 ∧ bin x 1=bin y 1 ∧ bin x 2=bin y 2 := by simpa [code] using eq
    fin_cases i <;> tauto
  have small (i : Fin 3) : (x i-y i)^2 < 1/4 := by
    have lo := Int.floor_le (2*x i)
    have hi := Int.lt_floor_add_one (2*x i)
    have lo' := Int.floor_le (2*y i)
    have hi' := Int.lt_floor_add_one (2*y i)
    change ((⌊2*x i⌋:ℤ):ℝ) ≤ _ at lo
    have e := coord i
    change ⌊2*x i⌋=⌊2*y i⌋ at e
    rw [e] at lo hi
    nlinarith [mul_pos (show 0 < 1/2-(x i-y i) by linarith)
      (show 0 < 1/2+(x i-y i) by linarith)]
  have ds : dist x y ^2 = (x 0-y 0)^2+(x 1-y 1)^2+(x 2-y 2)^2 := by
    rw [EuclideanSpace.dist_eq,Real.sq_sqrt (sum_nonneg fun i _ => sq_nonneg _)]
    simp [Fin.sum_univ_succ,Real.dist_eq,sq_abs,add_assoc]
  have sep := hs x hx y hy ne
  nlinarith [small 0,small 1,small 2]

/-- Follow a vertical line from an occupied point to the last covered
quarter-unit step. The next step exposes its covering center. -/
private lemma cover_column (cap : Kissing) (S : Finset Space) (hs : Hard S)
    {x : Space} (hx : x∈S) (k : Fin 3) :
    ∃ z∈S, (neighbors S z).card<12 ∧ ∀ i : Fin 3, i≠k →
      bin z i-4 ≤ bin x i ∧ bin x i ≤ bin z i+4 := by
  let q (m : ℤ) : Space := x + EuclideanSpace.single k ((m:ℝ)/4)
  let covered (m : ℤ) := ∃ z∈S, dist (q m) z≤2
  obtain ⟨y,_,highest⟩ := exists_max_image S (fun z => z k) ⟨x,hx⟩
  have bounded : ∃ b : ℤ, ∀m,covered m → m≤b := by
    refine ⟨⌊4*(y k+2-x k)⌋,?_⟩
    rintro m ⟨z,hz,close⟩
    have right := (PiLp.dist_apply_le (q m) z k).trans close
    simp [q,Real.dist_eq] at right
    have := (abs_le.mp right).2
    apply Int.le_floor.mpr
    linarith [highest z hz]
  have start : covered 0 := ⟨x,hx,by simp [q]⟩
  obtain ⟨m,⟨z,hz,close⟩,last⟩ := Int.exists_greatest_of_bdd bounded ⟨0,start⟩
  have empty (y) (hy:y∈S) : 2<dist (q (m+1)) y := by
    by_contra! no
    have := last (m+1) ⟨y,hy,no⟩
    omega
  have step : dist (q (m+1)) (q m) = 1/4 := by
    simp [q,Real.dist_eq]
    ring_nf
    norm_num
  have near : dist (q (m+1)) z≤9/4 := by linarith [dist_triangle (q (m+1)) (q m) z]
  refine ⟨z,hz,exposed cap hs hz empty near,?_⟩
  intro i ne
  have d := (PiLp.dist_apply_le (q m) z i).trans close
  simp [q,ne,Real.dist_eq] at d
  have a := (abs_le.mp d).1
  have b := (abs_le.mp d).2
  have left := Int.floor_mono (show 2*z i-4≤2*x i by linarith)
  have right := Int.floor_mono (show 2*x i≤2*z i+4 by linarith)
  simpa [bin] using And.intro left right

private def box (a b : ℤ) :=
  (Icc (a-4) (a+4)) ×ˢ (Icc (b-4) (b+4))

private lemma box_card (a b : ℤ) : (box a b).card=81 := by
  have side (c:ℤ) : c+4+1-(c-4)=9 := by ring
  simp [box,Int.card_Icc,side]

private lemma projection_bound (cap : Kissing) (S : Finset Space) (hs : Hard S)
    (i j k : Fin 3) (ik : i≠k) (jk : j≠k) :
    (S.image (fun x => (bin x i,bin x j))).card ≤
      81*(S.filter fun z => (neighbors S z).card<12).card := by
  let D := S.filter fun z => (neighbors S z).card<12
  let B (z : Space) := box (bin z i) (bin z j)
  have sub : S.image (fun x => (bin x i,bin x j)) ⊆ D.biUnion B := by
    rintro t ht
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    obtain ⟨z,hz,hd,coords⟩ := cover_column cap S hs hx k
    exact mem_biUnion.mpr ⟨z,mem_filter.mpr ⟨hz,hd⟩,
      mem_product.mpr ⟨mem_Icc.mpr (coords i ik),mem_Icc.mpr (coords j jk)⟩⟩
  calc
    _ ≤ _ := card_le_card sub
    _ ≤ ∑ z∈D, (B z).card := card_biUnion_le
    _ = D.card*81 := sum_const_nat (fun z _ => box_card _ _)
    _ = _ := Nat.mul_comm _ _

/-- Half-unit cells, the three projection counts and discrete Loomis–Whitney. -/
theorem shell (cap : Kissing) (S : Finset Space) (hs : Hard S) :
    S.card^2 ≤ (81*(S.filter fun z => (neighbors S z).card<12).card)^3 := by
  have main := three (S.image code)
  rw [card_image_of_injOn (distinct_codes hs)] at main
  simp only [image_image] at main
  have a := projection_bound cap S hs 0 1 2 (by decide) (by decide)
  have b := projection_bound cap S hs 0 2 1 (by decide) (by decide)
  have c := projection_bound cap S hs 1 2 0 (by decide) (by decide)
  simpa [pow_succ] using main.trans (Nat.mul_le_mul (Nat.mul_le_mul a b) c)

end OMA.ShellCount1084

/- # Counting missing contacts on the boundary of a sphere packing -/

namespace OMA.Upper1084

open Finset Filter Erdos1084 OMA.Boundary1084
open scoped Classical Topology

private theorem dist_quot_out (x y : Space) :
    dist (Sym2.mk x y).out.1 (Sym2.mk x y).out.2 = dist x y := by
  let e := Sym2.mk x y
  have h : Sym2.mk e.out.1 e.out.2 = Sym2.mk x y := e.out_eq
  change dist e.out.1 e.out.2 = _
  rcases Sym2.eq_iff.mp h with ⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;> rw [h₁,h₂]
  exact dist_comm _ _

/-- Every contact contributes to the neighbour count at each of its two endpoints. -/
theorem degree_sum (S : Finset Space) : 2*unitDistNum S = ∑ x ∈ S, (neighbors S x).card := by
  let U := S.sym2.filter fun e => dist e.out.1 e.out.2=1
  let R (e : Sym2 Space) (x : Space) := x ∈ e
  have incident (x : Space) (hx : x∈S) :
      U.bipartiteBelow R x = (neighbors S x).image (Sym2.mk x) := by
    ext e
    constructor
    · intro h
      obtain ⟨he,hx'⟩ := mem_filter.mp h
      obtain ⟨y,rfl⟩ := Sym2.mem_iff_exists.mp hx'
      obtain ⟨hy,hd⟩ := mem_filter.mp he
      exact mem_image.mpr ⟨y,mem_filter.mpr ⟨(mk_mem_sym2_iff.mp hy).2,
        by rwa [dist_quot_out,dist_comm x y] at hd⟩,rfl⟩
    · intro h
      obtain ⟨y,hy,rfl⟩ := mem_image.mp h
      obtain ⟨ys,hd⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mk_mem_sym2_iff.mpr ⟨hx,ys⟩,
        (dist_quot_out x y).trans ((dist_comm _ _).trans hd)⟩,Sym2.mem_mk_left x y⟩
  have endpoints (e : Sym2 Space) (he : e ∈ U) : (S.bipartiteAbove R e).card = 2 := by
    have hsub := mem_sym2_iff.mp (mem_filter.mp he).1
    have eqs : S.bipartiteAbove R e = e.toFinset := by
      ext x
      change x ∈ S.filter (fun y => y∈e) ↔ _
      rw [mem_filter,Sym2.mem_toFinset]
      exact ⟨And.right,fun h => ⟨hsub x h,h⟩⟩
    rw [eqs]
    apply Sym2.card_toFinset_of_not_isDiag
    induction e using Sym2.ind with | _ x y =>
      intro h
      have d := (mem_filter.mp he).2
      rw [dist_quot_out] at d
      simp [Sym2.mk_isDiag_iff.mp h] at d
  change 2*U.card = _
  calc
    _ = ∑ e ∈ U, (S.bipartiteAbove R e).card := by
      rw [sum_congr rfl endpoints]; simp [mul_comm]
    _ = ∑ x ∈ S, (U.bipartiteBelow R x).card := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
    _ = _ := sum_congr rfl fun x hx => by
      rw [incident x hx,card_image_of_injective]
      intro y z h
      rcases Sym2.eq_iff.mp h with h|h
      · exact h.2
      · exact h.2.trans h.1

private theorem deficit (cap : Kissing) (S : Finset Space) (hs : Hard S) :
    2*unitDistNum S + (S.filter (fun z => (neighbors S z).card < 12)).card ≤ 12*S.card := by
  rw [degree_sum,card_filter]
  rw [← sum_add_distrib]
  calc
    _ ≤ ∑ _z ∈ S, 12 := sum_le_sum fun z _ => by
      have h := neighbor_bound cap hs z
      split_ifs <;> omega
    _ = _ := by simp [mul_comm]

theorem upper (cap : Kissing) (C : ℕ) (hC : 0 < C)
    (shell : ∀ S : Finset Space, Hard S →
      S.card^2 ≤ (C*(S.filter (fun z => (neighbors S z).card<12)).card)^3) :
    ∀ n : ℕ, (f 3 n : ℝ) ≤ 6*n - (1/(2*C):ℝ)*(n:ℝ)^(2/3:ℝ) := by
  intro n
  let rhs := 6*(n:ℝ) - (1/(2*C):ℝ)*(n:ℝ)^(2/3:ℝ)
  have pc : (0:ℝ) < C := by exact_mod_cast hC
  have ok : 0 ≤ rhs := by
    by_cases hn : n=0
    · simp [hn,rhs]
    have nn : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hp : (n:ℝ)^(2/3:ℝ) ≤ n := by
      simpa using Real.rpow_le_rpow_of_exponent_le nn (show (2/3:ℝ) ≤ 1 by norm_num)
    have win : (1/(2*C):ℝ) ≤ 1 := (div_le_one (by positivity)).mpr (by
      have : (1:ℝ) ≤ C := by exact_mod_cast hC
      linarith)
    have h := mul_le_mul_of_nonneg_right win (show 0 ≤ (n:ℝ)^(2/3:ℝ) by positivity)
    dsimp [rhs]
    linarith
  suffices h : f 3 n ≤ ⌊rhs⌋₊ from (Nat.cast_le.mpr h).trans (Nat.floor_le ok)
  unfold f
  refine ciSup_le' fun S => ciSup_le' fun hn => ciSup_le' fun hsep => Nat.le_floor ?_
  have hs : Hard S := by
    intro x hx y hy hxy
    have gap : 1 ≤ edist x y := hsep hx hy hxy
    rw [edist_dist] at gap
    exact ENNReal.one_le_ofReal.mp gap
  let missing := (S.filter (fun z => (neighbors S z).card < 12)).card
  have sh : (n:ℝ)^2 ≤ ((C:ℝ)*missing)^3 := by exact_mod_cast hn ▸ shell S hs
  have power : (n:ℝ)^(2/3:ℝ) ≤ (C:ℝ)*missing := by
    apply (Real.rpow_le_rpow_iff (by positivity) (by positivity) (z := (3:ℝ)) (by norm_num)).mp
    rw [← Real.rpow_mul (by positivity)]
    norm_num
    exact sh
  have bound : 2*(unitDistNum S:ℝ) + missing ≤ 12*(n:ℝ) := by exact_mod_cast hn ▸ deficit cap S hs
  dsimp [rhs]
  field_simp
  nlinarith only [power,mul_nonneg (sub_nonneg.mpr bound) pc.le]

end OMA.Upper1084

/- # The three-dimensional contact asymptotic from the kissing number -/

open Filter

theorem OMA.finish1084 (cap : OMA.Boundary1084.Kissing) :
    type_of% @Erdos1084.erdos_1084.variants.upper_lower_d3 := by
  refine ⟨60, 1/(2*(81:ℝ)), by norm_num, ?_⟩
  filter_upwards [OMA.Fcc1084.lower] with n lower
  exact ⟨lower, OMA.Upper1084.upper cap 81 (by decide) (OMA.ShellCount1084.shell cap) n⟩

/-
# The Delsarte machinery on `S²`, and Musin's polynomial

Mathlib has no spherical harmonics, no positive-definite kernels on `S²` and no Gegenbauer
family, so they are built here from scratch. The rungs `pd_one` … `pd_five` and `pd_nine` are
the positivity facts `ΣΣ P_k(⟨u,v⟩) ≥ 0`, and `lp_bound` turns them into a cardinality bound.
`card_le_thirteen` is the result of the linear-programming method alone: **at most thirteen**.

**No linear-programming certificate reaches twelve.** The LP optimum is about `13.16` at every
degree (`scripts/delsarte_lp.py`), and degrees 6, 7 and 8 have the same optimum as degree 5,
which is why `pd_nine` is needed. Closing the last unit needs Musin's cap extension:

* `musinF` — Musin's degree-9 polynomial, with `musin_lemma2` giving `N² ≤ ΣΣ f`;
* `musin_f_nonpos` — `f ≤ 0` on `[−59/100, 1/2]`, by a Markov–Lukács certificate;
* `musinF_le_antipode` — `f ≤ f(−1)` on the far cap;
* `musin_h_zero`, `musin_h_one` — the first two cases of Musin's Lemma 3.

`KissingNumber/Musin.lean` supplies the rest: `cap_card_le_four` (at most four points in the
cap, by direction counting rather than spherical trigonometry), `cap_copositive` (the sign-free
cap condition), the remaining `h_m`, and the assembly `kissingBound3`.
-/

namespace Kissing3D

open Finset

/- Three-dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/- A hard-core configuration in space: no two particles closer than `1`. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def HardCore (X : Finset E3) : Prop :=
  ∀ z ∈ X, ∀ w ∈ X, z ≠ w → 1 ≤ dist z w

open scoped Classical in
/- The particles bonded to `z`. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
noncomputable def neighbors (X : Finset E3) (z : E3) : Finset E3 :=
  X.filter (fun w => dist z w = 1)

/- Twice the contact number. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
noncomputable def contactCount (X : Finset E3) : ℕ := ∑ z ∈ X, (neighbors X z).card

/- **The hypothesis this file is conditional on**: the kissing number of `ℝ³` is at most 12.

True (Schütte–van der Waerden 1953); proved in `KissingNumber/Musin.lean` as
`kissingBound3`. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def KissingBound3 : Prop :=
  ∀ S : Finset E3, (∀ u ∈ S, ‖u‖ = 1) →
    (∀ u ∈ S, ∀ v ∈ S, u ≠ v → 1 ≤ dist u v) → S.card ≤ 12

/- Given the kissing bound, no particle has more than twelve bonds. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem card_neighbors_le_twelve (hk : KissingBound3) {X : Finset E3} (hX : HardCore X)
    (z : E3) : (neighbors X z).card ≤ 12 := by
  classical
  have hinj : Set.InjOn (· - z) (neighbors X z) := fun a _ b _ h => by
    simpa using sub_left_injective h
  rw [← Finset.card_image_of_injOn hinj]
  refine hk _ ?_ ?_
  · intro u hu
    simp only [Finset.mem_image, neighbors, Finset.mem_filter] at hu
    obtain ⟨w, ⟨_, hw2⟩, rfl⟩ := hu
    rw [← hw2, dist_eq_norm]
    exact norm_sub_rev w z
  · intro u hu v hv huv
    simp only [Finset.mem_image, neighbors, Finset.mem_filter] at hu hv
    obtain ⟨a, ⟨ha1, _⟩, rfl⟩ := hu
    obtain ⟨b, ⟨hb1, _⟩, rfl⟩ := hv
    have hab : a ≠ b := fun h => huv (by rw [h])
    have hd : dist (a - z) (b - z) = dist a b := by
      simp [dist_eq_norm, sub_sub_sub_cancel_right]
    rw [hd]
    exact hX a ha1 b hb1 hab

/- **The bulk bound**: a packing of `N` balls has at most `6N` contacts (`contactCount`
counts each twice). A handshake; all the content is in the kissing bound it assumes. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contactCount_le (hk : KissingBound3) {X : Finset E3} (hX : HardCore X) :
    contactCount X ≤ 12 * X.card := by
  calc contactCount X ≤ ∑ _z ∈ X, 12 :=
        Finset.sum_le_sum fun z _ => card_neighbors_le_twelve hk hX z
    _ = 12 * X.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/- ## Building the Delsarte machinery

`KissingBound3` has to come from somewhere. The route is Delsarte's linear-programming bound,
and computing it (`scripts/delsarte_lp.py`) shows exactly what is needed:

| Legendre degree | bound on the kissing number |
|---|---|
| 2 | infeasible |
| 3 | 24 |
| 4 | 14 |
| **5** | **13.2857 → ≤ 13** |
| 9–12 | 13.16, saturating |

`pd_nine` below is proved anyway: the LP cannot reach 12 at any degree, but Musin's cap
extension needs degree 9 specifically, and degrees 6–8 are worthless (identical LP optimum to
degree 5).

Two things follow. Degree 5 suffices for `≤ 13` — the Newton–Gregory bound. And the LP
**never** reaches 12 however high the degree goes, which is why Musin's cap extension exists.

The engine is: for unit vectors on `S²`, `∑ᵤ∑ᵥ Pₖ(⟨u,v⟩) ≥ 0` for every `k`. Each such fact
is an explicit sum of squares of the harmonic part of the `k`-th moment tensor. Below are the
skeleton and rungs `k = 1,2,3`; `k = 4,5` are the remaining work.
-/

/- Dot product in `ℝ³`, written out so no inner-product-space instances are involved. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def dot3 (u v : Fin 3 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/- The moment matrix `M a b = ∑ᵤ uₐ u_b`. Its harmonic (traceless) part is what makes the
degree-2 positivity a sum of squares. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
noncomputable def moment (S : Finset (Fin 3 → ℝ)) (a b : Fin 3) : ℝ := ∑ u ∈ S, u a * u b

/- **Degree 1 positivity**: `∑ᵤ∑ᵥ ⟨u,v⟩ = ‖∑ᵤ u‖² ≥ 0`. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem pd_one (S : Finset (Fin 3 → ℝ)) : 0 ≤ ∑ u ∈ S, ∑ v ∈ S, dot3 u v := by
  have h : ∑ u ∈ S, ∑ v ∈ S, dot3 u v
      = (∑ u ∈ S, u 0) ^ 2 + (∑ u ∈ S, u 1) ^ 2 + (∑ u ∈ S, u 2) ^ 2 := by
    simp only [dot3, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [h]; positivity

/- The double sum of squared inner products is the squared Frobenius norm of the moment
matrix. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem sq_sum_eq_moment (S : Finset (Fin 3 → ℝ)) :
    ∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 2 = ∑ a : Fin 3, ∑ b : Fin 3, (moment S a b) ^ 2 := by
  simp only [Fin.sum_univ_three, moment, sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  simp only [dot3]
  ring

/- The trace of the moment matrix is the number of unit vectors. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem trace_moment {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment S 0 0 + moment S 1 1 + moment S 2 2 = S.card := by
  simp only [moment, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun u hu => (by simpa [dot3] using hunit u hu : _ = (1:ℝ))]
  simp

/- **Degree 2 positivity**, stated as `N² ≤ 3∑∑⟨u,v⟩²` — which is exactly
`∑∑P₂(⟨u,v⟩) ≥ 0` for `P₂(t) = (3t²−1)/2`.

The content is `‖M‖²_F ≥ (tr M)²/3` for the moment matrix: dropping the off-diagonal squares
and then applying the power-mean inequality to the diagonal. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem pd_two {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    ((S.card : ℝ)) ^ 2 ≤ 3 * ∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 2 := by
  rw [sq_sum_eq_moment]
  have htr := trace_moment hunit
  have hdiag : (moment S 0 0) ^ 2 + (moment S 1 1) ^ 2 + (moment S 2 2) ^ 2
      ≤ ∑ a : Fin 3, ∑ b : Fin 3, (moment S a b) ^ 2 := by
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (moment S 0 1), sq_nonneg (moment S 0 2), sq_nonneg (moment S 1 0),
      sq_nonneg (moment S 1 2), sq_nonneg (moment S 2 0), sq_nonneg (moment S 2 1)]
  nlinarith [hdiag, htr, sq_nonneg (moment S 0 0 - moment S 1 1),
    sq_nonneg (moment S 0 0 - moment S 2 2), sq_nonneg (moment S 1 1 - moment S 2 2)]

/- ### Degree 3

`∑∑P₃(⟨u,v⟩) ≥ 0` is `5‖T‖² ≥ 3‖V‖²` for the third moment tensor `T` and the vector sum `V`.
The sum of squares realising it is the harmonic (trace-free) part

`H a b c = T a b c − (1/5)(δ_ab V_c + δ_ac V_b + δ_bc V_a)`,

for which `‖H‖² = ‖T‖² − (3/5)‖V‖²`. Note the coefficient is `1/(d+2) = 1/5`, not `1/3`;
the crude Cauchy–Schwarz bound only gives `9‖T‖² ≥ 3‖V‖²`, which is too weak. -/

/- The third moment tensor `T a b c = ∑ᵤ uₐ u_b u_c`. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
noncomputable def moment3 (S : Finset (Fin 3 → ℝ)) (a b c : Fin 3) : ℝ :=
  ∑ u ∈ S, u a * u b * u c

/- The vector sum `V a = ∑ᵤ uₐ`. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
noncomputable def vsum (S : Finset (Fin 3 → ℝ)) (a : Fin 3) : ℝ := ∑ u ∈ S, u a

/- The cube analogue of `sq_sum_eq_moment`. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem cube_sum_eq_moment3 (S : Finset (Fin 3 → ℝ)) :
    ∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 3
      = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, (moment3 S a b c) ^ 2 := by
  simp only [Fin.sum_univ_three, moment3, sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  simp only [dot3]
  ring

/- Contracting two indices of the third moment recovers the vector sum — this is where the
unit-length hypothesis enters. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract_moment3 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1)
    (a : Fin 3) : moment3 S a 0 0 + moment3 S a 1 1 + moment3 S a 2 2 = vsum S a := by
  simp only [moment3, vsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u a) * h

/- The pair sum of inner products is `‖V‖²`. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem sum_eq_vsum (S : Finset (Fin 3 → ℝ)) :
    ∑ u ∈ S, ∑ v ∈ S, dot3 u v = (vsum S 0) ^ 2 + (vsum S 1) ^ 2 + (vsum S 2) ^ 2 := by
  simp only [dot3, vsum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/- Any permutation of the indices leaves the third moment unchanged. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem moment3_perm {S : Finset (Fin 3 → ℝ)} {a b c a' b' c' : Fin 3}
    (h : ∀ u : Fin 3 → ℝ, u a * u b * u c = u a' * u b' * u c') :
    moment3 S a b c = moment3 S a' b' c' :=
  Finset.sum_congr rfl fun u _ => h u

/- **Degree 3 positivity**: `3∑∑⟨u,v⟩ ≤ 5∑∑⟨u,v⟩³`, i.e. `∑∑P₃(⟨u,v⟩) ≥ 0`.

The certificate is a positive *linear* combination of the ten distinct squares of the harmonic
tensor `H = T − (1/5)(δ⊗V symmetrised)`, verified symbolically in `scripts/harmonic_sos.py`.
Because it is linear in those squares, `linarith` suffices — `nlinarith` times out, since it
forms pairwise products it does not need. The seventeen non-canonical index orders have to be
identified with their sorted representatives first. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem pd_three {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    3 * ∑ u ∈ S, ∑ v ∈ S, dot3 u v ≤ 5 * ∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 3 := by
  rw [cube_sum_eq_moment3, sum_eq_vsum]
  have c0 := contract_moment3 hunit 0
  have c1 := contract_moment3 hunit 1
  have c2 := contract_moment3 hunit 2
  simp only [Fin.sum_univ_three]
  have e1 : moment3 S 0 1 0 = moment3 S 0 0 1 := moment3_perm fun u => by ring
  have e2 : moment3 S 0 2 0 = moment3 S 0 0 2 := moment3_perm fun u => by ring
  have e3 : moment3 S 0 2 1 = moment3 S 0 1 2 := moment3_perm fun u => by ring
  have e4 : moment3 S 1 0 0 = moment3 S 0 0 1 := moment3_perm fun u => by ring
  have e5 : moment3 S 1 0 1 = moment3 S 0 1 1 := moment3_perm fun u => by ring
  have e6 : moment3 S 1 0 2 = moment3 S 0 1 2 := moment3_perm fun u => by ring
  have e7 : moment3 S 1 1 0 = moment3 S 0 1 1 := moment3_perm fun u => by ring
  have e8 : moment3 S 1 2 0 = moment3 S 0 1 2 := moment3_perm fun u => by ring
  have e9 : moment3 S 1 2 1 = moment3 S 1 1 2 := moment3_perm fun u => by ring
  have e10 : moment3 S 2 0 0 = moment3 S 0 0 2 := moment3_perm fun u => by ring
  have e11 : moment3 S 2 0 1 = moment3 S 0 1 2 := moment3_perm fun u => by ring
  have e12 : moment3 S 2 0 2 = moment3 S 0 2 2 := moment3_perm fun u => by ring
  have e13 : moment3 S 2 1 0 = moment3 S 0 1 2 := moment3_perm fun u => by ring
  have e14 : moment3 S 2 1 1 = moment3 S 1 1 2 := moment3_perm fun u => by ring
  have e15 : moment3 S 2 1 2 = moment3 S 1 2 2 := moment3_perm fun u => by ring
  have e16 : moment3 S 2 2 0 = moment3 S 0 2 2 := moment3_perm fun u => by ring
  have e17 : moment3 S 2 2 1 = moment3 S 1 2 2 := moment3_perm fun u => by ring
  rw [← c0, ← c1, ← c2, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17]
  linarith [sq_nonneg (2 * moment3 S 0 0 0 - 3 * moment3 S 0 1 1 - 3 * moment3 S 0 2 2),
    sq_nonneg (4 * moment3 S 0 0 1 - moment3 S 1 1 1 - moment3 S 1 2 2),
    sq_nonneg (4 * moment3 S 0 0 2 - moment3 S 1 1 2 - moment3 S 2 2 2),
    sq_nonneg (3 * moment3 S 0 0 1 - 2 * moment3 S 1 1 1 + 3 * moment3 S 1 2 2),
    sq_nonneg (3 * moment3 S 0 0 2 + 3 * moment3 S 1 1 2 - 2 * moment3 S 2 2 2),
    sq_nonneg (moment3 S 0 0 0 + moment3 S 0 1 1 - 4 * moment3 S 0 2 2),
    sq_nonneg (moment3 S 0 0 0 - 4 * moment3 S 0 1 1 + moment3 S 0 2 2),
    sq_nonneg (moment3 S 0 0 1 + moment3 S 1 1 1 - 4 * moment3 S 1 2 2),
    sq_nonneg (moment3 S 0 0 2 - 4 * moment3 S 1 1 2 + moment3 S 2 2 2),
    sq_nonneg (moment3 S 0 1 2)]

/- ### Degrees 4 and 5, machine-generated

Grouping index tuples by sorted representative builds the multiplicities in and removes
symmetry bookkeeping entirely — the 17 hand-written rewrites at degree 3 would have become 66
and 222. Contractions are emitted in sorted form for the same reason: stated naively they
reintroduce non-canonical orders and silently break the normalisation.

SOS certificates come from `scripts/harmonic_sos.py`, which diagonalises each quadratic form
exactly over `ℚ`. -/

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem pow2_sum_eq (S : Finset (Fin 3 → ℝ)) :
    ∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 2 = 1 * (moment S 0 0) ^ 2 + 2 * (moment S 0 1) ^ 2 + 2 * (moment S 0 2) ^ 2 + 1 * (moment S 1 1) ^ 2 + 2 * (moment S 1 2) ^ 2 + 1 * (moment S 2 2) ^ 2 := by
  simp only [moment, sq, Finset.sum_mul_sum]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  simp only [dot3]
  ring

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem pow3_sum_eq (S : Finset (Fin 3 → ℝ)) :
    ∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 3 = 1 * (moment3 S 0 0 0) ^ 2 + 3 * (moment3 S 0 0 1) ^ 2 + 3 * (moment3 S 0 0 2) ^ 2 + 3 * (moment3 S 0 1 1) ^ 2 + 6 * (moment3 S 0 1 2) ^ 2 + 3 * (moment3 S 0 2 2) ^ 2 + 1 * (moment3 S 1 1 1) ^ 2 + 3 * (moment3 S 1 1 2) ^ 2 + 3 * (moment3 S 1 2 2) ^ 2 + 1 * (moment3 S 2 2 2) ^ 2 := by
  simp only [moment3, sq, Finset.sum_mul_sum]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  simp only [dot3]
  ring

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract3_0 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment3 S 0 0 0 + moment3 S 0 1 1 + moment3 S 0 2 2 = vsum S 0 := by
  simp only [moment3, vsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 0) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract3_1 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment3 S 0 0 1 + moment3 S 1 1 1 + moment3 S 1 2 2 = vsum S 1 := by
  simp only [moment3, vsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 1) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract3_2 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment3 S 0 0 2 + moment3 S 1 1 2 + moment3 S 2 2 2 = vsum S 2 := by
  simp only [moment3, vsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 2) * h

/- The 4-th moment tensor. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
noncomputable def moment4 (S : Finset (Fin 3 → ℝ)) (a : Fin 3) (b : Fin 3) (c : Fin 3) (d : Fin 3) : ℝ := ∑ u ∈ S, u a * u b * u c * u d

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem pow4_sum_eq (S : Finset (Fin 3 → ℝ)) :
    ∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 4 = 1 * (moment4 S 0 0 0 0) ^ 2 + 4 * (moment4 S 0 0 0 1) ^ 2 + 4 * (moment4 S 0 0 0 2) ^ 2 + 6 * (moment4 S 0 0 1 1) ^ 2 + 12 * (moment4 S 0 0 1 2) ^ 2 + 6 * (moment4 S 0 0 2 2) ^ 2 + 4 * (moment4 S 0 1 1 1) ^ 2 + 12 * (moment4 S 0 1 1 2) ^ 2 + 12 * (moment4 S 0 1 2 2) ^ 2 + 4 * (moment4 S 0 2 2 2) ^ 2 + 1 * (moment4 S 1 1 1 1) ^ 2 + 4 * (moment4 S 1 1 1 2) ^ 2 + 6 * (moment4 S 1 1 2 2) ^ 2 + 4 * (moment4 S 1 2 2 2) ^ 2 + 1 * (moment4 S 2 2 2 2) ^ 2 := by
  simp only [moment4, sq, Finset.sum_mul_sum]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  simp only [dot3]
  ring

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract4_0 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment4 S 0 0 0 0 + moment4 S 0 0 1 1 + moment4 S 0 0 2 2 = moment S 0 0 := by
  simp only [moment4, moment, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 0 * u 0) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract4_1 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment4 S 0 0 0 1 + moment4 S 0 1 1 1 + moment4 S 0 1 2 2 = moment S 0 1 := by
  simp only [moment4, moment, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 0 * u 1) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract4_2 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment4 S 0 0 0 2 + moment4 S 0 1 1 2 + moment4 S 0 2 2 2 = moment S 0 2 := by
  simp only [moment4, moment, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 0 * u 2) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract4_3 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment4 S 0 0 1 1 + moment4 S 1 1 1 1 + moment4 S 1 1 2 2 = moment S 1 1 := by
  simp only [moment4, moment, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 1 * u 1) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract4_4 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment4 S 0 0 1 2 + moment4 S 1 1 1 2 + moment4 S 1 2 2 2 = moment S 1 2 := by
  simp only [moment4, moment, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 1 * u 2) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract4_5 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment4 S 0 0 2 2 + moment4 S 1 1 2 2 + moment4 S 2 2 2 2 = moment S 2 2 := by
  simp only [moment4, moment, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 2 * u 2) * h

/- **Degree 4 positivity**: `∑∑P_4(⟨u,v⟩) ≥ 0`. SOS certificate: 9 squares. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem pd_four {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    30 * ∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 2
      ≤ 35 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 4) + 3 * ((S.card : ℝ)) ^ 2 := by
  have htr := trace_moment hunit
  rw [pow4_sum_eq, pow2_sum_eq, ← htr]
  rw [← contract4_0 hunit]
  rw [← contract4_1 hunit]
  rw [← contract4_2 hunit]
  rw [← contract4_3 hunit]
  rw [← contract4_4 hunit]
  rw [← contract4_5 hunit]
  linarith [sq_nonneg ((moment4 S 0 0 0 0) - 3*(moment4 S 0 0 1 1) - 3*(moment4 S 0 0 2 2) + 3*(moment4 S 1 1 1 1)/8 + 3*(moment4 S 1 1 2 2)/4 + 3*(moment4 S 2 2 2 2)/8),
    sq_nonneg ((moment4 S 0 0 0 1) - 3*(moment4 S 0 1 1 1)/4 - 3*(moment4 S 0 1 2 2)/4),
    sq_nonneg ((moment4 S 0 0 0 2) - 3*(moment4 S 0 1 1 2)/4 - 3*(moment4 S 0 2 2 2)/4),
    sq_nonneg ((moment4 S 0 0 1 1) - (moment4 S 0 0 2 2) - (moment4 S 1 1 1 1)/6 + (moment4 S 2 2 2 2)/6),
    sq_nonneg ((moment4 S 0 0 1 2) - (moment4 S 1 1 1 2)/6 - (moment4 S 1 2 2 2)/6),
    sq_nonneg ((moment4 S 0 1 1 1) - 3*(moment4 S 0 1 2 2)),
    sq_nonneg ((moment4 S 0 1 1 2) - (moment4 S 0 2 2 2)/3),
    sq_nonneg ((moment4 S 1 1 1 1) - 6*(moment4 S 1 1 2 2) + (moment4 S 2 2 2 2)),
    sq_nonneg ((moment4 S 1 1 1 2) - (moment4 S 1 2 2 2))]

/- The 5-th moment tensor. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
noncomputable def moment5 (S : Finset (Fin 3 → ℝ)) (a : Fin 3) (b : Fin 3) (c : Fin 3) (d : Fin 3) (e : Fin 3) : ℝ := ∑ u ∈ S, u a * u b * u c * u d * u e

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem pow5_sum_eq (S : Finset (Fin 3 → ℝ)) :
    ∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 5 = 1 * (moment5 S 0 0 0 0 0) ^ 2 + 5 * (moment5 S 0 0 0 0 1) ^ 2 + 5 * (moment5 S 0 0 0 0 2) ^ 2 + 10 * (moment5 S 0 0 0 1 1) ^ 2 + 20 * (moment5 S 0 0 0 1 2) ^ 2 + 10 * (moment5 S 0 0 0 2 2) ^ 2 + 10 * (moment5 S 0 0 1 1 1) ^ 2 + 30 * (moment5 S 0 0 1 1 2) ^ 2 + 30 * (moment5 S 0 0 1 2 2) ^ 2 + 10 * (moment5 S 0 0 2 2 2) ^ 2 + 5 * (moment5 S 0 1 1 1 1) ^ 2 + 20 * (moment5 S 0 1 1 1 2) ^ 2 + 30 * (moment5 S 0 1 1 2 2) ^ 2 + 20 * (moment5 S 0 1 2 2 2) ^ 2 + 5 * (moment5 S 0 2 2 2 2) ^ 2 + 1 * (moment5 S 1 1 1 1 1) ^ 2 + 5 * (moment5 S 1 1 1 1 2) ^ 2 + 10 * (moment5 S 1 1 1 2 2) ^ 2 + 10 * (moment5 S 1 1 2 2 2) ^ 2 + 5 * (moment5 S 1 2 2 2 2) ^ 2 + 1 * (moment5 S 2 2 2 2 2) ^ 2 := by
  simp only [moment5, sq, Finset.sum_mul_sum]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  simp only [dot3]
  ring

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract5_0 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment5 S 0 0 0 0 0 + moment5 S 0 0 0 1 1 + moment5 S 0 0 0 2 2 = moment3 S 0 0 0 := by
  simp only [moment5, moment3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 0 * u 0 * u 0) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract5_1 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment5 S 0 0 0 0 1 + moment5 S 0 0 1 1 1 + moment5 S 0 0 1 2 2 = moment3 S 0 0 1 := by
  simp only [moment5, moment3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 0 * u 0 * u 1) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract5_2 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment5 S 0 0 0 0 2 + moment5 S 0 0 1 1 2 + moment5 S 0 0 2 2 2 = moment3 S 0 0 2 := by
  simp only [moment5, moment3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 0 * u 0 * u 2) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract5_3 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment5 S 0 0 0 1 1 + moment5 S 0 1 1 1 1 + moment5 S 0 1 1 2 2 = moment3 S 0 1 1 := by
  simp only [moment5, moment3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 0 * u 1 * u 1) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract5_4 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment5 S 0 0 0 1 2 + moment5 S 0 1 1 1 2 + moment5 S 0 1 2 2 2 = moment3 S 0 1 2 := by
  simp only [moment5, moment3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 0 * u 1 * u 2) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract5_5 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment5 S 0 0 0 2 2 + moment5 S 0 1 1 2 2 + moment5 S 0 2 2 2 2 = moment3 S 0 2 2 := by
  simp only [moment5, moment3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 0 * u 2 * u 2) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract5_6 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment5 S 0 0 1 1 1 + moment5 S 1 1 1 1 1 + moment5 S 1 1 1 2 2 = moment3 S 1 1 1 := by
  simp only [moment5, moment3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 1 * u 1 * u 1) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract5_7 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment5 S 0 0 1 1 2 + moment5 S 1 1 1 1 2 + moment5 S 1 1 2 2 2 = moment3 S 1 1 2 := by
  simp only [moment5, moment3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 1 * u 1 * u 2) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract5_8 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment5 S 0 0 1 2 2 + moment5 S 1 1 1 2 2 + moment5 S 1 2 2 2 2 = moment3 S 1 2 2 := by
  simp only [moment5, moment3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 1 * u 2 * u 2) * h

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contract5_9 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    moment5 S 0 0 2 2 2 + moment5 S 1 1 2 2 2 + moment5 S 2 2 2 2 2 = moment3 S 2 2 2 := by
  simp only [moment5, moment3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h := hunit u hu
  simp only [dot3] at h
  linear_combination (u 2 * u 2 * u 2) * h

/- **Degree 5 positivity**: `∑∑P_5(⟨u,v⟩) ≥ 0`. SOS certificate: 11 squares. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem pd_five {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    70 * ∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 3
      ≤ 63 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 5) + 15 * ∑ u ∈ S, ∑ v ∈ S, dot3 u v := by
  rw [pow5_sum_eq, pow3_sum_eq, sum_eq_vsum]
  rw [← contract3_0 hunit]
  rw [← contract3_1 hunit]
  rw [← contract3_2 hunit]
  rw [← contract5_0 hunit]
  rw [← contract5_1 hunit]
  rw [← contract5_2 hunit]
  rw [← contract5_3 hunit]
  rw [← contract5_4 hunit]
  rw [← contract5_5 hunit]
  rw [← contract5_6 hunit]
  rw [← contract5_7 hunit]
  rw [← contract5_8 hunit]
  rw [← contract5_9 hunit]
  linarith [sq_nonneg ((moment5 S 0 0 0 0 0) - 5*(moment5 S 0 0 0 1 1) - 5*(moment5 S 0 0 0 2 2) + 15*(moment5 S 0 1 1 1 1)/8 + 15*(moment5 S 0 1 1 2 2)/4 + 15*(moment5 S 0 2 2 2 2)/8),
    sq_nonneg ((moment5 S 0 0 0 0 1) - 3*(moment5 S 0 0 1 1 1)/2 - 3*(moment5 S 0 0 1 2 2)/2 + (moment5 S 1 1 1 1 1)/8 + (moment5 S 1 1 1 2 2)/4 + (moment5 S 1 2 2 2 2)/8),
    sq_nonneg ((moment5 S 0 0 0 0 2) - 3*(moment5 S 0 0 1 1 2)/2 - 3*(moment5 S 0 0 2 2 2)/2 + (moment5 S 1 1 1 1 2)/8 + (moment5 S 1 1 2 2 2)/4 + (moment5 S 2 2 2 2 2)/8),
    sq_nonneg ((moment5 S 0 0 0 1 1) - (moment5 S 0 0 0 2 2) - (moment5 S 0 1 1 1 1)/2 + (moment5 S 0 2 2 2 2)/2),
    sq_nonneg ((moment5 S 0 0 0 1 2) - (moment5 S 0 1 1 1 2)/2 - (moment5 S 0 1 2 2 2)/2),
    sq_nonneg ((moment5 S 0 0 1 1 1) - 3*(moment5 S 0 0 1 2 2) - (moment5 S 1 1 1 1 1)/8 + (moment5 S 1 1 1 2 2)/4 + 3*(moment5 S 1 2 2 2 2)/8),
    sq_nonneg ((moment5 S 0 0 1 1 2) - (moment5 S 0 0 2 2 2)/3 - (moment5 S 1 1 1 1 2)/8 - (moment5 S 1 1 2 2 2)/12 + (moment5 S 2 2 2 2 2)/24),
    sq_nonneg ((moment5 S 0 1 1 1 1) - 6*(moment5 S 0 1 1 2 2) + (moment5 S 0 2 2 2 2)),
    sq_nonneg ((moment5 S 0 1 1 1 2) - (moment5 S 0 1 2 2 2)),
    sq_nonneg ((moment5 S 1 1 1 1 1) - 10*(moment5 S 1 1 1 2 2) + 5*(moment5 S 1 2 2 2 2)),
    sq_nonneg ((moment5 S 1 1 1 1 2) - 2*(moment5 S 1 1 2 2 2) + (moment5 S 2 2 2 2 2)/5)]


/- ### Degree 9

The one ingredient Musin's `13 → 12` argument needs beyond what is proved above.
Degrees 6, 7 and 8 are useless here: the linear program they generate has exactly the
same optimum as degree 5 (`scripts/delsarte_lp.py`), and degree 9 is the first that
clears the bar. So this is not an arbitrary jump.

Rather than the moment-tensor contractions used for degrees 3–5, this uses the
reproducing kernel of the space of harmonic polynomials directly: with `Q₁ … Q₁₉` an
orthogonal basis of the degree-9 harmonics,
`19·P₉(⟨u,v⟩) = ∑ₚ Qₚ(u)Qₚ(v)/‖Qₚ‖²`, so summing over pairs gives a sum of squares.
The basis is computed in `scripts/emit_pd9.py`. -/

/- Harmonic basis polynomial 0 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_0 (u : Fin 3 → ℝ) : ℝ := 9 * u 1 ^ 8*u 2 - 84 * u 1 ^ 6*u 2 ^ 3 + 126 * u 1 ^ 4*u 2 ^ 5 - 36 * u 1 ^ 2*u 2 ^ 7 + 1 * u 2 ^ 9

/- Harmonic basis polynomial 1 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_1 (u : Fin 3 → ℝ) : ℝ := 1 * u 1 ^ 9 - 36 * u 1 ^ 7*u 2 ^ 2 + 126 * u 1 ^ 5*u 2 ^ 4 - 84 * u 1 ^ 3*u 2 ^ 6 + 9 * u 1*u 2 ^ 8

/- Harmonic basis polynomial 2 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_2 (u : Fin 3 → ℝ) : ℝ := 1 * u 0*u 1 ^ 7*u 2 - 7 * u 0*u 1 ^ 5*u 2 ^ 3 + 7 * u 0*u 1 ^ 3*u 2 ^ 5 - 1 * u 0*u 1*u 2 ^ 7

/- Harmonic basis polynomial 3 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_3 (u : Fin 3 → ℝ) : ℝ := 1 * u 0*u 1 ^ 8 - 28 * u 0*u 1 ^ 6*u 2 ^ 2 + 70 * u 0*u 1 ^ 4*u 2 ^ 4 - 28 * u 0*u 1 ^ 2*u 2 ^ 6 + 1 * u 0*u 2 ^ 8

/- Harmonic basis polynomial 4 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_4 (u : Fin 3 → ℝ) : ℝ := 112 * u 0 ^ 2*u 1 ^ 6*u 2 - 560 * u 0 ^ 2*u 1 ^ 4*u 2 ^ 3 + 336 * u 0 ^ 2*u 1 ^ 2*u 2 ^ 5 - 16 * u 0 ^ 2*u 2 ^ 7 - 7 * u 1 ^ 8*u 2 + 28 * u 1 ^ 6*u 2 ^ 3 + 14 * u 1 ^ 4*u 2 ^ 5 - 20 * u 1 ^ 2*u 2 ^ 7 + 1 * u 2 ^ 9

/- Harmonic basis polynomial 5 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_5 (u : Fin 3 → ℝ) : ℝ := 16 * u 0 ^ 2*u 1 ^ 7 - 336 * u 0 ^ 2*u 1 ^ 5*u 2 ^ 2 + 560 * u 0 ^ 2*u 1 ^ 3*u 2 ^ 4 - 112 * u 0 ^ 2*u 1*u 2 ^ 6 - 1 * u 1 ^ 9 + 20 * u 1 ^ 7*u 2 ^ 2 - 14 * u 1 ^ 5*u 2 ^ 4 - 28 * u 1 ^ 3*u 2 ^ 6 + 7 * u 1*u 2 ^ 8

/- Harmonic basis polynomial 6 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_6 (u : Fin 3 → ℝ) : ℝ := 42 * u 0 ^ 3*u 1 ^ 5*u 2 - 140 * u 0 ^ 3*u 1 ^ 3*u 2 ^ 3 + 42 * u 0 ^ 3*u 1*u 2 ^ 5 - 9 * u 0*u 1 ^ 7*u 2 + 21 * u 0*u 1 ^ 5*u 2 ^ 3 + 21 * u 0*u 1 ^ 3*u 2 ^ 5 - 9 * u 0*u 1*u 2 ^ 7

/- Harmonic basis polynomial 7 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_7 (u : Fin 3 → ℝ) : ℝ := 14 * u 0 ^ 3*u 1 ^ 6 - 210 * u 0 ^ 3*u 1 ^ 4*u 2 ^ 2 + 210 * u 0 ^ 3*u 1 ^ 2*u 2 ^ 4 - 14 * u 0 ^ 3*u 2 ^ 6 - 3 * u 0*u 1 ^ 8 + 42 * u 0*u 1 ^ 6*u 2 ^ 2 - 42 * u 0*u 1 ^ 2*u 2 ^ 6 + 3 * u 0*u 2 ^ 8

/- Harmonic basis polynomial 8 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_8 (u : Fin 3 → ℝ) : ℝ := 280 * u 0 ^ 4*u 1 ^ 4*u 2 - 560 * u 0 ^ 4*u 1 ^ 2*u 2 ^ 3 + 56 * u 0 ^ 4*u 2 ^ 5 - 140 * u 0 ^ 2*u 1 ^ 6*u 2 + 140 * u 0 ^ 2*u 1 ^ 4*u 2 ^ 3 + 252 * u 0 ^ 2*u 1 ^ 2*u 2 ^ 5 - 28 * u 0 ^ 2*u 2 ^ 7 + 5 * u 1 ^ 8*u 2 - 14 * u 1 ^ 4*u 2 ^ 5 - 8 * u 1 ^ 2*u 2 ^ 7 + 1 * u 2 ^ 9

/- Harmonic basis polynomial 9 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_9 (u : Fin 3 → ℝ) : ℝ := 56 * u 0 ^ 4*u 1 ^ 5 - 560 * u 0 ^ 4*u 1 ^ 3*u 2 ^ 2 + 280 * u 0 ^ 4*u 1*u 2 ^ 4 - 28 * u 0 ^ 2*u 1 ^ 7 + 252 * u 0 ^ 2*u 1 ^ 5*u 2 ^ 2 + 140 * u 0 ^ 2*u 1 ^ 3*u 2 ^ 4 - 140 * u 0 ^ 2*u 1*u 2 ^ 6 + 1 * u 1 ^ 9 - 8 * u 1 ^ 7*u 2 ^ 2 - 14 * u 1 ^ 5*u 2 ^ 4 + 5 * u 1*u 2 ^ 8

/- Harmonic basis polynomial 10 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_10 (u : Fin 3 → ℝ) : ℝ := 8 * u 0 ^ 5*u 1 ^ 3*u 2 - 8 * u 0 ^ 5*u 1*u 2 ^ 3 - 8 * u 0 ^ 3*u 1 ^ 5*u 2 + 8 * u 0 ^ 3*u 1*u 2 ^ 5 + 1 * u 0*u 1 ^ 7*u 2 + 1 * u 0*u 1 ^ 5*u 2 ^ 3 - 1 * u 0*u 1 ^ 3*u 2 ^ 5 - 1 * u 0*u 1*u 2 ^ 7

/- Harmonic basis polynomial 11 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_11 (u : Fin 3 → ℝ) : ℝ := 8 * u 0 ^ 5*u 1 ^ 4 - 48 * u 0 ^ 5*u 1 ^ 2*u 2 ^ 2 + 8 * u 0 ^ 5*u 2 ^ 4 - 8 * u 0 ^ 3*u 1 ^ 6 + 40 * u 0 ^ 3*u 1 ^ 4*u 2 ^ 2 + 40 * u 0 ^ 3*u 1 ^ 2*u 2 ^ 4 - 8 * u 0 ^ 3*u 2 ^ 6 + 1 * u 0*u 1 ^ 8 - 4 * u 0*u 1 ^ 6*u 2 ^ 2 - 10 * u 0*u 1 ^ 4*u 2 ^ 4 - 4 * u 0*u 1 ^ 2*u 2 ^ 6 + 1 * u 0*u 2 ^ 8

/- Harmonic basis polynomial 12 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_12 (u : Fin 3 → ℝ) : ℝ := 192 * u 0 ^ 6*u 1 ^ 2*u 2 - 64 * u 0 ^ 6*u 2 ^ 3 - 360 * u 0 ^ 4*u 1 ^ 4*u 2 - 240 * u 0 ^ 4*u 1 ^ 2*u 2 ^ 3 + 120 * u 0 ^ 4*u 2 ^ 5 + 108 * u 0 ^ 2*u 1 ^ 6*u 2 + 180 * u 0 ^ 2*u 1 ^ 4*u 2 ^ 3 + 36 * u 0 ^ 2*u 1 ^ 2*u 2 ^ 5 - 36 * u 0 ^ 2*u 2 ^ 7 - 3 * u 1 ^ 8*u 2 - 8 * u 1 ^ 6*u 2 ^ 3 - 6 * u 1 ^ 4*u 2 ^ 5 + 1 * u 2 ^ 9

/- Harmonic basis polynomial 13 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_13 (u : Fin 3 → ℝ) : ℝ := 64 * u 0 ^ 6*u 1 ^ 3 - 192 * u 0 ^ 6*u 1*u 2 ^ 2 - 120 * u 0 ^ 4*u 1 ^ 5 + 240 * u 0 ^ 4*u 1 ^ 3*u 2 ^ 2 + 360 * u 0 ^ 4*u 1*u 2 ^ 4 + 36 * u 0 ^ 2*u 1 ^ 7 - 36 * u 0 ^ 2*u 1 ^ 5*u 2 ^ 2 - 180 * u 0 ^ 2*u 1 ^ 3*u 2 ^ 4 - 108 * u 0 ^ 2*u 1*u 2 ^ 6 - 1 * u 1 ^ 9 + 6 * u 1 ^ 5*u 2 ^ 4 + 8 * u 1 ^ 3*u 2 ^ 6 + 3 * u 1*u 2 ^ 8

/- Harmonic basis polynomial 14 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_14 (u : Fin 3 → ℝ) : ℝ := 32 * u 0 ^ 7*u 1*u 2 - 112 * u 0 ^ 5*u 1 ^ 3*u 2 - 112 * u 0 ^ 5*u 1*u 2 ^ 3 + 70 * u 0 ^ 3*u 1 ^ 5*u 2 + 140 * u 0 ^ 3*u 1 ^ 3*u 2 ^ 3 + 70 * u 0 ^ 3*u 1*u 2 ^ 5 - 7 * u 0*u 1 ^ 7*u 2 - 21 * u 0*u 1 ^ 5*u 2 ^ 3 - 21 * u 0*u 1 ^ 3*u 2 ^ 5 - 7 * u 0*u 1*u 2 ^ 7

/- Harmonic basis polynomial 15 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_15 (u : Fin 3 → ℝ) : ℝ := 32 * u 0 ^ 7*u 1 ^ 2 - 32 * u 0 ^ 7*u 2 ^ 2 - 112 * u 0 ^ 5*u 1 ^ 4 + 112 * u 0 ^ 5*u 2 ^ 4 + 70 * u 0 ^ 3*u 1 ^ 6 + 70 * u 0 ^ 3*u 1 ^ 4*u 2 ^ 2 - 70 * u 0 ^ 3*u 1 ^ 2*u 2 ^ 4 - 70 * u 0 ^ 3*u 2 ^ 6 - 7 * u 0*u 1 ^ 8 - 14 * u 0*u 1 ^ 6*u 2 ^ 2 + 14 * u 0*u 1 ^ 2*u 2 ^ 6 + 7 * u 0*u 2 ^ 8

/- Harmonic basis polynomial 16 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_16 (u : Fin 3 → ℝ) : ℝ := 128 * u 0 ^ 8*u 2 - 896 * u 0 ^ 6*u 1 ^ 2*u 2 - 896 * u 0 ^ 6*u 2 ^ 3 + 1120 * u 0 ^ 4*u 1 ^ 4*u 2 + 2240 * u 0 ^ 4*u 1 ^ 2*u 2 ^ 3 + 1120 * u 0 ^ 4*u 2 ^ 5 - 280 * u 0 ^ 2*u 1 ^ 6*u 2 - 840 * u 0 ^ 2*u 1 ^ 4*u 2 ^ 3 - 840 * u 0 ^ 2*u 1 ^ 2*u 2 ^ 5 - 280 * u 0 ^ 2*u 2 ^ 7 + 7 * u 1 ^ 8*u 2 + 28 * u 1 ^ 6*u 2 ^ 3 + 42 * u 1 ^ 4*u 2 ^ 5 + 28 * u 1 ^ 2*u 2 ^ 7 + 7 * u 2 ^ 9

/- Harmonic basis polynomial 17 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_17 (u : Fin 3 → ℝ) : ℝ := 128 * u 0 ^ 8*u 1 - 896 * u 0 ^ 6*u 1 ^ 3 - 896 * u 0 ^ 6*u 1*u 2 ^ 2 + 1120 * u 0 ^ 4*u 1 ^ 5 + 2240 * u 0 ^ 4*u 1 ^ 3*u 2 ^ 2 + 1120 * u 0 ^ 4*u 1*u 2 ^ 4 - 280 * u 0 ^ 2*u 1 ^ 7 - 840 * u 0 ^ 2*u 1 ^ 5*u 2 ^ 2 - 840 * u 0 ^ 2*u 1 ^ 3*u 2 ^ 4 - 280 * u 0 ^ 2*u 1*u 2 ^ 6 + 7 * u 1 ^ 9 + 28 * u 1 ^ 7*u 2 ^ 2 + 42 * u 1 ^ 5*u 2 ^ 4 + 28 * u 1 ^ 3*u 2 ^ 6 + 7 * u 1*u 2 ^ 8

/- Harmonic basis polynomial 18 of degree 9. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
def q9_18 (u : Fin 3 → ℝ) : ℝ := 128 * u 0 ^ 9 - 2304 * u 0 ^ 7*u 1 ^ 2 - 2304 * u 0 ^ 7*u 2 ^ 2 + 6048 * u 0 ^ 5*u 1 ^ 4 + 12096 * u 0 ^ 5*u 1 ^ 2*u 2 ^ 2 + 6048 * u 0 ^ 5*u 2 ^ 4 - 3360 * u 0 ^ 3*u 1 ^ 6 - 10080 * u 0 ^ 3*u 1 ^ 4*u 2 ^ 2 - 10080 * u 0 ^ 3*u 1 ^ 2*u 2 ^ 4 - 3360 * u 0 ^ 3*u 2 ^ 6 + 315 * u 0*u 1 ^ 8 + 1260 * u 0*u 1 ^ 6*u 2 ^ 2 + 1890 * u 0*u 1 ^ 4*u 2 ^ 4 + 1260 * u 0*u 1 ^ 2*u 2 ^ 6 + 315 * u 0*u 2 ^ 8

/- **The addition theorem at degree 9**, in homogeneous form so that it is a plain
polynomial identity — no unit-vector side conditions. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem kernel9 (u v : Fin 3 → ℝ) :
    19 * ((12155 * (dot3 u v) ^ 9 - 25740 * (dot3 u v) ^ 7 * (dot3 u u) * (dot3 v v)
        + 18018 * (dot3 u v) ^ 5 * ((dot3 u u) * (dot3 v v)) ^ 2
        - 4620 * (dot3 u v) ^ 3 * ((dot3 u u) * (dot3 v v)) ^ 3
        + 315 * (dot3 u v) * ((dot3 u u) * (dot3 v v)) ^ 4) / 128)
      = (230945/32768) * q9_0 u * q9_0 v + (230945/32768) * q9_1 u * q9_1 v + (2078505/256) * q9_2 u * q9_2 v + (2078505/16384) * q9_3 u * q9_3 v + (122265/32768) * q9_4 u * q9_4 v + (122265/32768) * q9_5 u * q9_5 v + (40755/512) * q9_6 u * q9_6 v + (40755/2048) * q9_7 u * q9_7 v + (24453/8192) * q9_8 u * q9_8 v + (24453/8192) * q9_9 u * q9_9 v + (855855/256) * q9_10 u * q9_10 v + (855855/4096) * q9_11 u * q9_11 v + (21945/8192) * q9_12 u * q9_12 v + (21945/8192) * q9_13 u * q9_13 v + (9405/512) * q9_14 u * q9_14 v + (9405/2048) * q9_15 u * q9_15 v + (855/16384) * q9_16 u * q9_16 v + (855/16384) * q9_17 u * q9_17 v + (19/16384) * q9_18 u * q9_18 v := by
  simp only [dot3, q9_0, q9_1, q9_2, q9_3, q9_4, q9_5, q9_6, q9_7, q9_8, q9_9, q9_10, q9_11, q9_12, q9_13, q9_14, q9_15, q9_16, q9_17, q9_18]
  ring

/- Pulling a weighted square out of a double sum. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem sq_expand (S : Finset (Fin 3 → ℝ)) (w : ℝ) (q : (Fin 3 → ℝ) → ℝ) :
    ∑ u ∈ S, ∑ v ∈ S, (w * q u * q v) = w * (∑ u ∈ S, q u) ^ 2 := by
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

/- **Degree 9 positivity**: `∑∑P₉(⟨u,v⟩) ≥ 0`. SOS certificate: 19 squares, one for
each dimension of the space of degree-9 harmonics. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem pd_nine {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    25740 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 7)
        + 4620 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 3)
      ≤ 12155 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 9)
        + 18018 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 5)
        + 315 * (∑ u ∈ S, ∑ v ∈ S, dot3 u v) := by
  have e0 : ∑ u ∈ S, ∑ v ∈ S, ((230945/32768) * q9_0 u * q9_0 v)
      = (230945/32768) * (∑ u ∈ S, q9_0 u) ^ 2 := sq_expand S _ _
  have e1 : ∑ u ∈ S, ∑ v ∈ S, ((230945/32768) * q9_1 u * q9_1 v)
      = (230945/32768) * (∑ u ∈ S, q9_1 u) ^ 2 := sq_expand S _ _
  have e2 : ∑ u ∈ S, ∑ v ∈ S, ((2078505/256) * q9_2 u * q9_2 v)
      = (2078505/256) * (∑ u ∈ S, q9_2 u) ^ 2 := sq_expand S _ _
  have e3 : ∑ u ∈ S, ∑ v ∈ S, ((2078505/16384) * q9_3 u * q9_3 v)
      = (2078505/16384) * (∑ u ∈ S, q9_3 u) ^ 2 := sq_expand S _ _
  have e4 : ∑ u ∈ S, ∑ v ∈ S, ((122265/32768) * q9_4 u * q9_4 v)
      = (122265/32768) * (∑ u ∈ S, q9_4 u) ^ 2 := sq_expand S _ _
  have e5 : ∑ u ∈ S, ∑ v ∈ S, ((122265/32768) * q9_5 u * q9_5 v)
      = (122265/32768) * (∑ u ∈ S, q9_5 u) ^ 2 := sq_expand S _ _
  have e6 : ∑ u ∈ S, ∑ v ∈ S, ((40755/512) * q9_6 u * q9_6 v)
      = (40755/512) * (∑ u ∈ S, q9_6 u) ^ 2 := sq_expand S _ _
  have e7 : ∑ u ∈ S, ∑ v ∈ S, ((40755/2048) * q9_7 u * q9_7 v)
      = (40755/2048) * (∑ u ∈ S, q9_7 u) ^ 2 := sq_expand S _ _
  have e8 : ∑ u ∈ S, ∑ v ∈ S, ((24453/8192) * q9_8 u * q9_8 v)
      = (24453/8192) * (∑ u ∈ S, q9_8 u) ^ 2 := sq_expand S _ _
  have e9 : ∑ u ∈ S, ∑ v ∈ S, ((24453/8192) * q9_9 u * q9_9 v)
      = (24453/8192) * (∑ u ∈ S, q9_9 u) ^ 2 := sq_expand S _ _
  have e10 : ∑ u ∈ S, ∑ v ∈ S, ((855855/256) * q9_10 u * q9_10 v)
      = (855855/256) * (∑ u ∈ S, q9_10 u) ^ 2 := sq_expand S _ _
  have e11 : ∑ u ∈ S, ∑ v ∈ S, ((855855/4096) * q9_11 u * q9_11 v)
      = (855855/4096) * (∑ u ∈ S, q9_11 u) ^ 2 := sq_expand S _ _
  have e12 : ∑ u ∈ S, ∑ v ∈ S, ((21945/8192) * q9_12 u * q9_12 v)
      = (21945/8192) * (∑ u ∈ S, q9_12 u) ^ 2 := sq_expand S _ _
  have e13 : ∑ u ∈ S, ∑ v ∈ S, ((21945/8192) * q9_13 u * q9_13 v)
      = (21945/8192) * (∑ u ∈ S, q9_13 u) ^ 2 := sq_expand S _ _
  have e14 : ∑ u ∈ S, ∑ v ∈ S, ((9405/512) * q9_14 u * q9_14 v)
      = (9405/512) * (∑ u ∈ S, q9_14 u) ^ 2 := sq_expand S _ _
  have e15 : ∑ u ∈ S, ∑ v ∈ S, ((9405/2048) * q9_15 u * q9_15 v)
      = (9405/2048) * (∑ u ∈ S, q9_15 u) ^ 2 := sq_expand S _ _
  have e16 : ∑ u ∈ S, ∑ v ∈ S, ((855/16384) * q9_16 u * q9_16 v)
      = (855/16384) * (∑ u ∈ S, q9_16 u) ^ 2 := sq_expand S _ _
  have e17 : ∑ u ∈ S, ∑ v ∈ S, ((855/16384) * q9_17 u * q9_17 v)
      = (855/16384) * (∑ u ∈ S, q9_17 u) ^ 2 := sq_expand S _ _
  have e18 : ∑ u ∈ S, ∑ v ∈ S, ((19/16384) * q9_18 u * q9_18 v)
      = (19/16384) * (∑ u ∈ S, q9_18 u) ^ 2 := sq_expand S _ _
  have hpt : ∀ u ∈ S, ∀ v ∈ S,
      19 * ((12155 * (dot3 u v) ^ 9 - 25740 * (dot3 u v) ^ 7
            + 18018 * (dot3 u v) ^ 5 - 4620 * (dot3 u v) ^ 3 + 315 * (dot3 u v)) / 128)
        = (230945/32768) * q9_0 u * q9_0 v + (230945/32768) * q9_1 u * q9_1 v + (2078505/256) * q9_2 u * q9_2 v + (2078505/16384) * q9_3 u * q9_3 v + (122265/32768) * q9_4 u * q9_4 v + (122265/32768) * q9_5 u * q9_5 v + (40755/512) * q9_6 u * q9_6 v + (40755/2048) * q9_7 u * q9_7 v + (24453/8192) * q9_8 u * q9_8 v + (24453/8192) * q9_9 u * q9_9 v + (855855/256) * q9_10 u * q9_10 v + (855855/4096) * q9_11 u * q9_11 v + (21945/8192) * q9_12 u * q9_12 v + (21945/8192) * q9_13 u * q9_13 v + (9405/512) * q9_14 u * q9_14 v + (9405/2048) * q9_15 u * q9_15 v + (855/16384) * q9_16 u * q9_16 v + (855/16384) * q9_17 u * q9_17 v + (19/16384) * q9_18 u * q9_18 v := by
    intro u hu v hv
    have h := kernel9 u v
    rw [hunit u hu, hunit v hv] at h
    rw [← h]; ring
  have hchain : ∑ u ∈ S, ∑ v ∈ S,
      19 * ((12155 * (dot3 u v) ^ 9 - 25740 * (dot3 u v) ^ 7
            + 18018 * (dot3 u v) ^ 5 - 4620 * (dot3 u v) ^ 3 + 315 * (dot3 u v)) / 128)
      = (230945/32768) * (∑ u ∈ S, q9_0 u) ^ 2 + (230945/32768) * (∑ u ∈ S, q9_1 u) ^ 2 + (2078505/256) * (∑ u ∈ S, q9_2 u) ^ 2 + (2078505/16384) * (∑ u ∈ S, q9_3 u) ^ 2 + (122265/32768) * (∑ u ∈ S, q9_4 u) ^ 2 + (122265/32768) * (∑ u ∈ S, q9_5 u) ^ 2 + (40755/512) * (∑ u ∈ S, q9_6 u) ^ 2 + (40755/2048) * (∑ u ∈ S, q9_7 u) ^ 2 + (24453/8192) * (∑ u ∈ S, q9_8 u) ^ 2 + (24453/8192) * (∑ u ∈ S, q9_9 u) ^ 2 + (855855/256) * (∑ u ∈ S, q9_10 u) ^ 2 + (855855/4096) * (∑ u ∈ S, q9_11 u) ^ 2 + (21945/8192) * (∑ u ∈ S, q9_12 u) ^ 2 + (21945/8192) * (∑ u ∈ S, q9_13 u) ^ 2 + (9405/512) * (∑ u ∈ S, q9_14 u) ^ 2 + (9405/2048) * (∑ u ∈ S, q9_15 u) ^ 2 + (855/16384) * (∑ u ∈ S, q9_16 u) ^ 2 + (855/16384) * (∑ u ∈ S, q9_17 u) ^ 2 + (19/16384) * (∑ u ∈ S, q9_18 u) ^ 2 := by
    rw [Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => hpt u hu v hv]
    simp only [Finset.sum_add_distrib, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18]
  have hagg : ∑ u ∈ S, ∑ v ∈ S,
      19 * ((12155 * (dot3 u v) ^ 9 - 25740 * (dot3 u v) ^ 7
            + 18018 * (dot3 u v) ^ 5 - 4620 * (dot3 u v) ^ 3 + 315 * (dot3 u v)) / 128)
      = 19 / 128 * (12155 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 9)
          - 25740 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 7)
          + 18018 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 5)
          - 4620 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 3)
          + 315 * (∑ u ∈ S, ∑ v ∈ S, dot3 u v)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  have hnn : (0:ℝ) ≤ (230945/32768) * (∑ u ∈ S, q9_0 u) ^ 2 + (230945/32768) * (∑ u ∈ S, q9_1 u) ^ 2 + (2078505/256) * (∑ u ∈ S, q9_2 u) ^ 2 + (2078505/16384) * (∑ u ∈ S, q9_3 u) ^ 2 + (122265/32768) * (∑ u ∈ S, q9_4 u) ^ 2 + (122265/32768) * (∑ u ∈ S, q9_5 u) ^ 2 + (40755/512) * (∑ u ∈ S, q9_6 u) ^ 2 + (40755/2048) * (∑ u ∈ S, q9_7 u) ^ 2 + (24453/8192) * (∑ u ∈ S, q9_8 u) ^ 2 + (24453/8192) * (∑ u ∈ S, q9_9 u) ^ 2 + (855855/256) * (∑ u ∈ S, q9_10 u) ^ 2 + (855855/4096) * (∑ u ∈ S, q9_11 u) ^ 2 + (21945/8192) * (∑ u ∈ S, q9_12 u) ^ 2 + (21945/8192) * (∑ u ∈ S, q9_13 u) ^ 2 + (9405/512) * (∑ u ∈ S, q9_14 u) ^ 2 + (9405/2048) * (∑ u ∈ S, q9_15 u) ^ 2 + (855/16384) * (∑ u ∈ S, q9_16 u) ^ 2 + (855/16384) * (∑ u ∈ S, q9_17 u) ^ 2 + (19/16384) * (∑ u ∈ S, q9_18 u) ^ 2 := by
    repeat' apply add_nonneg
    all_goals exact mul_nonneg (by norm_num) (sq_nonneg _)
  have hfin := hagg.symm.trans hchain
  linarith [hfin, hnn]


/- **The Delsarte bound.** If `f` is non-positive on the off-diagonal inner products and its
aggregated positivity gives `c₀N² ≤ ∑∑f`, then `N ≤ f(1)/c₀`.

The `hpos` hypothesis is what the degree-by-degree positivity facts above supply, once `f` is
written with non-negative Legendre coefficients. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem lp_bound {S : Finset (Fin 3 → ℝ)} {f : ℝ → ℝ} {c0 : ℝ} (hc0 : 0 < c0)
    (hne : S.Nonempty) (hunit : ∀ u ∈ S, dot3 u u = 1)
    (hoff : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → f (dot3 u v) ≤ 0)
    (hpos : c0 * (S.card : ℝ) ^ 2 ≤ ∑ u ∈ S, ∑ v ∈ S, f (dot3 u v)) :
    (S.card : ℝ) ≤ f 1 / c0 := by
  classical
  have hrow : ∀ u ∈ S, ∑ v ∈ S, f (dot3 u v) ≤ f 1 := by
    intro u hu
    rw [← Finset.add_sum_erase S _ hu, hunit u hu]
    have : ∑ v ∈ S.erase u, f (dot3 u v) ≤ 0 :=
      Finset.sum_nonpos fun v hv =>
        hoff u hu v (Finset.mem_of_mem_erase hv) (Ne.symm (Finset.ne_of_mem_erase hv))
    linarith
  have hle : ∑ u ∈ S, ∑ v ∈ S, f (dot3 u v) ≤ (S.card : ℝ) * f 1 := by
    calc ∑ u ∈ S, ∑ v ∈ S, f (dot3 u v) ≤ ∑ _u ∈ S, f 1 := Finset.sum_le_sum hrow
      _ = (S.card : ℝ) * f 1 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hN : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hne
  rw [le_div_iff₀ hc0]
  nlinarith [hpos, hle]


/- ## The bound: at most thirteen

Assembling the certificate. `f(t) = (t + 15/17)²(t + 7/22)²(t − 1/2)` has all six Legendre
coefficients positive (`c₀ = 121538/524535`), so degrees 1–5 positivity gives
`c₀N² ≤ ∑∑f`; and its factored form makes `f ≤ 0` on `t ≤ 1/2` immediate. Then
`N ≤ f(1)/c₀ = 807360/60769 = 13.2857… < 14`.

The rational certificate was found by exact search near the numerical LP optimum
(`scripts/delsarte_lp.py`); the true optimum `93/7` is not attained at nice rationals but is
not needed — anything below 14 suffices. -/

/- **At most thirteen unit vectors on `S²` can be pairwise at angle `≥ 60°`.**

This is the Newton–Gregory bound. It is *not* the kissing number, which is 12: no
linear-programming certificate can reach 12, since the LP optimum saturates near 13.16
(see `scripts/delsarte_lp.py`). Closing the last unit needs Musin's cap extension. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem card_le_thirteen {S : Finset (Fin 3 → ℝ)} (hne : S.Nonempty)
    (hunit : ∀ u ∈ S, dot3 u u = 1)
    (hcode : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → dot3 u v ≤ 1 / 2) :
    S.card ≤ 13 := by
  have hcard : ∑ u ∈ S, ∑ v ∈ S, (1 : ℝ) = ((S.card : ℝ)) ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]; ring
  -- expand ∑∑f in the monomial basis
  have hexp : ∑ u ∈ S, ∑ v ∈ S,
        ((dot3 u v + 15/17) ^ 2 * (dot3 u v + 7/22) ^ 2 * (dot3 u v - 1/2))
      = (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 5)
        + (711/374) * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 4)
        + (112215/139876) * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 3)
        + (-91561/279752) * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 2)
        + (-9030/34969) * (∑ u ∈ S, ∑ v ∈ S, dot3 u v)
        + (-11025/279752) * ((S.card : ℝ)) ^ 2 := by
    rw [← hcard]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have key := lp_bound (f := fun t => (t + 15/17) ^ 2 * (t + 7/22) ^ 2 * (t - 1/2))
    (c0 := 121538/524535) (by norm_num) hne hunit
    (fun u hu v hv huv => by
      have h := hcode u hu v hv huv
      nlinarith [mul_nonneg (sq_nonneg (dot3 u v + 15/17)) (sq_nonneg (dot3 u v + 7/22))])
    (by
      rw [hexp]
      linarith [pd_one S, pd_two hunit, pd_three hunit, pd_four hunit, pd_five hunit])
  norm_num at key
  have h14 : (S.card : ℝ) < 14 := lt_of_le_of_lt key (by norm_num)
  have : S.card < 14 := by exact_mod_cast h14
  omega


/- ## Musin's polynomial

`pd_nine` exists in order to run Musin's `13 → 12` argument, whose engine is the degree-9
polynomial

`f = P₀ + (8/5)P₁ + (87/25)P₂ + (33/20)P₃ + (49/25)P₄ + (1/10)P₅ + (8/25)P₉`

with every Legendre coefficient nonnegative and `c₀ = 1`. Two properties are needed of it, and
both are proved here: it is nonpositive on `[-59/100, 1/2]`, and — because of the nonnegative
coefficients — it aggregates to `S(X) ≥ N²`.

What is *not* here is Musin's Lemma 3, `S(X) < 13N`, which is where the remaining work is. -/

/- Musin's degree-9 polynomial, cleared of denominators. `f(1) = 1011/100`. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
noncomputable def musinF (t : ℝ) : ℝ :=
  (12155 * t ^ 9 - 25740 * t ^ 7 + 18333 * t ^ 5 + 3430 * t ^ 4 - 3320 * t ^ 3
    - 852 * t ^ 2 + 40 * t - 2) / 400

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem musinF_one : musinF 1 = 1011 / 100 := by rw [musinF]; norm_num

/- **Musin's polynomial is nonpositive on `[-59/100, 1/2]`.**

The certificate is Markov–Lukács: `-f = (t + 59/100)·s₁ + (1/2 - t)·s₂` with `s₁, s₂` sums of
squares, found by semidefinite programming and rounded to exact rationals (the rounding
fix-up decouples into 2×2 blocks, so the identity below holds in `ℚ` on the nose).

`f(1/2) = -37/204800`, so the bound is tight at the right endpoint; the interior margins are
about ten times larger. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem musin_f_nonpos {t : ℝ} (h1 : -59/100 ≤ t) (h2 : t ≤ 1/2) : musinF t ≤ 0 := by
  rw [musinF, div_nonpos_iff]
  refine Or.inr ⟨?_, by norm_num⟩
  have h3 : (0:ℝ) ≤ t + 59/100 := by linarith
  have h4 : (0:ℝ) ≤ 1/2 - t := by linarith
  have hs1 : (0:ℝ) ≤ (76759/54500) * ((1) + (-842134/76759) * t ^ 1 + (-464558/76759) * t ^ 2 + (3771727/76759) * t ^ 3 + (-132653/76759) * t ^ 4) ^ 2 + (2616739186267/4183365500) * ((1) * t ^ 1 + (431129169756/2616739186267) * t ^ 2 + (-22829378928093/5233478372534) * t ^ 3 + (418681567591/5233478372534) * t ^ 4) ^ 2 + (1777661204577598786/35653071412887875) * ((1) * t ^ 2 + (-4356941067553075609/14221289636620790288) * t ^ 3 + (-11789733994343664415/3555322409155197572) * t ^ 4) ^ 2 + (46353258851414245898271797/1550120570391666141392000) * ((1) * t ^ 3 + (-89878604644034594828810684/46353258851414245898271797) * t ^ 4) ^ 2 + (161868258469202893132067892075819/10105010429608305605823251746000) * ((1) * t ^ 4) ^ 2 := by positivity
  have hs2 : (0:ℝ) ≤ (6371219/2725000) * ((1) + (-56780825/6371219) * t ^ 1 + (-221468925/6371219) * t ^ 2 + (-55805275/6371219) * t ^ 3 + (214195900/6371219) * t ^ 4) ^ 2 + (3217439334398281/4340392943750) * ((1) * t ^ 1 + (19870226658908075/6434878668796562) * t ^ 2 + (360070864703775/415153462503004) * t ^ 3 + (-16272903313094925/6434878668796562) * t ^ 4) ^ 2 + (3894100270926675641793913/8767522186235315725000) * ((1) * t ^ 2 + (26386852109817979581690125/7788200541853351283587826) * t ^ 3 + (11175551424216615889376125/3894100270926675641793913) * t ^ 4) ^ 2 + (6680895412158831544502159412809751/10611423238275191123888412925000) * ((1) * t ^ 3 + (11275539445581133283917134528224150/6680895412158831544502159412809751) * t ^ 4) ^ 2 + (3866907613045866568310813169825566054/728217599925312638350735375996262859) * ((1) * t ^ 4) ^ 2 := by positivity
  nlinarith [mul_nonneg h3 hs1, mul_nonneg h4 hs2]

/- **Musin's Lemma 2**: `S(X) ≥ N²` for any set of unit vectors.

Immediate from the Legendre positivity rungs, since every coefficient of `f` is nonnegative
and the constant one is `1`. This is the half of Musin's argument that the linear-programming
machinery supplies; the other half, `S(X) < 13N`, is the open part. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem musin_lemma2 {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1) :
    ((S.card : ℝ)) ^ 2 ≤ ∑ u ∈ S, ∑ v ∈ S, musinF (dot3 u v) := by
  have hcard : ∑ u ∈ S, ∑ v ∈ S, (1 : ℝ) = ((S.card : ℝ)) ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]; ring
  have hexp : 400 * (∑ u ∈ S, ∑ v ∈ S, musinF (dot3 u v))
      = 12155 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 9)
        - 25740 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 7)
        + 18333 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 5)
        + 3430 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 4)
        - 3320 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 3)
        - 852 * (∑ u ∈ S, ∑ v ∈ S, (dot3 u v) ^ 2)
        + 40 * (∑ u ∈ S, ∑ v ∈ S, dot3 u v)
        - 2 * ((S.card : ℝ)) ^ 2 := by
    rw [← hcard]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [musinF]; ring
  linarith [pd_one S, pd_two hunit, pd_three hunit, pd_four hunit, pd_five hunit,
    pd_nine hunit, hexp]

/- **`f(s) ≤ f(-1) = 277/100` on `[-1, -59/100]`.**

The far half of the picture: a point deep in the cap contributes at most what the antipode
itself contributes. Markov–Lukács again, but `f(-1) = 277/100` *exactly*, so the polynomial
`1108 - 400f` has a genuine root at the left endpoint and the Gram matrix there is forced to
be singular. Dividing that root out first leaves a degree-8 problem that is strictly positive
and very well conditioned. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem musinF_le_antipode {s : ℝ} (h1 : -1 ≤ s) (h2 : s ≤ -59/100) :
    musinF s ≤ 277/100 := by
  have h3 : (0:ℝ) ≤ s + 1 := by linarith
  have h4 : (0:ℝ) ≤ -59/100 - s := by linarith
  have hs0 : (0:ℝ) ≤ (35603114833/4000000) * ((1) + (1509340609013/1780155741650) * s ^ 1 + (-10241552784/35603114833) * s ^ 2 + (10085189216/35603114833) * s ^ 3 + (15755402900/35603114833) * s ^ 4) ^ 2 + (3179788589364019615154631/356031148330000000000) * ((1) * s ^ 1 + (604008504460331379657700/1059929529788006538384877) * s ^ 2 + (-1179707744912929194870400/3179788589364019615154631) * s ^ 3 + (16363887445731573105000/1059929529788006538384877) * s ^ 4) ^ 2 + (900540702154730556505519399459272333/105992952978800653838487700000000) * ((1) * s ^ 2 + (807694259683317744885137378001063359/1801081404309461113011038798918544666) * s ^ 3 + (-444293271660575187268775948381816800/900540702154730556505519399459272333) * s ^ 4) ^ 2 + (4084651109103329394814576343442985793382100524643/360216280861892222602207759783708933200000000) * ((1) * s ^ 3 + (3855005076418804734659875742891127631865088730468/4084651109103329394814576343442985793382100524643) * s ^ 4) ^ 2 + (296950049373516718456396446358977384488424406011291626196151/306348833182749704611093225758223934503657539348225000000) * ((1) * s ^ 4) ^ 2 := by positivity
  have hs1 : (0:ℝ) ≤ (528188387/40000) * ((1) + (-4027188384/13204709675) * s ^ 1 + (72781289/2640941935) * s ^ 2 + (-517044726/2640941935) * s ^ 3) ^ 2 + (74469497772628270947/6602354837500000) * ((1) * s ^ 1 + (-918715570409667015/49646331848418847298) * s ^ 2 + (19777273403232150565/74469497772628270947) * s ^ 3) ^ 2 + (1172697552184277282706000807643/49646331848418847298000000) * ((1) * s ^ 2 + (-871746286494808151842503424670/1172697552184277282706000807643) * s ^ 3) ^ 2 + (22310367357327284425966292475722388918889/1759046328276415924059001211464500000) * ((1) * s ^ 3) ^ 2 := by positivity
  have key : (0:ℝ) ≤ (s + 1) * (((35603114833/4000000) * ((1) + (1509340609013/1780155741650) * s ^ 1 + (-10241552784/35603114833) * s ^ 2 + (10085189216/35603114833) * s ^ 3 + (15755402900/35603114833) * s ^ 4) ^ 2 + (3179788589364019615154631/356031148330000000000) * ((1) * s ^ 1 + (604008504460331379657700/1059929529788006538384877) * s ^ 2 + (-1179707744912929194870400/3179788589364019615154631) * s ^ 3 + (16363887445731573105000/1059929529788006538384877) * s ^ 4) ^ 2 + (900540702154730556505519399459272333/105992952978800653838487700000000) * ((1) * s ^ 2 + (807694259683317744885137378001063359/1801081404309461113011038798918544666) * s ^ 3 + (-444293271660575187268775948381816800/900540702154730556505519399459272333) * s ^ 4) ^ 2 + (4084651109103329394814576343442985793382100524643/360216280861892222602207759783708933200000000) * ((1) * s ^ 3 + (3855005076418804734659875742891127631865088730468/4084651109103329394814576343442985793382100524643) * s ^ 4) ^ 2 + (296950049373516718456396446358977384488424406011291626196151/306348833182749704611093225758223934503657539348225000000) * ((1) * s ^ 4) ^ 2) + (s + 1) * (-59/100 - s) * ((528188387/40000) * ((1) + (-4027188384/13204709675) * s ^ 1 + (72781289/2640941935) * s ^ 2 + (-517044726/2640941935) * s ^ 3) ^ 2 + (74469497772628270947/6602354837500000) * ((1) * s ^ 1 + (-918715570409667015/49646331848418847298) * s ^ 2 + (19777273403232150565/74469497772628270947) * s ^ 3) ^ 2 + (1172697552184277282706000807643/49646331848418847298000000) * ((1) * s ^ 2 + (-871746286494808151842503424670/1172697552184277282706000807643) * s ^ 3) ^ 2 + (22310367357327284425966292475722388918889/1759046328276415924059001211464500000) * ((1) * s ^ 3) ^ 2)) :=
    mul_nonneg h3 (add_nonneg hs0 (mul_nonneg (mul_nonneg h3 h4) hs1))
  rw [musinF, div_le_iff₀ (by norm_num : (0:ℝ) < 400)]
  nlinarith [key]

/- **`h₀ < 13` and `h₁ < 13`**, the first two cases of Musin's Lemma 3.

`h₀ = f(1) = 1011/100`. `h₁ = f(1) + f(-1) = 1288/100 = 12.88`: a single point in the cap
contributes at most `f(-1)`. Both are comfortably under `13`; the remaining cases `h₂, h₃, h₄`
need the geometry of several points in the cap and are not proved here. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem musin_h_zero : musinF 1 < 13 := by rw [musinF]; norm_num

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem musin_h_one {s : ℝ} (h1 : -1 ≤ s) (h2 : s ≤ -59/100) :
    musinF 1 + musinF s < 13 := by
  have h := musinF_le_antipode h1 h2
  have h0 : musinF 1 = 1011/100 := by rw [musinF]; norm_num
  rw [h0]
  linarith

/- ## Harvesting thirteen

`card_le_thirteen` is unconditional, so the physics it implies should be too. It is stated
for `Fin 3 → ℝ` with `dot3`; the configurations live in `EuclideanSpace ℝ (Fin 3)` with its
norm. The two are the same type, and these lemmas are the dictionary. -/

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem dot3_eq_inner (u v : E3) : dot3 u v = inner ℝ u v := by
  rw [PiLp.inner_apply]
  simp [dot3, Fin.sum_univ_three, RCLike.inner_apply]
  ring

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem dot3_self_of_norm {u : E3} (h : ‖u‖ = 1) : dot3 u u = 1 := by
  rw [dot3_eq_inner, real_inner_self_eq_norm_sq, h]
  norm_num

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem dot3_le_half {u v : E3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (h : 1 ≤ dist u v) :
    dot3 u v ≤ 1 / 2 := by
  have hsq : (1 : ℝ) ≤ dist u v ^ 2 := by nlinarith [dist_nonneg (x := u) (y := v)]
  rw [dist_eq_norm, norm_sub_sq_real, hu, hv] at hsq
  rw [dot3_eq_inner]
  linarith

/- **The Newton–Gregory bound, in the configuration's own language.**

`EuclideanSpace ℝ (Fin 3)` is `WithLp 2 (Fin 3 → ℝ)`, which is a *structure*, not a type
synonym — so the plain-function statement has to be transported across `WithLp.ofLp`. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem kissing_le_thirteen (S : Finset E3) (hunit : ∀ u ∈ S, ‖u‖ = 1)
    (hsep : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → 1 ≤ dist u v) : S.card ≤ 13 := by
  classical
  have hinj : Set.InjOn (fun u : E3 => WithLp.ofLp u) ↑S :=
    fun a _ b _ h => WithLp.ofLp_injective _ h
  rw [← Finset.card_image_of_injOn hinj]
  set T : Finset (Fin 3 → ℝ) := S.image (fun u : E3 => WithLp.ofLp u) with hT
  have hmem : ∀ x ∈ T, ∃ w ∈ S, WithLp.ofLp w = x := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨w, hw, rfl⟩
  rcases T.eq_empty_or_nonempty with h | hne
  · simp [h]
  refine card_le_thirteen hne (fun x hx => ?_) (fun x hx y hy hxy => ?_)
  · obtain ⟨w, hw, rfl⟩ := hmem x hx
    exact dot3_self_of_norm (hunit w hw)
  · obtain ⟨w, hw, rfl⟩ := hmem x hx
    obtain ⟨w', hw', rfl⟩ := hmem y hy
    exact dot3_le_half (hunit w hw) (hunit w' hw')
      (hsep w hw w' hw' fun h => hxy (by rw [h]))

/- **Unconditional**: no particle has more than thirteen bonds. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem card_neighbors_le_thirteen {X : Finset E3} (hX : HardCore X) (z : E3) :
    (neighbors X z).card ≤ 13 := by
  classical
  have hinj : Set.InjOn (· - z) (neighbors X z) := fun a _ b _ h => by
    simpa using sub_left_injective h
  rw [← Finset.card_image_of_injOn hinj]
  refine kissing_le_thirteen _ ?_ ?_
  · intro u hu
    simp only [Finset.mem_image, neighbors, Finset.mem_filter] at hu
    obtain ⟨w, ⟨_, hw2⟩, rfl⟩ := hu
    rw [← hw2, dist_eq_norm]
    exact norm_sub_rev w z
  · intro u hu v hv huv
    simp only [Finset.mem_image, neighbors, Finset.mem_filter] at hu hv
    obtain ⟨a, ⟨ha1, _⟩, rfl⟩ := hu
    obtain ⟨b, ⟨hb1, _⟩, rfl⟩ := hv
    have hab : a ≠ b := fun h => huv (by rw [h])
    have hd : dist (a - z) (b - z) = dist a b := by
      simp [dist_eq_norm, sub_sub_sub_cancel_right]
    rw [hd]
    exact hX a ha1 b hb1 hab

/- **Unconditional bulk bound**, `2E ≤ 13N`. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem contactCount_le_thirteen {X : Finset E3} (hX : HardCore X) :
    contactCount X ≤ 13 * X.card := by
  calc contactCount X ≤ ∑ _z ∈ X, 13 :=
        Finset.sum_le_sum fun z _ => card_neighbors_le_thirteen hX z
    _ = 13 * X.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/- The energy of a hard-core configuration in space: `-1` per bond. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
noncomputable def energy (X : Finset E3) : ℝ := -(contactCount X : ℝ) / 2

/- **`E ≥ −6.5N`, unconditionally.**

The kissing bound `12` would give `−6N`, and that is the true constant; `13` is what a
linear-programming certificate can prove, and `13.158` is what the method can *ever* prove
(`scripts/delsarte_lp.py`). The gap of one half per particle is the whole thirteen-spheres
problem. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem energy_ge_thirteen {X : Finset E3} (hX : HardCore X) :
    -(13 / 2 : ℝ) * X.card ≤ energy X := by
  have h := contactCount_le_thirteen hX
  have hr : (contactCount X : ℝ) ≤ 13 * (X.card : ℝ) := by exact_mod_cast h
  rw [energy]
  linarith

/- The conditional bound, for comparison: the kissing number `12` gives `−6N`. -/
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem energy_ge_twelve (hk : KissingBound3) {X : Finset E3} (hX : HardCore X) :
    -6 * (X.card : ℝ) ≤ energy X := by
  have h := contactCount_le hk hX
  have hr : (contactCount X : ℝ) ≤ 12 * (X.card : ℝ) := by exact_mod_cast h
  rw [energy]
  linarith

end Kissing3D

/- A small integer sum-of-squares certificate checker for four-variable polynomials.
Each monomial stores its four exponents. Certificate checking only uses integer arithmetic. -/
namespace OMA.Sos1084

abbrev Exp := ℕ × ℕ × ℕ × ℕ
abbrev Term := Exp × ℤ
abbrev Poly := List Term
abbrev Point := ℝ × ℝ × ℝ × ℝ

def mon (x : Point) (e : Exp) : ℝ :=
  x.1 ^ e.1 * x.2.1 ^ e.2.1 * x.2.2.1 ^ e.2.2.1 * x.2.2.2 ^ e.2.2.2

def value (x : Point) : Poly → ℝ
  | [] => 0
  | (e, c) :: p => c * mon x e + value x p

def insertTerm (a : Term) : Poly → Poly
  | [] => [a]
  | b :: p => if a.1 = b.1 then (b.1, a.2 + b.2) :: p else b :: insertTerm a p

theorem value_insert (x : Point) (a : Term) (p : Poly) :
    value x (insertTerm a p) = a.2 * mon x a.1 + value x p := by
  induction p with
  | nil => simp [insertTerm, value]
  | cons b p ih =>
    rcases a with ⟨i, c⟩
    rcases b with ⟨j, d⟩
    by_cases h : i = j
    · subst j; simp [insertTerm, value, add_mul]; ring
    · simp [insertTerm, h, value, ih]; ring

def add : Poly → Poly → Poly
  | [], q => q
  | t :: p, q => insertTerm t (add p q)

theorem value_add (x : Point) (p q : Poly) :
    value x (add p q) = value x p + value x q := by
  induction p with
  | nil => simp [add, value]
  | cons t p ih => rcases t with ⟨e, c⟩; simp [add, value_insert, value, ih, add_assoc]

def timesTerm (t u : Term) : Term :=
  ((t.1.1 + u.1.1, t.1.2.1 + u.1.2.1, t.1.2.2.1 + u.1.2.2.1, t.1.2.2.2 + u.1.2.2.2),
    t.2 * u.2)

theorem value_map (x : Point) (t : Term) (p : Poly) :
    value x (p.map (timesTerm t)) = t.2 * mon x t.1 * value x p := by
  induction p with
  | nil => simp [value]
  | cons u p ih =>
    simp [value, timesTerm, ih, mon, pow_add, Int.cast_mul]
    ring

def prod : Poly → Poly → Poly
  | [], _ => []
  | t :: p, q => add (q.map (timesTerm t)) (prod p q)

theorem value_prod (x : Point) (p q : Poly) :
    value x (prod p q) = value x p * value x q := by
  induction p with
  | nil => simp [prod, value]
  | cons t p ih => rcases t with ⟨e, c⟩; simp [prod, value_add, value_map, ih, value, add_mul]

def scale (c : ℤ) (p : Poly) : Poly := p.map fun t => (t.1, c * t.2)

theorem value_scale (x : Point) (c : ℤ) (p : Poly) :
    value x (scale c p) = c * value x p := by
  induction p with
  | nil => simp [scale, value]
  | cons t p ih =>
    change (↑(c * t.2) : ℝ) * mon x t.1 + value x (scale c p) =
      ↑c * (↑t.2 * mon x t.1 + value x p)
    rw [Int.cast_mul, ih]
    ring

abbrev Block := List (ℕ × Poly)
def squares : Block → Poly
  | [] => []
  | (w, f) :: s => add (scale w (prod f f)) (squares s)

theorem squares_nonneg (x : Point) (s : Block) : 0 ≤ value x (squares s) := by
  induction s with
  | nil => simp [squares, value]
  | cons t s ih =>
    rcases t with ⟨w, f⟩
    rw [squares, value_add, value_scale, value_prod]
    exact add_nonneg (mul_nonneg (by positivity) (mul_self_nonneg _)) ih

def zeroCoeffs (p : Poly) : Bool := p.all fun t => t.2 == 0

theorem value_zero (x : Point) (p : Poly) (h : zeroCoeffs p = true) : value x p = 0 := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨e, c⟩
    obtain ⟨hc, hp⟩ : c = 0 ∧ zeroCoeffs p = true := by simpa [zeroCoeffs] using h
    simp [value, hc, ih hp]

theorem block_nonneg (x : Point) (s : Block) (p : Poly)
    (h : zeroCoeffs (add (squares s) (scale (-1) p)) = true) : 0 ≤ value x p := by
  have hz := value_zero x _ h
  rw [value_add, value_scale] at hz
  have hs := squares_nonneg x s
  norm_num at hz
  linarith

def factors : List (Poly × Poly) → Poly
  | [] => []
  | (p, q) :: l => add (prod p q) (factors l)

theorem factors_cons (x : Point) (p q : Poly) (l : List (Poly × Poly)) :
    value x (factors ((p,q)::l)) = value x p * value x q + value x (factors l) := by
  rw [factors, value_add, value_prod]

theorem transfer (x : Point) (l : List (Poly × Poly)) (p : Poly)
    (h : zeroCoeffs (add (factors l) (scale (-1) p)) = true)
    (hn : 0 ≤ value x (factors l)) : 0 ≤ value x p := by
  have hz := value_zero x _ h
  rw [value_add, value_scale] at hz
  norm_num at hz
  linarith

def term (key : ℕ) (c : ℤ) : Term :=
  ((key / 512, key / 64 % 8, key / 8 % 8, key % 8), c)

end OMA.Sos1084

namespace OMA.Sos1084

private noncomputable def majorant (c : ℝ) : ℝ := (131550023/1000000) + (-472486271/500000) * c ^ 1 + (2712544477/1000000) * c ^ 2 + (-970588931/250000) * c ^ 3 + (2760056463/1000000) * c ^ 4 + (-774046303/1000000) * c ^ 5

namespace Dim1

set_option maxHeartbeats 3000000 in
private def b0 : Block := [
  (200000000, [term 0 (12592), term 512 (-4537), term 1024 (-7980)]),
  (800000000, [term 512 (4727), term 1024 (-4659)]),
  (200000000, [term 1024 (1671)]),
  (84479194285, [term 0 (1), term 512 (-1)]),
  (1763811379830, [term 0 (1), term 1024 (-1)]),
  (386075365770, [term 512 (1), term 1024 (-1)]),
  (187783044150479, [term 0 (1)]),
  (186632445439945, [term 512 (1)]),
  (188291374127770, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p0 : Poly := [term 0 (31901324134724594), term 512 (-22852130558388570), term 1024 (-18017591622759660), term 1536 (-20755616950731540), term 2048 (30849994260873370)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id0 : zeroCoeffs (add (squares b0) (scale (-1) p0)) = true := by rfl

private theorem pos0 (x : Point) : 0 ≤ value x p0 := block_nonneg x b0 p0 id0

set_option maxHeartbeats 3000000 in
private def b1 : Block := [
  (200000000, [term 0 (8167)]),
  (13343022200000000, [term 0 (1)])
]

set_option maxHeartbeats 3000000 in
private def p1 : Poly := [term 0 (26683000000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id1 : zeroCoeffs (add (squares b1) (scale (-1) p1)) = true := by rfl

private theorem pos1 (x : Point) : 0 ≤ value x p1 := block_nonneg x b1 p1 id1

set_option maxHeartbeats 3000000 in
private def b2 : Block := [
  (800000000, [term 0 (4201)]),
  (14121479200000000, [term 0 (1)])
]

set_option maxHeartbeats 3000000 in
private def p2 : Poly := [term 0 (28240200000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id2 : zeroCoeffs (add (squares b2) (scale (-1) p2)) = true := by rfl

private theorem pos2 (x : Point) : 0 ≤ value x p2 := block_nonneg x b2 p2 id2

set_option maxHeartbeats 3000000 in
private def b3 : Block := [
  (200000000, [term 0 (11363)]),
  (25826046200000000, [term 0 (1)])
]

set_option maxHeartbeats 3000000 in
private def p3 : Poly := [term 0 (51649600000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id3 : zeroCoeffs (add (squares b3) (scale (-1) p3)) = true := by rfl

private theorem pos3 (x : Point) : 0 ≤ value x p3 := block_nonneg x b3 p3 id3

set_option maxHeartbeats 3000000 in
private def b4 : Block := [
  (800000000, [term 0 (9132), term 512 (-4435), term 1024 (-4671)]),
  (200000000, [term 512 (29463), term 1024 (-29415)]),
  (3200000000, [term 1024 (419)]),
  (264000000000, [term 0 (1), term 512 (-1)]),
  (142400000000, [term 0 (1), term 1024 (-1)]),
  (1121000000000, [term 512 (1), term 1024 (1)]),
  (187454400000000, [term 0 (1)]),
  (190161200000000, [term 512 (1)]),
  (181244336281806, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p4 : Poly := [term 0 (66902600000000000), term 512 (-64801200000000000), term 1024 (121291400000000000), term 1536 (-313514000000000000), term 2048 (191247340736281806)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id4 : zeroCoeffs (add (squares b4) (scale (-1) p4)) = true := by rfl

private theorem pos4 (x : Point) : 0 ≤ value x p4 := block_nonneg x b4 p4 id4

set_option maxHeartbeats 3000000 in
private def b5 : Block := [
  (200000000, [term 0 (10817), term 512 (-4127), term 1024 (-4970)]),
  (800000000, [term 512 (3666), term 1024 (-1519)]),
  (200000000, [term 1024 (4513)]),
  (151800000000, [term 0 (1), term 512 (1)]),
  (1098000000000, [term 0 (1), term 1024 (1)]),
  (514800000000, [term 512 (1), term 1024 (-1)]),
  (2352452400000000, [term 0 (1)]),
  (2353462800000000, [term 512 (1)]),
  (2353084600000000, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p5 : Poly := [term 0 (25755200000000000), term 512 (-17856400000000000), term 1024 (-4989800000000000), term 1536 (-706400000000000), term 2048 (13214200000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id5 : zeroCoeffs (add (squares b5) (scale (-1) p5)) = true := by rfl

private theorem pos5 (x : Point) : 0 ≤ value x p5 := block_nonneg x b5 p5 id5

private def cap : Poly := [term 1024 (10958439), term 1536 (-8132678), term 2048 (-2825761)]

private def con : Poly := [term 0 (50000000)]

private def v0 : Poly := [term 512 (1)]

private def u0 : Poly := [term 0 (1), term 512 (-1)]

set_option maxHeartbeats 3000000 in
private def target : Poly := [term 0 (2882826206736229700000000), term 512 (21943472080571500000000), term 1024 (-2639206562326583000000000), term 1536 (4347374857834023000000000), term 2048 (-13468138380691731500000000), term 2560 (8967806406367490300000000)]

private def products : List (Poly × Poly) := [(p0, con), (p1, cap), (p2, (prod cap v0)), (p3, (prod cap u0)), (p4, (scale 50000000 v0)), (p5, (scale 50000000 u0))]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem combined : zeroCoeffs (add (factors products) (scale (-1) target)) = true := by rfl

set_option maxHeartbeats 3000000 in
theorem certificate (x₁ : ℝ) (h0 : 0 ≤ x₁) (u0h : x₁ ≤ 1)
    (hc : (0 : ℝ) ≤ (-2825761*x₁^4/50000000 - 4066339*x₁^3/25000000 + 10958439*x₁^2/50000000)) :
    0 ≤ 2889/1000 - majorant ((41*x₁+59)/100) := by
  let x : Point := (x₁, 0, 0, 0)
  have posCap : 0 ≤ value x cap := by
    have eqCap : value x cap = 50000000 * (-2825761*x₁^4/50000000 - 4066339*x₁^3/25000000 + 10958439*x₁^2/50000000) := by
      norm_num [x, cap, value, term, mon]; ring
    rw [eqCap]; exact mul_nonneg (by norm_num) hc
  have posCon : 0 ≤ value x con := by norm_num [x, con, value, term, mon]
  have posV0 : 0 ≤ value x v0 := by simpa [x, v0, value, term, mon] using h0
  have posU0 : 0 ≤ value x u0 := by simpa [x, u0, value, term, mon] using (sub_nonneg.mpr u0h)
  have allPos : 0 ≤ value x (factors products) := by
    unfold products
    simp only [factors_cons]
    exact (add_nonneg (mul_nonneg (pos0 x) posCon) (add_nonneg (mul_nonneg (pos1 x) posCap) (add_nonneg (mul_nonneg (pos2 x) (by rw [value_prod]; exact mul_nonneg posCap posV0)) (add_nonneg (mul_nonneg (pos3 x) (by rw [value_prod]; exact mul_nonneg posCap posU0)) (add_nonneg (mul_nonneg (pos4 x) (by rw [value_scale]; exact mul_nonneg (by norm_num) posV0)) (add_nonneg (mul_nonneg (pos5 x) (by rw [value_scale]; exact mul_nonneg (by norm_num) posU0)) (le_refl 0)))))))
  have result := transfer x products target combined allPos
  have eqTarget : value x target = 1000000000000000000000000 * (2889/1000 - majorant ((41*x₁+59)/100)) := by
    norm_num [x, target, value, term, mon, majorant]; ring
  rw [eqTarget] at result
  exact (mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < 1000000000000000000000000)).mp result

end Dim1

namespace Dim2

set_option maxHeartbeats 3000000 in
private def b0 : Block := [
  (200000000, [term 0 (13450), term 64 (-1977), term 128 (-12431), term 512 (-1977), term 576 (4050), term 1024 (-12431)]),
  (200000000, [term 64 (8672), term 128 (-8955), term 512 (767), term 576 (-3405), term 1024 (-792)]),
  (200000000, [term 128 (1120), term 512 (6), term 576 (57), term 1024 (393)]),
  (800000000, [term 512 (4319), term 576 (-1558), term 1024 (-4460)]),
  (200000000, [term 576 (707), term 1024 (60)]),
  (3200000000, [term 1024 (261)]),
  (735279194285, [term 0 (1), term 64 (-1)]),
  (776198371830, [term 0 (1), term 128 (-1)]),
  (735279194285, [term 0 (1), term 512 (-1)]),
  (1132589788000, [term 0 (1), term 576 (1)]),
  (776198371830, [term 0 (1), term 1024 (-1)]),
  (663059812230, [term 64 (1), term 128 (1)]),
  (1009400000000, [term 64 (1), term 512 (1)]),
  (1324722408000, [term 64 (1), term 576 (-1)]),
  (1500677592000, [term 64 (1), term 1024 (1)]),
  (135600000000, [term 128 (1), term 512 (1)]),
  (848056240000, [term 128 (1), term 576 (-1)]),
  (1610927148000, [term 128 (1), term 1024 (1)]),
  (1569800000000, [term 512 (1), term 576 (-1)]),
  (324259812230, [term 512 (1), term 1024 (1)]),
  (985256240000, [term 576 (1), term 1024 (-1)]),
  (71992724528958, [term 0 (1)]),
  (72744260993485, [term 64 (1)]),
  (75028471741310, [term 128 (1)]),
  (74246060993485, [term 512 (1)]),
  (73123775324000, [term 576 (1)]),
  (74820194149310, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p0 : Poly := [term 0 (36256648269449188), term 64 (-10637730558388570), term 128 (-50979932396743660), term 192 (-21231343080375540), term 256 (47274299513313370), term 512 (-10637730558388570), term 576 (26017265179576000), term 640 (-7930653444816000), term 704 (-7917670112480000), term 1024 (-50979932396743660), term 1088 (-7930653444816000), term 1152 (72548934254296000), term 1536 (-21231343080375540), term 1600 (-7917670112480000), term 2048 (47274299513313370)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id0 : zeroCoeffs (add (squares b0) (scale (-1) p0)) = true := by rfl

private theorem pos0 (x : Point) : 0 ≤ value x p0 := block_nonneg x b0 p0 id0

set_option maxHeartbeats 3000000 in
private def b1 : Block := [
  (800000000, [term 0 (311)]),
  (77623200000000, [term 0 (1)])
]

set_option maxHeartbeats 3000000 in
private def p1 : Poly := [term 0 (155000000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id1 : zeroCoeffs (add (squares b1) (scale (-1) p1)) = true := by rfl

private theorem pos1 (x : Point) : 0 ≤ value x p1 := block_nonneg x b1 p1 id1

set_option maxHeartbeats 3000000 in
private def b2 : Block := [
  (20000000000, [term 0 (2491)]),
  (124099580000000000, [term 0 (1)])
]

set_option maxHeartbeats 3000000 in
private def p2 : Poly := [term 0 (248201200000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id2 : zeroCoeffs (add (squares b2) (scale (-1) p2)) = true := by rfl

private theorem pos2 (x : Point) : 0 ≤ value x p2 := block_nonneg x b2 p2 id2

set_option maxHeartbeats 3000000 in
private def b3 : Block := [
  (200000000, [term 0 (623)]),
  (77574200000000, [term 0 (1)])
]

set_option maxHeartbeats 3000000 in
private def p3 : Poly := [term 0 (155200000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id3 : zeroCoeffs (add (squares b3) (scale (-1) p3)) = true := by rfl

private theorem pos3 (x : Point) : 0 ≤ value x p3 := block_nonneg x b3 p3 id3

set_option maxHeartbeats 3000000 in
private def b6 : Block := [
  (200000000, [term 0 (13783), term 64 (-6322), term 128 (-6531), term 512 (-2151), term 576 (4016), term 1024 (-12610)]),
  (200000000, [term 64 (11934), term 128 (-8569), term 512 (-13051), term 576 (-3368), term 1024 (13574)]),
  (200000000, [term 128 (6734), term 512 (-17983), term 576 (-70), term 1024 (18732)]),
  (800000000, [term 512 (8868), term 576 (-3103), term 1024 (-9168)]),
  (800000000, [term 576 (673), term 1024 (180)]),
  (5000000000, [term 1024 (211)]),
  (574800000000, [term 0 (1), term 64 (-1)]),
  (154600000000, [term 0 (1), term 128 (1)]),
  (153400000000, [term 0 (1), term 512 (-1)]),
  (505600000000, [term 0 (1), term 576 (-1)]),
  (2474000000000, [term 0 (1), term 1024 (-1)]),
  (292800000000, [term 64 (1), term 128 (1)]),
  (602400000000, [term 64 (1), term 512 (1)]),
  (172800000000, [term 64 (1), term 576 (1)]),
  (892800000000, [term 64 (1), term 1024 (1)]),
  (1864400000000, [term 128 (1), term 512 (1)]),
  (271060120000, [term 128 (1), term 576 (1)]),
  (1744139880000, [term 128 (1), term 1024 (-1)]),
  (1490800000000, [term 512 (1), term 576 (1)]),
  (2003200000000, [term 512 (1), term 1024 (1)]),
  (1421669940000, [term 576 (1), term 1024 (-1)]),
  (75919800000000, [term 0 (1)]),
  (73456400000000, [term 64 (1)]),
  (70951660120000, [term 128 (1)]),
  (66408400000000, [term 512 (1)]),
  (73791669940000, [term 576 (1)]),
  (72782377649806, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p6 : Poly := [term 0 (38074000000000000), term 64 (-34855600000000000), term 128 (547200000000000), term 192 (-24388800000000000), term 256 (32360974260120000), term 512 (-11859200000000000), term 576 (-34719600000000000), term 640 (-24315200000000000), term 704 (864748520240000), term 1024 (93128000000000000), term 1088 (67292400000000000), term 1152 (50507348520240000), term 1536 (-324834000000000000), term 1600 (6640174260120000), term 2048 (206402302387469806)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id6 : zeroCoeffs (add (squares b6) (scale (-1) p6)) = true := by rfl

private theorem pos6 (x : Point) : 0 ≤ value x p6 := block_nonneg x b6 p6 id6

set_option maxHeartbeats 3000000 in
private def b7 : Block := [
  (200000000, [term 0 (7267), term 64 (-2236), term 128 (-5462), term 512 (-3392), term 576 (3443), term 1024 (-4259)]),
  (200000000, [term 64 (9013), term 128 (-9304), term 512 (633), term 576 (-3480), term 1024 (-645)]),
  (200000000, [term 128 (1117), term 512 (136), term 576 (8), term 1024 (259)]),
  (800000000, [term 512 (3271), term 576 (-1178), term 1024 (-3356)]),
  (200000000, [term 576 (708), term 1024 (57)]),
  (200000000, [term 1024 (1039)]),
  (602400000000, [term 0 (1), term 64 (1)]),
  (70800000000, [term 0 (1), term 128 (1)]),
  (467200000000, [term 0 (1), term 512 (-1)]),
  (256200000000, [term 0 (1), term 576 (-1)]),
  (630600000000, [term 0 (1), term 1024 (1)]),
  (1016000000000, [term 64 (1), term 128 (-1)]),
  (651800000000, [term 64 (1), term 512 (1)]),
  (442400000000, [term 64 (1), term 576 (-1)]),
  (547800000000, [term 64 (1), term 1024 (-1)]),
  (83200000000, [term 128 (1), term 512 (1)]),
  (362000000000, [term 128 (1), term 576 (1)]),
  (8200000000, [term 128 (1), term 1024 (-1)]),
  (928000000000, [term 512 (1), term 576 (-1)]),
  (287400000000, [term 512 (1), term 1024 (1)]),
  (647400000000, [term 576 (1), term 1024 (1)]),
  (74315000000000, [term 0 (1)]),
  (75166600000000, [term 64 (1)]),
  (76350000000000, [term 128 (1)]),
  (75659800000000, [term 512 (1)]),
  (75021400000000, [term 576 (1)]),
  (74498400000000, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p7 : Poly := [term 0 (10638200000000000), term 64 (-6498400000000000), term 128 (1448400000000000), term 192 (-28659600000000000), term 256 (23607000000000000), term 512 (-9860800000000000), term 576 (15324800000000000), term 640 (-10510400000000000), term 704 (5433200000000000), term 1024 (-1356200000000000), term 1088 (-10236400000000000), term 1152 (17902200000000000), term 1536 (-11934000000000000), term 1600 (1376000000000000), term 2048 (13027800000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id7 : zeroCoeffs (add (squares b7) (scale (-1) p7)) = true := by rfl

private theorem pos7 (x : Point) : 0 ≤ value x p7 := block_nonneg x b7 p7 id7

set_option maxHeartbeats 3000000 in
private def b8 : Block := [
  (200000000, [term 0 (13783), term 64 (-2151), term 128 (-12610), term 512 (-6322), term 576 (4016), term 1024 (-6531)]),
  (200000000, [term 64 (28430), term 128 (-29519), term 512 (-5478), term 576 (-2281), term 1024 (-325)]),
  (200000000, [term 128 (1120), term 512 (252), term 576 (-81), term 1024 (187)]),
  (200000000, [term 512 (10599), term 576 (-4969), term 1024 (-9821)]),
  (200000000, [term 576 (4666), term 1024 (-4531)]),
  (5000000000, [term 1024 (257)]),
  (153400000000, [term 0 (1), term 64 (-1)]),
  (2474000000000, [term 0 (1), term 128 (-1)]),
  (574800000000, [term 0 (1), term 512 (-1)]),
  (505600000000, [term 0 (1), term 576 (-1)]),
  (154600000000, [term 0 (1), term 1024 (1)]),
  (3212000000000, [term 64 (1), term 128 (1)]),
  (1616400000000, [term 64 (1), term 512 (-1)]),
  (249200000000, [term 64 (1), term 576 (1)]),
  (2886200000000, [term 64 (1), term 1024 (-1)]),
  (1851600000000, [term 128 (1), term 512 (1)]),
  (128200000000, [term 128 (1), term 576 (1)]),
  (2795000000000, [term 128 (1), term 1024 (1)]),
  (264600000000, [term 512 (1), term 576 (-1)]),
  (864600000000, [term 512 (1), term 1024 (1)]),
  (1083000000000, [term 576 (1), term 1024 (1)]),
  (75919800000000, [term 0 (1)]),
  (67942600000000, [term 64 (1)]),
  (64269387469806, [term 128 (1)]),
  (72733400000000, [term 512 (1)]),
  (75910400000000, [term 576 (1)]),
  (67860200000000, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p8 : Poly := [term 0 (38074000000000000), term 64 (-11859200000000000), term 128 (93128000000000000), term 192 (-324834000000000000), term 256 (206402302387469806), term 512 (-34855600000000000), term 576 (-34719600000000000), term 640 (67292400000000000), term 704 (6640400000000000), term 1024 (547200000000000), term 1088 (-24315200000000000), term 1152 (50507400000000000), term 1536 (-24388800000000000), term 1600 (864800000000000), term 2048 (32361200000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id8 : zeroCoeffs (add (squares b8) (scale (-1) p8)) = true := by rfl

private theorem pos8 (x : Point) : 0 ≤ value x p8 := block_nonneg x b8 p8 id8

set_option maxHeartbeats 3000000 in
private def b9 : Block := [
  (200000000, [term 0 (7267), term 64 (-3392), term 128 (-4259), term 512 (-2236), term 576 (3443), term 1024 (-5462)]),
  (200000000, [term 64 (6574), term 128 (-6736), term 512 (868), term 576 (-2680), term 1024 (-873)]),
  (200000000, [term 128 (1114), term 512 (31), term 576 (46), term 1024 (367)]),
  (200000000, [term 512 (8971), term 576 (-3237), term 1024 (-9264)]),
  (800000000, [term 576 (354), term 1024 (29)]),
  (800000000, [term 1024 (521)]),
  (467200000000, [term 0 (1), term 64 (-1)]),
  (630600000000, [term 0 (1), term 128 (1)]),
  (602400000000, [term 0 (1), term 512 (1)]),
  (256200000000, [term 0 (1), term 576 (-1)]),
  (70800000000, [term 0 (1), term 1024 (1)]),
  (187200000000, [term 64 (1), term 128 (1)]),
  (451200000000, [term 64 (1), term 512 (1)]),
  (204800000000, [term 64 (1), term 576 (-1)]),
  (399600000000, [term 64 (1), term 1024 (1)]),
  (762000000000, [term 128 (1), term 512 (-1)]),
  (2600000000, [term 128 (1), term 576 (1)]),
  (195200000000, [term 128 (1), term 1024 (1)]),
  (702200000000, [term 512 (1), term 576 (-1)]),
  (1660200000000, [term 512 (1), term 1024 (-1)]),
  (702400000000, [term 576 (1), term 1024 (1)]),
  (74315000000000, [term 0 (1)]),
  (76262000000000, [term 64 (1)]),
  (75267800000000, [term 128 (1)]),
  (74437600000000, [term 512 (1)]),
  (75492200000000, [term 576 (1)]),
  (75754600000000, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p9 : Poly := [term 0 (10638200000000000), term 64 (-9860800000000000), term 128 (-1356200000000000), term 192 (-11934000000000000), term 256 (13027800000000000), term 512 (-6498400000000000), term 576 (15324800000000000), term 640 (-10236400000000000), term 704 (1376000000000000), term 1024 (1448400000000000), term 1088 (-10510400000000000), term 1152 (17902200000000000), term 1536 (-28659600000000000), term 1600 (5433200000000000), term 2048 (23607000000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id9 : zeroCoeffs (add (squares b9) (scale (-1) p9)) = true := by rfl

private theorem pos9 (x : Point) : 0 ≤ value x p9 := block_nonneg x b9 p9 id9

private def cap : Poly := [term 128 (10958439), term 192 (-8132678), term 256 (-2825761), term 576 (5106878), term 640 (-8132678), term 1024 (10958439), term 1088 (-8132678), term 1152 (-5651522), term 1536 (-8132678), term 2048 (-2825761)]

private def con : Poly := [term 0 (50000000)]

private def v0 : Poly := [term 512 (1)]

private def u0 : Poly := [term 0 (1), term 512 (-1)]

private def v1 : Poly := [term 64 (1)]

private def u1 : Poly := [term 0 (1), term 64 (-1)]

set_option maxHeartbeats 3000000 in
private def target : Poly := [term 0 (2876652413472459400000000), term 64 (21943472080571500000000), term 128 (-2639206562326583000000000), term 192 (4347374857834023000000000), term 256 (-13468138380691731500000000), term 320 (8967806406367490300000000), term 512 (21943472080571500000000), term 1024 (-2639206562326583000000000), term 1536 (4347374857834023000000000), term 2048 (-13468138380691731500000000), term 2560 (8967806406367490300000000)]

private def products : List (Poly × Poly) := [(p0, con), (p1, cap), (p2, (prod cap v0)), (p3, (prod cap u0)), (p2, (prod cap v1)), (p3, (prod cap u1)), (p6, (scale 50000000 v0)), (p7, (scale 50000000 u0)), (p8, (scale 50000000 v1)), (p9, (scale 50000000 u1))]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem combined : zeroCoeffs (add (factors products) (scale (-1) target)) = true := by rfl

set_option maxHeartbeats 3000000 in
theorem certificate (x₁ x₂ : ℝ) (h0 : 0 ≤ x₁) (u0h : x₁ ≤ 1) (h1 : 0 ≤ x₂) (u1h : x₂ ≤ 1)
    (hc : (0 : ℝ) ≤ (-2825761*x₁^4/50000000 - 4066339*x₁^3/25000000 - 2825761*x₁^2*x₂^2/25000000 - 4066339*x₁^2*x₂/25000000 + 10958439*x₁^2/50000000 - 4066339*x₁*x₂^2/25000000 + 2553439*x₁*x₂/25000000 - 2825761*x₂^4/50000000 - 4066339*x₂^3/25000000 + 10958439*x₂^2/50000000)) :
    0 ≤ 2889/1000 - majorant ((41*x₁+59)/100) - majorant ((41*x₂+59)/100) := by
  let x : Point := (x₁, x₂, 0, 0)
  have posCap : 0 ≤ value x cap := by
    have eqCap : value x cap = 50000000 * (-2825761*x₁^4/50000000 - 4066339*x₁^3/25000000 - 2825761*x₁^2*x₂^2/25000000 - 4066339*x₁^2*x₂/25000000 + 10958439*x₁^2/50000000 - 4066339*x₁*x₂^2/25000000 + 2553439*x₁*x₂/25000000 - 2825761*x₂^4/50000000 - 4066339*x₂^3/25000000 + 10958439*x₂^2/50000000) := by
      norm_num [x, cap, value, term, mon]; ring
    rw [eqCap]; exact mul_nonneg (by norm_num) hc
  have posCon : 0 ≤ value x con := by norm_num [x, con, value, term, mon]
  have posV0 : 0 ≤ value x v0 := by simpa [x, v0, value, term, mon] using h0
  have posU0 : 0 ≤ value x u0 := by simpa [x, u0, value, term, mon] using (sub_nonneg.mpr u0h)
  have posV1 : 0 ≤ value x v1 := by simpa [x, v1, value, term, mon] using h1
  have posU1 : 0 ≤ value x u1 := by simpa [x, u1, value, term, mon] using (sub_nonneg.mpr u1h)
  have allPos : 0 ≤ value x (factors products) := by
    unfold products
    simp only [factors_cons]
    exact (add_nonneg (mul_nonneg (pos0 x) posCon) (add_nonneg (mul_nonneg (pos1 x) posCap) (add_nonneg (mul_nonneg (pos2 x) (by rw [value_prod]; exact mul_nonneg posCap posV0)) (add_nonneg (mul_nonneg (pos3 x) (by rw [value_prod]; exact mul_nonneg posCap posU0)) (add_nonneg (mul_nonneg (pos2 x) (by rw [value_prod]; exact mul_nonneg posCap posV1)) (add_nonneg (mul_nonneg (pos3 x) (by rw [value_prod]; exact mul_nonneg posCap posU1)) (add_nonneg (mul_nonneg (pos6 x) (by rw [value_scale]; exact mul_nonneg (by norm_num) posV0)) (add_nonneg (mul_nonneg (pos7 x) (by rw [value_scale]; exact mul_nonneg (by norm_num) posU0)) (add_nonneg (mul_nonneg (pos8 x) (by rw [value_scale]; exact mul_nonneg (by norm_num) posV1)) (add_nonneg (mul_nonneg (pos9 x) (by rw [value_scale]; exact mul_nonneg (by norm_num) posU1)) (le_refl 0)))))))))))
  have result := transfer x products target combined allPos
  have eqTarget : value x target = 1000000000000000000000000 * (2889/1000 - majorant ((41*x₁+59)/100) - majorant ((41*x₂+59)/100)) := by
    norm_num [x, target, value, term, mon, majorant]; ring
  rw [eqTarget] at result
  exact (mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < 1000000000000000000000000)).mp result

end Dim2

namespace Dim3

set_option maxHeartbeats 3000000 in
private def b0 : Block := [
  (200000000, [term 0 (16928), term 8 (-6143), term 16 (-11896), term 64 (-6143), term 72 (7634), term 128 (-11896), term 512 (-6143), term 520 (7634), term 576 (7634), term 1024 (-11896)]),
  (200000000, [term 8 (9442), term 16 (-9747), term 64 (4052), term 72 (-4925), term 128 (-4195), term 512 (4052), term 520 (-4925), term 576 (-2967), term 1024 (-4195)]),
  (200000000, [term 16 (1279), term 64 (-88), term 72 (102), term 128 (553), term 512 (-88), term 520 (102), term 576 (-15), term 1024 (553)]),
  (200000000, [term 64 (8528), term 72 (-3112), term 128 (-8793), term 512 (2560), term 520 (-944), term 576 (-4043), term 1024 (-2646)]),
  (200000000, [term 72 (808), term 128 (70), term 512 (-105), term 520 (138), term 576 (151), term 1024 (-56)]),
  (200000000, [term 128 (1190), term 512 (-36), term 520 (-105), term 576 (112), term 1024 (364)]),
  (800000000, [term 512 (4067), term 520 (-1482), term 576 (-1482), term 1024 (-4193)]),
  (200000000, [term 520 (793), term 576 (115), term 1024 (141)]),
  (800000000, [term 576 (392), term 1024 (61)]),
  (200000000, [term 1024 (1119)]),
  (924479194285, [term 0 (1), term 8 (-1)]),
  (1324787078170, [term 0 (1), term 16 (1)]),
  (924479194285, [term 0 (1), term 64 (-1)]),
  (1656539312000, [term 0 (1), term 72 (-1)]),
  (1324787078170, [term 0 (1), term 128 (1)]),
  (924479194285, [term 0 (1), term 512 (-1)]),
  (1656539312000, [term 0 (1), term 520 (-1)]),
  (1656539312000, [term 0 (1), term 576 (-1)]),
  (1324787078170, [term 0 (1), term 1024 (1)]),
  (329994924230, [term 8 (1), term 16 (1)]),
  (1113400000000, [term 8 (1), term 64 (1)]),
  (212275272000, [term 8 (1), term 72 (-1)]),
  (1297724728000, [term 8 (1), term 128 (1)]),
  (1113400000000, [term 8 (1), term 512 (1)]),
  (212275272000, [term 8 (1), term 520 (-1)]),
  (545475568000, [term 8 (1), term 576 (-1)]),
  (1297724728000, [term 8 (1), term 1024 (1)]),
  (853600000000, [term 16 (1), term 64 (1)]),
  (737906912000, [term 16 (1), term 72 (1)]),
  (1241958800000, [term 16 (1), term 128 (-1)]),
  (853600000000, [term 16 (1), term 512 (1)]),
  (737906912000, [term 16 (1), term 520 (1)]),
  (1191706912000, [term 16 (1), term 576 (1)]),
  (1241958800000, [term 16 (1), term 1024 (-1)]),
  (174800000000, [term 64 (1), term 72 (1)]),
  (796794924230, [term 64 (1), term 128 (1)]),
  (1284600000000, [term 64 (1), term 512 (1)]),
  (366000000000, [term 64 (1), term 520 (-1)]),
  (648675272000, [term 64 (1), term 576 (-1)]),
  (1838124728000, [term 64 (1), term 1024 (1)]),
  (193106912000, [term 72 (1), term 128 (1)]),
  (140400000000, [term 72 (1), term 512 (-1)]),
  (1243400000000, [term 72 (1), term 520 (-1)]),
  (1133293088000, [term 72 (1), term 576 (-1)]),
  (47506912000, [term 72 (1), term 1024 (1)]),
  (789200000000, [term 128 (1), term 512 (1)]),
  (796200000000, [term 128 (1), term 520 (1)]),
  (1180706912000, [term 128 (1), term 576 (1)]),
  (1921958800000, [term 128 (1), term 1024 (-1)]),
  (347200000000, [term 512 (1), term 520 (-1)]),
  (646200000000, [term 512 (1), term 576 (-1)]),
  (1997594924230, [term 512 (1), term 1024 (1)]),
  (812400000000, [term 520 (1), term 576 (-1)]),
  (309706912000, [term 520 (1), term 1024 (1)]),
  (359106912000, [term 576 (1), term 1024 (1)]),
  (86418187420417, [term 0 (1)]),
  (95590650313485, [term 8 (1)]),
  (91597407026970, [term 16 (1)]),
  (94263325881485, [term 64 (1)]),
  (93582171592000, [term 72 (1)]),
  (90201789210970, [term 128 (1)]),
  (93948525881485, [term 512 (1)]),
  (93051371592000, [term 520 (1)]),
  (92097696024000, [term 576 (1)]),
  (87201557570970, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p0 : Poly := [term 0 (57409572404173782), term 8 (-41597330558388570), term 16 (-55067345625843660), term 24 (-7580958410151540), term 32 (47731044027365370), term 64 (-41597330558388570), term 72 (82088427721376000), term 80 (-23969829350544000), term 88 (-17070376586176000), term 128 (-55067345625843660), term 136 (-23969829350544000), term 144 (91917223282400000), term 192 (-7580958410151540), term 200 (-17070376586176000), term 256 (47731044027365370), term 512 (-41597330558388570), term 520 (82088427721376000), term 528 (-23969829350544000), term 536 (-17070376586176000), term 576 (82088427721376000), term 584 (-89895521351136000), term 592 (9471623413824000), term 640 (-23969829350544000), term 648 (9471623413824000), term 704 (-17070376586176000), term 1024 (-55067345625843660), term 1032 (-23969829350544000), term 1040 (91917223282400000), term 1088 (-23969829350544000), term 1096 (9471623413824000), term 1152 (91917223282400000), term 1536 (-7580958410151540), term 1544 (-17070376586176000), term 1600 (-17070376586176000), term 2048 (47731044027365370)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id0 : zeroCoeffs (add (squares b0) (scale (-1) p0)) = true := by rfl

private theorem pos0 (x : Point) : 0 ≤ value x p0 := block_nonneg x b0 p0 id0

set_option maxHeartbeats 3000000 in
private def b1 : Block := [
  (12800000000, [term 0 (89)]),
  (101211200000000, [term 0 (1)])
]

set_option maxHeartbeats 3000000 in
private def p1 : Poly := [term 0 (202600000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id1 : zeroCoeffs (add (squares b1) (scale (-1) p1)) = true := by rfl

private theorem pos1 (x : Point) : 0 ≤ value x p1 := block_nonneg x b1 p1 id1

set_option maxHeartbeats 3000000 in
private def b2 : Block := [
  (800000000, [term 0 (12627)]),
  (127544896800000000, [term 0 (1)])
]

set_option maxHeartbeats 3000000 in
private def p2 : Poly := [term 0 (255097800000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id2 : zeroCoeffs (add (squares b2) (scale (-1) p2)) = true := by rfl

private theorem pos2 (x : Point) : 0 ≤ value x p2 := block_nonneg x b2 p2 id2

set_option maxHeartbeats 3000000 in
private def b8 : Block := [
  (200000000, [term 0 (14480), term 8 (-7093), term 16 (-6996), term 64 (-7093), term 72 (-5122), term 128 (-6996), term 512 (364), term 520 (3880), term 576 (3880), term 1024 (-16015)]),
  (200000000, [term 8 (11638), term 16 (-6986), term 64 (2894), term 72 (-8211), term 128 (-19), term 512 (-16319), term 520 (-3326), term 576 (1950), term 1024 (17001)]),
  (200000000, [term 16 (5779), term 64 (3461), term 72 (-4114), term 128 (-2213), term 512 (-9756), term 520 (-1976), term 576 (985), term 1024 (10224)]),
  (200000000, [term 64 (10728), term 72 (-5365), term 128 (-6860), term 512 (-10154), term 520 (3651), term 576 (-4452), term 1024 (10558)]),
  (200000000, [term 72 (7906), term 128 (-1577), term 512 (-1751), term 520 (807), term 576 (2329), term 1024 (1905)]),
  (200000000, [term 128 (5268), term 512 (-6961), term 520 (2647), term 576 (-2436), term 1024 (7342)]),
  (200000000, [term 512 (11874), term 520 (-4030), term 576 (-4030), term 1024 (-12153)]),
  (200000000, [term 520 (1509), term 576 (207), term 1024 (380)]),
  (200000000, [term 576 (1494), term 1024 (331)]),
  (200000000, [term 1024 (1149)]),
  (1472000000000, [term 0 (1), term 8 (-1)]),
  (216000000000, [term 0 (1), term 16 (1)]),
  (1472000000000, [term 0 (1), term 64 (-1)]),
  (1088000000000, [term 0 (1), term 72 (-1)]),
  (216000000000, [term 0 (1), term 128 (1)]),
  (1344000000000, [term 0 (1), term 512 (-1)]),
  (480000000000, [term 0 (1), term 520 (-1)]),
  (480000000000, [term 0 (1), term 576 (-1)]),
  (240000000000, [term 0 (1), term 1024 (1)]),
  (712000000000, [term 8 (1), term 16 (-1)]),
  (1595800000000, [term 8 (1), term 64 (1)]),
  (1054400000000, [term 8 (1), term 72 (1)]),
  (498800000000, [term 8 (1), term 128 (1)]),
  (725200000000, [term 8 (1), term 512 (-1)]),
  (365600000000, [term 8 (1), term 520 (1)]),
  (1148000000000, [term 8 (1), term 576 (1)]),
  (593400000000, [term 8 (1), term 1024 (1)]),
  (452600000000, [term 16 (1), term 64 (-1)]),
  (1449600000000, [term 16 (1), term 72 (1)]),
  (106295056000, [term 16 (1), term 128 (-1)]),
  (3186800000000, [term 16 (1), term 512 (1)]),
  (527904944000, [term 16 (1), term 520 (1)]),
  (31304944000, [term 16 (1), term 576 (1)]),
  (3231695056000, [term 16 (1), term 1024 (-1)]),
  (512400000000, [term 64 (1), term 72 (1)]),
  (326200000000, [term 64 (1), term 128 (1)]),
  (133200000000, [term 64 (1), term 512 (1)]),
  (741600000000, [term 64 (1), term 520 (-1)]),
  (502200000000, [term 64 (1), term 576 (1)]),
  (1644600000000, [term 64 (1), term 1024 (1)]),
  (388200000000, [term 72 (1), term 128 (-1)]),
  (222200000000, [term 72 (1), term 512 (1)]),
  (1043400000000, [term 72 (1), term 520 (-1)]),
  (1332495056000, [term 72 (1), term 576 (-1)]),
  (1531400000000, [term 72 (1), term 1024 (1)]),
  (1352800000000, [term 128 (1), term 512 (-1)]),
  (1300200000000, [term 128 (1), term 520 (1)]),
  (117504944000, [term 128 (1), term 576 (1)]),
  (498304944000, [term 128 (1), term 1024 (1)]),
  (174400000000, [term 512 (1), term 520 (-1)]),
  (1983000000000, [term 512 (1), term 576 (-1)]),
  (581200000000, [term 512 (1), term 1024 (-1)]),
  (1152400000000, [term 520 (1), term 576 (-1)]),
  (1483752472000, [term 520 (1), term 1024 (1)]),
  (1714952472000, [term 576 (1), term 1024 (1)]),
  (95112000000000, [term 0 (1)]),
  (94096200000000, [term 8 (1)]),
  (90533504944000, [term 16 (1)]),
  (94741400000000, [term 64 (1)]),
  (92085504944000, [term 72 (1)]),
  (96634200000000, [term 128 (1)]),
  (96115800000000, [term 512 (1)]),
  (92552342584000, [term 520 (1)]),
  (92427942584000, [term 576 (1)]),
  (86201927349806, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p8 : Poly := [term 0 (42036200000000000), term 8 (-41085600000000000), term 16 (-3267400000000000), term 24 (-12673600000000000), term 32 (26329458304944000), term 64 (-41085600000000000), term 72 (3930800000000000), term 80 (-3928000000000000), term 88 (27771200000000000), term 128 (-3267400000000000), term 136 (-3928000000000000), term 144 (54989316609888000), term 192 (-12673600000000000), term 200 (27771200000000000), term 256 (26329458304944000), term 512 (2105600000000000), term 520 (-54530400000000000), term 528 (-4453200000000000), term 536 (-6130283390112000), term 576 (-54530400000000000), term 584 (81303600000000000), term 592 (-13088683390112000), term 640 (-4453200000000000), term 648 (-13088683390112000), term 704 (-6130283390112000), term 1024 (38795200000000000), term 1032 (112663200000000000), term 1040 (34941316609888000), term 1088 (112663200000000000), term 1096 (-55542400000000000), term 1152 (34941316609888000), term 1536 (-275588400000000000), term 1544 (-11923941695056000), term 1600 (-11923941695056000), term 2048 (193761586432293806)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id8 : zeroCoeffs (add (squares b8) (scale (-1) p8)) = true := by rfl

private theorem pos8 (x : Point) : 0 ≤ value x p8 := block_nonneg x b8 p8 id8

set_option maxHeartbeats 3000000 in
private def b9 : Block := [
  (200000000, [term 0 (14480), term 8 (-7093), term 16 (-6996), term 64 (364), term 72 (3880), term 128 (-16015), term 512 (-7093), term 520 (-5122), term 576 (3880), term 1024 (-6996)]),
  (200000000, [term 8 (11638), term 16 (-6986), term 64 (-16319), term 72 (-3326), term 128 (17001), term 512 (2894), term 520 (-8211), term 576 (1950), term 1024 (-19)]),
  (200000000, [term 16 (5779), term 64 (-9756), term 72 (-1976), term 128 (10224), term 512 (3461), term 520 (-4114), term 576 (985), term 1024 (-2213)]),
  (200000000, [term 64 (17194), term 72 (-6093), term 128 (-17795), term 512 (-6335), term 520 (2363), term 576 (595), term 1024 (2079)]),
  (200000000, [term 72 (1542), term 128 (417), term 512 (365), term 520 (771), term 576 (-418), term 1024 (192)]),
  (200000000, [term 128 (1204), term 512 (314), term 520 (121), term 576 (-118), term 1024 (132)]),
  (200000000, [term 512 (8644), term 520 (-4963), term 576 (-5067), term 1024 (-7003)]),
  (200000000, [term 520 (7776), term 576 (2067), term 1024 (-1994)]),
  (800000000, [term 576 (2191), term 1024 (-2108)]),
  (800000000, [term 1024 (731)]),
  (1472000000000, [term 0 (1), term 8 (-1)]),
  (216000000000, [term 0 (1), term 16 (1)]),
  (1344000000000, [term 0 (1), term 64 (-1)]),
  (480000000000, [term 0 (1), term 72 (-1)]),
  (240000000000, [term 0 (1), term 128 (1)]),
  (1472000000000, [term 0 (1), term 512 (-1)]),
  (1088000000000, [term 0 (1), term 520 (-1)]),
  (480000000000, [term 0 (1), term 576 (-1)]),
  (216000000000, [term 0 (1), term 1024 (1)]),
  (712000000000, [term 8 (1), term 16 (-1)]),
  (725200000000, [term 8 (1), term 64 (-1)]),
  (365600000000, [term 8 (1), term 72 (1)]),
  (593400000000, [term 8 (1), term 128 (1)]),
  (1595800000000, [term 8 (1), term 512 (1)]),
  (1054400000000, [term 8 (1), term 520 (1)]),
  (1148000000000, [term 8 (1), term 576 (1)]),
  (498800000000, [term 8 (1), term 1024 (1)]),
  (3186800000000, [term 16 (1), term 64 (1)]),
  (527904944000, [term 16 (1), term 72 (1)]),
  (3231695056000, [term 16 (1), term 128 (-1)]),
  (452600000000, [term 16 (1), term 512 (-1)]),
  (1449600000000, [term 16 (1), term 520 (1)]),
  (227000000000, [term 16 (1), term 576 (-1)]),
  (364600000000, [term 16 (1), term 1024 (-1)]),
  (225600000000, [term 64 (1), term 72 (-1)]),
  (2070600000000, [term 64 (1), term 128 (1)]),
  (1491200000000, [term 64 (1), term 512 (-1)]),
  (898600000000, [term 64 (1), term 520 (1)]),
  (1608000000000, [term 64 (1), term 576 (-1)]),
  (1174200000000, [term 64 (1), term 1024 (-1)]),
  (1669352472000, [term 72 (1), term 128 (1)]),
  (447000000000, [term 72 (1), term 512 (1)]),
  (762600000000, [term 72 (1), term 520 (-1)]),
  (1089800000000, [term 72 (1), term 576 (-1)]),
  (736200000000, [term 72 (1), term 1024 (1)]),
  (2572200000000, [term 128 (1), term 512 (1)]),
  (1462200000000, [term 128 (1), term 520 (1)]),
  (2002600000000, [term 128 (1), term 576 (1)]),
  (920800000000, [term 128 (1), term 1024 (1)]),
  (558000000000, [term 512 (1), term 520 (-1)]),
  (90000000000, [term 512 (1), term 576 (-1)]),
  (84000000000, [term 512 (1), term 1024 (1)]),
  (31600000000, [term 520 (1), term 576 (1)]),
  (1394200000000, [term 520 (1), term 1024 (1)]),
  (1214200000000, [term 576 (1), term 1024 (1)]),
  (95112000000000, [term 0 (1)]),
  (94096200000000, [term 8 (1)]),
  (90079504944000, [term 16 (1)]),
  (89790000000000, [term 64 (1)]),
  (94162942584000, [term 72 (1)]),
  (80837184765806, [term 128 (1)]),
  (94799600000000, [term 512 (1)]),
  (91541400000000, [term 520 (1)]),
  (93568800000000, [term 576 (1)]),
  (93113000000000, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p9 : Poly := [term 0 (42036200000000000), term 8 (-41085600000000000), term 16 (-3267400000000000), term 24 (-12673600000000000), term 32 (26329458304944000), term 64 (2105600000000000), term 72 (-54530400000000000), term 80 (-4453200000000000), term 88 (-6130283390112000), term 128 (38795200000000000), term 136 (112663200000000000), term 144 (34941316609888000), term 192 (-275588400000000000), term 200 (-11923941695056000), term 256 (193761586432293806), term 512 (-41085600000000000), term 520 (3930800000000000), term 528 (-3928000000000000), term 536 (27771200000000000), term 576 (-54530400000000000), term 584 (81303600000000000), term 592 (-13089200000000000), term 640 (112663200000000000), term 648 (-55542400000000000), term 704 (-11924000000000000), term 1024 (-3267400000000000), term 1032 (-3928000000000000), term 1040 (54988800000000000), term 1088 (-4453200000000000), term 1096 (-13089200000000000), term 1152 (34941200000000000), term 1536 (-12673600000000000), term 1544 (27771200000000000), term 1600 (-6130400000000000), term 2048 (26329400000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id9 : zeroCoeffs (add (squares b9) (scale (-1) p9)) = true := by rfl

private theorem pos9 (x : Point) : 0 ≤ value x p9 := block_nonneg x b9 p9 id9

set_option maxHeartbeats 3000000 in
private def b10 : Block := [
  (200000000, [term 0 (14480), term 8 (364), term 16 (-16015), term 64 (-7093), term 72 (3880), term 128 (-6996), term 512 (-7093), term 520 (3880), term 576 (-5122), term 1024 (-6996)]),
  (200000000, [term 8 (25635), term 16 (-26650), term 64 (-7409), term 72 (-1217), term 128 (2248), term 512 (-7409), term 520 (-1217), term 576 (8378), term 1024 (2248)]),
  (200000000, [term 16 (1280), term 64 (320), term 72 (-94), term 128 (175), term 512 (320), term 520 (-94), term 576 (24), term 1024 (175)]),
  (200000000, [term 64 (8969), term 72 (-5318), term 128 (-7214), term 512 (-2376), term 520 (1529), term 576 (-3734), term 1024 (1827)]),
  (200000000, [term 72 (4970), term 128 (-4787), term 512 (216), term 520 (-1221), term 576 (2529), term 1024 (912)]),
  (200000000, [term 128 (1468), term 512 (187), term 520 (1), term 576 (-55), term 1024 (-135)]),
  (200000000, [term 512 (8644), term 520 (-5067), term 576 (-4963), term 1024 (-7003)]),
  (200000000, [term 520 (4845), term 576 (3317), term 1024 (-4663)]),
  (3200000000, [term 576 (1758), term 1024 (-1)]),
  (800000000, [term 1024 (731)]),
  (1344000000000, [term 0 (1), term 8 (-1)]),
  (240000000000, [term 0 (1), term 16 (1)]),
  (1472000000000, [term 0 (1), term 64 (-1)]),
  (480000000000, [term 0 (1), term 72 (-1)]),
  (216000000000, [term 0 (1), term 128 (1)]),
  (1472000000000, [term 0 (1), term 512 (-1)]),
  (480000000000, [term 0 (1), term 520 (-1)]),
  (1088000000000, [term 0 (1), term 576 (-1)]),
  (216000000000, [term 0 (1), term 1024 (1)]),
  (6242000000000, [term 8 (1), term 16 (1)]),
  (1113400000000, [term 8 (1), term 64 (1)]),
  (2305000000000, [term 8 (1), term 72 (-1)]),
  (2612800000000, [term 8 (1), term 128 (1)]),
  (1113400000000, [term 8 (1), term 512 (1)]),
  (2305000000000, [term 8 (1), term 520 (-1)]),
  (924400000000, [term 8 (1), term 576 (-1)]),
  (2612800000000, [term 8 (1), term 1024 (1)]),
  (231000000000, [term 16 (1), term 64 (1)]),
  (3094000000000, [term 16 (1), term 72 (1)]),
  (3148000000000, [term 16 (1), term 128 (-1)]),
  (231000000000, [term 16 (1), term 512 (1)]),
  (3094000000000, [term 16 (1), term 520 (1)]),
  (2230000000000, [term 16 (1), term 576 (1)]),
  (3148000000000, [term 16 (1), term 1024 (-1)]),
  (861800000000, [term 64 (1), term 72 (1)]),
  (966000000000, [term 64 (1), term 128 (-1)]),
  (602800000000, [term 64 (1), term 512 (1)]),
  (86800000000, [term 64 (1), term 520 (-1)]),
  (164400000000, [term 64 (1), term 576 (1)]),
  (1111800000000, [term 64 (1), term 1024 (-1)]),
  (383200000000, [term 72 (1), term 128 (-1)]),
  (815800000000, [term 72 (1), term 512 (1)]),
  (453400000000, [term 72 (1), term 520 (1)]),
  (380000000000, [term 72 (1), term 576 (-1)]),
  (818400000000, [term 72 (1), term 1024 (1)]),
  (36800000000, [term 128 (1), term 512 (-1)]),
  (911400000000, [term 128 (1), term 520 (1)]),
  (1306200000000, [term 128 (1), term 576 (1)]),
  (351400000000, [term 128 (1), term 1024 (1)]),
  (553600000000, [term 512 (1), term 520 (1)]),
  (557000000000, [term 512 (1), term 576 (1)]),
  (811800000000, [term 512 (1), term 1024 (-1)]),
  (701200000000, [term 520 (1), term 576 (1)]),
  (203200000000, [term 520 (1), term 1024 (-1)]),
  (819800000000, [term 576 (1), term 1024 (1)]),
  (95112000000000, [term 0 (1)]),
  (75883000000000, [term 8 (1)]),
  (71703432293806, [term 16 (1)]),
  (96531800000000, [term 64 (1)]),
  (90338600000000, [term 72 (1)]),
  (91401400000000, [term 128 (1)]),
  (96392400000000, [term 512 (1)]),
  (92107000000000, [term 520 (1)]),
  (96059400000000, [term 576 (1)]),
  (91490600000000, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p10 : Poly := [term 0 (42036200000000000), term 8 (2105600000000000), term 16 (38795200000000000), term 24 (-275588400000000000), term 32 (193761586432293806), term 64 (-41085600000000000), term 72 (-54530400000000000), term 80 (112663200000000000), term 88 (-11924000000000000), term 128 (-3267400000000000), term 136 (-4453200000000000), term 144 (34941200000000000), term 192 (-12673600000000000), term 200 (-6130400000000000), term 256 (26329400000000000), term 512 (-41085600000000000), term 520 (-54530400000000000), term 528 (112663200000000000), term 536 (-11924000000000000), term 576 (3930800000000000), term 584 (81303600000000000), term 592 (-55542400000000000), term 640 (-3928000000000000), term 648 (-13089200000000000), term 704 (27771200000000000), term 1024 (-3267400000000000), term 1032 (-4453200000000000), term 1040 (34941200000000000), term 1088 (-3928000000000000), term 1096 (-13089200000000000), term 1152 (54988800000000000), term 1536 (-12673600000000000), term 1544 (-6130400000000000), term 1600 (27771200000000000), term 2048 (26329400000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id10 : zeroCoeffs (add (squares b10) (scale (-1) p10)) = true := by rfl

private theorem pos10 (x : Point) : 0 ≤ value x p10 := block_nonneg x b10 p10 id10

private def cap : Poly := [term 16 (10958439), term 24 (-8132678), term 32 (-2825761), term 72 (5106878), term 80 (-8132678), term 128 (10958439), term 136 (-8132678), term 144 (-5651522), term 192 (-8132678), term 256 (-2825761), term 520 (5106878), term 528 (-8132678), term 576 (5106878), term 640 (-8132678), term 1024 (10958439), term 1032 (-8132678), term 1040 (-5651522), term 1088 (-8132678), term 1152 (-5651522), term 1536 (-8132678), term 2048 (-2825761)]

private def con : Poly := [term 0 (50000000)]

private def v0 : Poly := [term 512 (1)]

private def u0 : Poly := [term 0 (1), term 512 (-1)]

private def v1 : Poly := [term 64 (1)]

private def u1 : Poly := [term 0 (1), term 64 (-1)]

private def v2 : Poly := [term 8 (1)]

private def u2 : Poly := [term 0 (1), term 8 (-1)]

set_option maxHeartbeats 3000000 in
private def target : Poly := [term 0 (2870478620208689100000000), term 8 (21943472080571500000000), term 16 (-2639206562326583000000000), term 24 (4347374857834023000000000), term 32 (-13468138380691731500000000), term 40 (8967806406367490300000000), term 64 (21943472080571500000000), term 128 (-2639206562326583000000000), term 192 (4347374857834023000000000), term 256 (-13468138380691731500000000), term 320 (8967806406367490300000000), term 512 (21943472080571500000000), term 1024 (-2639206562326583000000000), term 1536 (4347374857834023000000000), term 2048 (-13468138380691731500000000), term 2560 (8967806406367490300000000)]

private def products : List (Poly × Poly) := [(p0, con), (p1, cap), (p2, (prod cap v0)), (p1, (prod cap u0)), (p2, (prod cap v1)), (p1, (prod cap u1)), (p2, (prod cap v2)), (p1, (prod cap u2)), (p8, (scale 50000000 v0)), (p9, (scale 50000000 v1)), (p10, (scale 50000000 v2))]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem combined : zeroCoeffs (add (factors products) (scale (-1) target)) = true := by rfl

set_option maxHeartbeats 3000000 in
theorem certificate (x₁ x₂ x₃ : ℝ) (h0 : 0 ≤ x₁) (u0h : x₁ ≤ 1) (h1 : 0 ≤ x₂) (u1h : x₂ ≤ 1) (h2 : 0 ≤ x₃) (u2h : x₃ ≤ 1)
    (hc : (0 : ℝ) ≤ (-2825761*x₁^4/50000000 - 4066339*x₁^3/25000000 - 2825761*x₁^2*x₂^2/25000000 - 4066339*x₁^2*x₂/25000000 - 2825761*x₁^2*x₃^2/25000000 - 4066339*x₁^2*x₃/25000000 + 10958439*x₁^2/50000000 - 4066339*x₁*x₂^2/25000000 + 2553439*x₁*x₂/25000000 - 4066339*x₁*x₃^2/25000000 + 2553439*x₁*x₃/25000000 - 2825761*x₂^4/50000000 - 4066339*x₂^3/25000000 - 2825761*x₂^2*x₃^2/25000000 - 4066339*x₂^2*x₃/25000000 + 10958439*x₂^2/50000000 - 4066339*x₂*x₃^2/25000000 + 2553439*x₂*x₃/25000000 - 2825761*x₃^4/50000000 - 4066339*x₃^3/25000000 + 10958439*x₃^2/50000000)) :
    0 ≤ 2889/1000 - majorant ((41*x₁+59)/100) - majorant ((41*x₂+59)/100) - majorant ((41*x₃+59)/100) := by
  let x : Point := (x₁, x₂, x₃, 0)
  have posCap : 0 ≤ value x cap := by
    have eqCap : value x cap = 50000000 * (-2825761*x₁^4/50000000 - 4066339*x₁^3/25000000 - 2825761*x₁^2*x₂^2/25000000 - 4066339*x₁^2*x₂/25000000 - 2825761*x₁^2*x₃^2/25000000 - 4066339*x₁^2*x₃/25000000 + 10958439*x₁^2/50000000 - 4066339*x₁*x₂^2/25000000 + 2553439*x₁*x₂/25000000 - 4066339*x₁*x₃^2/25000000 + 2553439*x₁*x₃/25000000 - 2825761*x₂^4/50000000 - 4066339*x₂^3/25000000 - 2825761*x₂^2*x₃^2/25000000 - 4066339*x₂^2*x₃/25000000 + 10958439*x₂^2/50000000 - 4066339*x₂*x₃^2/25000000 + 2553439*x₂*x₃/25000000 - 2825761*x₃^4/50000000 - 4066339*x₃^3/25000000 + 10958439*x₃^2/50000000) := by
      norm_num [x, cap, value, term, mon]; ring
    rw [eqCap]; exact mul_nonneg (by norm_num) hc
  have posCon : 0 ≤ value x con := by norm_num [x, con, value, term, mon]
  have posV0 : 0 ≤ value x v0 := by simpa [x, v0, value, term, mon] using h0
  have posU0 : 0 ≤ value x u0 := by simpa [x, u0, value, term, mon] using (sub_nonneg.mpr u0h)
  have posV1 : 0 ≤ value x v1 := by simpa [x, v1, value, term, mon] using h1
  have posU1 : 0 ≤ value x u1 := by simpa [x, u1, value, term, mon] using (sub_nonneg.mpr u1h)
  have posV2 : 0 ≤ value x v2 := by simpa [x, v2, value, term, mon] using h2
  have posU2 : 0 ≤ value x u2 := by simpa [x, u2, value, term, mon] using (sub_nonneg.mpr u2h)
  have allPos : 0 ≤ value x (factors products) := by
    unfold products
    simp only [factors_cons]
    exact (add_nonneg (mul_nonneg (pos0 x) posCon) (add_nonneg (mul_nonneg (pos1 x) posCap) (add_nonneg (mul_nonneg (pos2 x) (by rw [value_prod]; exact mul_nonneg posCap posV0)) (add_nonneg (mul_nonneg (pos1 x) (by rw [value_prod]; exact mul_nonneg posCap posU0)) (add_nonneg (mul_nonneg (pos2 x) (by rw [value_prod]; exact mul_nonneg posCap posV1)) (add_nonneg (mul_nonneg (pos1 x) (by rw [value_prod]; exact mul_nonneg posCap posU1)) (add_nonneg (mul_nonneg (pos2 x) (by rw [value_prod]; exact mul_nonneg posCap posV2)) (add_nonneg (mul_nonneg (pos1 x) (by rw [value_prod]; exact mul_nonneg posCap posU2)) (add_nonneg (mul_nonneg (pos8 x) (by rw [value_scale]; exact mul_nonneg (by norm_num) posV0)) (add_nonneg (mul_nonneg (pos9 x) (by rw [value_scale]; exact mul_nonneg (by norm_num) posV1)) (add_nonneg (mul_nonneg (pos10 x) (by rw [value_scale]; exact mul_nonneg (by norm_num) posV2)) (le_refl 0))))))))))))
  have result := transfer x products target combined allPos
  have eqTarget : value x target = 1000000000000000000000000 * (2889/1000 - majorant ((41*x₁+59)/100) - majorant ((41*x₂+59)/100) - majorant ((41*x₃+59)/100)) := by
    norm_num [x, target, value, term, mon, majorant]; ring
  rw [eqTarget] at result
  exact (mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < 1000000000000000000000000)).mp result

end Dim3

namespace Dim4

set_option maxHeartbeats 3000000 in
private def b0 : Block := [
  (200000000, [term 0 (16911), term 1 (-24545), term 2 (7368), term 8 (-24545), term 9 (20164), term 16 (7368), term 64 (-24545), term 65 (20164), term 72 (20164), term 128 (7368), term 512 (-24545), term 513 (20164), term 520 (20164), term 576 (20164), term 1024 (7368)]),
  (200000000, [term 1 (5336), term 2 (-5337), term 8 (-36), term 9 (-1926), term 16 (169), term 64 (-36), term 65 (-1926), term 72 (12), term 128 (169), term 512 (-36), term 513 (-1926), term 520 (12), term 576 (12), term 1024 (169)]),
  (200000000, [term 2 (1185), term 8 (596), term 9 (-129), term 16 (-208), term 64 (596), term 65 (-129), term 72 (-487), term 128 (-208), term 512 (596), term 513 (-129), term 520 (-488), term 576 (-487), term 1024 (-208)]),
  (200000000, [term 8 (5302), term 9 (-1936), term 16 (-5346), term 64 (-104), term 65 (14), term 72 (-1883), term 128 (194), term 512 (-104), term 513 (14), term 520 (-1883), term 576 (67), term 1024 (194)]),
  (200000000, [term 9 (755), term 16 (92), term 64 (-170), term 65 (141), term 72 (157), term 128 (41), term 512 (-170), term 513 (141), term 520 (157), term 576 (148), term 1024 (41)]),
  (200000000, [term 16 (1107), term 64 (443), term 65 (-257), term 72 (-54), term 128 (-166), term 512 (443), term 513 (-257), term 520 (-54), term 576 (-362), term 1024 (-166)]),
  (200000000, [term 64 (5280), term 65 (-1918), term 72 (-1918), term 128 (-5350), term 512 (-149), term 513 (40), term 520 (40), term 576 (-1854), term 1024 (214)]),
  (200000000, [term 65 (744), term 72 (101), term 128 (146), term 512 (-99), term 513 (95), term 520 (56), term 576 (125), term 1024 (20)]),
  (200000000, [term 72 (737), term 128 (128), term 512 (-87), term 513 (44), term 520 (88), term 576 (109), term 1024 (17)]),
  (200000000, [term 128 (1045), term 512 (344), term 513 (-192), term 520 (-192), term 576 (-11), term 1024 (-138)]),
  (200000000, [term 512 (5265), term 513 (-1907), term 520 (-1907), term 576 (-1907), term 1024 (-5349)]),
  (200000000, [term 513 (739), term 520 (93), term 576 (92), term 1024 (175)]),
  (200000000, [term 520 (733), term 576 (81), term 1024 (155)]),
  (200000000, [term 576 (728), term 1024 (139)]),
  (800000000, [term 1024 (499)]),
  (866279194285, [term 0 (1), term 1 (-1)]),
  (1012421095830, [term 0 (1), term 2 (-1)]),
  (866279194285, [term 0 (1), term 8 (-1)]),
  (1910504340000, [term 0 (1), term 9 (1)]),
  (1012421095830, [term 0 (1), term 16 (-1)]),
  (866279194285, [term 0 (1), term 64 (-1)]),
  (1910504340000, [term 0 (1), term 65 (1)]),
  (1910504340000, [term 0 (1), term 72 (1)]),
  (1012421095830, [term 0 (1), term 128 (-1)]),
  (866279194285, [term 0 (1), term 512 (-1)]),
  (1910504340000, [term 0 (1), term 513 (1)]),
  (1910504340000, [term 0 (1), term 520 (1)]),
  (1910504340000, [term 0 (1), term 576 (1)]),
  (1012421095830, [term 0 (1), term 1024 (-1)]),
  (1541923888230, [term 1 (1), term 2 (1)]),
  (614200000000, [term 1 (1), term 8 (1)]),
  (1863726676000, [term 1 (1), term 9 (-1)]),
  (1188273324000, [term 1 (1), term 16 (1)]),
  (614200000000, [term 1 (1), term 64 (1)]),
  (1863726676000, [term 1 (1), term 65 (-1)]),
  (2036016672000, [term 1 (1), term 72 (-1)]),
  (1188273324000, [term 1 (1), term 128 (1)]),
  (614200000000, [term 1 (1), term 512 (1)]),
  (1863726676000, [term 1 (1), term 513 (-1)]),
  (2236016672000, [term 1 (1), term 520 (-1)]),
  (2036016672000, [term 1 (1), term 576 (-1)]),
  (1188273324000, [term 1 (1), term 1024 (1)]),
  (1833600000000, [term 2 (1), term 8 (1)]),
  (1211802752000, [term 2 (1), term 9 (-1)]),
  (606050412000, [term 2 (1), term 16 (-1)]),
  (1833600000000, [term 2 (1), term 64 (1)]),
  (1211802752000, [term 2 (1), term 65 (-1)]),
  (1144602752000, [term 2 (1), term 72 (-1)]),
  (606050412000, [term 2 (1), term 128 (-1)]),
  (1833600000000, [term 2 (1), term 512 (1)]),
  (1211802752000, [term 2 (1), term 513 (-1)]),
  (907602752000, [term 2 (1), term 520 (-1)]),
  (1144602752000, [term 2 (1), term 576 (-1)]),
  (606050412000, [term 2 (1), term 1024 (-1)]),
  (2880000000000, [term 8 (1), term 9 (-1)]),
  (804323888230, [term 8 (1), term 16 (1)]),
  (1174200000000, [term 8 (1), term 64 (1)]),
  (2660000000000, [term 8 (1), term 65 (-1)]),
  (2420926676000, [term 8 (1), term 72 (-1)]),
  (1837873324000, [term 8 (1), term 128 (1)]),
  (1174200000000, [term 8 (1), term 512 (1)]),
  (2660000000000, [term 8 (1), term 513 (-1)]),
  (2301726676000, [term 8 (1), term 520 (-1)]),
  (2139616672000, [term 8 (1), term 576 (-1)]),
  (1837873324000, [term 8 (1), term 1024 (1)]),
  (103202752000, [term 9 (1), term 16 (-1)]),
  (2413200000000, [term 9 (1), term 64 (-1)]),
  (3127200000000, [term 9 (1), term 65 (1)]),
  (3371997248000, [term 9 (1), term 72 (1)]),
  (714202752000, [term 9 (1), term 128 (-1)]),
  (2413200000000, [term 9 (1), term 512 (-1)]),
  (3127200000000, [term 9 (1), term 513 (1)]),
  (3346197248000, [term 9 (1), term 520 (1)]),
  (3073000000000, [term 9 (1), term 576 (1)]),
  (714202752000, [term 9 (1), term 1024 (-1)]),
  (1373400000000, [term 16 (1), term 64 (1)]),
  (263800000000, [term 16 (1), term 65 (-1)]),
  (874002752000, [term 16 (1), term 72 (-1)]),
  (1234850412000, [term 16 (1), term 128 (-1)]),
  (1373400000000, [term 16 (1), term 512 (1)]),
  (263800000000, [term 16 (1), term 513 (-1)]),
  (915602752000, [term 16 (1), term 520 (-1)]),
  (977202752000, [term 16 (1), term 576 (-1)]),
  (1234850412000, [term 16 (1), term 1024 (-1)]),
  (2551000000000, [term 64 (1), term 65 (-1)]),
  (2823200000000, [term 64 (1), term 72 (-1)]),
  (1642723888230, [term 64 (1), term 128 (1)]),
  (1043600000000, [term 64 (1), term 512 (1)]),
  (2199000000000, [term 64 (1), term 513 (-1)]),
  (2352000000000, [term 64 (1), term 520 (-1)]),
  (2831326676000, [term 64 (1), term 576 (-1)]),
  (1708273324000, [term 64 (1), term 1024 (1)]),
  (3574400000000, [term 65 (1), term 72 (1)]),
  (456602752000, [term 65 (1), term 128 (-1)]),
  (2384200000000, [term 65 (1), term 512 (-1)]),
  (2980200000000, [term 65 (1), term 513 (1)]),
  (3333400000000, [term 65 (1), term 520 (1)]),
  (3414197248000, [term 65 (1), term 576 (1)]),
  (757402752000, [term 65 (1), term 1024 (-1)]),
  (733402752000, [term 72 (1), term 128 (-1)]),
  (2564000000000, [term 72 (1), term 512 (-1)]),
  (3287400000000, [term 72 (1), term 513 (1)]),
  (3251600000000, [term 72 (1), term 520 (1)]),
  (3545597248000, [term 72 (1), term 576 (1)]),
  (876402752000, [term 72 (1), term 1024 (-1)]),
  (1451200000000, [term 128 (1), term 512 (1)]),
  (742200000000, [term 128 (1), term 513 (-1)]),
  (956600000000, [term 128 (1), term 520 (-1)]),
  (390202752000, [term 128 (1), term 576 (-1)]),
  (1229450412000, [term 128 (1), term 1024 (-1)]),
  (2839800000000, [term 512 (1), term 513 (-1)]),
  (2999400000000, [term 512 (1), term 520 (-1)]),
  (2738200000000, [term 512 (1), term 576 (-1)]),
  (1103123888230, [term 512 (1), term 1024 (1)]),
  (3715800000000, [term 513 (1), term 520 (1)]),
  (3458600000000, [term 513 (1), term 576 (1)]),
  (13797248000, [term 513 (1), term 1024 (1)]),
  (3511800000000, [term 520 (1), term 576 (1)]),
  (319602752000, [term 520 (1), term 1024 (-1)]),
  (369802752000, [term 576 (1), term 1024 (-1)]),
  (70734511697916, [term 0 (1)]),
  (69900946901485, [term 1 (1)]),
  (71475423021310, [term 2 (1)]),
  (65446980245485, [term 8 (1)]),
  (61903563480000, [term 9 (1)]),
  (76423755201310, [term 16 (1)]),
  (64593596917485, [term 64 (1)]),
  (61631763480000, [term 65 (1)]),
  (60074546808000, [term 72 (1)]),
  (73359081877310, [term 128 (1)]),
  (64674796917485, [term 512 (1)]),
  (61859368984000, [term 513 (1)]),
  (60268346808000, [term 520 (1)]),
  (61209930136000, [term 576 (1)]),
  (75567608553310, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p0 : Poly := [term 0 (57286096538898376), term 1 (-166033930558388570), term 2 (176113674357808340), term 3 (-83727232952223540), term 4 (16923224535753370), term 8 (-166033930558388570), term 9 (377308382608680000), term 10 (-274060733853352000), term 11 (63475395994496000), term 16 (176113674357808340), term 17 (-274060733853352000), term 18 (104272784299176000), term 24 (-83727232952223540), term 25 (63475395994496000), term 32 (16923224535753370), term 64 (-166033930558388570), term 65 (377308382608680000), term 66 (-274060733853352000), term 67 (63475395994496000), term 72 (377308382608680000), term 73 (-593846211233344000), term 74 (223331795994496000), term 80 (-274060733853352000), term 81 (223331795994496000), term 88 (63475395994496000), term 128 (176113674357808340), term 129 (-274060733853352000), term 130 (104272784299176000), term 136 (-274060733853352000), term 137 (223331795994496000), term 144 (104272784299176000), term 192 (-83727232952223540), term 193 (63475395994496000), term 200 (63475395994496000), term 256 (16923224535753370), term 512 (-166033930558388570), term 513 (377308382608680000), term 514 (-274060733853352000), term 515 (63475395994496000), term 520 (377308382608680000), term 521 (-593846611233344000), term 522 (223331795994496000), term 528 (-274060733853352000), term 529 (223331795994496000), term 536 (63475395994496000), term 576 (377308382608680000), term 577 (-593846211233344000), term 578 (223331795994496000), term 584 (-593846211233344000), term 585 (487944000000000000), term 592 (223331795994496000), term 640 (-274060733853352000), term 641 (223331795994496000), term 648 (223331795994496000), term 704 (63475395994496000), term 1024 (176113674357808340), term 1025 (-274060733853352000), term 1026 (104272784299176000), term 1032 (-274060733853352000), term 1033 (223331795994496000), term 1040 (104272784299176000), term 1088 (-274060733853352000), term 1089 (223331795994496000), term 1096 (223331795994496000), term 1152 (104272784299176000), term 1536 (-83727232952223540), term 1537 (63475395994496000), term 1544 (63475395994496000), term 1600 (63475395994496000), term 2048 (16923224535753370)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id0 : zeroCoeffs (add (squares b0) (scale (-1) p0)) = true := by rfl

private theorem pos0 (x : Point) : 0 ≤ value x p0 := block_nonneg x b0 p0 id0

set_option maxHeartbeats 3000000 in
private def b1 : Block := [
  (20000000000, [term 0 (67)]),
  (89620000000000, [term 0 (1)])
]

set_option maxHeartbeats 3000000 in
private def p1 : Poly := [term 0 (179400000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id1 : zeroCoeffs (add (squares b1) (scale (-1) p1)) = true := by rfl

private theorem pos1 (x : Point) : 0 ≤ value x p1 := block_nonneg x b1 p1 id1

set_option maxHeartbeats 3000000 in
private def b2 : Block := [
  (5000000000, [term 0 (5049)]),
  (127458195000000000, [term 0 (1)])
]

set_option maxHeartbeats 3000000 in
private def p2 : Poly := [term 0 (254920200000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id2 : zeroCoeffs (add (squares b2) (scale (-1) p2)) = true := by rfl

private theorem pos2 (x : Point) : 0 ≤ value x p2 := block_nonneg x b2 p2 id2

set_option maxHeartbeats 3000000 in
private def b10 : Block := [
  (200000000, [term 0 (28843), term 1 (-16356), term 2 (-9887), term 8 (-16356), term 9 (4226), term 16 (-9887), term 64 (-16356), term 65 (4226), term 72 (4226), term 128 (-9887), term 512 (-19857), term 513 (14317), term 520 (14317), term 576 (14317), term 1024 (-10576)]),
  (200000000, [term 1 (10986), term 2 (-7412), term 8 (3680), term 9 (-5213), term 16 (-1382), term 64 (3680), term 65 (-5213), term 72 (-2962), term 128 (-1382), term 512 (-15109), term 513 (-2438), term 520 (1758), term 576 (1758), term 1024 (15756)]),
  (200000000, [term 2 (5226), term 8 (2315), term 9 (-3161), term 16 (-627), term 64 (2315), term 65 (-3161), term 72 (2977), term 128 (-627), term 512 (-14161), term 513 (188), term 520 (2614), term 576 (2614), term 1024 (14811)]),
  (200000000, [term 8 (10089), term 9 (-3049), term 16 (-7423), term 64 (2134), term 65 (-598), term 72 (-5279), term 128 (-857), term 512 (-7691), term 513 (2761), term 520 (-3896), term 576 (673), term 1024 (8010)]),
  (200000000, [term 9 (11695), term 16 (-829), term 64 (40), term 65 (-6546), term 72 (-5104), term 128 (2199), term 512 (-2122), term 513 (853), term 520 (1643), term 576 (-1458), term 1024 (2233)]),
  (200000000, [term 16 (4914), term 64 (1471), term 65 (3756), term 72 (-4788), term 128 (26), term 512 (-10299), term 513 (3781), term 520 (-903), term 576 (1726), term 1024 (10780)]),
  (200000000, [term 64 (9750), term 65 (-3564), term 72 (-3564), term 128 (-7507), term 512 (-4712), term 513 (1678), term 520 (1678), term 576 (-4433), term 1024 (4900)]),
  (200000000, [term 65 (8721), term 72 (-8584), term 128 (-4), term 512 (233), term 513 (66), term 520 (-149), term 576 (-37), term 1024 (-221)]),
  (200000000, [term 72 (1540), term 128 (-46), term 512 (2624), term 513 (-478), term 520 (-459), term 576 (-416), term 1024 (-2487)]),
  (200000000, [term 128 (4245), term 512 (-6752), term 513 (2437), term 520 (2437), term 576 (-1517), term 1024 (7066)]),
  (200000000, [term 512 (10817), term 513 (-3712), term 520 (-3712), term 576 (-3712), term 1024 (-11045)]),
  (200000000, [term 513 (1345), term 520 (77), term 576 (77), term 1024 (305)]),
  (200000000, [term 520 (1343), term 576 (73), term 1024 (288)]),
  (200000000, [term 576 (1341), term 1024 (273)]),
  (3200000000, [term 1024 (261)]),
  (1221600000000, [term 0 (1), term 1 (1)]),
  (1251800000000, [term 0 (1), term 2 (-1)]),
  (1221600000000, [term 0 (1), term 8 (1)]),
  (1903600000000, [term 0 (1), term 9 (-1)]),
  (1251800000000, [term 0 (1), term 16 (-1)]),
  (1221600000000, [term 0 (1), term 64 (1)]),
  (1903600000000, [term 0 (1), term 65 (-1)]),
  (1903600000000, [term 0 (1), term 72 (-1)]),
  (1251800000000, [term 0 (1), term 128 (-1)]),
  (109800000000, [term 0 (1), term 512 (-1)]),
  (1553800000000, [term 0 (1), term 513 (1)]),
  (1553800000000, [term 0 (1), term 520 (1)]),
  (1553800000000, [term 0 (1), term 576 (1)]),
  (913600000000, [term 0 (1), term 1024 (1)]),
  (292000000000, [term 1 (1), term 2 (1)]),
  (443200000000, [term 1 (1), term 8 (-1)]),
  (1094800000000, [term 1 (1), term 9 (1)]),
  (776000000000, [term 1 (1), term 16 (1)]),
  (443200000000, [term 1 (1), term 64 (-1)]),
  (1094800000000, [term 1 (1), term 65 (1)]),
  (1197600000000, [term 1 (1), term 72 (1)]),
  (776000000000, [term 1 (1), term 128 (1)]),
  (123600000000, [term 1 (1), term 512 (-1)]),
  (544000000000, [term 1 (1), term 513 (1)]),
  (107200000000, [term 1 (1), term 520 (-1)]),
  (107200000000, [term 1 (1), term 576 (-1)]),
  (1094400000000, [term 1 (1), term 1024 (-1)]),
  (160400000000, [term 2 (1), term 8 (-1)]),
  (818400000000, [term 2 (1), term 9 (1)]),
  (1042154976000, [term 2 (1), term 16 (1)]),
  (160400000000, [term 2 (1), term 64 (-1)]),
  (818400000000, [term 2 (1), term 65 (1)]),
  (663200000000, [term 2 (1), term 72 (1)]),
  (1042154976000, [term 2 (1), term 128 (1)]),
  (2663800000000, [term 2 (1), term 512 (1)]),
  (1620645024000, [term 2 (1), term 513 (-1)]),
  (1525445024000, [term 2 (1), term 520 (-1)]),
  (1525445024000, [term 2 (1), term 576 (-1)]),
  (2012845024000, [term 2 (1), term 1024 (-1)]),
  (325600000000, [term 8 (1), term 9 (-1)]),
  (228000000000, [term 8 (1), term 16 (1)]),
  (1057400000000, [term 8 (1), term 64 (-1)]),
  (46600000000, [term 8 (1), term 65 (1)]),
  (738400000000, [term 8 (1), term 72 (1)]),
  (953200000000, [term 8 (1), term 128 (1)]),
  (1951600000000, [term 8 (1), term 512 (-1)]),
  (1251400000000, [term 8 (1), term 513 (-1)]),
  (949200000000, [term 8 (1), term 520 (1)]),
  (421000000000, [term 8 (1), term 576 (1)]),
  (1501800000000, [term 8 (1), term 1024 (1)]),
  (84600000000, [term 9 (1), term 16 (-1)]),
  (1155400000000, [term 9 (1), term 64 (1)]),
  (960400000000, [term 9 (1), term 65 (1)]),
  (984800000000, [term 9 (1), term 72 (1)]),
  (229800000000, [term 9 (1), term 128 (-1)]),
  (3095000000000, [term 9 (1), term 512 (1)]),
  (1042800000000, [term 9 (1), term 513 (-1)]),
  (107754976000, [term 9 (1), term 520 (1)]),
  (1009400000000, [term 9 (1), term 576 (-1)]),
  (1134000000000, [term 9 (1), term 1024 (-1)]),
  (768200000000, [term 16 (1), term 64 (1)]),
  (1315400000000, [term 16 (1), term 65 (1)]),
  (1511200000000, [term 16 (1), term 72 (1)]),
  (507154976000, [term 16 (1), term 128 (1)]),
  (777800000000, [term 16 (1), term 512 (-1)]),
  (1211000000000, [term 16 (1), term 513 (-1)]),
  (1448845024000, [term 16 (1), term 520 (-1)]),
  (638445024000, [term 16 (1), term 576 (-1)]),
  (1301154976000, [term 16 (1), term 1024 (1)]),
  (218600000000, [term 64 (1), term 65 (-1)]),
  (1111000000000, [term 64 (1), term 72 (1)]),
  (1275000000000, [term 64 (1), term 128 (1)]),
  (2990800000000, [term 64 (1), term 512 (-1)]),
  (205400000000, [term 64 (1), term 513 (1)]),
  (1631800000000, [term 64 (1), term 520 (1)]),
  (588800000000, [term 64 (1), term 576 (1)]),
  (1071800000000, [term 64 (1), term 1024 (1)]),
  (3123000000000, [term 65 (1), term 72 (-1)]),
  (319400000000, [term 65 (1), term 128 (1)]),
  (3239400000000, [term 65 (1), term 512 (1)]),
  (1896400000000, [term 65 (1), term 513 (-1)]),
  (2315000000000, [term 65 (1), term 520 (-1)]),
  (1335445024000, [term 65 (1), term 576 (-1)]),
  (953200000000, [term 65 (1), term 1024 (-1)]),
  (438800000000, [term 72 (1), term 128 (1)]),
  (315200000000, [term 72 (1), term 512 (1)]),
  (231800000000, [term 72 (1), term 513 (-1)]),
  (752800000000, [term 72 (1), term 520 (-1)]),
  (1723845024000, [term 72 (1), term 576 (-1)]),
  (655800000000, [term 72 (1), term 1024 (1)]),
  (1997400000000, [term 128 (1), term 512 (-1)]),
  (1236000000000, [term 128 (1), term 513 (-1)]),
  (1333400000000, [term 128 (1), term 520 (-1)]),
  (1349645024000, [term 128 (1), term 576 (-1)]),
  (3561154976000, [term 128 (1), term 1024 (1)]),
  (2882200000000, [term 512 (1), term 513 (-1)]),
  (5069000000000, [term 512 (1), term 520 (-1)]),
  (4157000000000, [term 512 (1), term 576 (-1)]),
  (495400000000, [term 512 (1), term 1024 (1)]),
  (3594600000000, [term 513 (1), term 520 (1)]),
  (2237200000000, [term 513 (1), term 576 (1)]),
  (1307377488000, [term 513 (1), term 1024 (1)]),
  (1833000000000, [term 520 (1), term 576 (1)]),
  (2917777488000, [term 520 (1), term 1024 (1)]),
  (3007177488000, [term 576 (1), term 1024 (1)]),
  (70254400000000, [term 0 (1)]),
  (77698000000000, [term 1 (1)]),
  (74417464928000, [term 2 (1)]),
  (76294200000000, [term 8 (1)]),
  (76895245024000, [term 9 (1)]),
  (79193000000000, [term 16 (1)]),
  (74849000000000, [term 64 (1)]),
  (70548554976000, [term 65 (1)]),
  (75168554976000, [term 72 (1)]),
  (73310645024000, [term 128 (1)]),
  (59208200000000, [term 512 (1)]),
  (70419377488000, [term 513 (1)]),
  (67704377488000, [term 520 (1)]),
  (70611797392000, [term 576 (1)]),
  (65203594885806, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p10 : Poly := [term 0 (166472800000000000), term 1 (-188700000000000000), term 2 (-36341600000000000), term 3 (32114000000000000), term 4 (36090332354976000), term 8 (-188700000000000000), term 9 (171930400000000000), term 10 (8059200000000000), term 11 (-7863600000000000), term 16 (-36341600000000000), term 17 (8059200000000000), term 18 (82199864709952000), term 24 (32114000000000000), term 25 (-7863600000000000), term 32 (36090332354976000), term 64 (-188700000000000000), term 65 (171930400000000000), term 66 (8059200000000000), term 67 (-7863600000000000), term 72 (171930400000000000), term 73 (-121986000000000000), term 74 (-9587200000000000), term 80 (8059200000000000), term 81 (-9587200000000000), term 88 (-7863600000000000), term 128 (-36341600000000000), term 129 (8059200000000000), term 130 (82199864709952000), term 136 (8059200000000000), term 137 (-9587200000000000), term 144 (82199864709952000), term 192 (32114000000000000), term 193 (-7863600000000000), term 200 (-7863600000000000), term 256 (36090332354976000), term 512 (-229094400000000000), term 513 (228698400000000000), term 514 (-10651200000000000), term 515 (-49002935290048000), term 520 (228698400000000000), term 521 (-156581200000000000), term 522 (-26703335290048000), term 528 (-10651200000000000), term 529 (-26703335290048000), term 536 (-49002935290048000), term 576 (228698400000000000), term 577 (-156581200000000000), term 578 (-26703335290048000), term 584 (-156581200000000000), term 585 (28761600000000000), term 592 (-26703335290048000), term 640 (-10651200000000000), term 641 (-26703335290048000), term 648 (-26703335290048000), term 704 (-49002935290048000), term 1024 (114989400000000000), term 1025 (-12720400000000000), term 1026 (77796264709952000), term 1032 (-12720400000000000), term 1033 (15726400000000000), term 1040 (77796264709952000), term 1088 (-12720400000000000), term 1089 (15726400000000000), term 1096 (15726400000000000), term 1152 (77796264709952000), term 1536 (-244800800000000000), term 1537 (-21693467645024000), term 1544 (-21693467645024000), term 1600 (-21693467645024000), term 2048 (193752860482325806)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id10 : zeroCoeffs (add (squares b10) (scale (-1) p10)) = true := by rfl

private theorem pos10 (x : Point) : 0 ≤ value x p10 := block_nonneg x b10 p10 id10

set_option maxHeartbeats 3000000 in
private def b11 : Block := [
  (200000000, [term 0 (28843), term 1 (-16356), term 2 (-9887), term 8 (-16356), term 9 (4226), term 16 (-9887), term 64 (-19857), term 65 (14317), term 72 (14317), term 128 (-10576), term 512 (-16356), term 513 (4226), term 520 (4226), term 576 (14317), term 1024 (-9887)]),
  (200000000, [term 1 (10986), term 2 (-7412), term 8 (3680), term 9 (-5213), term 16 (-1382), term 64 (-15109), term 65 (-2438), term 72 (1758), term 128 (15756), term 512 (3680), term 513 (-5213), term 520 (-2962), term 576 (1758), term 1024 (-1382)]),
  (200000000, [term 2 (5226), term 8 (2315), term 9 (-3161), term 16 (-627), term 64 (-14161), term 65 (188), term 72 (2614), term 128 (14811), term 512 (2315), term 513 (-3161), term 520 (2977), term 576 (2614), term 1024 (-627)]),
  (200000000, [term 8 (10089), term 9 (-3049), term 16 (-7423), term 64 (-7691), term 65 (2761), term 72 (-3896), term 128 (8010), term 512 (2134), term 513 (-598), term 520 (-5279), term 576 (673), term 1024 (-857)]),
  (200000000, [term 9 (11695), term 16 (-829), term 64 (-2122), term 65 (853), term 72 (1643), term 128 (2233), term 512 (40), term 513 (-6546), term 520 (-5104), term 576 (-1458), term 1024 (2199)]),
  (200000000, [term 16 (4914), term 64 (-10299), term 65 (3780), term 72 (-903), term 128 (10780), term 512 (1471), term 513 (3756), term 520 (-4788), term 576 (1726), term 1024 (26)]),
  (200000000, [term 64 (13847), term 65 (-4749), term 72 (-4749), term 128 (-14216), term 512 (-3318), term 513 (1360), term 520 (1360), term 576 (-731), term 1024 (476)]),
  (200000000, [term 65 (1425), term 72 (208), term 128 (366), term 512 (426), term 513 (738), term 520 (-580), term 576 (-371), term 1024 (20)]),
  (200000000, [term 72 (1409), term 128 (315), term 512 (367), term 513 (-696), term 520 (832), term 576 (-320), term 1024 (17)]),
  (200000000, [term 128 (1085), term 512 (309), term 513 (-102), term 520 (-103), term 576 (-132), term 1024 (74)]),
  (200000000, [term 512 (9146), term 513 (-3309), term 520 (-3309), term 576 (-4956), term 1024 (-7834)]),
  (800000000, [term 513 (4328), term 520 (-4273), term 576 (6), term 1024 (9)]),
  (200000000, [term 520 (1379), term 576 (153), term 1024 (219)]),
  (800000000, [term 576 (1756), term 1024 (-1657)]),
  (800000000, [term 1024 (659)]),
  (1221600000000, [term 0 (1), term 1 (1)]),
  (1251800000000, [term 0 (1), term 2 (-1)]),
  (1221600000000, [term 0 (1), term 8 (1)]),
  (1903600000000, [term 0 (1), term 9 (-1)]),
  (1251800000000, [term 0 (1), term 16 (-1)]),
  (109800000000, [term 0 (1), term 64 (-1)]),
  (1553800000000, [term 0 (1), term 65 (1)]),
  (1553800000000, [term 0 (1), term 72 (1)]),
  (913600000000, [term 0 (1), term 128 (1)]),
  (1221600000000, [term 0 (1), term 512 (1)]),
  (1903600000000, [term 0 (1), term 513 (-1)]),
  (1903600000000, [term 0 (1), term 520 (-1)]),
  (1553800000000, [term 0 (1), term 576 (1)]),
  (1251800000000, [term 0 (1), term 1024 (-1)]),
  (292000000000, [term 1 (1), term 2 (1)]),
  (643200000000, [term 1 (1), term 8 (-1)]),
  (1094800000000, [term 1 (1), term 9 (1)]),
  (776000000000, [term 1 (1), term 16 (1)]),
  (123600000000, [term 1 (1), term 64 (-1)]),
  (544000000000, [term 1 (1), term 65 (1)]),
  (107200000000, [term 1 (1), term 72 (-1)]),
  (1094400000000, [term 1 (1), term 128 (-1)]),
  (643200000000, [term 1 (1), term 512 (-1)]),
  (1094800000000, [term 1 (1), term 513 (1)]),
  (1197600000000, [term 1 (1), term 520 (1)]),
  (107200000000, [term 1 (1), term 576 (-1)]),
  (776000000000, [term 1 (1), term 1024 (1)]),
  (160400000000, [term 2 (1), term 8 (-1)]),
  (818400000000, [term 2 (1), term 9 (1)]),
  (1042154976000, [term 2 (1), term 16 (1)]),
  (2663800000000, [term 2 (1), term 64 (1)]),
  (1620645024000, [term 2 (1), term 65 (-1)]),
  (1525445024000, [term 2 (1), term 72 (-1)]),
  (2012845024000, [term 2 (1), term 128 (-1)]),
  (160400000000, [term 2 (1), term 512 (-1)]),
  (1018400000000, [term 2 (1), term 513 (1)]),
  (663200000000, [term 2 (1), term 520 (1)]),
  (1457800000000, [term 2 (1), term 576 (-1)]),
  (1109800000000, [term 2 (1), term 1024 (1)]),
  (325600000000, [term 8 (1), term 9 (-1)]),
  (228000000000, [term 8 (1), term 16 (1)]),
  (1951600000000, [term 8 (1), term 64 (-1)]),
  (1251400000000, [term 8 (1), term 65 (-1)]),
  (949200000000, [term 8 (1), term 72 (1)]),
  (1501800000000, [term 8 (1), term 128 (1)]),
  (1257400000000, [term 8 (1), term 512 (-1)]),
  (46600000000, [term 8 (1), term 513 (1)]),
  (738400000000, [term 8 (1), term 520 (1)]),
  (421000000000, [term 8 (1), term 576 (1)]),
  (953200000000, [term 8 (1), term 1024 (1)]),
  (84600000000, [term 9 (1), term 16 (-1)]),
  (3095000000000, [term 9 (1), term 64 (1)]),
  (1042800000000, [term 9 (1), term 65 (-1)]),
  (107754976000, [term 9 (1), term 72 (1)]),
  (1134000000000, [term 9 (1), term 128 (-1)]),
  (1155400000000, [term 9 (1), term 512 (1)]),
  (960400000000, [term 9 (1), term 513 (1)]),
  (984800000000, [term 9 (1), term 520 (1)]),
  (1009400000000, [term 9 (1), term 576 (-1)]),
  (229800000000, [term 9 (1), term 1024 (-1)]),
  (777800000000, [term 16 (1), term 64 (-1)]),
  (228200000000, [term 16 (1), term 65 (-1)]),
  (1448845024000, [term 16 (1), term 72 (-1)]),
  (1301154976000, [term 16 (1), term 128 (1)]),
  (768200000000, [term 16 (1), term 512 (1)]),
  (1315400000000, [term 16 (1), term 513 (1)]),
  (1711200000000, [term 16 (1), term 520 (1)]),
  (570800000000, [term 16 (1), term 576 (-1)]),
  (574800000000, [term 16 (1), term 1024 (1)]),
  (3653000000000, [term 64 (1), term 65 (-1)]),
  (3827800000000, [term 64 (1), term 72 (-1)]),
  (370200000000, [term 64 (1), term 128 (1)]),
  (2521600000000, [term 64 (1), term 512 (-1)]),
  (1967600000000, [term 64 (1), term 513 (1)]),
  (822400000000, [term 64 (1), term 520 (1)]),
  (4091400000000, [term 64 (1), term 576 (-1)]),
  (2410200000000, [term 64 (1), term 1024 (-1)]),
  (2879800000000, [term 65 (1), term 72 (1)]),
  (1897977488000, [term 65 (1), term 128 (1)]),
  (246800000000, [term 65 (1), term 512 (-1)]),
  (708400000000, [term 65 (1), term 513 (-1)]),
  (772600000000, [term 65 (1), term 520 (-1)]),
  (2696000000000, [term 65 (1), term 576 (1)]),
  (817400000000, [term 65 (1), term 1024 (-1)]),
  (1730977488000, [term 72 (1), term 128 (1)]),
  (1153200000000, [term 72 (1), term 512 (1)]),
  (1119200000000, [term 72 (1), term 513 (-1)]),
  (1001600000000, [term 72 (1), term 520 (-1)]),
  (1912000000000, [term 72 (1), term 576 (1)]),
  (845400000000, [term 72 (1), term 1024 (-1)]),
  (977000000000, [term 128 (1), term 512 (1)]),
  (229000000000, [term 128 (1), term 513 (-1)]),
  (695600000000, [term 128 (1), term 520 (1)]),
  (2840800000000, [term 128 (1), term 576 (1)]),
  (3630200000000, [term 128 (1), term 1024 (1)]),
  (187400000000, [term 512 (1), term 513 (-1)]),
  (1342400000000, [term 512 (1), term 520 (1)]),
  (82800000000, [term 512 (1), term 576 (-1)]),
  (926400000000, [term 512 (1), term 1024 (1)]),
  (576400000000, [term 513 (1), term 520 (-1)]),
  (261200000000, [term 513 (1), term 576 (-1)]),
  (281400000000, [term 513 (1), term 1024 (1)]),
  (1663200000000, [term 520 (1), term 576 (-1)]),
  (1695400000000, [term 520 (1), term 1024 (1)]),
  (413000000000, [term 576 (1), term 1024 (1)]),
  (70254400000000, [term 0 (1)]),
  (77298000000000, [term 1 (1)]),
  (74217464928000, [term 2 (1)]),
  (75894200000000, [term 8 (1)]),
  (76895245024000, [term 9 (1)]),
  (79975800000000, [term 16 (1)]),
  (60729000000000, [term 64 (1)]),
  (71200577488000, [term 65 (1)]),
  (71583977488000, [term 72 (1)]),
  (66754127349806, [term 128 (1)]),
  (74587400000000, [term 512 (1)]),
  (77029600000000, [term 513 (1)]),
  (71687400000000, [term 520 (1)]),
  (73864200000000, [term 576 (1)]),
  (74515200000000, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p11 : Poly := [term 0 (166472800000000000), term 1 (-188700000000000000), term 2 (-36341600000000000), term 3 (32114000000000000), term 4 (36090332354976000), term 8 (-188700000000000000), term 9 (171930000000000000), term 10 (8059200000000000), term 11 (-7863600000000000), term 16 (-36341600000000000), term 17 (8059200000000000), term 18 (82199864709952000), term 24 (32114000000000000), term 25 (-7863600000000000), term 32 (36090332354976000), term 64 (-229094400000000000), term 65 (228698400000000000), term 66 (-10651200000000000), term 67 (-49002935290048000), term 72 (228698400000000000), term 73 (-156581200000000000), term 74 (-26703335290048000), term 80 (-10651200000000000), term 81 (-26703335290048000), term 88 (-49002935290048000), term 128 (114989400000000000), term 129 (-12720400000000000), term 130 (77796264709952000), term 136 (-12720400000000000), term 137 (15726400000000000), term 144 (77796264709952000), term 192 (-244800800000000000), term 193 (-21693467645024000), term 200 (-21693467645024000), term 256 (193752860482325806), term 512 (-188700000000000000), term 513 (171930000000000000), term 514 (8059200000000000), term 515 (-7863200000000000), term 520 (171930000000000000), term 521 (-121986000000000000), term 522 (-9587200000000000), term 528 (8059200000000000), term 529 (-9587200000000000), term 536 (-7863200000000000), term 576 (228698400000000000), term 577 (-156581200000000000), term 578 (-26703200000000000), term 584 (-156581200000000000), term 585 (28761600000000000), term 592 (-26703200000000000), term 640 (-12720400000000000), term 641 (15726800000000000), term 648 (15726800000000000), term 704 (-21693600000000000), term 1024 (-36341600000000000), term 1025 (8059200000000000), term 1026 (82200000000000000), term 1032 (8059200000000000), term 1033 (-9587200000000000), term 1040 (82200000000000000), term 1088 (-10651200000000000), term 1089 (-26703200000000000), term 1096 (-26703200000000000), term 1152 (77796400000000000), term 1536 (32114000000000000), term 1537 (-7863200000000000), term 1544 (-7863200000000000), term 1600 (-49002800000000000), term 2048 (36090200000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id11 : zeroCoeffs (add (squares b11) (scale (-1) p11)) = true := by rfl

private theorem pos11 (x : Point) : 0 ≤ value x p11 := block_nonneg x b11 p11 id11

set_option maxHeartbeats 3000000 in
private def b12 : Block := [
  (200000000, [term 0 (28843), term 1 (-16356), term 2 (-9887), term 8 (-19857), term 9 (14317), term 16 (-10576), term 64 (-16356), term 65 (4226), term 72 (14317), term 128 (-9887), term 512 (-16356), term 513 (4226), term 520 (14317), term 576 (4226), term 1024 (-9887)]),
  (200000000, [term 1 (10986), term 2 (-7412), term 8 (-15109), term 9 (-2438), term 16 (15756), term 64 (3680), term 65 (-5213), term 72 (1758), term 128 (-1382), term 512 (3680), term 513 (-5213), term 520 (1758), term 576 (-2962), term 1024 (-1382)]),
  (200000000, [term 2 (5226), term 8 (-14161), term 9 (188), term 16 (14811), term 64 (2315), term 65 (-3161), term 72 (2614), term 128 (-627), term 512 (2315), term 513 (-3161), term 520 (2614), term 576 (2977), term 1024 (-627)]),
  (200000000, [term 8 (19012), term 9 (-6719), term 16 (-19683), term 64 (-4081), term 65 (-72), term 72 (-1577), term 128 (433), term 512 (-4081), term 513 (-72), term 520 (-1577), term 576 (6289), term 1024 (433)]),
  (200000000, [term 9 (1443), term 16 (388), term 64 (299), term 65 (746), term 72 (-355), term 128 (201), term 512 (299), term 513 (746), term 520 (-355), term 576 (-1424), term 1024 (201)]),
  (200000000, [term 16 (1136), term 64 (326), term 65 (-10), term 72 (-129), term 128 (100), term 512 (326), term 513 (-10), term 520 (-129), term 576 (-307), term 1024 (100)]),
  (200000000, [term 64 (9216), term 65 (-3394), term 72 (-4947), term 128 (-7945), term 512 (507), term 513 (-710), term 520 (54), term 576 (-2937), term 1024 (-756)]),
  (200000000, [term 65 (11576), term 72 (1249), term 128 (-1222), term 512 (-417), term 513 (-6712), term 520 (-1621), term 576 (-4496), term 1024 (2215)]),
  (200000000, [term 72 (3823), term 128 (-3634), term 512 (924), term 513 (-3684), term 520 (-1038), term 576 (3023), term 1024 (-273)]),
  (200000000, [term 128 (1375), term 512 (-65), term 513 (712), term 520 (104), term 576 (-259), term 1024 (98)]),
  (200000000, [term 512 (9146), term 513 (-3309), term 520 (-4956), term 576 (-3309), term 1024 (-7834)]),
  (800000000, [term 513 (4328), term 520 (6), term 576 (-4273), term 1024 (9)]),
  (200000000, [term 520 (3516), term 576 (60), term 1024 (-3301)]),
  (200000000, [term 576 (1377), term 1024 (362)]),
  (800000000, [term 1024 (659)]),
  (1221600000000, [term 0 (1), term 1 (1)]),
  (1251800000000, [term 0 (1), term 2 (-1)]),
  (109800000000, [term 0 (1), term 8 (-1)]),
  (1553800000000, [term 0 (1), term 9 (1)]),
  (913600000000, [term 0 (1), term 16 (1)]),
  (1221600000000, [term 0 (1), term 64 (1)]),
  (1903600000000, [term 0 (1), term 65 (-1)]),
  (1553800000000, [term 0 (1), term 72 (1)]),
  (1251800000000, [term 0 (1), term 128 (-1)]),
  (1221600000000, [term 0 (1), term 512 (1)]),
  (1903600000000, [term 0 (1), term 513 (-1)]),
  (1553800000000, [term 0 (1), term 520 (1)]),
  (1903600000000, [term 0 (1), term 576 (-1)]),
  (1251800000000, [term 0 (1), term 1024 (-1)]),
  (292000000000, [term 1 (1), term 2 (1)]),
  (123600000000, [term 1 (1), term 8 (-1)]),
  (544000000000, [term 1 (1), term 9 (1)]),
  (1094400000000, [term 1 (1), term 16 (-1)]),
  (443200000000, [term 1 (1), term 64 (-1)]),
  (1094800000000, [term 1 (1), term 65 (1)]),
  (107200000000, [term 1 (1), term 72 (-1)]),
  (776000000000, [term 1 (1), term 128 (1)]),
  (443200000000, [term 1 (1), term 512 (-1)]),
  (1094800000000, [term 1 (1), term 513 (1)]),
  (107200000000, [term 1 (1), term 520 (-1)]),
  (1197600000000, [term 1 (1), term 576 (1)]),
  (776000000000, [term 1 (1), term 1024 (1)]),
  (2663800000000, [term 2 (1), term 8 (1)]),
  (1620645024000, [term 2 (1), term 9 (-1)]),
  (2012845024000, [term 2 (1), term 16 (-1)]),
  (160400000000, [term 2 (1), term 64 (-1)]),
  (1018400000000, [term 2 (1), term 65 (1)]),
  (1457800000000, [term 2 (1), term 72 (-1)]),
  (1109800000000, [term 2 (1), term 128 (1)]),
  (160400000000, [term 2 (1), term 512 (-1)]),
  (1018400000000, [term 2 (1), term 513 (1)]),
  (1457800000000, [term 2 (1), term 520 (-1)]),
  (663200000000, [term 2 (1), term 576 (1)]),
  (1109800000000, [term 2 (1), term 1024 (1)]),
  (2235400000000, [term 8 (1), term 9 (-1)]),
  (92200000000, [term 8 (1), term 16 (-1)]),
  (3257000000000, [term 8 (1), term 64 (-1)]),
  (3481600000000, [term 8 (1), term 65 (1)]),
  (3786200000000, [term 8 (1), term 72 (-1)]),
  (812000000000, [term 8 (1), term 128 (1)]),
  (3257000000000, [term 8 (1), term 512 (-1)]),
  (3481600000000, [term 8 (1), term 513 (1)]),
  (3786200000000, [term 8 (1), term 520 (-1)]),
  (2530600000000, [term 8 (1), term 576 (1)]),
  (812000000000, [term 8 (1), term 1024 (1)]),
  (324377488000, [term 9 (1), term 16 (1)]),
  (444800000000, [term 9 (1), term 64 (-1)]),
  (1582800000000, [term 9 (1), term 65 (-1)]),
  (2297000000000, [term 9 (1), term 72 (1)]),
  (1795400000000, [term 9 (1), term 128 (-1)]),
  (444800000000, [term 9 (1), term 512 (-1)]),
  (1582800000000, [term 9 (1), term 513 (-1)]),
  (2297000000000, [term 9 (1), term 520 (1)]),
  (1210200000000, [term 9 (1), term 576 (-1)]),
  (1795400000000, [term 9 (1), term 1024 (-1)]),
  (1545600000000, [term 16 (1), term 64 (1)]),
  (1497800000000, [term 16 (1), term 65 (-1)]),
  (2356600000000, [term 16 (1), term 72 (1)]),
  (305600000000, [term 16 (1), term 128 (1)]),
  (1545600000000, [term 16 (1), term 512 (1)]),
  (1497800000000, [term 16 (1), term 513 (-1)]),
  (2356600000000, [term 16 (1), term 520 (1)]),
  (249600000000, [term 16 (1), term 576 (-1)]),
  (305600000000, [term 16 (1), term 1024 (1)]),
  (497800000000, [term 64 (1), term 65 (1)]),
  (403200000000, [term 64 (1), term 72 (1)]),
  (1197400000000, [term 64 (1), term 128 (1)]),
  (177800000000, [term 64 (1), term 512 (1)]),
  (651000000000, [term 64 (1), term 513 (-1)]),
  (1360000000000, [term 64 (1), term 520 (1)]),
  (504000000000, [term 64 (1), term 576 (1)]),
  (32600000000, [term 64 (1), term 1024 (1)]),
  (776000000000, [term 65 (1), term 72 (-1)]),
  (184200000000, [term 65 (1), term 128 (1)]),
  (267000000000, [term 65 (1), term 512 (1)]),
  (158800000000, [term 65 (1), term 513 (-1)]),
  (2073200000000, [term 65 (1), term 520 (-1)]),
  (225000000000, [term 65 (1), term 576 (-1)]),
  (935000000000, [term 65 (1), term 1024 (1)]),
  (809200000000, [term 72 (1), term 128 (-1)]),
  (194800000000, [term 72 (1), term 512 (1)]),
  (697600000000, [term 72 (1), term 513 (-1)]),
  (1479400000000, [term 72 (1), term 520 (1)]),
  (1091600000000, [term 72 (1), term 576 (-1)]),
  (795800000000, [term 72 (1), term 1024 (-1)]),
  (280200000000, [term 128 (1), term 512 (-1)]),
  (341800000000, [term 128 (1), term 513 (1)]),
  (1623000000000, [term 128 (1), term 520 (-1)]),
  (894800000000, [term 128 (1), term 576 (1)]),
  (953200000000, [term 128 (1), term 1024 (1)]),
  (227800000000, [term 512 (1), term 513 (-1)]),
  (115400000000, [term 512 (1), term 520 (1)]),
  (676400000000, [term 512 (1), term 576 (1)]),
  (40000000000, [term 512 (1), term 1024 (1)]),
  (306800000000, [term 513 (1), term 520 (1)]),
  (954000000000, [term 513 (1), term 576 (1)]),
  (664600000000, [term 513 (1), term 1024 (-1)]),
  (1422800000000, [term 520 (1), term 576 (-1)]),
  (124400000000, [term 520 (1), term 1024 (-1)]),
  (2196200000000, [term 576 (1), term 1024 (1)]),
  (70254400000000, [term 0 (1)]),
  (77698000000000, [term 1 (1)]),
  (74017464928000, [term 2 (1)]),
  (60092000000000, [term 8 (1)]),
  (70494177488000, [term 9 (1)]),
  (70649859813806, [term 16 (1)]),
  (76252600000000, [term 64 (1)]),
  (72068400000000, [term 65 (1)]),
  (73437200000000, [term 72 (1)]),
  (76545200000000, [term 128 (1)]),
  (78377200000000, [term 512 (1)]),
  (75853200000000, [term 513 (1)]),
  (72177000000000, [term 520 (1)]),
  (74777200000000, [term 576 (1)]),
  (79956600000000, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p12 : Poly := [term 0 (166472800000000000), term 1 (-188700000000000000), term 2 (-36341600000000000), term 3 (32114000000000000), term 4 (36090332354976000), term 8 (-229094400000000000), term 9 (228698400000000000), term 10 (-10651200000000000), term 11 (-49002935290048000), term 16 (114989400000000000), term 17 (-12720400000000000), term 18 (77796264709952000), term 24 (-244800800000000000), term 25 (-21693467645024000), term 32 (193752860482325806), term 64 (-188700000000000000), term 65 (171930400000000000), term 66 (8059200000000000), term 67 (-7863200000000000), term 72 (228698400000000000), term 73 (-156581200000000000), term 74 (-26703200000000000), term 80 (-12720400000000000), term 81 (15726800000000000), term 88 (-21693600000000000), term 128 (-36341600000000000), term 129 (8059200000000000), term 130 (82200000000000000), term 136 (-10651200000000000), term 137 (-26703200000000000), term 144 (77796400000000000), term 192 (32114000000000000), term 193 (-7863200000000000), term 200 (-49002800000000000), term 256 (36090200000000000), term 512 (-188700000000000000), term 513 (171930400000000000), term 514 (8059200000000000), term 515 (-7863200000000000), term 520 (228698400000000000), term 521 (-156581200000000000), term 522 (-26703200000000000), term 528 (-12720400000000000), term 529 (15726800000000000), term 536 (-21693600000000000), term 576 (171930000000000000), term 577 (-121986000000000000), term 578 (-9587200000000000), term 584 (-156581200000000000), term 585 (28761600000000000), term 592 (15726800000000000), term 640 (8059200000000000), term 641 (-9587200000000000), term 648 (-26703200000000000), term 704 (-7863200000000000), term 1024 (-36341600000000000), term 1025 (8059200000000000), term 1026 (82200000000000000), term 1032 (-10651200000000000), term 1033 (-26703200000000000), term 1040 (77796400000000000), term 1088 (8059200000000000), term 1089 (-9587200000000000), term 1096 (-26703200000000000), term 1152 (82200000000000000), term 1536 (32114000000000000), term 1537 (-7863200000000000), term 1544 (-49002800000000000), term 1600 (-7863200000000000), term 2048 (36090200000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id12 : zeroCoeffs (add (squares b12) (scale (-1) p12)) = true := by rfl

private theorem pos12 (x : Point) : 0 ≤ value x p12 := block_nonneg x b12 p12 id12

set_option maxHeartbeats 3000000 in
private def b13 : Block := [
  (200000000, [term 0 (28843), term 1 (-19857), term 2 (-10576), term 8 (-16356), term 9 (14317), term 16 (-9887), term 64 (-16356), term 65 (14317), term 72 (4226), term 128 (-9887), term 512 (-16356), term 513 (14317), term 520 (4226), term 576 (4226), term 1024 (-9887)]),
  (200000000, [term 1 (28112), term 2 (-29241), term 8 (-5904), term 9 (-3329), term 16 (1351), term 64 (-5904), term 65 (-3329), term 72 (4346), term 128 (1351), term 512 (-5904), term 513 (-3329), term 520 (4346), term 576 (4346), term 1024 (1351)]),
  (200000000, [term 2 (1208), term 8 (369), term 9 (-122), term 16 (103), term 64 (369), term 65 (-122), term 72 (-163), term 128 (103), term 512 (369), term 513 (-122), term 520 (-163), term 576 (-163), term 1024 (103)]),
  (200000000, [term 8 (9257), term 9 (-5011), term 16 (-7939), term 64 (587), term 65 (-32), term 72 (-3408), term 128 (-782), term 512 (587), term 513 (-32), term 520 (-3408), term 576 (-737), term 1024 (-782)]),
  (200000000, [term 9 (4123), term 16 (-3934), term 64 (642), term 65 (-1203), term 72 (2677), term 128 (296), term 512 (642), term 513 (-1203), term 520 (2677), term 576 (-6253), term 1024 (296)]),
  (200000000, [term 16 (1381), term 64 (-38), term 65 (111), term 72 (-188), term 128 (64), term 512 (-38), term 513 (111), term 520 (-188), term 576 (872), term 1024 (64)]),
  (200000000, [term 64 (9216), term 65 (-4947), term 72 (-3394), term 128 (-7945), term 512 (507), term 513 (54), term 520 (-710), term 576 (-2937), term 1024 (-756)]),
  (200000000, [term 65 (4021), term 72 (3596), term 128 (-3834), term 512 (749), term 513 (-1491), term 520 (-5587), term 576 (1477), term 1024 (429)]),
  (200000000, [term 72 (11003), term 128 (-33), term 512 (-683), term 513 (-1219), term 520 (-5236), term 576 (-5213), term 1024 (2191)]),
  (200000000, [term 128 (1375), term 512 (-65), term 513 (104), term 520 (711), term 576 (-259), term 1024 (99)]),
  (200000000, [term 512 (9146), term 513 (-4956), term 520 (-3309), term 576 (-3309), term 1024 (-7834)]),
  (200000000, [term 513 (3516), term 520 (30), term 576 (30), term 1024 (-3301)]),
  (200000000, [term 520 (8656), term 576 (-8546), term 1024 (29)]),
  (200000000, [term 576 (1377), term 1024 (362)]),
  (800000000, [term 1024 (659)]),
  (109800000000, [term 0 (1), term 1 (-1)]),
  (913600000000, [term 0 (1), term 2 (1)]),
  (1221600000000, [term 0 (1), term 8 (1)]),
  (1553800000000, [term 0 (1), term 9 (1)]),
  (1251800000000, [term 0 (1), term 16 (-1)]),
  (1221600000000, [term 0 (1), term 64 (1)]),
  (1553800000000, [term 0 (1), term 65 (1)]),
  (1903600000000, [term 0 (1), term 72 (-1)]),
  (1251800000000, [term 0 (1), term 128 (-1)]),
  (1221600000000, [term 0 (1), term 512 (1)]),
  (1553800000000, [term 0 (1), term 513 (1)]),
  (1903600000000, [term 0 (1), term 520 (-1)]),
  (1903600000000, [term 0 (1), term 576 (-1)]),
  (1251800000000, [term 0 (1), term 1024 (-1)]),
  (2672000000000, [term 1 (1), term 2 (1)]),
  (2968800000000, [term 1 (1), term 8 (-1)]),
  (1103400000000, [term 1 (1), term 9 (1)]),
  (3305800000000, [term 1 (1), term 16 (1)]),
  (2968800000000, [term 1 (1), term 64 (-1)]),
  (1103400000000, [term 1 (1), term 65 (1)]),
  (14000000000, [term 1 (1), term 72 (-1)]),
  (3305800000000, [term 1 (1), term 128 (1)]),
  (2968800000000, [term 1 (1), term 512 (-1)]),
  (1103400000000, [term 1 (1), term 513 (1)]),
  (14000000000, [term 1 (1), term 520 (-1)]),
  (14000000000, [term 1 (1), term 576 (-1)]),
  (3305800000000, [term 1 (1), term 1024 (1)]),
  (1065600000000, [term 2 (1), term 8 (1)]),
  (2664200000000, [term 2 (1), term 9 (-1)]),
  (2149000000000, [term 2 (1), term 16 (-1)]),
  (1065600000000, [term 2 (1), term 64 (1)]),
  (2664200000000, [term 2 (1), term 65 (-1)]),
  (2493200000000, [term 2 (1), term 72 (1)]),
  (2149000000000, [term 2 (1), term 128 (-1)]),
  (1065600000000, [term 2 (1), term 512 (1)]),
  (2664200000000, [term 2 (1), term 513 (-1)]),
  (2493200000000, [term 2 (1), term 520 (1)]),
  (2493200000000, [term 2 (1), term 576 (1)]),
  (2149000000000, [term 2 (1), term 1024 (-1)]),
  (743800000000, [term 8 (1), term 9 (-1)]),
  (569600000000, [term 8 (1), term 16 (1)]),
  (394400000000, [term 8 (1), term 64 (-1)]),
  (64400000000, [term 8 (1), term 65 (-1)]),
  (448600000000, [term 8 (1), term 72 (1)]),
  (300200000000, [term 8 (1), term 128 (-1)]),
  (394400000000, [term 8 (1), term 512 (-1)]),
  (64400000000, [term 8 (1), term 513 (-1)]),
  (448600000000, [term 8 (1), term 520 (1)]),
  (1359200000000, [term 8 (1), term 576 (1)]),
  (300200000000, [term 8 (1), term 1024 (-1)]),
  (1444600000000, [term 9 (1), term 16 (-1)]),
  (411000000000, [term 9 (1), term 64 (-1)]),
  (600600000000, [term 9 (1), term 65 (1)]),
  (109400000000, [term 9 (1), term 72 (1)]),
  (1157200000000, [term 9 (1), term 128 (-1)]),
  (411000000000, [term 9 (1), term 512 (-1)]),
  (600600000000, [term 9 (1), term 513 (1)]),
  (109400000000, [term 9 (1), term 520 (1)]),
  (63600000000, [term 9 (1), term 576 (1)]),
  (1157200000000, [term 9 (1), term 1024 (-1)]),
  (435200000000, [term 16 (1), term 64 (-1)]),
  (1343400000000, [term 16 (1), term 65 (-1)]),
  (927800000000, [term 16 (1), term 72 (1)]),
  (840600000000, [term 16 (1), term 128 (1)]),
  (435200000000, [term 16 (1), term 512 (-1)]),
  (1343400000000, [term 16 (1), term 513 (-1)]),
  (927800000000, [term 16 (1), term 520 (1)]),
  (1245600000000, [term 16 (1), term 576 (1)]),
  (840600000000, [term 16 (1), term 1024 (1)]),
  (733200000000, [term 64 (1), term 65 (-1)]),
  (1641800000000, [term 64 (1), term 72 (1)]),
  (815800000000, [term 64 (1), term 128 (1)]),
  (239600000000, [term 64 (1), term 512 (1)]),
  (223600000000, [term 64 (1), term 513 (1)]),
  (493000000000, [term 64 (1), term 520 (1)]),
  (392000000000, [term 64 (1), term 576 (1)]),
  (349000000000, [term 64 (1), term 1024 (-1)]),
  (417000000000, [term 65 (1), term 72 (-1)]),
  (1643400000000, [term 65 (1), term 128 (-1)]),
  (963600000000, [term 65 (1), term 512 (-1)]),
  (1056200000000, [term 65 (1), term 513 (1)]),
  (498800000000, [term 65 (1), term 520 (-1)]),
  (843000000000, [term 65 (1), term 576 (1)]),
  (1551400000000, [term 65 (1), term 1024 (-1)]),
  (1844400000000, [term 72 (1), term 128 (1)]),
  (301600000000, [term 72 (1), term 512 (1)]),
  (423600000000, [term 72 (1), term 513 (1)]),
  (464400000000, [term 72 (1), term 520 (1)]),
  (734200000000, [term 72 (1), term 576 (-1)]),
  (146400000000, [term 72 (1), term 1024 (-1)]),
  (484800000000, [term 128 (1), term 512 (-1)]),
  (2701400000000, [term 128 (1), term 513 (-1)]),
  (693600000000, [term 128 (1), term 520 (1)]),
  (200000000000, [term 128 (1), term 576 (1)]),
  (1545800000000, [term 128 (1), term 1024 (1)]),
  (815600000000, [term 512 (1), term 513 (-1)]),
  (1575800000000, [term 512 (1), term 520 (1)]),
  (830800000000, [term 512 (1), term 576 (1)]),
  (483600000000, [term 512 (1), term 1024 (-1)]),
  (1168000000000, [term 513 (1), term 520 (-1)]),
  (156200000000, [term 513 (1), term 576 (1)]),
  (238400000000, [term 513 (1), term 1024 (1)]),
  (687000000000, [term 520 (1), term 576 (-1)]),
  (2287800000000, [term 520 (1), term 1024 (1)]),
  (1510800000000, [term 576 (1), term 1024 (1)]),
  (70254400000000, [term 0 (1)]),
  (63043600000000, [term 1 (1)]),
  (54734682325806, [term 2 (1)]),
  (78023800000000, [term 8 (1)]),
  (78097400000000, [term 9 (1)]),
  (73176200000000, [term 16 (1)]),
  (76826200000000, [term 64 (1)]),
  (76680000000000, [term 65 (1)]),
  (76938200000000, [term 72 (1)]),
  (70044200000000, [term 128 (1)]),
  (75334000000000, [term 512 (1)]),
  (76460400000000, [term 513 (1)]),
  (75014800000000, [term 520 (1)]),
  (76067400000000, [term 576 (1)]),
  (74114200000000, [term 1024 (1)])
]

set_option maxHeartbeats 3000000 in
private def p13 : Poly := [term 0 (166472800000000000), term 1 (-229094400000000000), term 2 (114989400000000000), term 3 (-244800800000000000), term 4 (193752860482325806), term 8 (-188700000000000000), term 9 (228698400000000000), term 10 (-12720400000000000), term 11 (-21693600000000000), term 16 (-36341600000000000), term 17 (-10651200000000000), term 18 (77796400000000000), term 24 (32114000000000000), term 25 (-49002800000000000), term 32 (36090200000000000), term 64 (-188700000000000000), term 65 (228698400000000000), term 66 (-12720400000000000), term 67 (-21693600000000000), term 72 (171930000000000000), term 73 (-156581200000000000), term 74 (15726800000000000), term 80 (8059200000000000), term 81 (-26703200000000000), term 88 (-7863200000000000), term 128 (-36341600000000000), term 129 (-10651200000000000), term 130 (77796400000000000), term 136 (8059200000000000), term 137 (-26703200000000000), term 144 (82200000000000000), term 192 (32114000000000000), term 193 (-49002800000000000), term 200 (-7863200000000000), term 256 (36090200000000000), term 512 (-188700000000000000), term 513 (228698400000000000), term 514 (-12720400000000000), term 515 (-21693600000000000), term 520 (171930000000000000), term 521 (-156581200000000000), term 522 (15726800000000000), term 528 (8059200000000000), term 529 (-26703200000000000), term 536 (-7863200000000000), term 576 (171930000000000000), term 577 (-156581200000000000), term 578 (15726800000000000), term 584 (-121986000000000000), term 585 (28761600000000000), term 592 (-9587200000000000), term 640 (8059200000000000), term 641 (-26703200000000000), term 648 (-9587200000000000), term 704 (-7863200000000000), term 1024 (-36341600000000000), term 1025 (-10651200000000000), term 1026 (77796400000000000), term 1032 (8059200000000000), term 1033 (-26703200000000000), term 1040 (82200000000000000), term 1088 (8059200000000000), term 1089 (-26703200000000000), term 1096 (-9587200000000000), term 1152 (82200000000000000), term 1536 (32114000000000000), term 1537 (-49002800000000000), term 1544 (-7863200000000000), term 1600 (-7863200000000000), term 2048 (36090200000000000)]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem id13 : zeroCoeffs (add (squares b13) (scale (-1) p13)) = true := by rfl

private theorem pos13 (x : Point) : 0 ≤ value x p13 := block_nonneg x b13 p13 id13

private def cap : Poly := [term 2 (10958439), term 3 (-8132678), term 4 (-2825761), term 9 (5106878), term 10 (-8132678), term 16 (10958439), term 17 (-8132678), term 18 (-5651522), term 24 (-8132678), term 32 (-2825761), term 65 (5106878), term 66 (-8132678), term 72 (5106878), term 80 (-8132678), term 128 (10958439), term 129 (-8132678), term 130 (-5651522), term 136 (-8132678), term 144 (-5651522), term 192 (-8132678), term 256 (-2825761), term 513 (5106878), term 514 (-8132678), term 520 (5106878), term 528 (-8132678), term 576 (5106878), term 640 (-8132678), term 1024 (10958439), term 1025 (-8132678), term 1026 (-5651522), term 1032 (-8132678), term 1040 (-5651522), term 1088 (-8132678), term 1152 (-5651522), term 1536 (-8132678), term 2048 (-2825761)]

private def con : Poly := [term 0 (50000000)]

private def v0 : Poly := [term 512 (1)]

private def u0 : Poly := [term 0 (1), term 512 (-1)]

private def v1 : Poly := [term 64 (1)]

private def u1 : Poly := [term 0 (1), term 64 (-1)]

private def v2 : Poly := [term 8 (1)]

private def u2 : Poly := [term 0 (1), term 8 (-1)]

private def v3 : Poly := [term 1 (1)]

private def u3 : Poly := [term 0 (1), term 1 (-1)]

set_option maxHeartbeats 3000000 in
private def target : Poly := [term 0 (2864304826944918800000000), term 1 (21943472080571500000000), term 2 (-2639206562326583000000000), term 3 (4347374857834023000000000), term 4 (-13468138380691731500000000), term 5 (8967806406367490300000000), term 8 (21943472080571500000000), term 16 (-2639206562326583000000000), term 24 (4347374857834023000000000), term 32 (-13468138380691731500000000), term 40 (8967806406367490300000000), term 64 (21943472080571500000000), term 128 (-2639206562326583000000000), term 192 (4347374857834023000000000), term 256 (-13468138380691731500000000), term 320 (8967806406367490300000000), term 512 (21943472080571500000000), term 1024 (-2639206562326583000000000), term 1536 (4347374857834023000000000), term 2048 (-13468138380691731500000000), term 2560 (8967806406367490300000000)]

private def products : List (Poly × Poly) := [(p0, con), (p1, cap), (p2, (prod cap v0)), (p1, (prod cap u0)), (p2, (prod cap v1)), (p1, (prod cap u1)), (p2, (prod cap v2)), (p1, (prod cap u2)), (p2, (prod cap v3)), (p1, (prod cap u3)), (p10, (scale 50000000 v0)), (p11, (scale 50000000 v1)), (p12, (scale 50000000 v2)), (p13, (scale 50000000 v3))]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem combined : zeroCoeffs (add (factors products) (scale (-1) target)) = true := by rfl

set_option maxHeartbeats 3000000 in
theorem certificate (x₁ x₂ x₃ x₄ : ℝ) (h0 : 0 ≤ x₁) (u0h : x₁ ≤ 1) (h1 : 0 ≤ x₂) (u1h : x₂ ≤ 1) (h2 : 0 ≤ x₃) (u2h : x₃ ≤ 1) (h3 : 0 ≤ x₄) (u3h : x₄ ≤ 1)
    (hc : (0 : ℝ) ≤ (-2825761*x₁^4/50000000 - 4066339*x₁^3/25000000 - 2825761*x₁^2*x₂^2/25000000 - 4066339*x₁^2*x₂/25000000 - 2825761*x₁^2*x₃^2/25000000 - 4066339*x₁^2*x₃/25000000 - 2825761*x₁^2*x₄^2/25000000 - 4066339*x₁^2*x₄/25000000 + 10958439*x₁^2/50000000 - 4066339*x₁*x₂^2/25000000 + 2553439*x₁*x₂/25000000 - 4066339*x₁*x₃^2/25000000 + 2553439*x₁*x₃/25000000 - 4066339*x₁*x₄^2/25000000 + 2553439*x₁*x₄/25000000 - 2825761*x₂^4/50000000 - 4066339*x₂^3/25000000 - 2825761*x₂^2*x₃^2/25000000 - 4066339*x₂^2*x₃/25000000 - 2825761*x₂^2*x₄^2/25000000 - 4066339*x₂^2*x₄/25000000 + 10958439*x₂^2/50000000 - 4066339*x₂*x₃^2/25000000 + 2553439*x₂*x₃/25000000 - 4066339*x₂*x₄^2/25000000 + 2553439*x₂*x₄/25000000 - 2825761*x₃^4/50000000 - 4066339*x₃^3/25000000 - 2825761*x₃^2*x₄^2/25000000 - 4066339*x₃^2*x₄/25000000 + 10958439*x₃^2/50000000 - 4066339*x₃*x₄^2/25000000 + 2553439*x₃*x₄/25000000 - 2825761*x₄^4/50000000 - 4066339*x₄^3/25000000 + 10958439*x₄^2/50000000)) :
    0 ≤ 2889/1000 - majorant ((41*x₁+59)/100) - majorant ((41*x₂+59)/100) - majorant ((41*x₃+59)/100) - majorant ((41*x₄+59)/100) := by
  let x : Point := (x₁, x₂, x₃, x₄)
  have posCap : 0 ≤ value x cap := by
    have eqCap : value x cap = 50000000 * (-2825761*x₁^4/50000000 - 4066339*x₁^3/25000000 - 2825761*x₁^2*x₂^2/25000000 - 4066339*x₁^2*x₂/25000000 - 2825761*x₁^2*x₃^2/25000000 - 4066339*x₁^2*x₃/25000000 - 2825761*x₁^2*x₄^2/25000000 - 4066339*x₁^2*x₄/25000000 + 10958439*x₁^2/50000000 - 4066339*x₁*x₂^2/25000000 + 2553439*x₁*x₂/25000000 - 4066339*x₁*x₃^2/25000000 + 2553439*x₁*x₃/25000000 - 4066339*x₁*x₄^2/25000000 + 2553439*x₁*x₄/25000000 - 2825761*x₂^4/50000000 - 4066339*x₂^3/25000000 - 2825761*x₂^2*x₃^2/25000000 - 4066339*x₂^2*x₃/25000000 - 2825761*x₂^2*x₄^2/25000000 - 4066339*x₂^2*x₄/25000000 + 10958439*x₂^2/50000000 - 4066339*x₂*x₃^2/25000000 + 2553439*x₂*x₃/25000000 - 4066339*x₂*x₄^2/25000000 + 2553439*x₂*x₄/25000000 - 2825761*x₃^4/50000000 - 4066339*x₃^3/25000000 - 2825761*x₃^2*x₄^2/25000000 - 4066339*x₃^2*x₄/25000000 + 10958439*x₃^2/50000000 - 4066339*x₃*x₄^2/25000000 + 2553439*x₃*x₄/25000000 - 2825761*x₄^4/50000000 - 4066339*x₄^3/25000000 + 10958439*x₄^2/50000000) := by
      norm_num [x, cap, value, term, mon]; ring
    rw [eqCap]; exact mul_nonneg (by norm_num) hc
  have posCon : 0 ≤ value x con := by norm_num [x, con, value, term, mon]
  have posV0 : 0 ≤ value x v0 := by simpa [x, v0, value, term, mon] using h0
  have posU0 : 0 ≤ value x u0 := by simpa [x, u0, value, term, mon] using (sub_nonneg.mpr u0h)
  have posV1 : 0 ≤ value x v1 := by simpa [x, v1, value, term, mon] using h1
  have posU1 : 0 ≤ value x u1 := by simpa [x, u1, value, term, mon] using (sub_nonneg.mpr u1h)
  have posV2 : 0 ≤ value x v2 := by simpa [x, v2, value, term, mon] using h2
  have posU2 : 0 ≤ value x u2 := by simpa [x, u2, value, term, mon] using (sub_nonneg.mpr u2h)
  have posV3 : 0 ≤ value x v3 := by simpa [x, v3, value, term, mon] using h3
  have posU3 : 0 ≤ value x u3 := by simpa [x, u3, value, term, mon] using (sub_nonneg.mpr u3h)
  have allPos : 0 ≤ value x (factors products) := by
    unfold products
    simp only [factors_cons]
    exact (add_nonneg (mul_nonneg (pos0 x) posCon) (add_nonneg (mul_nonneg (pos1 x) posCap) (add_nonneg (mul_nonneg (pos2 x) (by rw [value_prod]; exact mul_nonneg posCap posV0)) (add_nonneg (mul_nonneg (pos1 x) (by rw [value_prod]; exact mul_nonneg posCap posU0)) (add_nonneg (mul_nonneg (pos2 x) (by rw [value_prod]; exact mul_nonneg posCap posV1)) (add_nonneg (mul_nonneg (pos1 x) (by rw [value_prod]; exact mul_nonneg posCap posU1)) (add_nonneg (mul_nonneg (pos2 x) (by rw [value_prod]; exact mul_nonneg posCap posV2)) (add_nonneg (mul_nonneg (pos1 x) (by rw [value_prod]; exact mul_nonneg posCap posU2)) (add_nonneg (mul_nonneg (pos2 x) (by rw [value_prod]; exact mul_nonneg posCap posV3)) (add_nonneg (mul_nonneg (pos1 x) (by rw [value_prod]; exact mul_nonneg posCap posU3)) (add_nonneg (mul_nonneg (pos10 x) (by rw [value_scale]; exact mul_nonneg (by norm_num) posV0)) (add_nonneg (mul_nonneg (pos11 x) (by rw [value_scale]; exact mul_nonneg (by norm_num) posV1)) (add_nonneg (mul_nonneg (pos12 x) (by rw [value_scale]; exact mul_nonneg (by norm_num) posV2)) (add_nonneg (mul_nonneg (pos13 x) (by rw [value_scale]; exact mul_nonneg (by norm_num) posV3)) (le_refl 0)))))))))))))))
  have result := transfer x products target combined allPos
  have eqTarget : value x target = 1000000000000000000000000 * (2889/1000 - majorant ((41*x₁+59)/100) - majorant ((41*x₂+59)/100) - majorant ((41*x₃+59)/100) - majorant ((41*x₄+59)/100)) := by
    norm_num [x, target, value, term, mon, majorant]; ring
  rw [eqTarget] at result
  exact (mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < 1000000000000000000000000)).mp result

end Dim4

end OMA.Sos1084




/-
# At most four contacts in the cap

Musin's `13 → 12` scheme splits the thirteen putative contacts of a unit sphere into those
lying in a cap of angular radius `θ₀ = arccos(59/100) ≈ 53.84°` around a chosen axis `p`, and
those outside it. The outside points are handled by `musin_f_nonpos` and `musinF_le_antipode`;
the inside points by the `h_m` lemmas, `musin_h_zero` through `musin_h_four`. For that split to
close, the number of points **inside** the cap must be at most four.

Musin proves this — his Lemma 2 — by spherical trigonometry. The proof here is the same
computation organised as **direction counting**.

## The argument

Project the cap points `y₁, …, y_m` onto `p^⊥`, a **two**-dimensional space. Write
`cⱼ = ⟨p, yⱼ⟩ ≥ 59/100` and `zⱼ = yⱼ − cⱼ p`, so `‖zⱼ‖² = 1 − cⱼ²`. The separation
`⟨yᵢ, yⱼ⟩ ≤ 1/2` becomes, after projecting and normalising,

`cos ∠(zᵢ, zⱼ) = (⟨yᵢ,yⱼ⟩ − cᵢcⱼ) / √((1−cᵢ²)(1−cⱼ²)) ≤ (1/2 − cᵢcⱼ) / √((1−cᵢ²)(1−cⱼ²))`,

and the right-hand side is **increasing in each of `cᵢ`, `cⱼ`** on `[59/100, 1]`: its
`cᵢ`-derivative has numerator `cⱼ − cᵢ/2 ≥ 59/100 − 1/2 > 0`. So it is largest at the corner
`cᵢ = cⱼ = 59/100`, where it equals

`(1/2 − (59/100)²) / (1 − (59/100)²) = 1519/6519 = 0.23301…`.

That is `cos 76.52°`, and `76.52° > 72° = 2π/5`. Five directions in a plane pairwise more than
`2π/5` apart would need more than a full turn. Hence `m ≤ 4`.

The `2π/5` threshold is why `Real.cos_pi_div_five` appears: the comparison
`1519/6519 < cos(2π/5) = (√5 − 1)/4` is what makes the count work, and it is exact — no
numerical approximation of `π` is needed anywhere.
-/

namespace Kissing3D

open Real

/- ### The frame -/

/- The cross product, in coordinates. Together with `p` and `e` it completes an orthonormal
frame, which is all it is used for. -/
def cross3 (p e : Fin 3 → ℝ) : Fin 3 → ℝ := fun i =>
  if i = 0 then p 1 * e 2 - p 2 * e 1
  else if i = 1 then p 2 * e 0 - p 0 * e 2
  else p 0 * e 1 - p 1 * e 0

@[simp] theorem cross3_zero (p e : Fin 3 → ℝ) : cross3 p e 0 = p 1 * e 2 - p 2 * e 1 := rfl

@[simp] theorem cross3_one (p e : Fin 3 → ℝ) : cross3 p e 1 = p 2 * e 0 - p 0 * e 2 := rfl

@[simp] theorem cross3_two (p e : Fin 3 → ℝ) : cross3 p e 2 = p 0 * e 1 - p 1 * e 0 := rfl

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- **Parseval in the frame `{p, e, p × e}`.** For `p` and `e` orthonormal in `ℝ³` the three
vectors form an orthonormal basis, so every inner product splits into three coordinates. The
proof is ideal membership: the certificate below was computed once and is checked by `ring`. -/
theorem parseval3 (p e u v : Fin 3 → ℝ) (hp : dot3 p p = 1) (he : dot3 e e = 1)
    (hpe : dot3 p e = 0) :
    dot3 u v = dot3 p u * dot3 p v + dot3 e u * dot3 e v
             + dot3 (cross3 p e) u * dot3 (cross3 p e) v := by
  simp only [dot3, cross3_zero, cross3_one, cross3_two] at *
  linear_combination
    (-e 0 ^ 2 * u 1 * v 1 + e 0 * e 1 * u 0 * v 1 + e 0 * e 1 * u 1 * v 0
      + e 0 * e 2 * u 0 * v 2 + e 0 * e 2 * u 2 * v 0 - e 1 ^ 2 * u 0 * v 0
      + e 1 * e 2 * u 1 * v 2 + e 1 * e 2 * u 2 * v 1 - e 2 ^ 2 * u 0 * v 0
      - e 2 ^ 2 * u 1 * v 1 + e 2 ^ 2 * u 2 * v 2 - u 2 * v 2) * hp
    + (p 0 ^ 2 * u 0 * v 0 - p 0 ^ 2 * u 2 * v 2 + p 0 * p 1 * u 0 * v 1
      + p 0 * p 1 * u 1 * v 0 + p 0 * p 2 * u 0 * v 2 + p 0 * p 2 * u 2 * v 0
      + p 1 ^ 2 * u 1 * v 1 - p 1 ^ 2 * u 2 * v 2 + p 1 * p 2 * u 1 * v 2
      + p 1 * p 2 * u 2 * v 1 - u 0 * v 0 - u 1 * v 1) * he
    + (-e 0 * p 0 * u 0 * v 0 + e 0 * p 0 * u 1 * v 1 + e 0 * p 0 * u 2 * v 2
      - e 0 * p 1 * u 0 * v 1 - e 0 * p 1 * u 1 * v 0 - e 0 * p 2 * u 0 * v 2
      - e 0 * p 2 * u 2 * v 0 - e 1 * p 0 * u 0 * v 1 - e 1 * p 0 * u 1 * v 0
      + e 1 * p 1 * u 0 * v 0 - e 1 * p 1 * u 1 * v 1 + e 1 * p 1 * u 2 * v 2
      - e 1 * p 2 * u 1 * v 2 - e 1 * p 2 * u 2 * v 1 - e 2 * p 0 * u 0 * v 2
      - e 2 * p 0 * u 2 * v 0 - e 2 * p 1 * u 1 * v 2 - e 2 * p 1 * u 2 * v 1
      + e 2 * p 2 * u 0 * v 0 + e 2 * p 2 * u 1 * v 1 - e 2 * p 2 * u 2 * v 2) * hpe

/- ### The corner value `1519/6519`

The azimuthal separation of two cap points is smallest when both sit on the rim. -/

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- **The azimuth bound, squared.** For `a, b ≥ 59/100` with `ab ≤ 1/2`,
`(1/2 − ab)² ≤ (1519/6519)²(1−a²)(1−b²)`, with equality exactly at `a = b = 59/100`.

Written in the shifted variables `u = a − 59/100`, `v = b − 59/100` the claim is
`584239299·(u+v) ≥ 4019000000 u²v² + 4742420000(u²v+uv²) + 1629750000(u²+v²) + 1346319500uv`,
and the constraint `ab ≤ 1/2` caps `u + v` at `1519/5900`, which is small enough that the
linear term wins. -/
theorem azimuth_sq {a b : ℝ} (ha : 59/100 ≤ a) (hb : 59/100 ≤ b) (hab : a * b ≤ 1/2) :
    (1/2 - a*b)^2 ≤ (1519/6519)^2 * ((1-a^2) * (1-b^2)) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 59/50),
    mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb))
      (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)),
    mul_nonneg (sq_nonneg (a - b)) (sub_nonneg.mpr ha),
    mul_nonneg (sq_nonneg (a - b)) (sub_nonneg.mpr hb),
    sq_nonneg (a*b - 3481/10000)]

/- ### `2π/5` -/

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem cos_two_pi_div_five : Real.cos (2*π/5) = (Real.sqrt 5 - 1)/4 := by
  have h : (2*π/5) = 2 * (π/5) := by ring
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- `1519/6519 = cos 76.52°` is strictly less than `cos 72°`. This is the whole content of
the count: the azimuthal gaps are genuinely bigger than a fifth of a turn. -/
theorem lt_cos_two_pi_div_five : (1519:ℝ)/6519 < Real.cos (2*π/5) := by
  rw [cos_two_pi_div_five]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5, Real.sqrt_nonneg 5]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- **A gap of at least `76.52°`.** Any `d` in `(0, 2π)` whose cosine is at most `1519/6519`
lies strictly between `2π/5` and `8π/5`. -/
theorem gap_bounds {d : ℝ} (h0 : 0 < d) (h2 : d < 2*π) (hc : Real.cos d ≤ 1519/6519) :
    2*π/5 < d ∧ d < 8*π/5 := by
  have hpi := Real.pi_pos
  have key := lt_cos_two_pi_div_five
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    have : Real.cos (2*π/5) ≤ Real.cos d :=
      Real.cos_le_cos_of_nonneg_of_le_pi h0.le (by linarith) h
    linarith
  · by_contra h
    push Not at h
    have hle : Real.cos (2*π/5) ≤ Real.cos (2*π - d) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    rw [show (2*π - d) = -(d - 2*π) by ring, Real.cos_neg,
      show d - 2*π = d + (-1 : ℤ) * (2*π) by push_cast; ring, Real.cos_add_int_mul_two_pi] at hle
    linarith

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- **Five directions do not fit.** A set of five reals, pairwise less than a full turn apart
and pairwise of cosine at most `1519/6519`, cannot exist: the four consecutive gaps already
exceed `8π/5`, but the total span is bounded by `8π/5` for exactly the same reason. -/
theorem no_five {T : Finset ℝ} (hcard : 5 ≤ T.card)
    (hspan : ∀ x ∈ T, ∀ y ∈ T, x - y < 2*π)
    (hcos : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Real.cos (x - y) ≤ 1519/6519) : False := by
  obtain ⟨T', hsub, hc5⟩ := Finset.exists_subset_card_eq hcard
  set g := T'.orderEmbOfFin hc5 with hg
  have hmem : ∀ i, g i ∈ T := fun i => hsub (T'.orderEmbOfFin_mem hc5 i)
  have hlt : ∀ i j : Fin 5, i < j → g i < g j := fun i j h => g.strictMono h
  -- the four consecutive gaps, and the total span
  have gap : ∀ i j : Fin 5, i < j → 2*π/5 < g j - g i := by
    intro i j hij
    refine (gap_bounds (sub_pos.mpr (hlt i j hij)) ?_ ?_).1
    · exact hspan _ (hmem j) _ (hmem i)
    · exact hcos _ (hmem j) _ (hmem i) (hlt i j hij).ne'
  have top : g 4 - g 0 < 8*π/5 := by
    refine (gap_bounds (sub_pos.mpr (hlt 0 4 (by decide))) ?_ ?_).2
    · exact hspan _ (hmem 4) _ (hmem 0)
    · exact hcos _ (hmem 4) _ (hmem 0) (hlt 0 4 (by decide)).ne'
  have g01 := gap 0 1 (by decide)
  have g12 := gap 1 2 (by decide)
  have g23 := gap 2 3 (by decide)
  have g34 := gap 3 4 (by decide)
  linarith

/- ### Cauchy–Schwarz in three coordinates -/

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem lagrange3 (u v : Fin 3 → ℝ) :
    dot3 u u * dot3 v v - dot3 u v ^ 2 =
      (u 0 * v 1 - u 1 * v 0)^2 + (u 0 * v 2 - u 2 * v 0)^2 + (u 1 * v 2 - u 2 * v 1)^2 := by
  simp only [dot3]; ring

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem cauchy3 (u v : Fin 3 → ℝ) : dot3 u v ^ 2 ≤ dot3 u u * dot3 v v := by
  have h := lagrange3 u v
  nlinarith [sq_nonneg (u 0 * v 1 - u 1 * v 0), sq_nonneg (u 0 * v 2 - u 2 * v 0),
    sq_nonneg (u 1 * v 2 - u 2 * v 1)]

/- ### The count -/

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- **Musin's Lemma 2, by direction counting: at most four contacts in the cap.**

If `p` is a unit vector and `S` a set of unit vectors, pairwise at inner product at most `1/2`
(the hard-core separation) and each at inner product at least `59/100` with `p` (inside the
cap), then `S` has at most four elements.

This is sharp: the four upper neighbours of an icosahedral contact configuration realise it,
with margin `1/2 − 1/√5`. -/
theorem cap_card_le_four {S : Finset (Fin 3 → ℝ)} {p : Fin 3 → ℝ} (hp : dot3 p p = 1)
    (hunit : ∀ y ∈ S, dot3 y y = 1)
    (hsep : ∀ y ∈ S, ∀ y' ∈ S, y ≠ y' → dot3 y y' ≤ 1/2)
    (hcap : ∀ y ∈ S, 59/100 ≤ dot3 p y) : S.card ≤ 4 := by
  by_contra hcon
  push Not at hcon
  have hcard : 5 ≤ S.card := hcon
  -- notation: the cap coordinate and the projection to `p^⊥`
  set c : (Fin 3 → ℝ) → ℝ := fun y => dot3 p y with hc
  set z : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y i => y i - c y * p i with hz
  have hpz : ∀ y, dot3 p (z y) = 0 := by
    intro y; simp only [hz, hc, dot3] at *
    linear_combination (-(p 0 * y 0 + p 1 * y 1 + p 2 * y 2)) * hp
  have hzz : ∀ y ∈ S, dot3 (z y) (z y) = 1 - c y ^ 2 := by
    intro y hy
    have h1 := hunit y hy
    simp only [hz, hc, dot3] at *
    linear_combination h1 + (p 0 * y 0 + p 1 * y 1 + p 2 * y 2)^2 * hp
  have hzz' : ∀ y y', dot3 (z y) (z y') = dot3 y y' - c y * c y' := by
    intro y y'; simp only [hz, hc, dot3] at *
    linear_combination ((p 0 * y 0 + p 1 * y 1 + p 2 * y 2) *
      (p 0 * y' 0 + p 1 * y' 1 + p 2 * y' 2)) * hp
  -- the cap coordinate is strictly less than one
  have hclt : ∀ y ∈ S, c y < 1 := by
    intro y hy
    obtain ⟨y', hy', hne⟩ : ∃ y' ∈ S, y' ≠ y := by
      by_contra h
      push Not at h
      have : S ⊆ {y} := fun w hw => Finset.mem_singleton.mpr (h w hw)
      have := Finset.card_le_card this
      simp at this; omega
    by_contra hge
    push Not at hge
    have hcle : c y ≤ 1 := by nlinarith [cauchy3 p y, hp, hunit y hy]
    have hc1 : c y = 1 := le_antisymm hcle hge
    have hcs := cauchy3 (z y) (z y')
    rw [hzz' y y', hzz y hy, hzz y' hy', hc1] at hcs
    have ht := hsep y hy y' hy' (Ne.symm hne)
    have hc' := hcap y' hy'
    simp only [hc] at hc' hcs ⊢
    nlinarith [hcs, ht, hc']
  -- the frame, built on the projection of one chosen element
  obtain ⟨y₀, hy₀⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  set R : (Fin 3 → ℝ) → ℝ := fun y => Real.sqrt (1 - c y ^ 2) with hR
  have hRpos : ∀ y ∈ S, 0 < R y := by
    intro y hy
    have h1 := hclt y hy
    have h2 := hcap y hy
    exact Real.sqrt_pos.mpr (by simp only [hc] at *; nlinarith)
  have hRsq : ∀ y ∈ S, R y ^ 2 = 1 - c y ^ 2 := by
    intro y hy
    have h1 := hclt y hy
    have h2 := hcap y hy
    exact Real.sq_sqrt (by simp only [hc] at *; nlinarith)
  set e : Fin 3 → ℝ := fun i => (R y₀)⁻¹ * z y₀ i with he
  have hee : dot3 e e = 1 := by
    have h := hzz y₀ hy₀
    have hr := hRsq y₀ hy₀
    have hrne : R y₀ ≠ 0 := (hRpos y₀ hy₀).ne'
    have hexp : dot3 e e = (R y₀)⁻¹ ^ 2 * dot3 (z y₀) (z y₀) := by
      simp only [he, dot3]; ring
    rw [hexp, h, ← hr]
    field_simp
  have hpe : dot3 p e = 0 := by
    have hexp : dot3 p e = (R y₀)⁻¹ * dot3 p (z y₀) := by simp only [he, dot3]; ring
    rw [hexp, hpz y₀, mul_zero]
  -- planar coordinates
  set f := cross3 p e with hf
  set A : (Fin 3 → ℝ) → ℝ := fun y => dot3 e (z y) with hA
  set B : (Fin 3 → ℝ) → ℝ := fun y => dot3 f (z y) with hB
  have hpars : ∀ y y', dot3 (z y) (z y') = A y * A y' + B y * B y' := by
    intro y y'
    have := parseval3 p e (z y) (z y') hp hee hpe
    rw [hpz y, hpz y'] at this
    simp only [hA, hB, hf]
    linarith [this]
  have hnormsq : ∀ y ∈ S, A y ^ 2 + B y ^ 2 = R y ^ 2 := by
    intro y hy
    have h := hpars y y
    rw [hzz y hy] at h
    rw [hRsq y hy]; nlinarith [h]
  -- the planar coordinates as a complex number, and its argument
  set w : (Fin 3 → ℝ) → ℂ := fun y => ⟨A y, B y⟩ with hw
  have hNsq : ∀ y, ‖w y‖ ^ 2 = A y ^ 2 + B y ^ 2 := by
    intro y; rw [Complex.sq_norm]; simp only [hw, Complex.normSq_mk]; ring
  have hNR : ∀ y ∈ S, ‖w y‖ = R y := by
    intro y hy
    have h1 : ‖w y‖ ^ 2 = R y ^ 2 := by rw [hNsq y, hnormsq y hy]
    nlinarith [norm_nonneg (w y), h1, (hRpos y hy).le]
  have hwne : ∀ y ∈ S, w y ≠ 0 := by
    intro y hy
    have : 0 < ‖w y‖ := by rw [hNR y hy]; exact hRpos y hy
    exact norm_pos_iff.mp this
  set θ : (Fin 3 → ℝ) → ℝ := fun y => Complex.arg (w y) with hθ
  have hcosdiff : ∀ y ∈ S, ∀ y' ∈ S,
      Real.cos (θ y - θ y') = (A y * A y' + B y * B y') / (R y * R y') := by
    intro y hy y' hy'
    have hy0 := hRpos y hy
    have hy0' := hRpos y' hy'
    rw [Real.cos_sub, hθ]
    rw [Complex.cos_arg (hwne y hy), Complex.cos_arg (hwne y' hy'),
      Complex.sin_arg, Complex.sin_arg, hNR y hy, hNR y' hy']
    have hre : (w y).re = A y := rfl
    have him : (w y).im = B y := rfl
    have hre' : (w y').re = A y' := rfl
    have him' : (w y').im = B y' := rfl
    rw [hre, him, hre', him']
    field_simp
  -- the separation, transported to the plane
  have hkey : ∀ y ∈ S, ∀ y' ∈ S, y ≠ y' → Real.cos (θ y - θ y') ≤ 1519/6519 := by
    intro y hy y' hy' hne
    have hy0 := hRpos y hy
    have hy0' := hRpos y' hy'
    have hAB : A y * A y' + B y * B y' = dot3 y y' - c y * c y' := by
      rw [← hpars y y', hzz' y y']
    rw [hcosdiff y hy y' hy', hAB, div_le_iff₀ (by positivity)]
    have ht := hsep y hy y' hy' hne
    rcases le_or_gt (c y * c y') (1/2) with h | h
    · have ha : (59:ℝ)/100 ≤ c y := by simpa [hc] using hcap y hy
      have hb : (59:ℝ)/100 ≤ c y' := by simpa [hc] using hcap y' hy'
      have hsq := azimuth_sq ha hb h
      rw [← hRsq y hy, ← hRsq y' hy'] at hsq
      nlinarith [hsq, mul_pos hy0 hy0', ht]
    · nlinarith [mul_pos hy0 hy0', ht]
  -- distinct points have distinct arguments
  have hinj : Set.InjOn θ ↑S := by
    intro y hy y' hy' heq
    by_contra hne
    have hb := hkey y (by simpa using hy) y' (by simpa using hy') hne
    rw [heq, sub_self, Real.cos_zero] at hb
    norm_num at hb
  -- five arguments on the circle: impossible
  refine no_five (T := S.image θ) ?_ ?_ ?_
  · rw [Finset.card_image_of_injOn hinj]; omega
  · intro x hx y hy
    simp only [Finset.mem_image] at hx hy
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, rfl⟩ := hy
    have h1 := Complex.arg_le_pi (w a)
    have h2 := Complex.neg_pi_lt_arg (w b)
    simp only [hθ]
    linarith
  · intro x hx y hy hxy
    simp only [Finset.mem_image] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact hkey a ha b hb (fun h => hxy (by rw [h]))

/- ### The cap condition

The inequality that feeds the `h_m` certificates. Musin's is
`2Σcᵢ² − 2S²/(m+1) ≤ 1`, obtained by putting `v* = 2c − (2S/(m+1))·1` into the estimate below;
that needs `v* ≥ 0`, i.e. `(m+1)cᵢ ≥ S`, which bootstraps for `m ≤ 3` but not for `m = 4`.

So the estimate is stated for a general nonnegative weight and used with `vᵢ = cᵢ − 59/100`,
which is nonnegative *by hypothesis*. The resulting condition is weaker but needs no
bootstrapping at all, and it still caps every `h_m`, `m ≤ 4`, below `13`. -/

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem dot3_sum_right (p : Fin 3 → ℝ) (S : Finset (Fin 3 → ℝ)) (f : (Fin 3 → ℝ) → ℝ) :
    dot3 p (fun i => ∑ y ∈ S, f y * y i) = ∑ y ∈ S, f y * dot3 p y := by
  simp only [dot3, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem dot3_sum_both (S : Finset (Fin 3 → ℝ)) (f : (Fin 3 → ℝ) → ℝ) :
    dot3 (fun i => ∑ y ∈ S, f y * y i) (fun i => ∑ y ∈ S, f y * y i)
      = ∑ y ∈ S, ∑ y' ∈ S, f y * f y' * dot3 y y' := by
  have h : ∀ i : Fin 3, (∑ y ∈ S, f y * y i) * (∑ y ∈ S, f y * y i)
      = ∑ y ∈ S, ∑ y' ∈ S, f y * f y' * (y i * y' i) := by
    intro i
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => by ring
  simp only [dot3, h, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => by ring

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- **The sign-free cap condition.** For unit vectors pairwise at inner product at most `1/2`
and any nonnegative weight `v`,

`2·(Σ vᵧ⟨p,y⟩)² ≤ Σ vᵧ² + (Σ vᵧ)²`.

Cauchy–Schwarz against `p` on the left; on the right the diagonal of the Gram matrix
contributes `Σvᵧ²` and the off-diagonal at most `½((Σv)² − Σv²)`, which is where the
nonnegativity of `v` is used. -/
theorem cap_copositive {S : Finset (Fin 3 → ℝ)} {p : Fin 3 → ℝ} (hp : dot3 p p = 1)
    (hunit : ∀ y ∈ S, dot3 y y = 1)
    (hsep : ∀ y ∈ S, ∀ y' ∈ S, y ≠ y' → dot3 y y' ≤ 1/2)
    {v : (Fin 3 → ℝ) → ℝ} (hv : ∀ y ∈ S, 0 ≤ v y) :
    2 * (∑ y ∈ S, v y * dot3 p y) ^ 2 ≤ (∑ y ∈ S, v y ^ 2) + (∑ y ∈ S, v y) ^ 2 := by
  classical
  set w : Fin 3 → ℝ := fun i => ∑ y ∈ S, v y * y i with hw
  have hpw : dot3 p w = ∑ y ∈ S, v y * dot3 p y := dot3_sum_right p S v
  have hww : dot3 w w = ∑ y ∈ S, ∑ y' ∈ S, v y * v y' * dot3 y y' := dot3_sum_both S v
  -- split the double sum into diagonal and off-diagonal
  have hsplit : ∑ y ∈ S, ∑ y' ∈ S, v y * v y' * dot3 y y'
      = (∑ y ∈ S, v y ^ 2) + ∑ y ∈ S, ∑ y' ∈ S.erase y, v y * v y' * dot3 y y' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [← Finset.add_sum_erase S _ hy, hunit y hy]; ring
  have hoff : ∑ y ∈ S, ∑ y' ∈ S.erase y, v y * v y' * dot3 y y'
      ≤ (1/2) * ∑ y ∈ S, ∑ y' ∈ S.erase y, v y * v y' := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y hy => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y' hy' => ?_
    have hy'S := Finset.mem_of_mem_erase hy'
    have hne : y ≠ y' := (Finset.ne_of_mem_erase hy').symm
    have := hsep y hy y' hy'S hne
    have hvv : 0 ≤ v y * v y' := mul_nonneg (hv y hy) (hv y' hy'S)
    nlinarith [this, hvv]
  have hcross : ∑ y ∈ S, ∑ y' ∈ S.erase y, v y * v y'
      = (∑ y ∈ S, v y) ^ 2 - ∑ y ∈ S, v y ^ 2 := by
    have : ∀ y ∈ S, ∑ y' ∈ S.erase y, v y * v y' = v y * (∑ y' ∈ S, v y') - v y ^ 2 := by
      intro y hy
      rw [Finset.mul_sum, ← Finset.add_sum_erase S (fun y' => v y * v y') hy]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.sum_mul, sq]
  have hcs := cauchy3 p w
  rw [hp, one_mul, hpw, hww, hsplit] at hcs
  rw [hcross] at hoff
  linarith [hcs, hoff]

/- ### A tight majorant -/

/- A **tight** degree-5 majorant of `c ↦ f(-c)` on `[59/100, 1]`.

`musinMaj`, built for `h₂`, sits a uniform `0.020`–`0.024` above `f(-c)`; summed over four cap
points that eats `0.08` of the `0.13` budget in `h₄`.  This one is the Chebyshev-optimal
degree-5 majorant, bumped by `1/500` so that the gap stays bounded away from zero (an
equioscillating majorant touches `f`, which would make the certificate below singular).  Its
gap is under `0.0064`, leaving margin `0.11` at `m = 4` instead of `0.034`. -/
noncomputable def musinMaj2 (c : ℝ) : ℝ := (131550023/1000000) + (-472486271/500000) * c ^ 1 + (2712544477/1000000) * c ^ 2 + (-970588931/250000) * c ^ 3 + (2760056463/1000000) * c ^ 4 + (-774046303/1000000) * c ^ 5

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- `f(-c) ≤ musinMaj2 c` on the cap. Markov–Lukács again:
`400·(musinMaj2 c - f(-c)) = (c - 59/100)·s₁ + (1 - c)·s₂` with `s₁, s₂` sums of squares. -/
theorem musinF_le_maj2 {c : ℝ} (h1 : 59/100 ≤ c) (h2 : c ≤ 1) : musinF (-c) ≤ musinMaj2 c := by
  have h3 : (0:ℝ) ≤ c - 59/100 := by linarith
  have h4 : (0:ℝ) ≤ 1 - c := by linarith
  have hs1 : (0:ℝ) ≤ (480014358763/5125000) * ((1) + (-1455051441919/480014358763) * c ^ 1 + (2725627981045/1920057435052) * c ^ 2 + (9985669796793/3840114870104) * c ^ 3 + (-1916152357391/960028717526) * c ^ 4) ^ 2 + (104720027416570650554787/1968058870928300000) * ((1) * c ^ 1 + (-1795800790000612668254549/523600137082853252773935) * c ^ 2 + (2035883017602186091566428/523600137082853252773935) * c ^ 3 + (-1527518233147633994889557/1047200274165706505547870) * c ^ 4) ^ 2 + (977627295766378029788258136702947/42935211240793966727462670000000) * ((1) * c ^ 2 + (-3000974023241033924639861804296333/1955254591532756059576516273405894) * c ^ 3 + (661511957361585580713208122172648/977627295766378029788258136702947) * c ^ 4) ^ 2 + (29844169626897792998706635960053625952293/20041359563210749610659291802410413500000) * ((1) * c ^ 3 + (-7438092614390229999702164441752499813913/17053811215370167427832363405744929115596) * c ^ 4) ^ 2 + (13302616575670502662349023635703062964479501917/39954643418867249402350108550602405356539200000) * ((1) * c ^ 4) ^ 2 := by positivity
  have hs2 : (0:ℝ) ≤ (55289626882017/512500000) * ((1) + (-358106750250725/110579253764034) * c ^ 1 + (22851594748475/10052659433094) * c ^ 2 + (87632742822275/55289626882017) * c ^ 3 + (-181412950004675/110579253764034) * c ^ 4) ^ 2 + (51523924836017753402487071/1770995861064607031250) * ((1) * c ^ 1 + (-13722171506763566676453049525/3297531189505136217759172544) * c ^ 2 + (9328184308562922501663970825/1648765594752568108879586272) * c ^ 3 + (-8288448819289077375480699475/3297531189505136217759172544) * c ^ 4) ^ 2 + (249316291734781414435999946896236867751/6759938938485529246406303715200000000) * ((1) * c ^ 2 + (-426577345828752970701134320902535004550/249316291734781414435999946896236867751) * c ^ 3 + (208105141216637563331660473068110885425/249316291734781414435999946896236867751) * c ^ 4) ^ 2 + (1029955008080908211808251200206073258155809273187/511098398056301899593799891137285578889550000000) * ((1) * c ^ 3 + (-177465094974133496235539356557387301300314651550/343318336026969403936083733402024419385269757729) * c ^ 4) ^ 2 + (199311715477595857321615892474755335088514729429438199/563042071084229822455177322779320047791842402675560000) * ((1) * c ^ 4) ^ 2 := by positivity
  rw [musinF, musinMaj2, div_le_iff₀ (by norm_num : (0:ℝ) < 400)]
  nlinarith [mul_nonneg h3 hs1, mul_nonneg h4 hs2]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- `h₁ < 13`: one point in the cap. -/
theorem musin_h_1 {c₁ : ℝ} (ha1 : 59/100 ≤ c₁) (hb1 : c₁ ≤ 1)
    (hq : 2 * ((c₁ - 59/100) * c₁) ^ 2 ≤ ((c₁ - 59/100) ^ 2) + ((c₁ - 59/100)) ^ 2) :
    musinF 1 + musinF (-c₁) < 13 := by
  obtain ⟨x₁, rfl⟩ : ∃ x : ℝ, c₁ = (41 * x + 59) / 100 := ⟨(100 * c₁ - 59) / 41, by ring⟩
  have g0 : (0:ℝ) ≤ x₁ := by linarith
  have G0 : x₁ ≤ 1 := by linarith
  have e0 : (0:ℝ) ≤ (-2825761*x₁^4/50000000 - 4066339*x₁^3/25000000 + 10958439*x₁^2/50000000) := by nlinarith only [hq]
  have hnn : 0 ≤ 2889/1000 - musinMaj2 ((41 * x₁ + 59) / 100) :=
    OMA.Sos1084.Dim1.certificate x₁ g0 G0 e0
  have m1 := musinF_le_maj2 ha1 hb1
  have h1 : musinF 1 = 1011/100 := by rw [musinF]; norm_num
  linarith only [hnn, h1, m1]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- `h₂ < 13`: two points in the cap. -/
theorem musin_h_2 {c₁ c₂ : ℝ} (ha1 : 59/100 ≤ c₁) (hb1 : c₁ ≤ 1) (ha2 : 59/100 ≤ c₂) (hb2 : c₂ ≤ 1)
    (hq : 2 * ((c₁ - 59/100) * c₁ + (c₂ - 59/100) * c₂) ^ 2 ≤ ((c₁ - 59/100) ^ 2 + (c₂ - 59/100) ^ 2) + ((c₁ - 59/100) + (c₂ - 59/100)) ^ 2) :
    musinF 1 + musinF (-c₁) + musinF (-c₂) < 13 := by
  obtain ⟨x₁, rfl⟩ : ∃ x : ℝ, c₁ = (41 * x + 59) / 100 := ⟨(100 * c₁ - 59) / 41, by ring⟩
  obtain ⟨x₂, rfl⟩ : ∃ x : ℝ, c₂ = (41 * x + 59) / 100 := ⟨(100 * c₂ - 59) / 41, by ring⟩
  have g0 : (0:ℝ) ≤ x₁ := by linarith
  have G0 : x₁ ≤ 1 := by linarith
  have g1 : (0:ℝ) ≤ x₂ := by linarith
  have G1 : x₂ ≤ 1 := by linarith
  have e0 : (0:ℝ) ≤ (-2825761*x₁^4/50000000 - 4066339*x₁^3/25000000 - 2825761*x₁^2*x₂^2/25000000 - 4066339*x₁^2*x₂/25000000 + 10958439*x₁^2/50000000 - 4066339*x₁*x₂^2/25000000 + 2553439*x₁*x₂/25000000 - 2825761*x₂^4/50000000 - 4066339*x₂^3/25000000 + 10958439*x₂^2/50000000) := by nlinarith only [hq]
  have hnn : 0 ≤ 2889/1000 - musinMaj2 ((41 * x₁ + 59) / 100) - musinMaj2 ((41 * x₂ + 59) / 100) :=
    OMA.Sos1084.Dim2.certificate x₁ x₂ g0 G0 g1 G1 e0
  have m1 := musinF_le_maj2 ha1 hb1
  have m2 := musinF_le_maj2 ha2 hb2
  have h1 : musinF 1 = 1011/100 := by rw [musinF]; norm_num
  linarith only [hnn, h1, m1, m2]

/- ### The remaining two cases, as explicit propositions

`h₁` and `h₂` are certified below.  `h₃` and `h₄` are the same kind of object — one polynomial
inequality each, on three and four variables, under the same sign-free cap condition — and are
named here so that everything downstream is stated against them rather than against an unproved
kissing bound.  The maxima their hypotheses permit are `2.7887` and `2.7949`, against a budget
of `2.889`; what is missing is only a certificate small enough to elaborate. -/

/- The `m = 3` case of Musin's Lemma 3. -/
def MusinH3 : Prop := ∀ c₁ c₂ c₃ : ℝ, 59/100 ≤ c₁ → c₁ ≤ 1 → 59/100 ≤ c₂ → c₂ ≤ 1 →
  59/100 ≤ c₃ → c₃ ≤ 1 →
  2 * ((c₁ - 59/100) * c₁ + (c₂ - 59/100) * c₂ + (c₃ - 59/100) * c₃) ^ 2
    ≤ ((c₁ - 59/100) ^ 2 + (c₂ - 59/100) ^ 2 + (c₃ - 59/100) ^ 2)
      + ((c₁ - 59/100) + (c₂ - 59/100) + (c₃ - 59/100)) ^ 2 →
  musinF 1 + musinF (-c₁) + musinF (-c₂) + musinF (-c₃) < 13

/- The `m = 4` case of Musin's Lemma 3. -/
def MusinH4 : Prop := ∀ c₁ c₂ c₃ c₄ : ℝ, 59/100 ≤ c₁ → c₁ ≤ 1 → 59/100 ≤ c₂ → c₂ ≤ 1 →
  59/100 ≤ c₃ → c₃ ≤ 1 → 59/100 ≤ c₄ → c₄ ≤ 1 →
  2 * ((c₁ - 59/100) * c₁ + (c₂ - 59/100) * c₂ + (c₃ - 59/100) * c₃ + (c₄ - 59/100) * c₄) ^ 2
    ≤ ((c₁ - 59/100) ^ 2 + (c₂ - 59/100) ^ 2 + (c₃ - 59/100) ^ 2 + (c₄ - 59/100) ^ 2)
      + ((c₁ - 59/100) + (c₂ - 59/100) + (c₃ - 59/100) + (c₄ - 59/100)) ^ 2 →
  musinF 1 + musinF (-c₁) + musinF (-c₂) + musinF (-c₃) + musinF (-c₄) < 13

/- ### The assembly

`musin_lemma2` gives `N² ≤ ΣΣ f`. Musin's Lemma 3 gives the matching upper bound `ΣΣ f < 13N`,
one row at a time: the diagonal contributes `f(1)`, everything outside the cap contributes at
most `0` by `musin_f_nonpos`, and the cap contains at most four points by `cap_card_le_four`,
each of which is covered by one of `musin_h_0` … `musin_h_4`. Together `N < 13`. -/

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- The four cap cases, indexed by a finite set instead of by arity. -/
theorem musin_cap_sum (H3 : MusinH3) (H4 : MusinH4)
    {C : Finset (Fin 3 → ℝ)} {g : (Fin 3 → ℝ) → ℝ} (hcard : C.card ≤ 4)
    (ha : ∀ y ∈ C, 59/100 ≤ g y) (hb : ∀ y ∈ C, g y ≤ 1)
    (hq : 2 * (∑ y ∈ C, (g y - 59/100) * g y) ^ 2
          ≤ (∑ y ∈ C, (g y - 59/100) ^ 2) + (∑ y ∈ C, (g y - 59/100)) ^ 2) :
    musinF 1 + ∑ y ∈ C, musinF (-(g y)) < 13 := by
  interval_cases h : C.card
  · rw [Finset.card_eq_zero.mp h]; simpa using musin_h_zero
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    simp only [Finset.sum_singleton] at hq ⊢
    exact musin_h_1 (ha a (by simp)) (hb a (by simp)) (by linarith)
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    simp only [Finset.sum_pair hab] at hq ⊢
    have e := musin_h_2 (ha a (by simp)) (hb a (by simp)) (ha b (by simp)) (hb b (by simp))
      (by linarith)
    linarith
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h
    have hs : ∀ f : (Fin 3 → ℝ) → ℝ, ∑ y ∈ ({a, b, c} : Finset (Fin 3 → ℝ)), f y
        = f a + f b + f c := fun f => by
      rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc]; ring
    simp only [hs] at hq ⊢
    have e := H3 (g a) (g b) (g c) (ha a (by simp)) (hb a (by simp)) (ha b (by simp))
      (hb b (by simp)) (ha c (by simp)) (hb c (by simp)) (by linarith)
    linarith
  · obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp h
    have hs : ∀ f : (Fin 3 → ℝ) → ℝ, ∑ y ∈ ({a, b, c, d} : Finset (Fin 3 → ℝ)), f y
        = f a + f b + f c + f d := fun f => by
      rw [Finset.sum_insert (by simp [hab, hac, had]),
        Finset.sum_insert (by simp [hbc, hbd]), Finset.sum_pair hcd]; ring
    simp only [hs] at hq ⊢
    have e := H4 (g a) (g b) (g c) (g d) (ha a (by simp)) (hb a (by simp)) (ha b (by simp))
      (hb b (by simp)) (ha c (by simp)) (hb c (by simp)) (ha d (by simp)) (hb d (by simp))
      (by linarith)
    linarith

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- **Musin's Lemma 3**: every row of `f(⟨u,v⟩)` sums to less than `13`.

The diagonal contributes `f(1) = 10.11`. Everything at inner product in `[−59/100, 1/2]`
contributes at most `0`. What is left is the cap around `−u`, which holds at most four points
by `cap_card_le_four`, and those are exactly the `h_m` cases. -/
theorem musin_row (H3 : MusinH3) (H4 : MusinH4) {S : Finset (Fin 3 → ℝ)}
    (hunit : ∀ u ∈ S, dot3 u u = 1)
    (hcode : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → dot3 u v ≤ 1/2) {u : Fin 3 → ℝ} (hu : u ∈ S) :
    ∑ v ∈ S, musinF (dot3 u v) < 13 := by
  classical
  set p : Fin 3 → ℝ := fun i => -u i with hp
  set g : (Fin 3 → ℝ) → ℝ := fun y => dot3 p y with hg
  have hpy : ∀ y, g y = -dot3 u y := fun y => by simp only [hg, hp, dot3]; ring
  have hpp : dot3 p p = 1 := by
    have := hunit u hu; simp only [hp, dot3] at *; linarith
  set C : Finset (Fin 3 → ℝ) := (S.erase u).filter (fun y => 59/100 ≤ g y) with hC
  set R : Finset (Fin 3 → ℝ) := (S.erase u).filter (fun y => ¬ (59/100 ≤ g y)) with hR
  have hsplit : ∑ v ∈ S, musinF (dot3 u v)
      = musinF 1 + ((∑ y ∈ C, musinF (dot3 u y)) + ∑ y ∈ R, musinF (dot3 u y)) := by
    rw [← Finset.add_sum_erase S _ hu, hunit u hu, hC, hR]
    congr 1
    exact (Finset.sum_filter_add_sum_filter_not (S.erase u) _ _).symm
  have hrest : ∑ y ∈ R, musinF (dot3 u y) ≤ 0 := by
    refine Finset.sum_nonpos fun y hy => ?_
    rw [hR, Finset.mem_filter] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have h1 : -59/100 ≤ dot3 u y := by rw [hpy] at hy2; push Not at hy2; linarith
    exact musin_f_nonpos h1
      (hcode u hu y (Finset.mem_of_mem_erase hy1) (Finset.ne_of_mem_erase hy1).symm)
  have hCsub : ∀ y ∈ C, y ∈ S := fun y hy =>
    Finset.mem_of_mem_erase (Finset.mem_filter.mp hy).1
  have hCa : ∀ y ∈ C, 59/100 ≤ g y := fun y hy => (Finset.mem_filter.mp hy).2
  have hCb : ∀ y ∈ C, g y ≤ 1 := fun y hy => by
    have hu1 := hunit y (hCsub y hy)
    nlinarith [cauchy3 p y, hpp, hu1]
  have hcard : C.card ≤ 4 :=
    cap_card_le_four hpp (fun y hy => hunit y (hCsub y hy))
      (fun y hy y' hy' hne => hcode y (hCsub y hy) y' (hCsub y' hy') hne) hCa
  have hq := cap_copositive (S := C) hpp (fun y hy => hunit y (hCsub y hy))
      (fun y hy y' hy' hne => hcode y (hCsub y hy) y' (hCsub y' hy') hne)
      (v := fun y => g y - 59/100) (fun y hy => by linarith [hCa y hy])
  have hcap : musinF 1 + ∑ y ∈ C, musinF (-(g y)) < 13 :=
    musin_cap_sum H3 H4 hcard hCa hCb hq
  have hrw : ∑ y ∈ C, musinF (dot3 u y) = ∑ y ∈ C, musinF (-(g y)) :=
    Finset.sum_congr rfl fun y _ => by rw [hpy, neg_neg]
  rw [hsplit, hrw]
  linarith

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- **The kissing number of `S²` is at most twelve** — the Newton–Gregory question, settled.

`musin_lemma2` gives `N² ≤ ΣΣ f` from the degree-9 positive-definite kernel; `musin_row` gives
`ΣΣ f < 13N`. Hence `N < 13`. -/
theorem card_le_twelve (H3 : MusinH3) (H4 : MusinH4) {S : Finset (Fin 3 → ℝ)}
    (hunit : ∀ u ∈ S, dot3 u u = 1)
    (hcode : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → dot3 u v ≤ 1/2) : S.card ≤ 12 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hlo := musin_lemma2 hunit
  have hhi : ∑ u ∈ S, ∑ v ∈ S, musinF (dot3 u v) < 13 * (S.card : ℝ) := by
    calc ∑ u ∈ S, ∑ v ∈ S, musinF (dot3 u v) < ∑ _u ∈ S, (13 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty hne fun u hu => musin_row H3 H4 hunit hcode hu
      _ = 13 * (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hN : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hlt : (S.card : ℝ) < 13 := by nlinarith [hlo, hhi]
  have : S.card < 13 := by exact_mod_cast hlt
  omega

/- ### The last two cases, certified

Same shape as `h₁` and `h₂`: one polynomial inequality each, under the same sign-free cap
condition, with a rounded-Cholesky-plus-diagonally-dominant-remainder certificate. -/

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- `h₃ < 13`: three points in the cap. -/
theorem musin_h_3 {c₁ c₂ c₃ : ℝ} (ha1 : 59/100 ≤ c₁) (hb1 : c₁ ≤ 1) (ha2 : 59/100 ≤ c₂) (hb2 : c₂ ≤ 1) (ha3 : 59/100 ≤ c₃) (hb3 : c₃ ≤ 1)
    (hq : 2 * ((c₁ - 59/100) * c₁ + (c₂ - 59/100) * c₂ + (c₃ - 59/100) * c₃) ^ 2 ≤ ((c₁ - 59/100) ^ 2 + (c₂ - 59/100) ^ 2 + (c₃ - 59/100) ^ 2) + ((c₁ - 59/100) + (c₂ - 59/100) + (c₃ - 59/100)) ^ 2) :
    musinF 1 + musinF (-c₁) + musinF (-c₂) + musinF (-c₃) < 13 := by
  obtain ⟨x₁, rfl⟩ : ∃ x : ℝ, c₁ = (41 * x + 59) / 100 := ⟨(100 * c₁ - 59) / 41, by ring⟩
  obtain ⟨x₂, rfl⟩ : ∃ x : ℝ, c₂ = (41 * x + 59) / 100 := ⟨(100 * c₂ - 59) / 41, by ring⟩
  obtain ⟨x₃, rfl⟩ : ∃ x : ℝ, c₃ = (41 * x + 59) / 100 := ⟨(100 * c₃ - 59) / 41, by ring⟩
  have g0 : (0:ℝ) ≤ x₁ := by linarith
  have G0 : x₁ ≤ 1 := by linarith
  have g1 : (0:ℝ) ≤ x₂ := by linarith
  have G1 : x₂ ≤ 1 := by linarith
  have g2 : (0:ℝ) ≤ x₃ := by linarith
  have G2 : x₃ ≤ 1 := by linarith
  have e0 : (0:ℝ) ≤ (-2825761*x₁^4/50000000 - 4066339*x₁^3/25000000 - 2825761*x₁^2*x₂^2/25000000 - 4066339*x₁^2*x₂/25000000 - 2825761*x₁^2*x₃^2/25000000 - 4066339*x₁^2*x₃/25000000 + 10958439*x₁^2/50000000 - 4066339*x₁*x₂^2/25000000 + 2553439*x₁*x₂/25000000 - 4066339*x₁*x₃^2/25000000 + 2553439*x₁*x₃/25000000 - 2825761*x₂^4/50000000 - 4066339*x₂^3/25000000 - 2825761*x₂^2*x₃^2/25000000 - 4066339*x₂^2*x₃/25000000 + 10958439*x₂^2/50000000 - 4066339*x₂*x₃^2/25000000 + 2553439*x₂*x₃/25000000 - 2825761*x₃^4/50000000 - 4066339*x₃^3/25000000 + 10958439*x₃^2/50000000) := by nlinarith only [hq]
  have hnn : 0 ≤ 2889/1000 - musinMaj2 ((41 * x₁ + 59) / 100) - musinMaj2 ((41 * x₂ + 59) / 100) - musinMaj2 ((41 * x₃ + 59) / 100) :=
    OMA.Sos1084.Dim3.certificate x₁ x₂ x₃ g0 G0 g1 G1 g2 G2 e0
  have m1 := musinF_le_maj2 ha1 hb1
  have m2 := musinF_le_maj2 ha2 hb2
  have m3 := musinF_le_maj2 ha3 hb3
  have h1 : musinF 1 = 1011/100 := by rw [musinF]; norm_num
  linarith only [hnn, h1, m1, m2, m3]


set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem musin_h_4 {c₁ c₂ c₃ c₄ : ℝ} (ha1 : 59/100 ≤ c₁) (hb1 : c₁ ≤ 1) (ha2 : 59/100 ≤ c₂) (hb2 : c₂ ≤ 1) (ha3 : 59/100 ≤ c₃) (hb3 : c₃ ≤ 1) (ha4 : 59/100 ≤ c₄) (hb4 : c₄ ≤ 1)
    (hq : 2 * ((c₁ - 59/100) * c₁ + (c₂ - 59/100) * c₂ + (c₃ - 59/100) * c₃ + (c₄ - 59/100) * c₄) ^ 2 ≤ ((c₁ - 59/100) ^ 2 + (c₂ - 59/100) ^ 2 + (c₃ - 59/100) ^ 2 + (c₄ - 59/100) ^ 2) + ((c₁ - 59/100) + (c₂ - 59/100) + (c₃ - 59/100) + (c₄ - 59/100)) ^ 2) :
    musinF 1 + musinF (-c₁) + musinF (-c₂) + musinF (-c₃) + musinF (-c₄) < 13 := by
  obtain ⟨x₁, rfl⟩ : ∃ x : ℝ, c₁ = (41 * x + 59) / 100 := ⟨(100 * c₁ - 59) / 41, by ring⟩
  obtain ⟨x₂, rfl⟩ : ∃ x : ℝ, c₂ = (41 * x + 59) / 100 := ⟨(100 * c₂ - 59) / 41, by ring⟩
  obtain ⟨x₃, rfl⟩ : ∃ x : ℝ, c₃ = (41 * x + 59) / 100 := ⟨(100 * c₃ - 59) / 41, by ring⟩
  obtain ⟨x₄, rfl⟩ : ∃ x : ℝ, c₄ = (41 * x + 59) / 100 := ⟨(100 * c₄ - 59) / 41, by ring⟩
  have g0 : (0:ℝ) ≤ x₁ := by linarith
  have G0 : x₁ ≤ 1 := by linarith
  have g1 : (0:ℝ) ≤ x₂ := by linarith
  have G1 : x₂ ≤ 1 := by linarith
  have g2 : (0:ℝ) ≤ x₃ := by linarith
  have G2 : x₃ ≤ 1 := by linarith
  have g3 : (0:ℝ) ≤ x₄ := by linarith
  have G3 : x₄ ≤ 1 := by linarith
  have e0 : (0:ℝ) ≤ (-2825761*x₁^4/50000000 - 4066339*x₁^3/25000000 - 2825761*x₁^2*x₂^2/25000000 - 4066339*x₁^2*x₂/25000000 - 2825761*x₁^2*x₃^2/25000000 - 4066339*x₁^2*x₃/25000000 - 2825761*x₁^2*x₄^2/25000000 - 4066339*x₁^2*x₄/25000000 + 10958439*x₁^2/50000000 - 4066339*x₁*x₂^2/25000000 + 2553439*x₁*x₂/25000000 - 4066339*x₁*x₃^2/25000000 + 2553439*x₁*x₃/25000000 - 4066339*x₁*x₄^2/25000000 + 2553439*x₁*x₄/25000000 - 2825761*x₂^4/50000000 - 4066339*x₂^3/25000000 - 2825761*x₂^2*x₃^2/25000000 - 4066339*x₂^2*x₃/25000000 - 2825761*x₂^2*x₄^2/25000000 - 4066339*x₂^2*x₄/25000000 + 10958439*x₂^2/50000000 - 4066339*x₂*x₃^2/25000000 + 2553439*x₂*x₃/25000000 - 4066339*x₂*x₄^2/25000000 + 2553439*x₂*x₄/25000000 - 2825761*x₃^4/50000000 - 4066339*x₃^3/25000000 - 2825761*x₃^2*x₄^2/25000000 - 4066339*x₃^2*x₄/25000000 + 10958439*x₃^2/50000000 - 4066339*x₃*x₄^2/25000000 + 2553439*x₃*x₄/25000000 - 2825761*x₄^4/50000000 - 4066339*x₄^3/25000000 + 10958439*x₄^2/50000000) := by nlinarith only [hq]
  have hnn : 0 ≤ 2889/1000 - musinMaj2 ((41 * x₁ + 59) / 100) - musinMaj2 ((41 * x₂ + 59) / 100) - musinMaj2 ((41 * x₃ + 59) / 100) - musinMaj2 ((41 * x₄ + 59) / 100) :=
    OMA.Sos1084.Dim4.certificate x₁ x₂ x₃ x₄ g0 G0 g1 G1 g2 G2 g3 G3 e0
  have m1 := musinF_le_maj2 ha1 hb1
  have m2 := musinF_le_maj2 ha2 hb2
  have m3 := musinF_le_maj2 ha3 hb3
  have m4 := musinF_le_maj2 ha4 hb4
  have h1 : musinF 1 = 1011/100 := by rw [musinF]; norm_num
  linarith only [hnn, h1, m1, m2, m3, m4]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem musinH3_holds : MusinH3 :=
  fun _ _ _ a1 b1 a2 b2 a3 b3 hq => musin_h_3 a1 b1 a2 b2 a3 b3 hq

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem musinH4_holds : MusinH4 :=
  fun _ _ _ _ a1 b1 a2 b2 a3 b3 a4 b4 hq => musin_h_4 a1 b1 a2 b2 a3 b3 a4 b4 hq

/- ### Unconditional statements -/

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- **The kissing number of three-space is twelve.** -/
theorem card_le_twelve' {S : Finset (Fin 3 → ℝ)} (hunit : ∀ u ∈ S, dot3 u u = 1)
    (hcode : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → dot3 u v ≤ 1/2) : S.card ≤ 12 :=
  card_le_twelve musinH3_holds musinH4_holds hunit hcode


/- ### Back to the sphere -/

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- **At most twelve unit vectors on `S²` are pairwise at distance one.** -/
theorem kissing_le_twelve (H3 : MusinH3) (H4 : MusinH4) (S : Finset E3)
    (hunit : ∀ u ∈ S, ‖u‖ = 1) (hsep : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → 1 ≤ dist u v) :
    S.card ≤ 12 := by
  classical
  have hinj : Set.InjOn (fun u : E3 => WithLp.ofLp u) ↑S :=
    fun a _ b _ h => WithLp.ofLp_injective _ h
  rw [← Finset.card_image_of_injOn hinj]
  set T : Finset (Fin 3 → ℝ) := S.image (fun u : E3 => WithLp.ofLp u) with hT
  have hmem : ∀ x ∈ T, ∃ w ∈ S, WithLp.ofLp w = x := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨w, hw, rfl⟩
  refine card_le_twelve H3 H4 (fun x hx => ?_) (fun x hx y hy hxy => ?_)
  · obtain ⟨w, hw, rfl⟩ := hmem x hx
    exact dot3_self_of_norm (hunit w hw)
  · obtain ⟨w, hw, rfl⟩ := hmem x hx
    obtain ⟨w', hw', rfl⟩ := hmem y hy
    exact dot3_le_half (hunit w hw) (hunit w' hw')
      (hsep w hw w' hw' fun h => hxy (by rw [h]))

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- **`KissingBound3`**, the hypothesis the whole 3D file was written against, discharged down
to the two remaining polynomial inequalities. -/
theorem kissingBound3_of (H3 : MusinH3) (H4 : MusinH4) : KissingBound3 :=
  fun S h1 h2 => kissing_le_twelve H3 H4 S h1 h2

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- **`E ≥ −6N`** for a hard-core configuration in `ℝ³`, modulo `h₃` and `h₄`. This is the 3D
bulk bound: the exact analogue of `E ≥ −3N` in the plane. -/
theorem energy_ge_six (H3 : MusinH3) (H4 : MusinH4) {X : Finset E3} (hX : HardCore X) :
    -6 * (X.card : ℝ) ≤ energy X :=
  energy_ge_twelve (kissingBound3_of H3 H4) hX

/- ### Unconditional forms of the sphere statements -/

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/- **`KissingBound3`**, unconditionally. -/
theorem kissingBound3 : KissingBound3 := kissingBound3_of musinH3_holds musinH4_holds
end Kissing3D

/- # Translation from the unit-sphere bound to an arbitrary packing center -/
namespace OMA.Boundary1084
open Finset
open scoped Classical

theorem of_unit_sphere (bound : Kissing3D.KissingBound3) : Kissing := by
  intro V z radial sep
  let shift (x : Space) := x-z
  have inj : Function.Injective shift := fun _ _ h => sub_left_inj.mp h
  have h := bound (V.image shift) (by
    intro u hu
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
    exact (dist_eq_norm x z) ▸ radial x hx) (by
    intro u hu v hv hne
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hv
    simpa [shift] using sep x hx y hy (fun he => hne (congrArg shift he)))
  rwa [card_image_of_injective V inj] at h

end OMA.Boundary1084

theorem OMA.solution : type_of% @Erdos1084.erdos_1084.variants.upper_lower_d3 :=
  OMA.finish1084 (OMA.Boundary1084.of_unit_sphere Kissing3D.kissingBound3)

/-
Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
