import OMAReductions.R_OeisA245211_conjecture_R2
import Mathlib.Dynamics.PeriodicPts.Lemmas
/-!
A squarefree fixed point gives a cycle of distinct prime coordinates. With r odd
and below 65, excluding prime powers leaves ten factor counts. The product of
the edge cofactors is 2^r+1. Start just after a cofactor divisible by three.
The residue walk modulo three limits where its prime factors can occur. We
test the remaining allocations by the exact forced starting coordinate or a
projection modulo a divisor of the yet-unplaced factors minus one.
The single-orbit argument is adapted from Denyven's PR 7273.
-/


namespace FiniteFactorCycles

open Finset Function
open OMA.R_OeisA245211_conjecture_R2 (baseProduct_lt large_prime squarefree_fixed_point_product)

section PrimeProducts

variable {ι : Type*}
variable (p : ι → ℕ)

private theorem baseProduct (s : Finset ι) :
    2 ^ s.card * (∏ i ∈ s, p i) ≤ ∏ i ∈ s, (2 * p i + 1) := by
  rw [← prod_const, ← prod_mul_distrib]
  exact prod_le_prod' fun _ _ => Nat.le_succ _

variable [Fintype ι] [DecidableEq ι]

private theorem closed_eq_univ (hp : ∀ i, (p i).Prime) (hinj : Injective p)
    (hf : ι → ι) (hdvd : ∀ i, p i ∣ 2 * p (hf i) + 1)
    (hprod : (∏ i, (2 * p i + 1)) = (2 ^ Fintype.card ι + 1) * ∏ i, p i)
    (s : Finset ι) (hs : s.Nonempty) (hclosed : ∀ i ∈ s, hf i ∈ s) : s = univ := by
  have hd : (∏ i ∈ s, p i) ∣ ∏ i ∈ s, (2 * p i + 1) := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro i _ j _ hne
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hne (hinj h)))
    · intro i hi
      exact (hdvd i).trans (dvd_prod_of_mem _ (hclosed i hi))
  obtain ⟨d, hd⟩ := hd
  have hpos : 0 < ∏ i ∈ s, p i := prod_pos fun i _ => (hp i).pos
  have hds : 2 ^ s.card + 1 ≤ d := by
    have hh := baseProduct_lt p s hs hp
    rw [hd, mul_comm (∏ i ∈ s, p i)] at hh
    exact Nat.succ_le_of_lt ((Nat.mul_lt_mul_right hpos).mp hh)
  let t := univ \ s
  have hdis : Disjoint t s := disjoint_sdiff_self_left
  have hunion : t ∪ s = univ := sdiff_union_of_subset (subset_univ s)
  have hcard : Fintype.card ι = t.card + s.card := by
    rw [← card_union_of_disjoint hdis, hunion, card_univ]
  have hbalance : d * (∏ i ∈ t, (2 * p i + 1)) =
      (2 ^ (t.card + s.card) + 1) * ∏ i ∈ t, p i := by
    rw [← hunion, prod_union hdis, prod_union hdis, hd, hcard] at hprod
    apply Nat.eq_of_mul_eq_mul_right hpos
    linarith only [hprod]
  by_contra hne
  have ht : t.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he
    apply hne
    simpa [he] using hunion
  have ht2 : 2 ≤ 2 ^ t.card := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 2) (card_pos.mpr ht))
  have htp : 0 < ∏ i ∈ t, p i := prod_pos fun i _ => (hp i).pos
  have hle := Nat.mul_le_mul hds (baseProduct p t)
  rw [hbalance, pow_add, ← mul_assoc] at hle
  have : (2 ^ s.card + 1) * 2 ^ t.card ≤ 2 ^ t.card * 2 ^ s.card + 1 :=
    le_of_mul_le_mul_right hle htp
  rw [add_mul, one_mul, mul_comm (2 ^ s.card)] at this
  omega

private theorem orbit_length (hp : ∀ i, (p i).Prime) (hinj : Injective p)
    (f : ι → ι) (hdvd : ∀ i, p i ∣ 2 * p (f i) + 1)
    (hprod : (∏ i, (2 * p i + 1)) = (2 ^ Fintype.card ι + 1) * ∏ i, p i)
    [Nonempty ι] : Bijective f ∧ ∀ x, minimalPeriod f x = Fintype.card ι := by
  have hsurj : Surjective f := by
    intro x
    have hi : univ.image f = univ := closed_eq_univ p hp hinj f hdvd hprod _
      (univ_nonempty.image f) (fun i _ => mem_image.mpr ⟨i, mem_univ _, rfl⟩)
    obtain ⟨y, _, hy⟩ := mem_image.mp (hi ▸ mem_univ x)
    exact ⟨y, hy⟩
  have hfinj : Injective f := Finite.injective_iff_surjective.mpr hsurj
  refine ⟨⟨hfinj, hsurj⟩, fun x => ?_⟩
  let r := minimalPeriod f x
  have hr : 0 < r := minimalPeriod_pos_of_mem_periodicPts (hfinj.mem_periodicPts x)
  let s := (range r).image fun i => f^[i] x
  have hs : s.Nonempty := ⟨x, mem_image.mpr ⟨0, mem_range.mpr hr, rfl⟩⟩
  have hclosed (i : ι) (hi : i ∈ s) : f i ∈ s := by
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    apply mem_image.mpr
    refine ⟨(j + 1) % r, mem_range.mpr (Nat.mod_lt _ hr), ?_⟩
    rw [iterate_mod_minimalPeriod_eq, iterate_succ_apply']
  have hu := closed_eq_univ p hp hinj f hdvd hprod s hs hclosed
  have hcard : s.card = r := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj hij
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod (mem_range.mp hi)
      (mem_range.mp hj)).mp hij
  rw [hu, card_univ] at hcard
  exact hcard.symm

end PrimeProducts

private theorem cofactorData {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Injective p)
    (heq : (∏ i, (2 * p i + 1)) = (2 ^ Fintype.card ι + 1) * ∏ i, p i) :
    ∃ (f : ι → ι) (d : ι → ℕ), Bijective f ∧ (∀ i, minimalPeriod f i = Fintype.card ι) ∧
      (∀ i, 2 * p (f i) + 1 = p i * d i) ∧ (∏ i, d i) = 2 ^ Fintype.card ι + 1 := by
  have successor (i : ι) : ∃ j, p i ∣ 2 * p j + 1 := by
    have hi : p i ∣ ∏ j, p j := dvd_prod_of_mem p (mem_univ i)
    have hs : p i ∣ ∏ j, (2 * p j + 1) := heq ▸ dvd_mul_of_dvd_right hi _
    obtain ⟨j, _, hj⟩ := ((hp i).prime.dvd_finsetProd_iff (fun j => 2 * p j + 1)).mp hs
    exact ⟨j, hj⟩
  choose f hf using successor
  obtain ⟨hb, hperiod⟩ := orbit_length p hp hinj f hf heq
  choose d hd using hf
  refine ⟨f, d, hb, hperiod, hd, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (show 0 < ∏ i, p i from prod_pos fun i _ => (hp i).pos)
  calc
    (∏ i, p i) * (∏ i, d i) = ∏ i, (2 * p (f i) + 1) := by
      rw [← prod_mul_distrib]
      exact prod_congr rfl fun i _ => (hd i).symm
    _ = ∏ i, (2 * p i + 1) :=
      Fintype.prod_equiv (Equiv.ofBijective f hb) _ _ (fun _ => rfl)
    _ = (∏ i, p i) * (2 ^ Fintype.card ι + 1) := heq.trans (mul_comm _ _)




def Walk : List ℕ → ℕ → ℕ → Prop
  | [], x, y => x = y
  | d :: ds, x, y => x.Prime ∧ 12000 < x ∧ ∃ z, 2*z+1 = d*x ∧ Walk ds z y

def forced (weight acc : ℕ) : List ℕ → ℕ
  | [] => acc
  | d :: ds => forced (2*weight) (d*acc+weight) ds

theorem affine_walk {ds : List ℕ} {x y : ℕ} (h : Walk ds x y) (weight acc : ℕ) :
    forced weight acc ds + weight*2^ds.length*y = ds.prod*(acc+weight*x) := by
  induction ds generalizing x weight acc with
  | nil =>
    change x = y at h
    simp [forced,h]
  | cons d ds ih =>
    obtain ⟨_,_,z,hz,hw⟩ := h
    have t := ih hw (2*weight) (d*acc+weight)
    simp only [forced,List.length_cons,List.prod_cons,pow_succ]
    linear_combination t + ds.prod * weight * hz

def sievePass (x : ℕ) : List ℕ → Bool
  | [] => true
  | d :: ds => (x.gcd (3*5*7*11*13*29) == 1) && sievePass ((d*x-1)/2) ds

def reject (ds : List ℕ) : Bool := !(sievePass (forced 1 0 ds) ds)

theorem sieve_walk {ds : List ℕ} {x y : ℕ} (h : Walk ds x y) : sievePass x ds = true := by
  induction ds generalizing x with
  | nil => rfl
  | cons d ds ih =>
    obtain ⟨hp,hlarge,z,hz,hw⟩ := h
    have hsmall (a : ℕ) (ha : 0<a) (hlt : a≤29) : ¬x ∣ a := fun hd =>
      (Nat.not_le.mpr (lt_of_le_of_lt hlt (by omega))) (Nat.le_of_dvd ha hd)
    have hc : x.Coprime (3*5*7*11*13*29) := by
      apply hp.coprime_iff_not_dvd.mpr
      simp only [hp.dvd_mul]
      exact fun h => by rcases h with (((((h|h)|h)|h)|h)|h) <;> exact hsmall _ (by decide) (by decide) h
    have he : (d*x-1)/2=z := by omega
    simp only [sievePass,he,ih hw,Bool.and_true,beq_iff_eq]
    exact hc

theorem reject_of_walk {w : List ℕ} {x : ℕ} (h : Walk w x x) (hw : w.prod = 2^w.length+1) :
    reject w = false := by
  have t := affine_walk h 1 0
  simp only [one_mul,zero_add,hw,add_mul] at t
  have hseed : forced 1 0 w = x := by omega
  simp [reject,hseed,sieve_walk h]

def next3 (x d : ℕ) : ℕ := 2 * (d*x+2) % 3

def shadow (x : ℕ) : List ℕ → Bool
  | [] => true
  | d :: ds => let y := next3 x d; (y != 0) && shadow y ds

theorem shadow_walk {ds : List ℕ} {x y : ℕ} (h : Walk ds x y) (hy : y.Prime) (hyl : 12000<y) :
    shadow (x%3) ds = true := by
  induction ds generalizing x with
  | nil => rfl
  | cons d ds ih =>
    obtain ⟨_,_,z,hz,hw⟩ := h
    have hpz : z.Prime ∧ 12000<z := by
      cases ds with
      | nil => change z=y at hw; exact hw ▸ ⟨hy,hyl⟩
      | cons e es => exact ⟨hw.1,hw.2.1⟩
    have hnz : z%3≠0 := by
      intro h0
      have he := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hpz.1).mp (Nat.dvd_of_mod_eq_zero h0)
      omega
    have hnext : next3 (x%3) d = z%3 := by
      unfold next3
      have hmod : 2 * (d*(x%3)+2) ≡ 2*(d*x+2) [MOD 3] :=
        (((Nat.mod_modEq _ _).mul_left d).add (Nat.ModEq.refl 2)).mul_left 2
      calc
        _ = 2*(d*x+2)%3 := hmod
        _ = z%3 := by rw [← hz]; omega
    simp [shadow,hnext,hnz,ih hw]




def bump (q : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | 0, a :: w => q*a :: w
  | i+1, a :: w => a :: bump q i w

@[simp] theorem length_bump (q i : ℕ) (w : List ℕ) : (bump q i w).length = w.length := by
  induction w generalizing i with
  | nil => cases i <;> rfl
  | cons a w ih => cases i <;> simp [bump,ih]

theorem prime_slot {q : ℕ} (hp : q.Prime) {w : List ℕ} (h : q ∣ w.prod) :
    ∃ (b : List ℕ) (i : ℕ), i < b.length ∧ w = bump q i b ∧ w.prod = q*b.prod := by
  induction w with
  | nil => exact False.elim (hp.not_dvd_one h)
  | cons a w ih =>
    rw [List.prod_cons,hp.dvd_mul] at h
    rcases h with ha|hw
    · obtain ⟨b,hb⟩ := ha
      exact ⟨b::w,0,by simp,by simp [bump,hb],by simp [hb,Nat.mul_assoc]⟩
    · obtain ⟨b,i,hi,e,ep⟩ := ih hw
      exact ⟨a::b,i+1,by simpa using hi,by simp [bump,e],by simp [ep,Nat.mul_left_comm]⟩

theorem residue_bump {q : ℕ} (hq : q%3=1) (w : List ℕ) (i : ℕ) :
    (bump q i w).map (·%3) = w.map (·%3) := by
  induction w generalizing i with
  | nil => cases i <;> rfl
  | cons a w ih =>
    cases i with
    | zero =>
      simp only [bump,List.map_cons,List.cons.injEq,and_true]
      rw [Nat.mul_mod,hq,one_mul,Nat.mod_mod]
    | succ i => simp [bump,ih]

def subsetProds : List ℕ → List ℕ
  | [] => [1]
  | p::ps => let ds := subsetProds ps; ds ++ ds.map (p*·)

theorem divisor_mem {fs : List ℕ} (hf : ∀ p ∈ fs, Nat.Prime p) {d : ℕ} (hd : d ∣ fs.prod) :
    d ∈ subsetProds fs := by
  induction fs generalizing d with
  | nil => simp [subsetProds,Nat.dvd_one.mp hd]
  | cons p ps ih =>
    obtain ⟨a,b,ha,hb,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul (show d∣p*ps.prod from hd)
    have ih' := ih (fun x hx => hf x (by simp [hx])) hb
    rcases (Nat.dvd_prime (hf p (by simp))).mp ha with h|h
    · simp [subsetProds,h,ih']
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨b,ih',by rw [h]⟩


theorem shadow_residue (u v : List ℕ) (h : u.map (·%3)=v.map (·%3)) (x : ℕ) :
    shadow x u = shadow x v := by
  induction u generalizing v x with
  | nil => cases v <;> simp_all
  | cons a u ih =>
    cases v with
    | nil => simp at h
    | cons b v =>
      have hh := List.cons.inj h
      have ht : next3 x a=next3 x b :=
        (((show a ≡ b [MOD 3] from hh.1).mul_right x).add (Nat.ModEq.refl 2)).mul_left 2
      simp only [shadow,ht,ih v hh.2]

def scan (choices : List ℕ) (test : List ℕ → Bool) : ℕ → ℕ → ℕ → List ℕ → Bool
  | 0, _, _, _ => true
  | 1, _, left, pref => if 3 ∣ left then test (left::pref).reverse else true
  | k+2, x, left, pref => choices.all fun d =>
      if d≠0 ∧ d∣left ∧ 3∣left/d ∧ next3 x d≠0 then
        scan choices test (k+1) (next3 x d) (left/d) (d::pref)
      else true

theorem lastFactor (a : ℕ) (w : List ℕ) : (a::w).getLastD 1 ∣ (a::w).prod := by
  induction w generalizing a with
  | nil => simp
  | cons b w ih =>
    change (b::w).getLastD 1 ∣ a*(b::w).prod
    exact dvd_mul_of_dvd_right (ih b) a

theorem scan_complete (choices : List ℕ) (test : List ℕ → Bool) (w : List ℕ) (x : ℕ)
    (pref : List ℕ) (hne : w≠[]) (hpos : 0<w.prod) (h3 : 3∣w.getLastD 1)
    (hc : ∀ a ∈ w, a ∈ choices) (hs : shadow x w=true)
    (hf : test (pref.reverse ++ w)=false) :
    scan choices test w.length x w.prod pref=false := by
  induction w generalizing x pref with
  | nil => contradiction
  | cons d w ih =>
    cases w with
    | nil =>
      simpa [scan,List.reverse_cons,show 3∣d from h3] using hf
    | cons a as =>
      let rest := a::as
      change 0<d*rest.prod at hpos
      have dp : 0<d := by
        by_contra! hh
        have he : d=0 := by omega
        simp [he] at hpos
      have rp : 0<rest.prod := by
        by_contra! hh
        have he : rest.prod=0 := by omega
        simp [he] at hpos
      have hd : d∣d*rest.prod := dvd_mul_right _ _
      have div : (d*rest.prod)/d=rest.prod := Nat.mul_div_cancel_left _ dp
      have ht : 3 ∣ rest.prod := h3.trans (lastFactor a as)
      change ((next3 x d != 0) && shadow (next3 x d) rest)=true at hs
      obtain ⟨hn,hs⟩ := Bool.and_eq_true_iff.mp hs
      have ih' := ih (next3 x d) (d::pref) (by simp) rp h3
        (fun t h => hc t (List.mem_cons_of_mem _ h)) hs
        (by simpa [List.reverse_cons,List.append_assoc] using hf)
      change (choices.all _) = false
      apply List.all_eq_false.mpr
      refine ⟨d,hc d (by simp),?_⟩
      have hn' : next3 x d≠0 := by simpa using hn
      change (if d≠0 ∧ d∣d*rest.prod ∧ 3∣(d*rest.prod)/d ∧ next3 x d ≠ 0 then
        scan choices test (as.length+1) (next3 x d) ((d*rest.prod)/d) (d::pref) else true) ≠ true
      rw [if_pos ⟨dp.ne',hd,by simpa [div] using ht,hn'⟩,div]
      change scan choices test (a::as).length (next3 x d) (a::as).prod (d::pref) ≠ true
      rw [ih']
      decide


def projOK (m : ℕ) (x : ℕ) : List ℕ → Bool
  | [] => true
  | d::w => (x.gcd m == 1) && projOK m (((d*x+(m-1))*((m+1)/2))%m) w

def projectReject (m : ℕ) (w : List ℕ) : Bool :=
  if m≤1 then false else
    let b := w.map (·%m)
    !(projOK m ((forced 1 0 b)%m) b)

theorem forced_mod (m a b : ℕ) (w : List ℕ) :
    forced a b (w.map (·%m)) ≡ forced a b w [MOD m] := by
  have aux (w : List ℕ) (a b c e : ℕ) (ha : a ≡ c [MOD m]) (hb : b ≡ e [MOD m]) :
      forced a b (w.map (·%m)) ≡ forced c e w [MOD m] := by
    induction w generalizing a b c e with
    | nil => exact hb
    | cons d ds ih =>
      exact ih _ _ _ _ (ha.mul_left 2) (((Nat.mod_modEq d m).mul hb).add ha)
  exact aux _ _ _ _ _ (Nat.ModEq.refl _) (Nat.ModEq.refl _)

theorem proj_walk {w : List ℕ} {x y : ℕ} (hw : Walk w x y) {m : ℕ} (hm : 1 < m) (hb : m≤12000)
    (hinv : (m+1)/2*2 ≡ 1 [MOD m]) : projOK m (x%m) (w.map (·%m)) = true := by
  induction w generalizing x with
  | nil => rfl
  | cons d ds ih =>
    obtain ⟨hx,hxl,z,hz,ht⟩ := hw
    have gx : x.Coprime m := hx.coprime_iff_not_dvd.mpr (fun hd => by
      have h := Nat.le_of_dvd (by omega : 0 < m) hd
      omega)
    have gx' : (x%m).gcd m=1 := by rw [← Nat.gcd_rec m x,Nat.gcd_comm]; exact gx
    have hs : ((d%m)*(x%m)+(m-1))*((m+1)/2) ≡ z [MOD m] := by
      calc
        _ ≡ (d*x+(m-1))*((m+1)/2) [MOD m] :=
          (((Nat.mod_modEq d m).mul (Nat.mod_modEq x m)).add (Nat.ModEq.refl _)).mul_right _
        _ = (2*z+m)*((m+1)/2) := by rw [←hz]; congr 1; omega
        _ ≡ (2*z+0)*((m+1)/2) [MOD m] :=
          ((Nat.ModEq.refl (2*z)).add (Nat.modEq_zero_iff_dvd.mpr (dvd_refl m))).mul_right _
        _ = ((m+1)/2*2)*z := by ring
        _ ≡ 1*z [MOD m] := hinv.mul_right _
        _ = z := one_mul _
    change ((x%m).gcd m == 1 && projOK m _ (ds.map (·%m)))=true
    simp only [gx',beq_self_eq_true]
    exact hs ▸ ih ht

theorem project_of_walk {w : List ℕ} {x m : ℕ} (hw : Walk w x x) (hc : w.prod=2^w.length+1)
    (hb : m≤12000) (hi : (m+1)/2*2 ≡ 1 [MOD m]) : projectReject m w=false := by
  by_cases hm : m≤1
  · simp [projectReject,hm]
  have t := affine_walk hw 1 0
  simp only [one_mul,zero_add,hc,add_mul] at t
  have seed : forced 1 0 w=x := by omega
  have mod := forced_mod m 1 0 w
  rw [seed] at mod
  simp only [projectReject,hm,if_false]
  rw [show forced 1 0 (w.map (·%m)) % m=x%m from mod,proj_walk hw (by omega) hb hi]
  rfl

theorem residues_bump_general {q m : ℕ} (hq : q ≡ 1 [MOD m]) (w : List ℕ) (i : ℕ) :
    (bump q i w).map (·%m) = w.map (·%m) := by
  induction w generalizing i with
  | nil => cases i <;> rfl
  | cons a w ih =>
    cases i with
    | zero =>
      simp only [bump,List.map_cons,List.cons.injEq,and_true]
      exact (hq.mul_right a).trans (by rw [one_mul])
    | succ i => simp [bump,ih]

theorem project_bump {q m : ℕ} (hq : q ≡ 1 [MOD m]) (w : List ℕ) (i : ℕ) :
    projectReject m (bump q i w) = projectReject m w := by
  simp only [projectReject,residues_bump_general hq]

def filteredFill : List (ℕ × ℕ) → (List ℕ → Bool) → List ℕ → Bool
  | [], test, w => test w
  | (q,m)::ps, test, w => filteredFill ps (fun b => projectReject m b ||
      (List.range b.length).all (fun i => test (bump q i b))) w

theorem peelFiltered {base : ℕ} {ps : List (ℕ × ℕ)}
    (hq : ∀ t ∈ ps, t.1.Prime ∧ t.1%3=1 ∧ t.1 ≡ 1 [MOD t.2])
    (compat : ps.Pairwise (fun a b => a.1 ≡ 1 [MOD b.2]))
    (w : List ℕ) (hw : w.prod=(ps.map Prod.fst).prod*base)
    (clear : ∀ t ∈ ps, projectReject t.2 w = false)
    (test : List ℕ → Bool) (hf : test w=false) :
    ∃ b : List ℕ, b.prod=base ∧ b.map (·%3)=w.map (·%3) ∧ filteredFill ps test b=false := by
  induction ps generalizing w test with
  | nil => exact ⟨w,by simpa using hw,rfl,hf⟩
  | cons t ps ih =>
    rcases t with ⟨q,m⟩
    obtain ⟨qp,qr,qm⟩ := hq (q,m) (by simp)
    have hd : q ∣ w.prod := by rw [hw]; simp [mul_assoc]
    obtain ⟨b,i,hi,he,hp⟩ := prime_slot qp hd
    have hb : b.prod=(ps.map Prod.fst).prod*base := by
      simpa [hp,List.map_cons,List.prod_cons,mul_assoc,Nat.mul_right_inj qp.ne_zero] using hw
    let test' (v : List ℕ) := projectReject m v || (List.range v.length).all fun j => test (bump q j v)
    have fail : test' b=false := by
      have hbase := clear (q,m) (by simp)
      rw [he,project_bump qm] at hbase
      simp only [test',hbase,Bool.false_or]
      apply List.all_eq_false.mpr
      exact ⟨i,List.mem_range.mpr hi,by rw [←he,hf]; decide⟩
    obtain ⟨agree,tail⟩ := List.pairwise_cons.mp compat
    have still (s : ℕ×ℕ) (hs : s∈ps) : projectReject s.2 b=false := by
      have hh := clear s (by simp [hs])
      rw [he,project_bump (agree s hs)] at hh
      exact hh
    obtain ⟨v,hvp,hm,hf'⟩ := ih (fun z hz => hq z (by simp [hz])) tail b hb still test' fail
    exact ⟨v,hvp,by rw [he,residue_bump qr]; exact hm,hf'⟩

def exhaustive (r : ℕ) (bad : List ℕ) (good : List (ℕ×ℕ)) : Bool :=
  scan (subsetProds bad).eraseDups (filteredFill good reject) r 1 bad.prod []

theorem exhaustive_sound {r : ℕ} {bad w : List ℕ} {good : List (ℕ×ℕ)} {x : ℕ}
    (hw : Walk w x x) (hpx : x.Prime) (hx : 12000<x) (hx3 : x%3=1)
    (hr : w.length=r) (hrpos : 0<r) (hlast : 3 ∣ w.getLastD 1)
    (hc : w.prod=2^w.length+1) (hsplit : w.prod=(good.map Prod.fst).prod*bad.prod)
    (hgood : ∀ t ∈ good, t.1.Prime ∧ t.1%3=1 ∧ t.1 ≡ 1 [MOD t.2])
    (compat : good.Pairwise (fun a b => a.1 ≡ 1 [MOD b.2]))
    (bounds : ∀ t ∈ good, t.2≤12000 ∧ (t.2+1)/2*2 ≡ 1 [MOD t.2]) (hbad : ∀ q ∈ bad, q.Prime) :
    exhaustive r bad good = false := by
  obtain ⟨v,hp,hm,hno⟩ := peelFiltered hgood compat w hsplit (fun t ht => project_of_walk hw hc (bounds t ht).1 (bounds t ht).2) reject (reject_of_walk hw hc)
  have hvlen : v.length=w.length := by simpa using congrArg List.length hm
  have hv3 : 3 ∣ v.getLastD 1 := by
    have hh := congrArg (fun t : List ℕ => t.getLastD (1%3)) hm
    simp only [List.getLastD_map] at hh
    exact Nat.dvd_of_mod_eq_zero (hh.trans (Nat.mod_eq_zero_of_dvd hlast))
  have hvpos : 0<v.prod := by
    rw [hp]
    apply List.prod_pos
    intro q hq
    exact (hbad q hq).pos
  have hh := shadow_walk hw hpx hx
  rw [hx3] at hh
  have result := scan_complete (subsetProds bad).eraseDups (filteredFill good reject) v 1 []
    (by intro e; simp [e] at hvlen; omega) hvpos hv3 (fun q hq =>
      List.mem_eraseDups.mpr (divisor_mem hbad (hp ▸ List.dvd_prod hq))) ((shadow_residue v w hm 1).trans hh) hno
  simpa [exhaustive,hp,hvlen,hr] using result

open Finset Function
open OMA.R_OeisA245211_conjecture_R2 (large_prime squarefree_fixed_point_product)

theorem fixed_excluded {n r : ℕ} (hs : Squarefree n) (ha : OeisA245211.a n=n)
    (hcard : n.primeFactors.card=r) (hr : 15≤r) (h3 : 3∣2^r+1)
    {bad : List ℕ} {good : List (ℕ×ℕ)} (hsplit : 2^r+1=(good.map Prod.fst).prod*bad.prod)
    (hgood : ∀ t ∈ good, t.1.Prime ∧ t.1%3=1 ∧ t.1 ≡ 1 [MOD t.2])
    (compat : good.Pairwise (fun a b => a.1 ≡ 1 [MOD b.2]))
    (bounds : ∀ t ∈ good, t.2≤12000 ∧ (t.2+1)/2*2 ≡ 1 [MOD t.2]) (hbad : ∀ q ∈ bad, q.Prime) :
    exhaustive r bad good=false := by
  classical
  let P := n.primeFactors
  let p : P → ℕ := Subtype.val
  have hp (i : P) : (p i).Prime := Nat.prime_of_mem_primeFactors i.property
  have card : Fintype.card P=r := by simpa [P] using hcard
  letI : Nonempty P := (Finset.card_pos.mp (show 0<P.card by change 0<n.primeFactors.card; omega)).to_subtype
  have heq : (∏ i, (2*p i+1))=(2^Fintype.card P+1)*∏ i,p i := by
    calc
      _ = ∏ k ∈ P, (2*k+1) := Finset.prod_coe_sort P (fun k => 2*k+1)
      _ = (2^P.card+1) * ∏ k ∈ P, k := squarefree_fixed_point_product hs ha
      _ = _ := by
        rw [Fintype.card_coe]
        exact congrArg (fun z => (2^P.card+1)*z) (Finset.prod_coe_sort P (fun k => k)).symm
  have hlarge (i : P) : 12000<p i := by
    have large := large_prime p hp (by omega : 2≤Fintype.card P) heq i
    have powle := Nat.pow_le_pow_right (by decide : 0<2) (show 14≤Fintype.card P-1 by omega)
    omega
  obtain ⟨f,d,hbij,hperiod,step,product⟩ := cofactorData p hp Subtype.val_injective heq
  rw [card] at product
  obtain ⟨j,_,hj⟩ := ((show Prime (3:ℕ) from (by decide : Nat.Prime 3).prime).dvd_finsetProd_iff d).mp
    (show 3∣∏ i,d i by rw [product]; exact h3)
  let start := f j
  let orbit (i : ℕ) := f^[i] start
  let value (i : ℕ) := p (orbit i)
  let digit (i : ℕ) := d (orbit i)
  have period (i : P) : f^[r] i=i := by
    have h := isPeriodicPt_minimalPeriod f i
    rwa [hperiod i,card] at h
  have next (i : ℕ) : 2*value (i+1)+1 = digit i*value i := by
    simpa [value,digit,orbit,iterate_succ_apply',mul_comm] using step (orbit i)
  have hwalk (k s : ℕ) : Walk ((List.range' s k).map digit) (value s) (value (s+k)) := by
    induction k generalizing s with
    | zero => simp [Walk]
    | succ k ih =>
      change (value s).Prime ∧ 12000<value s ∧ ∃ z, 2*z+1=digit s*value s ∧
        Walk ((List.range' (s+1) k).map digit) z (value (s+(k+1)))
      exact ⟨hp _,hlarge _,value (s+1),next s,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (s+1)⟩
  let w := (List.range r).map digit
  have returning : value r=value 0 := by simp [value,orbit,period]
  have walk' : Walk w (value 0) (value 0) := by simpa [w,List.range_eq_range',returning] using hwalk r 0
  have mapbij : Bijective (fun i : Fin r => orbit i.val) := by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨?_, by simp [card]⟩
    intro i j hh
    apply Fin.ext
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod
      (show i.val < minimalPeriod f start by rw [hperiod,card]; exact i.isLt)
      (show j.val < minimalPeriod f start by rw [hperiod,card]; exact j.isLt)).mp hh
  have wprod : w.prod=2^r+1 := by
    calc
      _ = ∏ i ∈ Finset.range r, digit i := by
        have hrange : (List.range r).toFinset=Finset.range r := by ext i; simp
        simpa [w,hrange] using (List.prod_toFinset digit (List.nodup_range (n:=r))).symm
      _ = ∏ i : Fin r, digit i.val := (Fin.prod_univ_eq_prod_range digit r).symm
      _ = ∏ i : P, d i := Fintype.prod_equiv (Equiv.ofBijective _ mapbij) _ _ (fun _ => rfl)
      _ = _ := product
  have x01 : value 0%3=1 := by
    change p (f j)%3=1
    have hh : 3∣2*p (f j)+1 := (step j) ▸ dvd_mul_of_dvd_right hj _
    omega
  have last : 3∣w.getLastD 1 := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
    have fin : f^[k] (f j)=j := by
      rw [← iterate_succ_apply,←hk,period]
    simpa [w,hk,List.range_succ,digit,orbit,start,fin] using hj
  have len : w.length=r := by simp [w]
  exact exhaustive_sound walk' (hp _) (hlarge _) x01 len (by omega) last (by simpa [len] using wprod)
    (wprod.trans hsplit) hgood compat bounds hbad

/-- Keep the possible divisors of the unused product. Placing a factor of one
leaves this list unchanged. Every other placement reduces the list. -/
private def fastScan (test : List ℕ → Bool) :
    ℕ → ℕ → ℕ → List ℕ → List ℕ → Bool
  | 0, _, _, _, _ => true
  | 1, _, left, pref, _ => if 3 ∣ left then test (left::pref).reverse else true
  | k+2, x, left, pref, live => live.all fun d =>
      let y := next3 x d
      if y = 0 then true
      else if d = 1 then fastScan test (k+1) y left (1::pref) live
      else
        let rem := left/d
        fastScan test (k+1) y rem (d::pref) (live.filter fun t => 3*t ∣ rem)

private theorem fastScan_implies (choices : List ℕ) (test : List ℕ → Bool) :
    ∀ k x left pref live,
      (∀ d ∈ choices, 3*d ∣ left → d ∈ live) →
      fastScan test k x left pref live = true → scan choices test k x left pref = true
  | 0, _, _, _, _, _, _ => rfl
  | 1, _, _, _, _, _, h => h
  | k+2, x, left, pref, live, cover, h => by
    apply List.all_eq_true.mpr
    intro d hd
    by_cases he : d≠0 ∧ d∣left ∧ 3∣left/d ∧ next3 x d≠0
    · have he' := he
      obtain ⟨_,dl,dm,hy⟩ := he'
      have back : left = left/d*d := (Nat.div_mul_cancel dl).symm
      have sub : left/d ∣ left := ⟨d,back⟩
      have ok : 3*d ∣ left := by
        obtain ⟨a, ha⟩ := dm
        exact ⟨a,calc left = left/d*d := back
                      _ = (3*d)*a := by rw [ha]; ring⟩
      have hh := List.all_eq_true.mp h d (cover d hd ok)
      simp only [if_pos he]
      by_cases ho : d=1
      · subst d
        simp only [hy,if_false,if_true,Nat.div_one] at hh ⊢
        exact fastScan_implies choices test (k+1) _ _ _ _ cover hh
      · apply fastScan_implies choices test (k+1) _ _ _ (live.filter fun t => 3*t ∣ left/d)
        · intro t ht dt
          exact List.mem_filter.mpr ⟨cover t ht (dt.trans sub),by simpa using dt⟩
        · simpa [hy,ho] using hh
    · simp [he]

private theorem checkedScan {bad : List ℕ} {good : List (ℕ×ℕ)} {r : ℕ}
    (h : fastScan (filteredFill good reject) r 1 bad.prod []
      ((subsetProds bad).eraseDups.filter fun d => 3*d ∣ bad.prod) = true) :
    exhaustive r bad good = true := by
  apply fastScan_implies _ _ _ _ _ _ _ _ h
  intro d hd hdiv
  exact List.mem_filter.mpr ⟨hd,by simpa using hdiv⟩

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem checked_15 : exhaustive 15 [3,3,11] [(331,55)] = true := by
  apply checkedScan
  decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem checked_21 : exhaustive 21 [3,3] [(5419,1),(43,1)] = true := by
  apply checkedScan
  decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem checked_33 : exhaustive 33 [3,3,683] [(20857,869),(67,11)] = true := by
  apply checkedScan
  decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem checked_35 : exhaustive 35 [3,11,281,86171] [(43,7)] = true := by
  apply checkedScan
  decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem checked_39 : exhaustive 39 [3,3] [(22366891,1),(2731,1)] = true := by
  apply checkedScan
  decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem checked_45 : exhaustive 45 [3,3,3,11] [(18837001,10465),(331,5),(19,1)] = true := by
  apply checkedScan
  decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem checked_55 : exhaustive 55 [3,11,11,683,48912491] [(2971,55)] = true := by
  apply checkedScan
  decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem checked_57 : exhaustive 57 [3,3] [(160465489,1),(174763,1),(571,1)] = true := by
  apply checkedScan
  decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem checked_63 : exhaustive 63 [3,3,3] [(77158673929,1),(5419,1),(43,1),(19,1)] = true := by
  apply checkedScan
  decide +kernel

theorem scan_mono (choices : List ℕ) (P Q : List ℕ → Bool) (h : ∀ w, P w=true → Q w=true) :
    ∀ k x left pref, scan choices P k x left pref = true → scan choices Q k x left pref = true
  | 0, _, _, _, _ => rfl
  | 1, x, left, pref, hh => by
    by_cases hd : 3∣left
    · simpa [scan,hd] using h _ (by simpa [scan,hd] using hh)
    · simp [scan,hd]
  | k+2, x, left, pref, hh => by
    apply List.all_eq_true.mpr
    intro d hd
    have src := List.all_eq_true.mp hh d hd
    by_cases he : d≠0 ∧ d∣left ∧ 3∣left/d ∧ next3 x d≠0
    · simpa [he] using scan_mono choices P Q h (k+1) (next3 x d) (left/d) (d::pref)
        (by simpa [he] using src)
    · simp [he]

private def shape0 : List ℕ := [3] ++ [43691] ++ List.replicate 48 1 ++ [3]

private def shape1 : List ℕ := [43691] ++ List.replicate 49 1 ++ [9]

private def shape2 : List ℕ := [43691] ++ List.replicate 48 1 ++ [3] ++ [3]

private def afterSecond (w : List ℕ) : Bool :=
  projectReject 119 w || (List.range w.length).all (fun i => reject (bump 2857 i w))
private def afterFirst (w : List ℕ) : Bool :=
  projectReject 17 w || (List.range w.length).all (fun i => afterSecond (bump 6529 i w))
private def complete51 (w : List ℕ) : Bool :=
  projectReject 17 w || (List.range w.length).all (fun i => afterFirst (bump 307 i w))

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shapesCover : scan (subsetProds [3,3,43691]).eraseDups (fun w => [shape0,shape1,shape2].contains w) 51 1 393219 [] = true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot0 : afterFirst (bump 307 0 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot1 : afterFirst (bump 307 1 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot2 : afterFirst (bump 307 2 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot3 : afterFirst (bump 307 3 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot4 : afterFirst (bump 307 4 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot5 : afterFirst (bump 307 5 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot6 : afterFirst (bump 307 6 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot7 : afterFirst (bump 307 7 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot8 : afterFirst (bump 307 8 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot9 : afterFirst (bump 307 9 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot10 : afterFirst (bump 307 10 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot11 : afterFirst (bump 307 11 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot12 : afterFirst (bump 307 12 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot13 : afterFirst (bump 307 13 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot14 : afterFirst (bump 307 14 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot15 : afterFirst (bump 307 15 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot16 : afterFirst (bump 307 16 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot17 : afterFirst (bump 307 17 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot18 : afterFirst (bump 307 18 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot19 : afterFirst (bump 307 19 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot20 : afterFirst (bump 307 20 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot21 : afterFirst (bump 307 21 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot22 : afterFirst (bump 307 22 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot23 : afterFirst (bump 307 23 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot24 : afterFirst (bump 307 24 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot25 : afterFirst (bump 307 25 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot26 : afterFirst (bump 307 26 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot27 : afterFirst (bump 307 27 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot28 : afterFirst (bump 307 28 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot29 : afterFirst (bump 307 29 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot30 : afterFirst (bump 307 30 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot31 : afterFirst (bump 307 31 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot32 : afterFirst (bump 307 32 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot33 : afterFirst (bump 307 33 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot34 : afterFirst (bump 307 34 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot35 : afterFirst (bump 307 35 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot36 : afterFirst (bump 307 36 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot37 : afterFirst (bump 307 37 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot38 : afterFirst (bump 307 38 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot39 : afterFirst (bump 307 39 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot40 : afterFirst (bump 307 40 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot41 : afterFirst (bump 307 41 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot42 : afterFirst (bump 307 42 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot43 : afterFirst (bump 307 43 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot44 : afterFirst (bump 307 44 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot45 : afterFirst (bump 307 45 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot46 : afterFirst (bump 307 46 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot47 : afterFirst (bump 307 47 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot48 : afterFirst (bump 307 48 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot49 : afterFirst (bump 307 49 shape0)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape0_slot50 : afterFirst (bump 307 50 shape0)=true := by decide +kernel

private theorem acceptedShape0 : complete51 shape0=true := by
  refine Bool.or_eq_true_iff.mpr (Or.inr (List.all_eq_true.mpr ?_))
  intro i hi
  have hi' : i < 51 := List.mem_range.mp hi
  interval_cases i
  · exact shape0_slot0
  · exact shape0_slot1
  · exact shape0_slot2
  · exact shape0_slot3
  · exact shape0_slot4
  · exact shape0_slot5
  · exact shape0_slot6
  · exact shape0_slot7
  · exact shape0_slot8
  · exact shape0_slot9
  · exact shape0_slot10
  · exact shape0_slot11
  · exact shape0_slot12
  · exact shape0_slot13
  · exact shape0_slot14
  · exact shape0_slot15
  · exact shape0_slot16
  · exact shape0_slot17
  · exact shape0_slot18
  · exact shape0_slot19
  · exact shape0_slot20
  · exact shape0_slot21
  · exact shape0_slot22
  · exact shape0_slot23
  · exact shape0_slot24
  · exact shape0_slot25
  · exact shape0_slot26
  · exact shape0_slot27
  · exact shape0_slot28
  · exact shape0_slot29
  · exact shape0_slot30
  · exact shape0_slot31
  · exact shape0_slot32
  · exact shape0_slot33
  · exact shape0_slot34
  · exact shape0_slot35
  · exact shape0_slot36
  · exact shape0_slot37
  · exact shape0_slot38
  · exact shape0_slot39
  · exact shape0_slot40
  · exact shape0_slot41
  · exact shape0_slot42
  · exact shape0_slot43
  · exact shape0_slot44
  · exact shape0_slot45
  · exact shape0_slot46
  · exact shape0_slot47
  · exact shape0_slot48
  · exact shape0_slot49
  · exact shape0_slot50

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem acceptedShape1 : complete51 shape1=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot0 : afterFirst (bump 307 0 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot1 : afterFirst (bump 307 1 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot2 : afterFirst (bump 307 2 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot3 : afterFirst (bump 307 3 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot4 : afterFirst (bump 307 4 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot5 : afterFirst (bump 307 5 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot6 : afterFirst (bump 307 6 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot7 : afterFirst (bump 307 7 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot8 : afterFirst (bump 307 8 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot9 : afterFirst (bump 307 9 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot10 : afterFirst (bump 307 10 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot11 : afterFirst (bump 307 11 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot12 : afterFirst (bump 307 12 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot13 : afterFirst (bump 307 13 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot14 : afterFirst (bump 307 14 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot15 : afterFirst (bump 307 15 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot16 : afterFirst (bump 307 16 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot17 : afterFirst (bump 307 17 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot18 : afterFirst (bump 307 18 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot19 : afterFirst (bump 307 19 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot20 : afterFirst (bump 307 20 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot21 : afterFirst (bump 307 21 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot22 : afterFirst (bump 307 22 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot23 : afterFirst (bump 307 23 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot24 : afterFirst (bump 307 24 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot25 : afterFirst (bump 307 25 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot26 : afterFirst (bump 307 26 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot27 : afterFirst (bump 307 27 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot28 : afterFirst (bump 307 28 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot29 : afterFirst (bump 307 29 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot30 : afterFirst (bump 307 30 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot31 : afterFirst (bump 307 31 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot32 : afterFirst (bump 307 32 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot33 : afterFirst (bump 307 33 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot34 : afterFirst (bump 307 34 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot35 : afterFirst (bump 307 35 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot36 : afterFirst (bump 307 36 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot37 : afterFirst (bump 307 37 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot38 : afterFirst (bump 307 38 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot39 : afterFirst (bump 307 39 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot40 : afterFirst (bump 307 40 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot41 : afterFirst (bump 307 41 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot42 : afterFirst (bump 307 42 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot43 : afterFirst (bump 307 43 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot44 : afterFirst (bump 307 44 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot45 : afterFirst (bump 307 45 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot46 : afterFirst (bump 307 46 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot47 : afterFirst (bump 307 47 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot48 : afterFirst (bump 307 48 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot49 : afterFirst (bump 307 49 shape2)=true := by decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem shape2_slot50 : afterFirst (bump 307 50 shape2)=true := by decide +kernel

private theorem acceptedShape2 : complete51 shape2=true := by
  refine Bool.or_eq_true_iff.mpr (Or.inr (List.all_eq_true.mpr ?_))
  intro i hi
  have hi' : i < 51 := List.mem_range.mp hi
  interval_cases i
  · exact shape2_slot0
  · exact shape2_slot1
  · exact shape2_slot2
  · exact shape2_slot3
  · exact shape2_slot4
  · exact shape2_slot5
  · exact shape2_slot6
  · exact shape2_slot7
  · exact shape2_slot8
  · exact shape2_slot9
  · exact shape2_slot10
  · exact shape2_slot11
  · exact shape2_slot12
  · exact shape2_slot13
  · exact shape2_slot14
  · exact shape2_slot15
  · exact shape2_slot16
  · exact shape2_slot17
  · exact shape2_slot18
  · exact shape2_slot19
  · exact shape2_slot20
  · exact shape2_slot21
  · exact shape2_slot22
  · exact shape2_slot23
  · exact shape2_slot24
  · exact shape2_slot25
  · exact shape2_slot26
  · exact shape2_slot27
  · exact shape2_slot28
  · exact shape2_slot29
  · exact shape2_slot30
  · exact shape2_slot31
  · exact shape2_slot32
  · exact shape2_slot33
  · exact shape2_slot34
  · exact shape2_slot35
  · exact shape2_slot36
  · exact shape2_slot37
  · exact shape2_slot38
  · exact shape2_slot39
  · exact shape2_slot40
  · exact shape2_slot41
  · exact shape2_slot42
  · exact shape2_slot43
  · exact shape2_slot44
  · exact shape2_slot45
  · exact shape2_slot46
  · exact shape2_slot47
  · exact shape2_slot48
  · exact shape2_slot49
  · exact shape2_slot50

private theorem checked_51 : exhaustive 51 [3,3,43691] [(2857,119),(6529,17),(307,17)]=true := by
  apply scan_mono (subsetProds [3,3,43691]).eraseDups (fun w => [shape0,shape1,shape2].contains w) complete51 _ _ _ _ _ shapesCover
  intro w hw
  have hm : w ∈ [shape0,shape1,shape2] := by simpa using hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl|rfl
  · exact acceptedShape0
  · exact acceptedShape1
  · exact acceptedShape2

set_option maxRecDepth 16000 in
private theorem exclude_15 {n : ℕ} (hs : Squarefree n) (ha : OeisA245211.a n=n) (hr : n.primeFactors.card=15) : False := by
  have h := fixed_excluded hs ha hr (by decide) (by decide) (bad:=[3,3,11]) (good:=[(331,55)]) (by decide) ?_ ?_ ?_ ?_
  · rw [checked_15] at h
    contradiction
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    all_goals exact ⟨by norm_num1,by decide,by decide⟩
  · decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl <;> decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> norm_num1

set_option maxRecDepth 16000 in
private theorem exclude_21 {n : ℕ} (hs : Squarefree n) (ha : OeisA245211.a n=n) (hr : n.primeFactors.card=21) : False := by
  have h := fixed_excluded hs ha hr (by decide) (by decide) (bad:=[3,3]) (good:=[(5419,1),(43,1)]) (by decide) ?_ ?_ ?_ ?_
  · rw [checked_21] at h
    contradiction
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    all_goals exact ⟨by norm_num1,by decide,by decide⟩
  · decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl <;> decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl <;> norm_num1

set_option maxRecDepth 16000 in
private theorem exclude_33 {n : ℕ} (hs : Squarefree n) (ha : OeisA245211.a n=n) (hr : n.primeFactors.card=33) : False := by
  have h := fixed_excluded hs ha hr (by decide) (by decide) (bad:=[3,3,683]) (good:=[(20857,869),(67,11)]) (by decide) ?_ ?_ ?_ ?_
  · rw [checked_33] at h
    contradiction
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    all_goals exact ⟨by norm_num1,by decide,by decide⟩
  · decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl <;> decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> norm_num1

set_option maxRecDepth 16000 in
private theorem exclude_35 {n : ℕ} (hs : Squarefree n) (ha : OeisA245211.a n=n) (hr : n.primeFactors.card=35) : False := by
  have h := fixed_excluded hs ha hr (by decide) (by decide) (bad:=[3,11,281,86171]) (good:=[(43,7)]) (by decide) ?_ ?_ ?_ ?_
  · rw [checked_35] at h
    contradiction
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    all_goals exact ⟨by norm_num1,by decide,by decide⟩
  · decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl <;> decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl <;> norm_num1

set_option maxRecDepth 16000 in
private theorem exclude_39 {n : ℕ} (hs : Squarefree n) (ha : OeisA245211.a n=n) (hr : n.primeFactors.card=39) : False := by
  have h := fixed_excluded hs ha hr (by decide) (by decide) (bad:=[3,3]) (good:=[(22366891,1),(2731,1)]) (by decide) ?_ ?_ ?_ ?_
  · rw [checked_39] at h
    contradiction
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    all_goals exact ⟨by norm_num1,by decide,by decide⟩
  · decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl <;> decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl <;> norm_num1

set_option maxRecDepth 16000 in
private theorem exclude_45 {n : ℕ} (hs : Squarefree n) (ha : OeisA245211.a n=n) (hr : n.primeFactors.card=45) : False := by
  have h := fixed_excluded hs ha hr (by decide) (by decide) (bad:=[3,3,3,11]) (good:=[(18837001,10465),(331,5),(19,1)]) (by decide) ?_ ?_ ?_ ?_
  · rw [checked_45] at h
    contradiction
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl
    all_goals exact ⟨by norm_num1,by decide,by decide⟩
  · decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl <;> decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl <;> norm_num1

set_option maxRecDepth 16000 in
private theorem exclude_51 {n : ℕ} (hs : Squarefree n) (ha : OeisA245211.a n=n) (hr : n.primeFactors.card=51) : False := by
  have h := fixed_excluded hs ha hr (by decide) (by decide) (bad:=[3,3,43691]) (good:=[(2857,119),(6529,17),(307,17)]) (by decide) ?_ ?_ ?_ ?_
  · rw [checked_51] at h
    contradiction
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl
    all_goals exact ⟨by norm_num1,by decide,by decide⟩
  · decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl <;> decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> norm_num1

set_option maxRecDepth 16000 in
private theorem exclude_55 {n : ℕ} (hs : Squarefree n) (ha : OeisA245211.a n=n) (hr : n.primeFactors.card=55) : False := by
  have h := fixed_excluded hs ha hr (by decide) (by decide) (bad:=[3,11,11,683,48912491]) (good:=[(2971,55)]) (by decide) ?_ ?_ ?_ ?_
  · rw [checked_55] at h
    contradiction
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl
    all_goals exact ⟨by norm_num1,by decide,by decide⟩
  · decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl <;> decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl <;> norm_num1

set_option maxRecDepth 16000 in
private theorem exclude_57 {n : ℕ} (hs : Squarefree n) (ha : OeisA245211.a n=n) (hr : n.primeFactors.card=57) : False := by
  have h := fixed_excluded hs ha hr (by decide) (by decide) (bad:=[3,3]) (good:=[(160465489,1),(174763,1),(571,1)]) (by decide) ?_ ?_ ?_ ?_
  · rw [checked_57] at h
    contradiction
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl
    all_goals exact ⟨by norm_num1,by decide,by decide⟩
  · decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl <;> decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl <;> norm_num1

set_option maxRecDepth 16000 in
private theorem exclude_63 {n : ℕ} (hs : Squarefree n) (ha : OeisA245211.a n=n) (hr : n.primeFactors.card=63) : False := by
  have h := fixed_excluded hs ha hr (by decide) (by decide) (bad:=[3,3,3]) (good:=[(77158673929,1),(5419,1),(43,1),(19,1)]) (by decide) ?_ ?_ ?_ ?_
  · rw [checked_63] at h
    contradiction
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl
    all_goals exact ⟨by norm_num1,by decide,by decide⟩
  · decide
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl <;> decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> norm_num1

end FiniteFactorCycles

open FiniteFactorCycles in
theorem OMA.solution : OMA.R_OeisA245211_conjecture_R2.H2 := by
  intro n hs hl hu ho hn ha
  let r := n.primeFactors.card
  change 3 ≤ r at hl
  change r < 65 at hu
  change Odd r at ho
  obtain ⟨k,hk⟩ := ho
  have h3 : r ≠ 3 := hn 3 1 (by decide) (by decide)
  have h9 : r ≠ 9 := hn 3 2 (by decide) (by decide)
  have h27 : r ≠ 27 := hn 3 3 (by decide) (by decide)
  have h5 : r ≠ 5 := hn 5 1 (by decide) (by decide)
  have h25 : r ≠ 25 := hn 5 2 (by decide) (by decide)
  have h7 : r ≠ 7 := hn 7 1 (by decide) (by decide)
  have h49 : r ≠ 49 := hn 7 2 (by decide) (by decide)
  have h11 : r ≠ 11 := hn 11 1 (by decide) (by decide)
  have h13 : r ≠ 13 := hn 13 1 (by decide) (by decide)
  have h17 : r ≠ 17 := hn 17 1 (by decide) (by decide)
  have h19 : r ≠ 19 := hn 19 1 (by decide) (by decide)
  have h23 : r ≠ 23 := hn 23 1 (by decide) (by decide)
  have h29 : r ≠ 29 := hn 29 1 (by decide) (by decide)
  have h31 : r ≠ 31 := hn 31 1 (by decide) (by decide)
  have h37 : r ≠ 37 := hn 37 1 (by decide) (by decide)
  have h41 : r ≠ 41 := hn 41 1 (by decide) (by decide)
  have h43 : r ≠ 43 := hn 43 1 (by decide) (by decide)
  have h47 : r ≠ 47 := hn 47 1 (by decide) (by decide)
  have h53 : r ≠ 53 := hn 53 1 (by decide) (by decide)
  have h59 : r ≠ 59 := hn 59 1 (by decide) (by decide)
  have h61 : r ≠ 61 := hn 61 1 (by decide) (by decide)
  have cases : r = 15 ∨ r = 21 ∨ r = 33 ∨ r = 35 ∨ r = 39 ∨ r = 45 ∨ r = 51 ∨ r = 55 ∨ r = 57 ∨ r = 63 := by omega
  rcases cases with h|h|h|h|h|h|h|h|h|h
  · exact exclude_15 hs ha h
  · exact exclude_21 hs ha h
  · exact exclude_33 hs ha h
  · exact exclude_35 hs ha h
  · exact exclude_39 hs ha h
  · exact exclude_45 hs ha h
  · exact exclude_51 hs ha h
  · exact exclude_55 hs ha h
  · exact exclude_57 hs ha h
  · exact exclude_63 hs ha h
