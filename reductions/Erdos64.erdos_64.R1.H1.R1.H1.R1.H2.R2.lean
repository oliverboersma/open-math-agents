import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1
import Mathlib

/-!
# Normal 2-subgroups in the Erdős–Gyárfás matching problem

The normalized matching presentation comes from PR 5246, building on @JamesSlash's
bridge reduction in PR 592. This sibling of the central-commutator split in PR 5820
uses descent on the number of points. Among finite pointwise-separated counterexamples
with matching labels 1, p and q, any least one has trivial normal 2-core.

For a nontrivial normal 2-subgroup K, the central elements of K whose square is one
form a nontrivial normal elementary abelian subgroup E. Pass to E-orbits. A return
permutation of one orbit has a point there of 2-power period. This is the elementary
abelian case of Glauberman's coprime fixed-point lemma (I. M. Isaacs, 1968, Lemma 4,
doi:10.4153/CJM-1968-130-7). The proof below proves this case using commuting
involutions and works for actions with point stabilizers.

Two quotient labels coinciding on a fiber force an alternating power-of-two cycle
upstairs. Otherwise a quotient cycle lifts in a power-of-two number of laps, and the
parent's defect-density estimate applies again on the smaller set. The remaining cases
have odd generated group order, or even order and no nontrivial normal 2-subgroup.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2
open SimpleGraph

/-- Pointwise-separated matchings whose generated group has odd order. -/
def H1 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
    Fintype.card X ≤ 3 * {x : X | p (q x) ≠ q (p x)}.ncard →
    Odd (Nat.card (Subgroup.closure ({p,q} : Set (Equiv.Perm X)))) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ (SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = p u.2 ∨ v.2 = q u.2)))

/-- Even generated group order and no nontrivial normal 2-subgroup. -/
def H2 : Prop :=
  ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
    (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
    Fintype.card X ≤ 3 * {x : X | p (q x) ≠ q (p x)}.ncard →
    Even (Nat.card (Subgroup.closure ({p,q} : Set (Equiv.Perm X)))) →
    (∀ K : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))), K.Normal → IsPGroup 2 K → K = ⊥) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ (SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = p u.2 ∨ v.2 = q u.2)))

lemma adj_mod {n : ℕ} (hn : 2≤n) (i j : Fin n) :
    (cycleGraph n).Adj i j ↔ j.val = (i.val+1)%n ∨ i.val = (j.val+1)%n := by
  obtain ⟨m,rfl⟩ : ∃ m,n=m+2 := ⟨n-2,by omega⟩
  rw [cycleGraph_adj,sub_eq_iff_eq_add,sub_eq_iff_eq_add]
  simp only [Fin.ext_iff,Fin.val_add,Fin.val_one,add_comm 1]
  tauto

lemma cycle_from_period {V : Type*} (G : SimpleGraph V) (m : ℕ) (hm : 2 ≤ m)
    (p : ℕ → V) (stepEdge : ∀ k,G.Adj (p k) (p (k+1))) (last : p m=p 0)
    (distinct : ∀ i j, i < m → j < m → p i=p j → i=j) : cycleGraph m ⊑ G := by
  have along (i j : Fin m) (h : j.val=(i.val+1)%m) : G.Adj (p i.val) (p j.val) := by
    rw [h]
    by_cases hk : i.val+1 < m
    · rw [Nat.mod_eq_of_lt hk]; exact stepEdge _
    · have eq : i.val+1=m := by omega
      rw [eq,Nat.mod_self,←last,←congrArg p eq]; exact stepEdge _
  exact ⟨⟨⟨fun i => p i.val,fun {i j} h =>
    ((adj_mod hm i j).mp h).elim (along i j) (fun k => (along j i k).symm)⟩,
    fun i j h => Fin.ext (distinct i j i.isLt j.isLt h)⟩⟩

namespace ElementaryOrbit
variable {M X : Type*} [Group M] [MulAction M X]

lemma move (h v : M) (x : X) : h • (v • x)=(h*v*h⁻¹) • (h • x) := by
  simp [← mul_smul,mul_assoc]

lemma odd_fold (E : Subgroup M) [E.Normal]
    (comm : ∀ v ∈ E,∀ w ∈ E,Commute v w) (square : ∀ v ∈ E,v*v=1)
    (h : M) (x : X) (stable : ∃ c ∈ E,h • x=c • x) (t : ℕ) :
    ∃ a ∈ E, h • (a • x)=a • ((h^(2*t+1)) • x) := by
  obtain ⟨c,hc,cx⟩ := stable
  have swap (u v : M) (hu : u∈E) (hv : v∈E) (y : X) : u • (v • y)=v • (u • y) := by
    rw [← mul_smul,← mul_smul,(comm u hu v hv).eq]
  induction t with
  | zero => exact ⟨1,E.one_mem,by simp⟩
  | succ t ih =>
    obtain ⟨a,ha,old⟩ := ih
    let k := 2*t+1
    let y := (h^k) • x
    let v := h^k*c*(h^k)⁻¹
    let w := h*v*h⁻¹
    have hv : v∈E := Subgroup.Normal.conj_mem inferInstance c hc _
    have hw : w∈E := Subgroup.Normal.conj_mem inferInstance v hv _
    have hy : h • y=v • y := by
      calc
        _ = h^k • (h • x) := by simp [y,←mul_smul,←pow_succ',←pow_succ]
        _ = h^k • (c • x) := by rw [cx]
        _ = _ := move _ _ _
    have hh : h • (h • y)=w • (v • y) := by
      calc
        _ = h • (v • y) := congrArg (fun s => h • s) hy
        _ = w • (h • y) := move _ _ _
        _ = _ := by rw [hy]
    have cancel : v • (h • (h • y))=w • y := by
      rw [hh,swap v w hv hw,←mul_smul v v,square v hv,one_smul]
    have last : (h^(2*(t+1)+1)) • x=h • (h • y) := by
      have e : 2*(t+1)+1=1+(1+k) := by dsimp [k]; omega
      rw [e,pow_add,pow_add,pow_one,mul_smul,mul_smul]
    refine ⟨a*v,E.mul_mem ha hv,?_⟩
    calc
      _ = h • (v • (a • x)) := by rw [mul_smul,swap a v ha hv]
      _ = w • (h • (a • x)) := move _ _ _
      _ = w • (a • y) := congrArg (fun s => w • s) old
      _ = a • (w • y) := swap w a hw ha _
      _ = _ := by rw [mul_smul a v,last,cancel]

theorem two_period (E : Subgroup M) [E.Normal]
    (comm : ∀ v ∈ E,∀ w ∈ E,Commute v w) (square : ∀ v ∈ E,v*v=1)
    (g : M) (finiteOrder : 0<orderOf g) (x : X) (stable : ∃ v ∈ E,g • x=v • x) :
    ∃ a ∈ E, ∃ s : ℕ,(g^(2^s)) • (a • x)=a • x := by
  obtain ⟨s,m,odd,order⟩ := Nat.exists_eq_two_pow_mul_odd finiteOrder.ne'
  let h := g^(2^s)
  have powers (n : ℕ) : ∃ c ∈ E,(g^n) • x=c • x := by
    induction n with
    | zero => exact ⟨1,E.one_mem,by simp⟩
    | succ n ih =>
      obtain ⟨c,hc,eq⟩ := ih
      obtain ⟨v,hv,gx⟩ := stable
      refine ⟨(g*c*g⁻¹)*v,E.mul_mem (Subgroup.Normal.conj_mem inferInstance c hc _) hv,?_⟩
      rw [pow_succ',mul_smul,eq,move g c,gx]; exact (mul_smul _ _ _).symm
  obtain ⟨t,ht⟩ := odd
  obtain ⟨a,ha,fixed⟩ := odd_fold E comm square h x (powers _) t
  have one : h^(2*t+1)=1 := by
    change (g^(2^s))^(2*t+1)=1
    rw [←pow_mul,←ht,←order,pow_orderOf_eq_one]
  exact ⟨a,ha,s,by simpa only [one,one_smul] using fixed⟩

end ElementaryOrbit

namespace OrbitDescent
variable {M : Type*} [Group M]

theorem find_elementary (K : Subgroup M) [K.Normal] [Finite K] (two : IsPGroup 2 K) (hne : K≠⊥) :
    ∃ E : Subgroup M,E.Normal ∧ E≠⊥ ∧
      (∀ v ∈ E,∀ w ∈ E,Commute v w) ∧ (∀ v ∈ E,v*v=1) := by
  let T : Subgroup K := {
    carrier := {x | x ∈ Subgroup.center K ∧ x^2=1}
    one_mem' := by simp
    mul_mem' := by
      rintro x y ⟨hx,sx⟩ ⟨hy,sy⟩
      have c : Commute x y := (Subgroup.mem_center_iff.mp hy x)
      exact ⟨(Subgroup.center K).mul_mem hx hy,by rw [c.mul_pow,sx,sy,one_mul]⟩
    inv_mem' := by
      rintro x ⟨hx,sx⟩
      exact ⟨(Subgroup.center K).inv_mem hx,by simp [inv_pow,sx]⟩ }
  let E := T.map K.subtype
  have normal : E.Normal := by
    constructor
    rintro _ ⟨x,hx,rfl⟩ g
    let z : K := ⟨g*(x:M)*g⁻¹,Subgroup.Normal.conj_mem inferInstance _ x.2 _⟩
    refine ⟨z,⟨Subgroup.mem_center_iff.mpr ?_,?_⟩,rfl⟩
    · intro t
      let u : K := ⟨g⁻¹*(t:M)*g,by
        simpa using Subgroup.Normal.conj_mem (H := K) inferInstance (t:M) t.2 g⁻¹⟩
      have c := congrArg (fun a : K => g*(a:M)*g⁻¹) (Subgroup.mem_center_iff.mp hx.1 u)
      apply Subtype.ext
      change (t:M)*(g*(x:M)*g⁻¹)=(g*(x:M)*g⁻¹)*(t:M)
      simpa [u,mul_assoc] using c
    · apply Subtype.ext
      have sq := congrArg (fun t : K => (t:M)) hx.2
      change (x:M)^2=1 at sq
      change (g*(x:M)*g⁻¹)^2=1
      simpa [pow_two,mul_assoc] using congrArg (fun t : M => g*t*g⁻¹) sq
  have nontriv : E≠⊥ := by
    let : Nontrivial K := K.nontrivial_iff_ne_bot.mpr hne
    let : Nontrivial (Subgroup.center K) := two.center_nontrivial
    obtain ⟨c,hc⟩ := exists_ne (1 : Subgroup.center K)
    let x : K := c.val
    have ne : x≠1 := fun e => hc (Subtype.ext e)
    obtain ⟨s,hs⟩ := two.exists_orderOf_eq_pow x
    cases s with
    | zero => exact (ne (orderOf_eq_one_iff.mp (by simpa using hs))).elim
    | succ s =>
      let y := x^(2^s)
      have small : 2^s<orderOf x := by rw [hs,pow_succ]; have := Nat.two_pow_pos s; omega
      have ny : y≠1 := pow_ne_one_of_lt_orderOf (by positivity) small
      have sy : y^2=1 := by
        change (x^(2^s))^2=1
        rw [←pow_mul,←pow_succ,←hs,pow_orderOf_eq_one]
      have ymem : y ∈ T := ⟨(Subgroup.center K).pow_mem c.property _,sy⟩
      intro bot
      have mem : (y:M)∈E := ⟨y,ymem,rfl⟩
      rw [bot,Subgroup.mem_bot] at mem
      exact ny (Subtype.ext mem)
  refine ⟨E,normal,nontriv,?_,?_⟩
  · rintro _ ⟨u,hu,rfl⟩ _ ⟨v,_,rfl⟩
    exact (congrArg K.subtype (Subgroup.mem_center_iff.mp hu.1 v)).symm
  · rintro _ ⟨u,hu,rfl⟩
    exact congrArg K.subtype (show u*u=1 by simpa only [pow_two] using hu.2)

set_option maxHeartbeats 2000000 in
theorem normalizedSmaller {X : Type} [Finite X] [Nonempty X] (p q : Equiv.Perm X)
    (sep : ∀ x,p x≠x ∧ q x≠x ∧ p x≠q x)
    (bad : ¬(∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ (SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = p u.2 ∨ v.2 = q u.2)))))
    (K : Subgroup (Subgroup.closure ({p,q}:Set (Equiv.Perm X)))) [K.Normal]
    (two : IsPGroup 2 K) (nontrivial : K≠⊥) :
    ∃ (Y : Type) (_ : Finite Y) (_ : Nonempty Y) (r s : Equiv.Perm Y),
      Nat.card Y < Nat.card X ∧ (∀ y,r y≠y ∧ s y≠y ∧ r y≠s y) ∧
        ¬(∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ (SimpleGraph.fromRel (fun u v : Bool × Y =>
      u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = r u.2 ∨ v.2 = s u.2)))) := by
  classical
  let powerCycle {V : Type} (G : SimpleGraph V) :=
    ∃ t : ℕ, 2 ≤ t ∧ cycleGraph (2^t) ⊑ G
  let actVertex {M : Type} [Group M] {X : Type} [MulAction M X] (side : ℕ → Bool) (pref : ℕ → M) (k : ℕ) (x : X) : Bool × X :=
    (side k,pref k • x)
  have point_lap {M : Type} [Group M] {X Y : Type} [MulAction M X] [MulAction M Y] (G : SimpleGraph (Bool × X)) (π : X → Y) (map : ∀ (g : M) (x : X),π (g • x)=g • π x)
      (n : ℕ) (hn : 2≤n) (side : ℕ → Bool) (pref : ℕ → M) (p0 : pref 0=1)
      (sameSide : side n=side 0) (g : M) (lastPref : pref n=g) (x : X)
      (fixedBase : g • (π x)=π x) (ho : 0<MulAction.period g x)
      (edges : ∀ k,k<n → ∀ y : X,G.Adj (actVertex side pref k y) (actVertex side pref (k+1) y))
      (distinct : ∀ i j,i<n → j<n →
        actVertex side pref i (π x) = actVertex side pref j (π x) → i=j) :
      cycleGraph (n*MulAction.period g x) ⊑ G := by
    have hn' : 0<n := by omega
    let v (k : ℕ) := actVertex side pref (k%n) ((g^(k/n)) • x)
    have gfix (k : ℕ) : (g^k) • (π x)=π x := by
      induction k with
      | zero => simp
      | succ k h => rw [pow_succ,mul_smul,fixedBase,h]
    have projected (k : ℕ) : ((v k).1,π (v k).2)=actVertex side pref (k%n) (π x) := by
      simp [v,actVertex,map,gfix]
    have stepEdge (k : ℕ) : G.Adj (v k) (v (k+1)) := by
      have hrem := Nat.mod_lt k hn'
      have oneM : 1%n=1 := Nat.mod_eq_of_lt (by omega)
      have oneD : 1/n=0 := Nat.div_eq_of_lt (by omega)
      have h := edges (k%n) hrem ((g^(k/n)) • x)
      by_cases hk : k%n+1<n
      · have lt : k%n+1%n<n := by simpa [oneM] using hk
        simpa [v,Nat.add_div_eq_of_add_mod_lt lt,Nat.add_mod_of_add_mod_lt lt,oneD,oneM] using h
      · have eq : k%n+1=n := by omega
        have ge : n ≤ k%n+1%n := by omega
        have md : (k+1)%n=0 := by rw [←Nat.mod_add_mod,eq,Nat.mod_self]
        rw [eq] at h
        simpa [v,actVertex,Nat.add_div_eq_of_le_mod_add_mod ge hn',oneD,md,pow_succ',
          sameSide,p0,lastPref,mul_smul] using h
    have last : v (n*MulAction.period g x)=v 0 := by simp [v,Nat.mul_div_cancel_left _ hn']
    have inject (i j : ℕ) (hi : i<n*MulAction.period g x) (hj : j<n*MulAction.period g x)
        (eq : v i=v j) : i=j := by
      have re := (projected i).symm.trans
        ((congrArg (fun z : Bool × X => (z.1,π z.2)) eq).trans (projected j))
      have rem := distinct _ _ (Nat.mod_lt _ hn') (Nat.mod_lt _ hn') re
      have power := congrArg Prod.snd eq
      change pref (i%n) • ((g^(i/n)) • x)=pref (j%n) • ((g^(j/n)) • x) at power
      rw [rem] at power
      have bound (k : ℕ) (hk : k<n*MulAction.period g x) : k/n<MulAction.period g x :=
        (Nat.div_lt_iff_lt_mul hn').mpr (by simpa [Nat.mul_comm] using hk)
      have quo : i/n=j/n :=
        Function.iterate_injOn_Iio_minimalPeriod (f := fun y : X => g • y) (x := x)
          (bound i hi) (bound j hj) (by
          simpa only [smul_iterate_apply] using (MulAction.injective (pref (j%n))) power)
      have h := Nat.mod_add_div i n
      rw [rem,quo,Nat.mod_add_div] at h
      exact h.symm
    exact cycle_from_period G _ (by nlinarith) v stepEdge last inject
  have word {M : Type} [Group M] {X Y : Type} [MulAction M X] [MulAction M Y] [Finite M] (E : Subgroup M) [E.Normal]
      (comm : ∀ v ∈ E,∀ w ∈ E,Commute v w) (square : ∀ v ∈ E,v*v=1)
      (π : X → Y) (map : ∀ (g : M) (x : X),π (g • x)=g • π x)
      (fibers : ∀ x y,π x=π y ↔ ∃ v ∈ E,x=v • y)
      (G : SimpleGraph (Bool × X)) (n : ℕ) (hn : 2≤n)
      (side : ℕ → Bool) (pref : ℕ → M) (p0 : pref 0=1) (sameSide : side n=side 0)
      (x : X) (base : pref n • (π x)=π x)
      (edges : ∀ k,k<n → ∀ y : X,G.Adj (actVertex side pref k y) (actVertex side pref (k+1) y))
      (distinct : ∀ i j,i<n → j<n →
        actVertex side pref i (π x) = actVertex side pref j (π x) → i=j) :
      ∃ s : ℕ,(s=0 → ∃ y : X,pref n • y=y) ∧ cycleGraph (n*2^s) ⊑ G := by
    let g := pref n
    have stable := (fibers (g • x) x).mp ((map _ _).trans base)
    obtain ⟨a,ha,s,fix⟩ := ElementaryOrbit.two_period E comm square g (orderOf_pos _) x stable
    let y := a • x
    have same : π y=π x := (fibers y x).mpr ⟨a,ha,rfl⟩
    have dvd : MulAction.period g y ∣ 2^s := MulAction.pow_smul_eq_iff_period_dvd.mp fix
    obtain ⟨r,_,er⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp dvd
    have base' : g • π y=π y := by rw [same]; exact base
    have d' : ∀ i j,i<n → j<n → actVertex side pref i (π y)=actVertex side pref j (π y) → i=j :=
      by rw [same]; exact distinct
    have lift := point_lap G π map n hn side pref p0 sameSide g rfl y base'
      (by rw [er]; positivity) edges d'
    refine ⟨r,?_,?_⟩
    · rintro rfl
      have h := MulAction.pow_period_smul g y
      rw [er] at h
      exact ⟨y,by simpa using h⟩
    · rwa [er] at lift
  let letter {M : Type} [Group M] (S : Fin 3 → M) (s : Bool) (i : Fin 3) : M := if s then (S i)⁻¹ else S i
  let step {M : Type} [Group M] {X : Type} [MulAction M X] (S : Fin 3 → M) (v : Bool × X) (i : Fin 3) : Bool × X :=
    (!v.1,letter S v.1 i • v.2)
  let graph {M : Type} [Group M] (X : Type) [MulAction M X] (S : Fin 3 → M) : SimpleGraph (Bool × X) := {
    Adj v w := ∃ i,step S v i=w
    symm.symm := by
      rintro ⟨s,x⟩ _ ⟨i,rfl⟩
      exact ⟨i,by cases s <;> simp [step,letter]⟩
    loopless := ⟨by
      rintro ⟨s,x⟩ ⟨i,eq⟩
      have h := congrArg Prod.fst eq
      cases s <;> simp [step] at h⟩ }
  have quotient_cycle {M : Type} [Group M] {X Y : Type} [MulAction M X] [MulAction M Y] [Finite M] (E : Subgroup M) [E.Normal]
      (comm : ∀ v ∈ E,∀ w ∈ E, Commute v w) (square : ∀ v ∈ E,v*v=1)
      (π : X → Y) (onto : Function.Surjective π) (map : ∀ (g : M) (x : X),π (g • x)=g • π x)
      (fibers : ∀ x y,π x=π y ↔ ∃ v ∈ E,x=v • y) (S : Fin 3 → M)
      (n : ℕ) (hn : 2≤n) (cyc : cycleGraph n ⊑ graph Y S) :
      ∃ s : ℕ,cycleGraph (n*2^s) ⊑ graph X S := by
    classical
    obtain ⟨c⟩ := cyc
    let ix (k : ℕ) : Fin n := ⟨k%n,Nat.mod_lt _ (by omega)⟩
    let v (k : ℕ) := c (ix k)
    let side (k : ℕ) := (v k).1
    have edge (k : ℕ) : (graph Y S).Adj (v k) (v (k+1)) :=
      c.toHom.map_rel ((adj_mod hn _ _).mpr (.inl (Nat.mod_add_mod _ _ _).symm))
    choose label matched using edge
    let pref : ℕ → M := Nat.rec 1 (fun k h => letter S (side k) (label k)*h)
    obtain ⟨x,proj⟩ := onto (v 0).2
    have coords (k : ℕ) : pref k • (π x)=(v k).2 := by
      induction k with
      | zero => simpa [pref] using proj
      | succ k ih =>
        change (letter S (side k) (label k)*pref k) • π x=(v (k+1)).2
        rw [mul_smul,ih]
        exact congrArg Prod.snd (matched k)
    have down (k : ℕ) : actVertex side pref k (π x)=v k := Prod.ext rfl (coords k)
    have last : v n=v 0 := congrArg c (Fin.ext (by simp [ix]))
    have edges (k : ℕ) (_ : k<n) (y : X) : (graph X S).Adj (actVertex side pref k y)
        (actVertex side pref (k+1) y) := by
      refine ⟨label k,Prod.ext ?_ ?_⟩
      · exact congrArg (fun t : Bool × Y => t.1) (matched k)
      · exact (mul_smul _ _ _).symm
    have distinct (i j : ℕ) (hi : i<n) (hj : j<n)
        (eq : actVertex side pref i (π x)=actVertex side pref j (π x)) : i=j := by
      rw [down,down] at eq
      have ij := congrArg Fin.val (c.injective eq)
      simpa [ix,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using ij
    obtain ⟨s,_,up⟩ := word E comm square π map fibers (graph X S) n hn side pref rfl
      (congrArg Prod.fst last) x ((coords n).trans ((congrArg Prod.snd last).trans proj.symm)) edges distinct
    exact ⟨s,up⟩
  have collision {M : Type} [Group M] {X Y : Type} [MulAction M X] [MulAction M Y] [Finite M] (E : Subgroup M) [E.Normal]
      (comm : ∀ v ∈ E,∀ w ∈ E,Commute v w) (square : ∀ v ∈ E,v*v=1)
      (π : X → Y) (onto : Function.Surjective π) (map : ∀ (g : M) (x : X),π (g • x)=g • π x)
      (fibers : ∀ x y,π x=π y ↔ ∃ v ∈ E,x=v • y) (S : Fin 3 → M)
      (sep : ∀ x : X,Function.Injective (fun i => S i • x))
      (i j : Fin 3) (ne : i≠j) (y : Y) (eq : S i • y=S j • y) :
      powerCycle (graph X S) := by
    let g := (S j)⁻¹*S i
    let side (k : ℕ) := decide (k=1)
    let pref (k : ℕ) : M := if k=0 then 1 else if k=1 then S i else g
    obtain ⟨x,hx⟩ := onto y
    have base : pref 2 • (π x)=π x := by simp [pref,g,hx,mul_smul,eq]
    have edges (k : ℕ) (hk : k<2) (z : X) :
        (graph X S).Adj (actVertex side pref k z) (actVertex side pref (k+1) z) := by
      interval_cases k
      · exact ⟨i,by simp [actVertex,step,letter,side,pref]⟩
      · exact ⟨j,by simp [actVertex,step,letter,side,pref,g,mul_smul]⟩
    have distinct (k l : ℕ) (hk : k<2) (hl : l<2)
        (e : actVertex side pref k (π x)=actVertex side pref l (π x)) : k=l := by
      have s := congrArg Prod.fst e
      interval_cases k <;> interval_cases l <;> first | rfl | simp [actVertex,side] at s
    obtain ⟨r,zero,up⟩ := word E comm square π map fibers (graph X S) 2 (by decide)
      side pref (by simp [pref]) (by decide) x base edges distinct
    have pos : r≠0 := by
      intro r0
      obtain ⟨z,e⟩ := zero r0
      change ((S j)⁻¹*S i) • z=z at e
      have eq' : S i • z=S j • z := by simpa [mul_smul] using congrArg (fun u : X => S j • u) e
      exact ne (sep z eq')
    exact ⟨r+1,by omega,by rwa [pow_succ']⟩
  have elementary_transfer {M : Type} [Group M] {X Y : Type} [MulAction M X] [MulAction M Y] [Finite M] (E : Subgroup M) [E.Normal]
      (comm : ∀ v ∈ E,∀ w ∈ E,Commute v w) (square : ∀ v ∈ E,v*v=1)
      (π : X → Y) (onto : Function.Surjective π) (map : ∀ (g : M) (x : X),π (g • x)=g • π x)
      (fibers : ∀ x y,π x=π y ↔ ∃ v ∈ E,x=v • y) (S : Fin 3 → M)
      (sep : ∀ x : X,Function.Injective (fun i => S i • x))
      (down : (∀ y : Y,Function.Injective (fun i => S i • y)) → powerCycle (graph Y S)) :
      powerCycle (graph X S) := by
    classical
    by_cases h : ∀ y : Y,Function.Injective (fun i => S i • y)
    · obtain ⟨t,ht,cyc⟩ := down h
      have hn : 2 ≤ 2^t := by
        have : 2^2 ≤ 2^t := Nat.pow_le_pow_right (by decide) ht
        omega
      obtain ⟨s,up⟩ := quotient_cycle E comm square π onto map fibers S _ hn cyc
      exact ⟨t+s,by omega,by rwa [pow_add]⟩
    · obtain ⟨y,notInj⟩ := not_forall.mp h
      obtain ⟨i,j,eq,ne⟩ := Function.not_injective_iff.mp notInj
      exact collision E comm square π onto map fibers S sep i j ne y eq
  let orbitAction {M : Type} [Group M] (E : Subgroup M) [E.Normal] (X : Type) [MulAction M X] :
      MulAction M (MulAction.orbitRel.Quotient E X) := {
    smul g := Quotient.map (fun x => g • x) (by
      rintro x y ⟨e,he⟩
      refine ⟨⟨g*(e:M)*g⁻¹,Subgroup.Normal.conj_mem inferInstance _ e.2 _⟩,?_⟩
      change (g*(e:M)*g⁻¹) • (g • y)=g • x
      rw [← ElementaryOrbit.move]
      exact congrArg (fun z : X => g • z) he)
    one_smul := by
      intro v
      induction v using Quotient.inductionOn with | h x => exact congrArg (Quotient.mk _) (one_smul M x)
    mul_smul := by
      intro g h v
      induction v using Quotient.inductionOn with | h x => exact congrArg (Quotient.mk _) (mul_smul g h x) }
  let orbitMap {M : Type} [Group M] (E : Subgroup M) (X : Type) [MulAction M X] : X → MulAction.orbitRel.Quotient E X :=
    Quotient.mk _
  have actual_fibers {M : Type} [Group M] {X : Type} [MulAction M X] (E : Subgroup M) (x y : X) :
      orbitMap E X x=orbitMap E X y ↔ ∃ v ∈ E,x=v • y := by
    change Quotient.mk (MulAction.orbitRel E X) x = Quotient.mk _ y ↔ _
    rw [Quotient.eq]
    constructor
    · rintro ⟨v,e⟩; exact ⟨v.val,v.property,e.symm⟩
    · rintro ⟨v,hv,e⟩; exact ⟨⟨v,hv⟩,e.symm⟩
  have descend {M : Type} [Group M] {X : Type} [MulAction M X] [Finite M] [Finite X] [FaithfulSMul M X]
      (E : Subgroup M) [E.Normal] (ne : E≠⊥)
      (comm : ∀ v ∈ E,∀ w ∈ E,Commute v w) (square : ∀ v ∈ E,v*v=1)
      (S : Fin 3 → M) (sep : ∀ x : X,Function.Injective (fun i => S i • x))
      (bad : ¬powerCycle (graph X S)) :
      let Y := MulAction.orbitRel.Quotient E X
      let : MulAction M Y := orbitAction E X
      Nat.card Y < Nat.card X ∧ (∀ y : Y,Function.Injective (fun i => S i • y)) ∧
        ¬powerCycle (graph Y S) := by
    classical
    let Y := MulAction.orbitRel.Quotient E X
    let : MulAction M Y := orbitAction E X
    let π := orbitMap E X
    have onto : Function.Surjective π := Quotient.mk_surjective
    have map (g : M) (x : X) : π (g • x)=g • π x := rfl
    have separate : ∀ y : Y,Function.Injective (fun i => S i • y) := by
      intro y
      by_contra h
      obtain ⟨i,j,eq,ne⟩ := Function.not_injective_iff.mp h
      exact bad (collision E comm square π onto map (actual_fibers E) S sep i j ne y eq)
    have small : Nat.card Y<Nat.card X := by
      let := Fintype.ofFinite X
      let := Fintype.ofFinite Y
      rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
      apply Fintype.card_lt_of_surjective_not_injective π onto
      intro inj
      apply ne
      rw [Subgroup.eq_bot_iff_forall]
      intro e he
      apply eq_of_smul_eq_smul (α := X)
      intro x
      rw [one_smul]
      exact inj ((actual_fibers E _ _).mpr ⟨e,he,rfl⟩)
    exact ⟨small,separate,fun h => bad
      (elementary_transfer E comm square π onto map (actual_fibers E) S sep (fun _ => h))⟩
  have smaller_from_normal_two {M : Type} [Group M] {X : Type} [MulAction M X] [Finite M] [Finite X] [Nonempty X] [FaithfulSMul M X]
      (S : Fin 3 → M) (sep : ∀ x : X,Function.Injective (fun i => S i • x))
      (bad : ¬powerCycle (graph X S)) (K : Subgroup M) [K.Normal]
      (two : IsPGroup 2 K) (nontrivial : K≠⊥) :
      ∃ (Y : Type) (_ : Finite Y) (_ : Nonempty Y) (act : MulAction M Y),
        let := act
        Nat.card Y < Nat.card X ∧ (∀ y : Y,Function.Injective (fun i => S i • y)) ∧
          ¬powerCycle (graph Y S) := by
    obtain ⟨E,_,ne,comm,square⟩ := find_elementary K two nontrivial
    let Y := MulAction.orbitRel.Quotient E X
    exact ⟨Y,inferInstance,Nonempty.map (orbitMap E X) inferInstance,orbitAction E X,
      descend E ne comm square S sep bad⟩
  let normalized {X : Type} (p q : Equiv.Perm X) : SimpleGraph (Bool × X) :=
    SimpleGraph.fromRel (fun u v : Bool × X => u.1=false ∧ v.1=true ∧
        (v.2=u.2 ∨ v.2=p u.2 ∨ v.2=q u.2))
  let three {M : Type} [Group M] (a b : M) : Fin 3 → M := ![1,a,b]
  have action_normalized {M : Type} [Group M] {X : Type} [MulAction M X] (a b : M) : graph X (three a b) =
      normalized (MulAction.toPerm (β := X) a) (MulAction.toPerm (β := X) b) := by
    have forward (x y : X) : (graph X (three a b)).Adj (false,x) (true,y) ↔
        y=x ∨ y=a • x ∨ y=b • x := by
      constructor
      · rintro ⟨i,eq⟩
        have snd := congrArg Prod.snd eq
        fin_cases i
        · exact .inl (by simpa [step,letter,three] using snd.symm)
        · exact .inr (.inl (by simpa [step,letter,three] using snd.symm))
        · exact .inr (.inr (by simpa [step,letter,three] using snd.symm))
      · rintro (rfl|rfl|rfl)
        · exact ⟨0,by simp [step,letter,three]⟩
        · exact ⟨1,by simp [step,letter,three]⟩
        · exact ⟨2,by simp [step,letter,three]⟩
    ext ⟨s,x⟩ ⟨t,y⟩
    cases s <;> cases t
    · simp [graph,step,normalized,SimpleGraph.fromRel]
    · rw [forward]
      simp [normalized,SimpleGraph.fromRel]
    · rw [adj_comm,forward]
      simp [normalized,SimpleGraph.fromRel]
    · simp [graph,step,normalized,SimpleGraph.fromRel]
  have separated_iff {M : Type} [Group M] {X : Type} [MulAction M X] (a b : M) (x : X) : Function.Injective (fun i => three a b i • x) ↔
      a • x≠x ∧ b • x≠x ∧ a • x≠b • x := by
    constructor
    · intro inj
      have ne (i j : Fin 3) (h : i≠j) : three a b i • x≠three a b j • x := fun eq => h (inj eq)
      exact ⟨by simpa [three] using ne 1 0 (by decide),by simpa [three] using ne 2 0 (by decide),
        by simpa [three] using ne 1 2 (by decide)⟩
    · intro sep i j eq
      obtain ⟨ha,hb,hab⟩ := sep
      fin_cases i <;> fin_cases j <;> first | rfl | (
        simp [three] at eq
        first | exact (ha eq).elim | exact (ha eq.symm).elim | exact (hb eq).elim |
          exact (hb eq.symm).elim | exact (hab eq).elim | exact (hab eq.symm).elim)
  let H := Subgroup.closure ({p,q}:Set (Equiv.Perm X))
  let a : H := ⟨p,Subgroup.subset_closure (by simp)⟩
  let b : H := ⟨q,Subgroup.subset_closure (by simp)⟩
  have pa : MulAction.toPerm (β := X) a=p := by ext x; rfl
  have qb : MulAction.toPerm (β := X) b=q := by ext x; rfl
  have ori : graph X (three a b)=normalized p q := by rw [action_normalized,pa,qb]
  have hsep (x : X) : Function.Injective (fun i => three a b i • x) :=
    (separated_iff a b x).mpr (sep x)
  have fail : ¬powerCycle (graph X (three a b)) := ori ▸ bad
  obtain ⟨Y,hfin,hne,act,smaller,hsep',fail'⟩ :=
    smaller_from_normal_two (three a b) hsep fail K two nontrivial
  have eq' := action_normalized (X := Y) a b
  have finalBad : ¬powerCycle (normalized (MulAction.toPerm (β := Y) a) (MulAction.toPerm (β := Y) b)) := by
    rw [←eq']; exact fail'
  exact ⟨Y,hfin,hne,MulAction.toPerm (β := Y) a,MulAction.toPerm (β := Y) b,smaller,
    fun y => (separated_iff a b y).mp (hsep' y),finalBad⟩

end OrbitDescent

theorem allSizes (oddCase : H1) (evenCase : H2) (n : ℕ) :
    ∀ (X : Type) [Fintype X] [Nonempty X] (p q : Equiv.Perm X),
      Fintype.card X = n → (∀ x, p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x) →
      ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × X =>
        u.1 = false ∧ v.1 = true ∧ (v.2=u.2 ∨ v.2=p u.2 ∨ v.2=q u.2)) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X _ _ p q size sep
    let G := SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1 = false ∧ v.1 = true ∧ (v.2=u.2 ∨ v.2=p u.2 ∨ v.2=q u.2))
    change ∃ k : ℕ,2 ≤ k ∧ cycleGraph (2^k) ⊑ G
    by_contra bad
    have noShort : ¬(cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
      rintro (h|h|h)
      · exact bad ⟨2,by decide,h⟩
      · exact bad ⟨3,by decide,h⟩
      · exact bad ⟨4,by decide,h⟩
    have den := OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.LocalCommutation.defectDensity G p q sep
      (fun z => ⟨by simp,Or.inl ⟨rfl,rfl,Or.inl rfl⟩⟩)
      (fun z => ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inl rfl)⟩⟩)
      (fun z => ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inr rfl)⟩⟩) noShort
    have count : (Finset.univ.filter (fun x => p (q x)≠q (p x))).card =
        {x : X | p (q x)≠q (p x)}.ncard := by rw [← Set.ncard_coe_finset]; congr 1; ext; simp
    let M := Subgroup.closure ({p,q}:Set (Equiv.Perm X))
    by_cases odd : Odd (Nat.card M)
    · exact bad (oddCase X p q sep (count ▸ den) odd)
    have even : Even (Nat.card M) := Nat.not_odd_iff_even.mp odd
    by_cases trivial : ∀ K : Subgroup M, K.Normal → IsPGroup 2 K → K=⊥
    · exact bad (evenCase X p q sep (count ▸ den) even trivial)
    push Not at trivial
    obtain ⟨K,normal,two,nontrivial⟩ := trivial
    obtain ⟨Y,fin,inh,r,s,less,sep',fail⟩ := OrbitDescent.normalizedSmaller p q sep bad K two nontrivial
    let := Fintype.ofFinite Y
    have small : Fintype.card Y < n := by simpa [Nat.card_eq_fintype_card,size] using less
    exact fail (ih _ small Y r s rfl sep')

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.H2 := by
  intro oddCase evenCase X _ _ p q sep _
  exact allSizes oddCase evenCase _ X p q rfl sep


end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2
