import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1
import Mathlib

/-!
# Power-of-two cycles for three regular matchings

For the regular matching graph with shifts 1, a and b, it suffices to work on the
subgroup they generate. A nontrivial normal 2-subgroup gives a strict descent in
group order. A quotient cycle of length n lifts to length n times the order of
its return element. Two coincident quotient shifts give an alternating cycle.
Burkhart (arXiv:2611.05060, Lemma 1.3) proves the corresponding result for
ordinary Cayley graphs. Here the two sides are distinct copies of the group.

Once the normal 2-core is trivial, suppose the fourth lower central subgroup is
a 2-group. It must then be trivial. Write ab=bac, ca=acd, cb=bce. Both d and e
are central. If both have square one they are trivial too, giving the class-two
case of the parent. Otherwise the word 01021021201201012012102121021012,
with the shifts swapped if necessary, gives a simple 32-cycle. Prefix coordinates
are checked explicitly. In the quotient by the center a same-side collision
forces a small power of c to be central. The same power of e is then one.

The normalized matching presentation comes from PR 5246 and @JamesSlash's PR 592.
We use the class-two permutation theorem and the regular branch of PR 5820. Both
remaining cases require that the fourth lower central subgroup is not a 2-group.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1
open SimpleGraph
open scoped commutatorElement

/-- Odd group order after restricting to the two generators. -/
def H1 : Prop :=
  ∀ (A : Type) [Group A] [Fintype A] (a b : A),
    Subgroup.closure ({a,b}:Set A)=⊤ →
    a≠1 → b≠1 → a≠b → ¬(Commute a ⁅a,b⁆ ∧ Commute b ⁅a,b⁆) →
    ¬ IsPGroup 2 ((⊤ : Subgroup A).lowerCentralSeries 3) →
    Odd (Nat.card A) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))

/-- Even group order and no nontrivial normal 2-subgroup. -/
def H2 : Prop :=
  ∀ (A : Type) [Group A] [Fintype A] (a b : A),
    Subgroup.closure ({a,b}:Set A)=⊤ →
    a≠1 → b≠1 → a≠b → ¬(Commute a ⁅a,b⁆ ∧ Commute b ⁅a,b⁆) →
    ¬ IsPGroup 2 ((⊤ : Subgroup A).lowerCentralSeries 3) →
    Even (Nat.card A) → (∀ N : Subgroup A,N.Normal → IsPGroup 2 N → N=⊥) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))

namespace HaarWeightThree
open SimpleGraph
variable {A : Type*} [Group A]

lemma twice_tri (n : ℤ) : 2*(n*(n-1)/2)=n*(n-1) := by
  have dv : 2 ∣ n*(n-1) := by
    rcases Int.even_or_odd n with ⟨a,ha⟩ | ⟨a,ha⟩
    · exact ⟨a*(n-1),by rw [ha]; ring⟩
    · exact ⟨n*a,by rw [ha]; ring⟩
  exact Int.mul_ediv_cancel' dv

lemma collect_class_two (a b c : A) (ab : a*b = b*a*c) (ac : Commute a c) (bc : Commute b c)
    (x y : ℤ) : a^x*b^y = b^y*a^x*c^(x*y) := by
  have hr : SemiconjBy b (a*c) a := by simpa only [SemiconjBy,mul_assoc] using ab.symm
  have hh := (hr.zpow_right x).eq.symm
  rw [ac.mul_zpow] at hh
  have hx : SemiconjBy (a^x) b (b*c^x) := by
    change a^x*b = b*c^x*a^x
    rw [hh,mul_assoc,(ac.zpow_zpow x x).symm.eq]
  have hy := (hx.zpow_right y).eq
  rw [(bc.zpow_right x).mul_zpow, ← zpow_mul] at hy
  calc
    a^x*b^y = b^y*c^(x*y)*a^x := hy
    _ = b^y*a^x*c^(x*y) := by rw [mul_assoc,(ac.zpow_zpow x (x*y)).symm.eq,mul_assoc]

lemma collect_a_power_b (a b c d : A) (ab : a*b=b*a*c) (ca : c*a=a*c*d)
    (dc : ∀ t : A, Commute d t) (n : ℤ) :
    a^n*b = b*a^n*c^n*d^(n*(n-1)/2) := by
  let tri (n : ℤ) := n*(n-1)/2
  change a^n*b=b*a^n*c^n*d^tri n
  have tri_zero : tri 0=0 := rfl
  have tri_succ (i : ℤ) : tri (i+1)=tri i+i := by
    dsimp [tri]
    nlinarith only [twice_tri i,twice_tri (i+1)]
  have shift (i : ℤ) : c^i*a=a*c^i*d^i := by
    simpa using collect_class_two c a d ca (dc c).symm (dc a).symm i 1
  have step (i : ℤ) :
      a^(i+1)*b = b*a^(i+1)*c^(i+1)*d^tri (i+1) ↔
      a^i*b = b*a^i*c^i*d^tri i := by
    have left : a^(i+1)*b=(a^i*b)*(a*c) := by
      rw [zpow_add_one,mul_assoc,ab]
      simp only [mul_assoc]
    have right : b*a^(i+1)*c^(i+1)*d^tri (i+1) = (b*a^i*c^i*d^tri i)*(a*c) := by
      have c1 := ((dc (a*c)).zpow_left (tri i)).eq
      have c2 := ((dc c).zpow_left i).eq
      symm
      calc
        _ = (b*a^i)*(c^i*a)*c*d^tri i := by
          simpa only [mul_assoc] using congrArg (fun t => b*a^i*c^i*t) c1
        _ = (b*a^i)*(a*c^i*d^i)*c*d^tri i := by rw [shift i]
        _ = b*a^(i+1)*c^(i+1)*d^tri (i+1) := by
          rw [zpow_add_one,zpow_add_one,tri_succ,add_comm (tri i),zpow_add]
          simpa only [mul_assoc] using congrArg (fun t => b*a^i*a*c^i*t*d^tri i) c2
    rw [left,right,mul_left_inj]
  induction n using Int.induction_on with
  | zero => simp [tri_zero]
  | succ k ih => exact (step _).mpr ih
  | pred k ih =>
    apply (step _).mp
    simpa using ih

lemma central_slide (d : A) (hd : ∀ x, Commute d x) (k : ℤ) (s t : A) :
    d^k*(s*t)=s*(d^k*t) := by rw [←mul_assoc,((hd s).zpow_left k).eq,mul_assoc]

/- The 32-letter cycle and its same-side collision test, evaluated in actual group elements. -/
set_option maxRecDepth 4500 in
set_option maxHeartbeats 3200000 in
theorem direct_vertical (a b c d e : A)
    (ab : a*b=b*a*c) (ca : c*a=a*c*d) (cb : c*b=b*c*e)
    (hd : ∀ t : A,Commute d t) (he : ∀ t : A,Commute e t) (order : e^2≠1)
    (G : SimpleGraph (Bool × A)) (h0 : ∀ x,G.Adj (false,x) (true,x))
    (ha : ∀ x,G.Adj (false,x) (true,x*a)) (hb : ∀ x,G.Adj (false,x) (true,x*b)) :
    cycleGraph 32 ⊑ G := by
  let T := ℤ × ℤ × ℤ × ℤ × ℤ
  let tri (n : ℤ) := n*(n-1)/2
  let val (g : T) := b^g.2.1*a^g.1*c^g.2.2.1*(d^g.2.2.2.1*e^g.2.2.2.2)
  let nextA (g : T) : T := (g.1+1,g.2.1,g.2.2.1,g.2.2.2.1+g.2.2.1,g.2.2.2.2)
  let nextB (g : T) : T := (g.1,g.2.1+1,g.2.2.1+g.1,g.2.2.2.1+tri g.1,g.2.2.2.2+g.2.2.1)
  have steps (g : T) : val (nextA g)=val g*a ∧ val (nextB g)=val g*b := by
    obtain ⟨x,y,z,u,v⟩ := g
    let tail := d^u*e^v
    have tc (t : A) : Commute tail t := ((hd t).zpow_left u).mul_left ((he t).zpow_left v)
    have shiftA : c^z*a=a*c^z*d^z := by
      simpa using collect_class_two c a d ca (hd c).symm (hd a).symm z 1
    have shiftB : c^z*b=b*c^z*e^z := by
      simpa using collect_class_two c b e cb (he c).symm (he b).symm z 1
    have right (t : A) : val (x,y,z,u,v)*t=b^y*a^x*(c^z*t)*tail := by
      simpa only [val,tail,mul_assoc] using congrArg (fun w => b^y*a^x*c^z*w) (tc t).eq
    constructor
    · rw [right,shiftA]
      simp [val,nextA,tail,zpow_add,mul_assoc]
      rw [(Commute.zpow_zpow_self d z u).left_comm]
    · rw [right,shiftB]
      have hb' := collect_a_power_b a b c d ab ca hd x
      have exp : b^y*a^x*(b*c^z*e^z)*tail=b^y*(b*a^x*c^x*d^tri x)*c^z*e^z*tail := by
        rw [show b*a^x*c^x*d^tri x=a^x*b from hb'.symm]; simp only [mul_assoc]
      rw [exp]
      have zz : z+x=x+z := add_comm _ _
      have uu : u+tri x=tri x+u := add_comm _ _
      have vv : v+z=z+v := add_comm _ _
      simp [val,nextB,zz,uu,vv,tail,zpow_add,mul_assoc]
      rw [central_slide d hd (tri x) (c^z),central_slide e he z (d^u)]
  let f := QuotientGroup.mk' (Subgroup.center A)
  have kill (t : A) (cen : ∀ g : A,Commute t g) : f t=1 :=
    (QuotientGroup.eq_one_iff t).mpr (Subgroup.mem_center_iff.mpr (fun g => (cen g).eq.symm))
  have fd := kill d hd
  have fe := kill e he
  have ac : Commute (f a) (f c) := by
    change f a*f c=f c*f a
    simpa [fd] using congrArg f ca.symm
  have bc : Commute (f b) (f c) := by
    change f b*f c=f c*f b
    simpa [fe] using congrArg f cb.symm
  have ab' : f a*f b=f b*f a*f c := by simpa using congrArg f ab
  have ba' : f b*f a=f a*f b*(f c)⁻¹ := by rw [ab']; group
  let QV (g : T) := (f b)^g.2.1*(f a)^g.1*(f c)^g.2.2.1
  have mapped (g : T) : f (val g)=QV g := by simp [QV,val,fd,fe]
  have moveB (g : T) : QV g*f b=f b*QV g*(f c)^g.1 := by
    obtain ⟨x,y,z,u,v⟩ := g
    change (f b)^y*(f a)^x*(f c)^z*f b=f b*((f b)^y*(f a)^x*(f c)^z)*(f c)^x
    have hx : (f a)^x*f b=f b*(f a)^x*(f c)^x := by
      simpa using collect_class_two (f a) (f b) (f c) ab' ac bc x 1
    calc
      _ = (f b)^y*((f a)^x*f b)*(f c)^z := by
        simp only [mul_assoc,(bc.symm.zpow_left z).eq]
      _ = _ := by
        rw [hx]
        simp only [←mul_assoc]
        rw [(Commute.zpow_self (f b) y).eq]
        simp only [mul_assoc]
        rw [(Commute.zpow_zpow_self (f c) x z).eq]
  have moveA (g : T) : QV g*f a=f a*QV g*(f c)^(-g.2.1) := by
    obtain ⟨x,y,z,u,v⟩ := g
    change (f b)^y*(f a)^x*(f c)^z*f a=f a*((f b)^y*(f a)^x*(f c)^z)*(f c)^(-y)
    have hy : (f b)^y*f a=f a*(f b)^y*(f c)^(-y) := by
      simpa [inv_zpow,zpow_neg] using collect_class_two (f b) (f a) (f c)⁻¹ ba' bc.inv_right ac.inv_right y 1
    calc
      _ = ((f b)^y*f a)*(f a)^x*(f c)^z := by
        simp only [mul_assoc,(ac.symm.zpow_left z).eq,(Commute.zpow_self (f a) x).left_comm]
      _ = _ := by
        rw [hy]
        simp only [mul_assoc]
        rw [((ac.symm.zpow_zpow (-y) x).mul_right (Commute.zpow_zpow_self (f c) (-y) z)).eq]
        simp only [mul_assoc]
  have detect (r s : ℤ) (h : (f c)^r=(f c)^s) : e^(s-r)=1 := by
    have central : c^(s-r) ∈ Subgroup.center A := (QuotientGroup.eq_one_iff _).mp (by
      change f (c^(s-r))=1
      simp [zpow_sub,h])
    have rel : c^(s-r)*b=b*c^(s-r)*e^(s-r) := by
      simpa using collect_class_two c b e cb (he c).symm (he b).symm (s-r) 1
    rw [←Subgroup.mem_center_iff.mp central b] at rel
    exact (mul_eq_left.mp rel.symm)
  let small (t : ℤ) := t==1 || t==(-1) || t==2 || t==(-2)
  have impossible (t : ℤ) (s : small t) (h : e^t=1) : False := by
    apply order
    simp only [small,Bool.or_eq_true,beq_iff_eq] at s
    rcases s with ((rfl|rfl)|rfl)|rfl
    · have h1 : e=1 := by simpa using h
      simp [h1]
    · have h1 : e=1 := by simpa using h
      simp [h1]
    · simpa using h
    · simpa using h
  let separates (g h : T) :=
    small (h.1-g.1) || small (h.2.1-g.2.1) ||
    (g.1==h.1 && g.2.1==h.2.1 && (small (h.2.2.1-g.2.2.1) ||
     (g.2.2.1==h.2.2.1 && g.2.2.2.1==h.2.2.2.1 && small (h.2.2.2.2-g.2.2.2.2))))
  have distinct (g h : T) (s : separates g h) (eq : val g=val h) : False := by
    have mappedEq : QV g=QV h := (mapped g).symm.trans ((congrArg f eq).trans (mapped h))
    simp only [separates,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at s
    rcases s with (sx|sy)|⟨⟨xe,ye⟩,sz|⟨⟨ze,ue⟩,sv⟩⟩
    · have eq' := moveB g
      rw [mappedEq,moveB h] at eq'
      exact impossible _ sx (detect _ _ (mul_left_cancel eq'.symm))
    · have eq' := moveA g
      rw [mappedEq,moveA h] at eq'
      have neg := congrArg Inv.inv (mul_left_cancel eq'.symm)
      exact impossible _ sy (detect _ _ (by simpa [zpow_neg] using neg))
    · simp only [QV,xe,ye,mul_right_inj] at mappedEq
      exact impossible _ sz (detect _ _ mappedEq)
    · simp only [val,xe,ye,ze,ue,mul_right_inj] at eq
      exact impossible _ sv (by simp [zpow_sub,eq])
  let forward (g h : T) := g==h || nextA g==h || nextB g==h
  let edge (g h : Bool × T) := if g.1 then !h.1 && forward h.2 g.2 else h.1 && forward g.2 h.2
  have fs (g h : T) (yes : forward g h) : G.Adj (false,val g) (true,val h) := by
    simp only [forward,Bool.or_eq_true,beq_iff_eq] at yes
    rcases yes with (eq|eq)|eq
    · rw [←eq]; exact h0 _
    · rw [←eq,(steps g).1]; exact ha _
    · rw [←eq,(steps g).2]; exact hb _
  let p : Fin 32 → Bool × T := ![(false,⟨0,0,0,0,0⟩),(true,⟨0,0,0,0,0⟩),(false,⟨-1,0,0,0,0⟩),(true,⟨-1,0,0,0,0⟩),(false,⟨-1,-1,1,-1,-1⟩),(true,⟨0,-1,1,0,-1⟩),(false,⟨0,-1,1,0,-1⟩),(true,⟨0,0,1,0,0⟩),(false,⟨-1,0,1,-1,0⟩),(true,⟨-1,1,0,0,1⟩),(false,⟨-1,1,0,0,1⟩),(true,⟨0,1,0,0,1⟩),(false,⟨0,0,0,0,1⟩),(true,⟨0,0,0,0,1⟩),(false,⟨-1,0,0,0,1⟩),(true,⟨-1,0,0,0,1⟩),(false,⟨-2,0,0,0,1⟩),(true,⟨-2,1,-2,3,1⟩),(false,⟨-2,1,-2,3,1⟩),(true,⟨-1,1,-2,1,1⟩),(false,⟨-1,0,-1,0,2⟩),(true,⟨0,0,-1,-1,2⟩),(false,⟨0,0,-1,-1,2⟩),(true,⟨0,1,-1,-1,1⟩),(false,⟨-1,1,-1,0,1⟩),(true,⟨-1,2,-2,1,0⟩),(false,⟨-2,2,-2,3,0⟩),(true,⟨-2,2,-2,3,0⟩),(false,⟨-2,1,0,0,0⟩),(true,⟨-1,1,0,0,0⟩),(false,⟨-1,1,0,0,0⟩),(true,⟨0,1,0,0,0⟩)]
  have verified : (∀ i j,(cycleGraph 32).Adj i j → edge (p i) (p j)) ∧
      (∀ i j,i<j → (p i).1=(p j).1 → separates (p i).2 (p j).2) := by
    dsimp only [p,edge,forward,nextA,nextB,tri,separates,small,T]
    decide
  let h : cycleGraph 32 →g G := ⟨fun i => ((p i).1,val (p i).2),by
    intro i j hij
    have e := verified.1 i j hij
    cases hi : (p i).1 <;> cases hj : (p j).1 <;> simp [edge,hi,hj] at e ⊢
    · exact fs _ _ e
    · exact (fs _ _ e).symm⟩
  refine ⟨h.toCopy ?_⟩
  intro i j eq
  by_contra ne
  have no (i j : Fin 32) (lt : i<j) (eq : h i=h j) : False := by
    have side := congrArg (fun z : Bool × A => z.1) eq
    have valEq := congrArg (fun z : Bool × A => z.2) eq
    exact distinct _ _ (verified.2 i j lt side) valEq
  exact (lt_or_gt_of_ne ne).elim (fun t => no i j t eq) (fun t => no j i t eq.symm)

theorem noninvolutory_cycle (a b c d e : A)
    (ab : a*b=b*a*c) (ca : c*a=a*c*d) (cb : c*b=b*c*e)
    (hd : ∀ t : A, Commute d t) (he : ∀ t : A, Commute e t) (order : d^2≠1 ∨ e^2≠1)
    (G : SimpleGraph (Bool × A)) (h0 : ∀ x,G.Adj (false,x) (true,x))
    (ha : ∀ x,G.Adj (false,x) (true,x*a)) (hb : ∀ x,G.Adj (false,x) (true,x*b)) :
    cycleGraph 32 ⊑ G := by
  rcases order with h|h
  · have ab' : b*a=a*b*c⁻¹ := by rw [ab]; group
    have ca' : c⁻¹*b=b*c⁻¹*e⁻¹ := by
      simpa using collect_class_two c b e cb (he c).symm (he b).symm (-1) 1
    have cb' : c⁻¹*a=a*c⁻¹*d⁻¹ := by
      simpa using collect_class_two c a d ca (hd c).symm (hd a).symm (-1) 1
    apply direct_vertical b a c⁻¹ e⁻¹ d⁻¹ ab' ca' cb' (fun t => (he t).inv_left)
      (fun t => (hd t).inv_left) _ G h0 hb ha
    intro eq
    apply h
    simpa using congrArg Inv.inv eq
  · exact direct_vertical a b c d e ab ca cb hd he h G h0 ha hb

end HaarWeightThree

namespace HaarTwoQuotient
open SimpleGraph

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

/- A regular counterexample descends through every nontrivial normal 2-subgroup.
Coincident quotient shifts would already give an alternating power-of-two cycle. -/
set_option maxHeartbeats 2200000 in
theorem quotient_failure {A : Type} [Group A] [Finite A] (N : Subgroup A) [N.Normal]
    (proper : N≠⊥) (two : IsPGroup 2 N) (a b : A) (sep : a≠1 ∧ b≠1 ∧ a≠b)
    (bad : ¬(∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ (SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))))) :
    let f := QuotientGroup.mk' N
    Nat.card (A ⧸ N)<Nat.card A ∧ (f a≠1 ∧ f b≠1 ∧ f a≠f b) ∧ ¬(∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ (SimpleGraph.fromRel (fun u v : Bool × (A ⧸ N) =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=f a*u.2 ∨ v.2=f b*u.2)))) := by
  classical
  let powerCycle {V : Type} (G : SimpleGraph V) :=
    ∃ t : ℕ, 2 ≤ t ∧ cycleGraph (2^t) ⊑ G
  let step {A : Type} [Group A] (S : Fin 3 → A) (v : Bool × A) (i : Fin 3) : Bool × A :=
    (!v.1,(if v.1 then (S i)⁻¹ else S i)*v.2)
  have reverse {A : Type} [Group A] (S : Fin 3 → A) (v : Bool × A) (i : Fin 3) : step S (step S v i) i=v := by
    rcases v with ⟨s,g⟩
    cases s <;> simp [step]
  let graph {A : Type} [Group A] (S : Fin 3 → A) : SimpleGraph (Bool × A) := {
    Adj v w := ∃ i,step S v i=w
    symm.symm := by rintro v w ⟨i,rfl⟩; exact ⟨i,reverse ..⟩
    loopless := ⟨by
      rintro ⟨s,g⟩ ⟨i,eq⟩
      have h := congrArg Prod.fst eq
      cases s <;> simp [step] at h⟩ }
  have namedEdge {A : Type} [Group A] (S : Fin 3 → A) (i : Fin 3) (g : A) :
      (graph S).Adj (false,g) (true,S i*g) := ⟨i,rfl⟩
  let deck {A : Type} [Group A] (a : A) (v : Bool × A) : Bool × A := (v.1,v.2*a)
  have deck_edges {A : Type} [Group A] (S : Fin 3 → A) (a : A) (v w : Bool × A)
      (h : (graph S).Adj v w) : (graph S).Adj (deck a v) (deck a w) := by
    rcases h with ⟨i,rfl⟩
    rcases v with ⟨s,g⟩
    exact ⟨i,by cases s <;> simp [deck,step,mul_assoc]⟩
  let project {A : Type} [Group A] {Q : Type} [Group Q] (f : A →* Q) (v : Bool × A) : Bool × Q := (v.1,f v.2)
  have repeat_lap {A : Type} [Group A] {Q : Type} [Group Q] (S : Fin 3 → A) (f : A →* Q) (n : ℕ) (hn : 2≤n)
      (p : ℕ → Bool × A) (z : A) (ker : f z=1) (finiteOrder : 0<orderOf z)
      (edges : ∀ k, k<n → (graph S).Adj (p k) (p (k+1))) (close : p n=deck z (p 0))
      (distinct : ∀ i j, i<n → j<n → project f (p i)=project f (p j) → i=j) :
      cycleGraph (n*orderOf z) ⊑ graph S := by
    have hn' : 0<n := by omega
    let v (k : ℕ) := deck (z^(k/n)) (p (k%n))
    have proj (k : ℕ) : project f (v k) = project f (p (k%n)) := by
      simp [v,project,deck,ker]
    have stepEdge (k : ℕ) : (graph S).Adj (v k) (v (k+1)) := by
      have hrem := Nat.mod_lt k hn'
      have oneM : 1%n = 1 := Nat.mod_eq_of_lt (by omega)
      have oneD : 1/n = 0 := Nat.div_eq_of_lt (by omega)
      have h := deck_edges S (z^(k/n)) _ _ (edges (k%n) hrem)
      by_cases hk : k%n+1<n
      · have lt : k%n+1%n<n := by simpa [oneM] using hk
        simpa [v,Nat.add_div_eq_of_add_mod_lt lt,Nat.add_mod_of_add_mod_lt lt,oneD,oneM] using h
      · have eq : k%n+1=n := by omega
        have ge : n ≤ k%n+1%n := by omega
        have md : (k+1)%n=0 := by rw [←Nat.mod_add_mod,eq,Nat.mod_self]
        rw [eq,close] at h
        simpa [v,Nat.add_div_eq_of_le_mod_add_mod ge hn',oneD,md,pow_succ',deck,mul_assoc] using h
    have last : v (n*orderOf z)=v 0 := by simp [v,Nat.mul_div_cancel_left _ hn',deck,pow_orderOf_eq_one]
    have inject (i j : ℕ) (hi : i<n*orderOf z) (hj : j<n*orderOf z) (eq : v i=v j) : i=j := by
      have re := (proj i).symm.trans ((congrArg (project f) eq).trans (proj j))
      have rem := distinct _ _ (Nat.mod_lt _ hn') (Nat.mod_lt _ hn') re
      have power := congrArg Prod.snd eq
      change (p (i%n)).2*z^(i/n)=(p (j%n)).2*z^(j/n) at power
      rw [rem] at power
      have bound (k : ℕ) (hk : k<n*orderOf z) : k/n<orderOf z :=
        (Nat.div_lt_iff_lt_mul hn').mpr (by simpa [Nat.mul_comm] using hk)
      have quo : i/n=j/n := pow_injOn_Iio_orderOf (bound i hi) (bound j hj) (mul_left_cancel power)
      have h := Nat.mod_add_div i n
      rw [rem,quo,Nat.mod_add_div] at h
      exact h.symm
    exact cycle_from_period (graph S) _ (by nlinarith) v stepEdge last inject
  have monodromy {A : Type} [Group A] {Q : Type} [Group Q] (S : Fin 3 → A) (f : A →* Q) (surj : Function.Surjective f)
      (n : ℕ) (hn : 2≤n) (cyc : cycleGraph n ⊑ graph (fun i => f (S i))) :
      ∃ z : A, f z=1 ∧ (0<orderOf z → cycleGraph (n*orderOf z) ⊑ graph S) := by
    classical
    obtain ⟨c⟩ := cyc
    let ix (k : ℕ) : Fin n := ⟨k%n,Nat.mod_lt _ (by omega)⟩
    have e (k : ℕ) : (graph (fun i => f (S i))).Adj (c (ix k)) (c (ix (k+1))) := by
      apply c.toHom.map_rel
      apply (adj_mod hn _ _).mpr
      exact .inl (Nat.mod_add_mod _ _ _).symm
    have stepMap (v : Bool × A) (i : Fin 3) :
        project f (step S v i)=step (fun j => f (S j)) (project f v) i := by
      rcases v with ⟨s,g⟩
      cases s <;> simp [project,step]
    let F (k : ℕ) := {v : Bool × A // project f v=c (ix k)}
    have next (k : ℕ) (v : F k) : ∃ w,(graph S).Adj v.val w ∧ project f w=c (ix (k+1)) := by
      obtain ⟨i,hi⟩ := e k
      exact ⟨step S v.val i,⟨i,rfl⟩,(stepMap _ _).trans (by rw [v.property]; exact hi)⟩
    let start : F 0 := ⟨((c (ix 0)).1,(surj (c (ix 0)).2).choose),
      Prod.ext rfl (surj (c (ix 0)).2).choose_spec⟩
    let q : ∀ k,F k := Nat.rec start (fun k v => ⟨(next k v).choose,(next k v).choose_spec.2⟩)
    let p (k : ℕ) := (q k).val
    have ep (k : ℕ) : (graph S).Adj (p k) (p (k+1)) := (next k (q k)).choose_spec.1
    have pi (k : ℕ) : project f (p k)=c (ix k) := (q k).property
    have base : ix n=ix 0 := Fin.ext (by simp [ix])
    have eq : project f (p n)=project f (p 0) := (pi n).trans ((congrArg c base).trans (pi 0).symm)
    let z := (p 0).2⁻¹*(p n).2
    have ker : f z=1 := by
      have e := congrArg Prod.snd eq
      change f (p n).2=f (p 0).2 at e
      simp [z,e]
    refine ⟨z,ker,fun ho => repeat_lap S f n hn p z ker ho (fun k _ => ep k) ?_ ?_⟩
    · exact Prod.ext (congrArg (fun t : Bool × Q => t.1) eq) (by simp [deck,z])
    · intro i j hi hj piEq
      have equal : ix i=ix j := c.injective ((pi i).symm.trans (piEq.trans (pi j)))
      simpa [ix,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using congrArg Fin.val equal
  have alternating {A : Type} [Group A] {Q : Type} [Group Q] (S : Fin 3 → A) (f : A →* Q) (i j : Fin 3)
      (eq : f (S i)=f (S j)) (finiteOrder : 0<orderOf ((S j)⁻¹*S i)) :
      cycleGraph (2*orderOf ((S j)⁻¹*S i)) ⊑ graph S := by
    let z := (S j)⁻¹*S i
    let p (k : ℕ) : Bool × A := if k=0 then (false,1) else if k=1 then (true,S i) else (false,z)
    have ker : f z=1 := by simp [z,eq]
    apply repeat_lap S f 2 (by decide) p z ker finiteOrder
    · intro k hk
      interval_cases k
      · simpa [p] using namedEdge S i 1
      · simpa [p,z] using (namedEdge S j z).symm
    · simp [p,deck]
    · intro k l hk hl h
      have s := congrArg Prod.fst h
      interval_cases k <;> interval_cases l <;> first | rfl | simp [p,project] at s
  let shifts {A : Type} [Group A] (a b : A) : Fin 3 → A := ![1,a,b]
  have shapes {A : Type} [Group A] (a b : A) : graph (shifts a b) =
      SimpleGraph.fromRel (fun u v : Bool × A => u.1=false ∧ v.1=true ∧
        (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2)) := by
    have forward (x y : A) : (graph (shifts a b)).Adj (false,x) (true,y) ↔
        y=x ∨ y=a*x ∨ y=b*x := by
      constructor
      · rintro ⟨i,eq⟩
        have h := congrArg Prod.snd eq
        fin_cases i
        · exact .inl (by simpa [step,shifts] using h.symm)
        · exact .inr (.inl (by simpa [step,shifts] using h.symm))
        · exact .inr (.inr (by simpa [step,shifts] using h.symm))
      · rintro (rfl|rfl|rfl)
        · exact ⟨0,by simp [step,shifts]⟩
        · exact ⟨1,by simp [step,shifts]⟩
        · exact ⟨2,by simp [step,shifts]⟩
    ext ⟨s,x⟩ ⟨t,y⟩
    cases s <;> cases t
    · simp [graph,step,SimpleGraph.fromRel]
    · rw [forward]; simp [SimpleGraph.fromRel]
    · rw [adj_comm,forward]; simp [SimpleGraph.fromRel]
    · simp [graph,step,SimpleGraph.fromRel]
  let f := QuotientGroup.mk' N
  let S := shifts a b
  have fail : ¬powerCycle (graph S) := by change ¬powerCycle (graph (shifts a b)); rw [shapes]; exact bad
  have orders (z : A) (hz : f z=1) : ∃ k : ℕ,orderOf z=2^k := by
    have h := (QuotientGroup.eq_one_iff _).mp hz
    obtain ⟨k,e⟩ := two.exists_orderOf_eq_pow (⟨z,h⟩ : N)
    exact ⟨k,(Subgroup.orderOf_mk (H:=N) z h).symm.trans e⟩
  have inj : Function.Injective S := by
    intro i j eq
    obtain ⟨ha,hb,hab⟩ := sep
    fin_cases i <;> fin_cases j <;> first | rfl | (
      simp [S,shifts] at eq
      first | exact (ha eq).elim | exact (ha eq.symm).elim | exact (hb eq).elim |
        exact (hb eq.symm).elim | exact (hab eq).elim | exact (hab eq.symm).elim)
  have distinctQ : Function.Injective (fun i => f (S i)) := by
    by_contra no
    obtain ⟨i,j,eq,ne⟩ := Function.not_injective_iff.mp no
    let z := (S j)⁻¹*S i
    have ker : f z=1 := by simp [z,eq]
    obtain ⟨s,ord⟩ := orders z ker
    have nz : z≠1 := fun h => ne (inj (inv_mul_eq_one.mp h).symm)
    have pos : s≠0 := by
      intro z0
      exact nz (orderOf_eq_one_iff.mp (by simpa [z0] using ord))
    have cyc := alternating S f i j eq (by change 0<orderOf z; rw [ord]; positivity)
    change cycleGraph (2*orderOf z) ⊑ _ at cyc
    exact fail ⟨s+1,by omega,by rw [pow_succ',←ord]; exact cyc⟩
  have pair (i j : Fin 3) (ne : i≠j) : f (S i)≠f (S j) := fun eq => ne (distinctQ eq)
  have smallQ : Nat.card (A ⧸ N)<Nat.card A := by
    have idx : 0<N.index := by rw [Subgroup.index_eq_card]; exact Nat.card_pos
    have big := N.one_lt_card_iff_ne_bot.mpr proper
    rw [← Subgroup.index_eq_card,← N.card_mul_index]
    nlinarith
  refine ⟨smallQ,⟨by change f a≠1; simpa [S,shifts] using pair 1 0 (by decide),
    by change f b≠1; simpa [S,shifts] using pair 2 0 (by decide),pair 1 2 (by decide)⟩,?_⟩
  rintro ⟨t,ht,cyc⟩
  have hn : 2≤2^t := by
    have h : 2^2≤2^t := Nat.pow_le_pow_right (by decide) ht
    omega
  have shiftsQ : (fun i => f (S i))=shifts (f a) (f b) := by
    funext i
    fin_cases i <;> simp [S,shifts]
  have down : cycleGraph (2^t) ⊑ graph (fun i => f (S i)) := by rw [shiftsQ,shapes]; exact cyc
  obtain ⟨z,ker,lift⟩ := monodromy S f QuotientGroup.mk_surjective (2^t) hn down
  obtain ⟨s,ord⟩ := orders z ker
  have up := lift (by rw [ord]; positivity)
  exact fail ⟨t+s,by omega,by rw [pow_add,←ord]; exact up⟩


end HaarTwoQuotient

open scoped commutatorElement

/-- A regular matching commutator that is central for the two shifts already
satisfies the class-two permutation theorem in the parent reduction. -/
theorem central_left {A : Type} [Group A] (a b : A) (sep : a≠1 ∧ b≠1 ∧ a≠b)
    (pc : Commute a ⁅a,b⁆) (qc : Commute b ⁅a,b⁆)
    (G : SimpleGraph (Bool × A)) (h0 : ∀ x,G.Adj (false,x) (true,x))
    (ha : ∀ x,G.Adj (false,x) (true,a*x)) (hb : ∀ x,G.Adj (false,x) (true,b*x)) :
    ∃ k : ℕ,2≤k ∧ cycleGraph (2^k) ⊑ G := by
  let F := MulAction.toPermHom A A
  have sep' (x : A) : F a x≠x ∧ F b x≠x ∧ F a x≠F b x := by
    change a*x≠x ∧ b*x≠x ∧ a*x≠b*x
    simpa using sep
  have hpc : Commute (F a) ⁅F a,F b⁆ := by rw [←map_commutatorElement]; exact pc.map F
  have hqc : Commute (F b) ⁅F a,F b⁆ := by rw [←map_commutatorElement]; exact qc.map F
  obtain h|h|h := OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1.classTwoPerm_short
    G (F a) (F b) sep' h0 ha hb hpc hqc
  · exact ⟨2,by decide,h⟩
  · exact ⟨3,by decide,h⟩
  · exact ⟨4,by decide,h⟩

/-- Without a nontrivial normal 2-subgroup, a central element with square one is the identity. -/
lemma center_two_trivial {A : Type} [Group A]
    (core : ∀ N : Subgroup A,N.Normal → IsPGroup 2 N → N=⊥)
    (v : A) (central : ∀ x : A,Commute v x) (sq : v^2=1) : v=1 := by
  let N : Subgroup A := {
    carrier := {z | z ∈ Subgroup.center A ∧ z^2=1}
    one_mem' := by simp
    mul_mem' := by
      rintro x y ⟨hx,sx⟩ ⟨hy,sy⟩
      have c : Commute x y := Subgroup.mem_center_iff.mp hy x
      exact ⟨(Subgroup.center A).mul_mem hx hy,by rw [c.mul_pow,sx,sy,one_mul]⟩
    inv_mem' := by
      rintro x ⟨hx,sx⟩
      exact ⟨(Subgroup.center A).inv_mem hx,by simp [inv_pow,sx]⟩ }
  have normal : N.Normal := ⟨fun x hx y => by simpa [Subgroup.mem_center_iff.mp hx.1 y] using hx⟩
  have two : IsPGroup 2 N := fun z => ⟨1,Subtype.ext (by change (z:A)^2=1; exact z.2.2)⟩
  have mem : v ∈ N := ⟨Subgroup.mem_center_iff.mpr (fun z => (central z).eq.symm),sq⟩
  rwa [core N normal two,Subgroup.mem_bot] at mem

theorem low_class_left {A : Type} [Group A] (a b : A)
    (nc : ¬(Commute a ⁅a,b⁆ ∧ Commute b ⁅a,b⁆))
    (core : ∀ N : Subgroup A,N.Normal → IsPGroup 2 N → N=⊥)
    (four : IsPGroup 2 ((⊤ : Subgroup A).lowerCentralSeries 3))
    (G : SimpleGraph (Bool × A)) (h0 : ∀ x,G.Adj (false,x) (true,x))
    (ha : ∀ x,G.Adj (false,x) (true,a*x)) (hb : ∀ x,G.Adj (false,x) (true,b*x)) :
    cycleGraph 32 ⊑ G := by
  let c := ⁅a⁻¹,b⁻¹⁆
  let d := ⁅c⁻¹,a⁻¹⁆
  let e := ⁅c⁻¹,b⁻¹⁆
  have c1 : c ∈ (⊤ : Subgroup A).lowerCentralSeries 1 :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have bot : (⊤ : Subgroup A).lowerCentralSeries 3=⊥ := core _ inferInstance four
  have center : (⊤ : Subgroup A).lowerCentralSeries 2 ≤ Subgroup.center A :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mp bot
  have third (v x : A) : Commute ⁅c⁻¹,v⁻¹⁆ x :=
    (Subgroup.mem_center_iff.mp (center (Subgroup.commutator_mem_commutator
      (((⊤ : Subgroup A).lowerCentralSeries 1).inv_mem c1) (Subgroup.mem_top _))) x).symm
  have ab : a*b=b*a*c := by dsimp [c,commutatorElement_def]; group
  have ca : c*a=a*c*d := by dsimp only [d,commutatorElement_def]; group
  have cb : c*b=b*c*e := by dsimp only [e,commutatorElement_def]; group
  have nonTwo : d^2≠1 ∨ e^2≠1 := by
    by_contra! h
    have dd : d=1 := center_two_trivial core d (third a) h.1
    have ee : e=1 := center_two_trivial core e (third b) h.2
    have ac : Commute a c := by simpa [Commute,SemiconjBy,dd] using ca.symm
    have bc : Commute b c := by simpa [Commute,SemiconjBy,ee] using cb.symm
    have eq : ⁅a,b⁆=c := by
      rw [commutatorElement_def,ab]
      calc
        _ = b*(a*c*a⁻¹)*b⁻¹ := by simp only [mul_assoc]
        _ = c := by rw [ac.eq, mul_inv_cancel_right,bc.eq,mul_inv_cancel_right]
    exact nc ⟨eq ▸ ac,eq ▸ bc⟩
  let flip : (Bool × A) ↪ (Bool × A) := {
    toFun v := (!v.1,v.2⁻¹)
    inj' := by
      rintro ⟨s,x⟩ ⟨t,y⟩ eq
      have b := congrArg Prod.fst eq
      have z := congrArg Prod.snd eq
      exact Prod.ext (by simpa using b) (inv_injective z) }
  have sub : G.comap flip ⊑ G := ⟨(SimpleGraph.Embedding.comap flip G).toCopy⟩
  have z (x : A) : (G.comap flip).Adj (false,x) (true,x) := (h0 x⁻¹).symm
  have x1 (x : A) : (G.comap flip).Adj (false,x) (true,x*a) := by
    change G.Adj (true,x⁻¹) (false,(x*a)⁻¹)
    simpa [mul_assoc] using (ha ((x*a)⁻¹)).symm
  have x2 (x : A) : (G.comap flip).Adj (false,x) (true,x*b) := by
    change G.Adj (true,x⁻¹) (false,(x*b)⁻¹)
    simpa [mul_assoc] using (hb ((x*b)⁻¹)).symm
  exact (HaarWeightThree.noninvolutory_cycle a b c d e ab ca cb (third a) (third b) nonTwo
    (G.comap flip) z x1 x2).trans sub

theorem generating_sizes (oddCase : H1) (evenCase : H2) (n : ℕ) :
    ∀ (A : Type) [Group A] [Fintype A] (a b : A),
      Fintype.card A=n → Subgroup.closure ({a,b}:Set A)=⊤ → (a≠1 ∧ b≠1 ∧ a≠b) →
      ∃ k : ℕ, 2≤k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × A =>
        u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2)) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A _ _ a b size generated sep
    let G := SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))
    have h0 (z : A) : G.Adj (false,z) (true,z) := ⟨by simp,Or.inl ⟨rfl,rfl,Or.inl rfl⟩⟩
    have ha (z : A) : G.Adj (false,z) (true,a*z) := ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inl rfl)⟩⟩
    have hb (z : A) : G.Adj (false,z) (true,b*z) := ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inr rfl)⟩⟩
    by_cases comm : Commute a ⁅a,b⁆ ∧ Commute b ⁅a,b⁆
    · exact central_left a b sep comm.1 comm.2 G h0 ha hb
    by_contra bad
    by_cases core : ∀ N : Subgroup A,N.Normal → IsPGroup 2 N → N=⊥
    · by_cases four : IsPGroup 2 ((⊤ : Subgroup A).lowerCentralSeries 3)
      · exact bad ⟨5,by decide,low_class_left a b comm core four G h0 ha hb⟩
      · rcases Nat.even_or_odd (Nat.card A) with even|odd
        · exact bad (evenCase A a b generated sep.1 sep.2.1 sep.2.2 comm four even core)
        · exact bad (oddCase A a b generated sep.1 sep.2.1 sep.2.2 comm four odd)
    · push Not at core
      obtain ⟨N,normal,two,nontrivial⟩ := core
      let f := QuotientGroup.mk' N
      obtain ⟨small,sep',bad'⟩ := HaarTwoQuotient.quotient_failure N nontrivial two a b sep bad
      have top : Subgroup.closure ({f a,f b}:Set (A ⧸ N))=⊤ := by
        have im := MonoidHom.map_closure f ({a,b}:Set A)
        rw [generated,Subgroup.map_top_of_surjective f QuotientGroup.mk_surjective] at im
        simpa only [Set.image_pair] using im.symm
      let := Fintype.ofFinite (A ⧸ N)
      have lt : Fintype.card (A ⧸ N)<n := by simpa [Nat.card_eq_fintype_card,size] using small
      exact bad' (ih _ lt (A ⧸ N) (f a) (f b) rfl top sep')

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1.H1 := by
  intro oddCase evenCase A _ _ a b ha hb hab _
  classical
  let U := Subgroup.closure ({a,b}:Set A)
  let x : U := ⟨a,Subgroup.subset_closure (by simp)⟩
  let y : U := ⟨b,Subgroup.subset_closure (by simp)⟩
  have gen : Subgroup.closure ({x,y}:Set U)=⊤ := by
    apply Subgroup.map_injective (f := U.subtype) Subtype.coe_injective
    rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,Subgroup.subtype_range]
    rw [Set.image_pair]
    rfl
  have sep : x≠1 ∧ y≠1 ∧ x≠y :=
    ⟨fun h => ha (congrArg Subtype.val h),fun h => hb (congrArg Subtype.val h),
      fun h => hab (congrArg Subtype.val h)⟩
  obtain ⟨k,hk,cyc⟩ := generating_sizes oddCase evenCase _ U x y rfl gen sep
  let f : (Bool × U) ↪ (Bool × A) := {
    toFun v := (v.1,v.2.val)
    inj' := by
      rintro ⟨s,u⟩ ⟨t,v⟩ eq
      exact Prod.ext (congrArg (fun z : Bool × A => z.1) eq)
        (Subtype.ext (congrArg (fun z : Bool × A => z.2) eq)) }
  refine ⟨k,hk,cyc.trans (isContained_iff_exists_le_comap.mpr ⟨f,?_⟩)⟩
  intro u v edge
  have dir (z w : Bool × U) (s : z.1=false) (t : w.1=true)
      (h : w.2=z.2 ∨ w.2=x*z.2 ∨ w.2=y*z.2) :
      (f z).1=false ∧ (f w).1=true ∧ ((f w).2=(f z).2 ∨ (f w).2=a*(f z).2 ∨ (f w).2=b*(f z).2) := by
    refine ⟨s,t,?_⟩
    rcases h with h|h|h
    · exact .inl (congrArg Subtype.val h)
    · exact .inr (.inl (congrArg Subtype.val h))
    · exact .inr (.inr (congrArg Subtype.val h))
  refine ⟨fun eq => edge.ne (f.injective eq),?_⟩
  rcases edge.2 with ⟨s,t,h⟩|⟨s,t,h⟩
  · exact .inl (dir u v s t h)
  · exact .inr (dir v u s t h)


end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1
