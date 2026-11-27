import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1

/-!
The two coset actions here use left multiplication on left cosets. The
subgroup need not be normal. Repeat one lifted lap by right translation
until its return element in the subgroup has completed its order. This
extends the normal-quotient argument of the ancestor HaarTwoQuotient.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1_H2_R1

open SimpleGraph
open scoped commutatorElement

/-- The group-theoretic Frobenius kernel theorem, in the form needed for a
coset action with nontrivial 2-group point stabilizers. -/
def H1 : Prop := ∀ (A : Type) [Group A] [Fintype A] (P : Sylow 2 A),
    (P : Subgroup A) ≠ ⊥ →
    (∀ g : A, g ≠ 1 → ∀ x y : A ⧸ (P : Subgroup A),
      g • x = x → g • y = y → x=y) →
    ∃ K : Subgroup A, K ≠ ⊤ ∧
      ∀ g : A, (∀ x : A ⧸ (P : Subgroup A), g • x ≠ x) → g ∈ K

/-- The residual matching problem on strictly fewer, oddly many cosets.
An involution fixes at least three cosets. The three matchings are separated
at each point and the two shifts fail to commute on at least one third. -/
def H2 : Prop := ∀ (A : Type) [Group A] [Fintype A] (P : Sylow 2 A) (a b : A),
    Subgroup.closure ({a,b}:Set A)=⊤ →
    Odd P.index → 7 ≤ P.index → P.index < Nat.card A →
    (∀ x : A ⧸ (P : Subgroup A), a • x ≠ x ∧ b • x ≠ x ∧ a • x ≠ b • x) →
    (∃ z : A, z ≠ 1 ∧ z^2=1 ∧
      3 ≤ {x : A ⧸ (P : Subgroup A) | z • x = x}.ncard) →
    P.index ≤ 3 * {x : A ⧸ (P : Subgroup A) | a • b • x ≠ b • a • x}.ncard →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel
      (fun u v : Bool × (A ⧸ (P : Subgroup A)) => u.1=false ∧ v.1=true ∧
        (v.2=u.2 ∨ v.2=a • u.2 ∨ v.2=b • u.2))

section Proof

/-- A coset cycle lifts, and a coincidence of colors at even one coset also
produces an alternating cycle in the regular graph. -/
private theorem descend {A : Type} [Group A] [Fintype A] (N : Subgroup A)
    (two : IsPGroup 2 N) (a b : A) (sep : a≠1 ∧ b≠1 ∧ a≠b)
    (bad : ¬ ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel
      (fun u v : Bool × A => u.1=false ∧ v.1=true ∧
        (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))) :
    (∀ x : A ⧸ N, a • x ≠ x ∧ b • x ≠ x ∧ a • x ≠ b • x) ∧
    ¬ ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel
      (fun u v : Bool × (A ⧸ N) => u.1=false ∧ v.1=true ∧
        (v.2=u.2 ∨ v.2=a • u.2 ∨ v.2=b • u.2)) := by
  classical
  let S : Fin 3 → A := ![1,a,b]
  let G (X : Type) [MulAction A X] := SimpleGraph.fromRel
    (fun u v : Bool × X => u.1=false ∧ v.1=true ∧
      (v.2=u.2 ∨ v.2=a • u.2 ∨ v.2=b • u.2))
  let step {X : Type} [MulAction A X] (v : Bool × X) (i : Fin 3) : Bool × X :=
    (!v.1,(if v.1 then (S i)⁻¹ else S i) • v.2)
  have colored {X : Type} [MulAction A X] (v w : Bool × X) :
      (G X).Adj v w ↔ ∃ i, step v i=w := by
    have forward (x y : X) : (∃ i,step (false,x) i=(true,y)) ↔
        y=x ∨ y=a • x ∨ y=b • x := by
      constructor
      · rintro ⟨i,eq⟩
        have h := congrArg Prod.snd eq
        fin_cases i
        · exact .inl (by simpa [step,S] using h.symm)
        · exact .inr (.inl (by simpa [step,S] using h.symm))
        · exact .inr (.inr (by simpa [step,S] using h.symm))
      · rintro (rfl|rfl|rfl)
        · exact ⟨0,by simp [step,S]⟩
        · exact ⟨1,by simp [step,S]⟩
        · exact ⟨2,by simp [step,S]⟩
    have rev (v : Bool × X) (i : Fin 3) : step (step v i) i=v := by
      rcases v with ⟨s,x⟩; cases s <;> simp [step]
    have symm (v w : Bool × X) : (∃ i,step v i=w) ↔ ∃ i,step w i=v := by
      constructor <;> rintro ⟨i,rfl⟩ <;> exact ⟨i,rev ..⟩
    rcases v with ⟨s,x⟩; rcases w with ⟨t,y⟩
    cases s <;> cases t
    · simp [G,SimpleGraph.fromRel,step]
    · rw [forward]; simp [G,SimpleGraph.fromRel]
    · rw [adj_comm,symm,forward]; simp [G,SimpleGraph.fromRel]
    · simp [G,SimpleGraph.fromRel,step]
  let project (v : Bool × A) : Bool × (A ⧸ N) := (v.1,QuotientGroup.mk v.2)
  let deck (z : A) (v : Bool × A) : Bool × A := (v.1,v.2*z)
  have translate (z : A) (v w : Bool × A) (adj : (G A).Adj v w) :
      (G A).Adj (deck z v) (deck z w) := by
    obtain ⟨i,rfl⟩ := (colored v w).mp adj
    apply (colored ..).mpr
    exact ⟨i, by rcases v with ⟨s,g⟩; cases s <;> simp [deck,step,smul_eq_mul,mul_assoc]⟩
  have repeatLap (n : ℕ) (hn : 2≤n) (p : ℕ → Bool × A) (z : A) (hz : z∈N)
      (edges : ∀ k, k<n → (G A).Adj (p k) (p (k+1))) (close : p n=deck z (p 0))
      (distinct : ∀ i j, i<n → j<n → project (p i)=project (p j) → i=j) :
      cycleGraph (n*orderOf z) ⊑ G A := by
    have hn' : 0<n := by omega
    have ho := orderOf_pos z
    let v (k : ℕ) := deck (z^(k/n)) (p (k%n))
    have proj (k : ℕ) : project (v k) = project (p (k%n)) :=
      Prod.ext rfl (QuotientGroup.mk_mul_of_mem _ (N.pow_mem hz _))
    have stepEdge (k : ℕ) : (G A).Adj (v k) (v (k+1)) := by
      have hrem := Nat.mod_lt k hn'
      have oneM : 1%n = 1 := Nat.mod_eq_of_lt (by omega)
      have oneD : 1/n = 0 := Nat.div_eq_of_lt (by omega)
      have h := translate (z^(k/n)) _ _ (edges (k%n) hrem)
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
      have re := (proj i).symm.trans ((congrArg project eq).trans (proj j))
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
    exact OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1.HaarTwoQuotient.cycle_from_period (G A) _ (by nlinarith) v stepEdge last inject
  have ord (z : A) (hz : z∈N) : ∃ k : ℕ,orderOf z=2^k := by
    obtain ⟨k,e⟩ := two.exists_orderOf_eq_pow (⟨z,hz⟩ : N)
    exact ⟨k,(Subgroup.orderOf_mk (H:=N) z hz).symm.trans e⟩
  have inj : Function.Injective S := by
    intro i j eq
    obtain ⟨ha,hb,hab⟩ := sep
    fin_cases i <;> fin_cases j <;> first | rfl | (
      simp [S] at eq
      first | exact (ha eq).elim | exact (ha eq.symm).elim | exact (hb eq).elim |
        exact (hb eq.symm).elim | exact (hab eq).elim | exact (hab eq.symm).elim)
  have separate (x : A ⧸ N) : Function.Injective (fun i => S i • x) := by
    intro i j eq
    by_contra ne
    let g := x.out
    have gx : (QuotientGroup.mk g : A ⧸ N)=x := QuotientGroup.out_eq' x
    let z := (S j*g)⁻¹*(S i*g)
    have hz : z∈N := by
      apply QuotientGroup.eq.mp
      change S j • (QuotientGroup.mk g : A ⧸ N) = S i • (QuotientGroup.mk g : A ⧸ N)
      rw [gx]; exact eq.symm
    have nz : z≠1 := fun h => ne (inj (mul_right_cancel (inv_mul_eq_one.mp h)).symm)
    obtain ⟨s,hs⟩ := ord z hz
    have hpos : s≠0 := fun h => nz (orderOf_eq_one_iff.mp (by simpa [h] using hs))
    let path (k : ℕ) : Bool × A := if k=0 then (false,g) else if k=1 then (true,S i*g) else (false,g*z)
    have cyc : cycleGraph (2*orderOf z) ⊑ G A := by
      apply repeatLap 2 (by decide) path z hz
      · intro k hk
        interval_cases k
        · exact (colored ..).mpr ⟨i,by simp [path,step,smul_eq_mul]⟩
        · apply (colored ..).mpr
          exact ⟨j,by simp [path,step,z,smul_eq_mul,mul_assoc]⟩
      · simp [path,deck]
      · intro i j hi hj eq
        have e := congrArg Prod.fst eq
        interval_cases i <;> interval_cases j <;> first | rfl | simp [path,project] at e
    exact bad ⟨s+1,by omega,by rw [pow_succ',←hs]; exact cyc⟩
  constructor
  · intro x
    have pair (i j : Fin 3) (ne : i≠j) : S i • x ≠ S j • x := fun eq => ne (separate x eq)
    exact ⟨by simpa [S] using pair 1 0 (by decide),by simpa [S] using pair 2 0 (by decide),
      by simpa [S] using pair 1 2 (by decide)⟩
  · rintro ⟨t,ht,cyc⟩
    let n := 2^t
    have hn : 2≤n := (by have := Nat.pow_le_pow_right (by decide : 0<2) ht; dsimp [n]; omega)
    obtain ⟨c⟩ := cyc
    let ix (k : ℕ) : Fin n := ⟨k%n,Nat.mod_lt _ (by omega)⟩
    have edge (k : ℕ) : (G (A ⧸ N)).Adj (c (ix k)) (c (ix (k+1))) := by
      apply c.toHom.map_rel; apply (OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1.HaarTwoQuotient.adj_mod hn _ _).mpr
      exact .inl (Nat.mod_add_mod _ _ _).symm
    have stepMap (v : Bool × A) (i : Fin 3) : project (step v i)=step (project v) i := by
      rcases v with ⟨s,g⟩; cases s <;> rfl
    let F (k : ℕ) := {v : Bool × A // project v=c (ix k)}
    have next (k : ℕ) (v : F k) : ∃ w,(G A).Adj v.val w ∧ project w=c (ix (k+1)) := by
      obtain ⟨i,hi⟩ := (colored ..).mp (edge k)
      exact ⟨step v.val i,(colored ..).mpr ⟨i,rfl⟩,(stepMap _ _).trans (by rw [v.property]; exact hi)⟩
    let start : F 0 := ⟨((c (ix 0)).1,(c (ix 0)).2.out),Prod.ext rfl (QuotientGroup.out_eq' _)⟩
    let q : ∀ k,F k := Nat.rec start (fun k v => ⟨(next k v).choose,(next k v).choose_spec.2⟩)
    let path (k : ℕ) := (q k).val
    have ep (k : ℕ) : (G A).Adj (path k) (path (k+1)) := (next k (q k)).choose_spec.1
    have pi (k : ℕ) : project (path k)=c (ix k) := (q k).property
    have ixn : ix n=ix 0 := Fin.ext (by simp [ix])
    have eq : project (path n)=project (path 0) := (pi n).trans ((congrArg c ixn).trans (pi 0).symm)
    let z := (path 0).2⁻¹*(path n).2
    have hz : z∈N := QuotientGroup.eq.mp (congrArg Prod.snd eq.symm)
    obtain ⟨s,hs⟩ := ord z hz
    have up : cycleGraph (n*orderOf z) ⊑ G A := by
      apply repeatLap n hn path z hz (fun k _ => ep k)
      · exact Prod.ext (congrArg (fun v : Bool × (A ⧸ N) => v.1) eq) (by simp [deck,z])
      · intro i j hi hj h
        have equal := c.injective ((pi i).symm.trans (h.trans (pi j)))
        simpa [ix,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using congrArg Fin.val equal
    exact bad ⟨t+s,by omega,by rw [pow_add,←hs]; exact up⟩



/-- A cubic three-matching graph without a four-cycle has at least seven
points on each side. The six two-step walks from x all end at different
points, and none ends at x. -/
private theorem seven {X : Type} [Fintype X] [Nonempty X] (G : SimpleGraph (Bool × X))
    (u v : Equiv.Perm X) (sep : ∀ x, u x ≠ x ∧ v x ≠ x ∧ u x ≠ v x)
    (eid : ∀ x,G.Adj (false,x) (true,x)) (eu : ∀ x,G.Adj (false,x) (true,u x))
    (ev : ∀ x,G.Adj (false,x) (true,v x)) (no : ¬ cycleGraph 4 ⊑ G) :
    7 ≤ Fintype.card X := by
  classical
  let S : Fin 3 → Equiv.Perm X := ![1,u,v]
  have inj (y : X) : Function.Injective (fun i => S i y) := by
    intro i j e
    obtain ⟨hu,hv,huv⟩ := sep y
    fin_cases i <;> fin_cases j <;> first | rfl | (
      simp [S] at e
      first | exact (hu e).elim | exact (hu e.symm).elim | exact (hv e).elim |
        exact (hv e.symm).elim | exact (huv e).elim | exact (huv e.symm).elim)
  have edge (i : Fin 3) (y : X) : G.Adj (false,y) (true,S i y) := by
    fin_cases i
    · exact eid y
    · exact eu y
    · exact ev y
  let x : X := Classical.choice inferInstance
  let C := {ij : Fin 3 × Fin 3 // ij.1 ≠ ij.2}
  let endPt (ij : C) := (S ij.val.2).symm (S ij.val.1 x)
  have right (ij : C) : S ij.val.2 (endPt ij)=S ij.val.1 x := Equiv.apply_symm_apply ..
  have diff (ij : C) : endPt ij ≠ x := by
    intro hx
    have e := right ij
    rw [hx] at e
    exact ij.property ((inj x e).symm)
  have single : Function.Injective endPt := by
    intro i j eq
    by_cases firstEq : i.val.1=j.val.1
    · have h2 : i.val.2=j.val.2 := inj (endPt j) (calc S i.val.2 (endPt j)=S i.val.2 (endPt i) := congrArg _ eq.symm
                                           _ = S j.val.1 x := (right i).trans (congrArg (fun d => S d x) firstEq)
                                           _ = S j.val.2 (endPt j) := (right j).symm)
      exact Subtype.ext (Prod.ext firstEq h2)
    · apply False.elim
      apply no
      have ei : G.Adj (false,endPt i) (true,S i.val.1 x) := (right i) ▸ edge i.val.2 (endPt i)
      have ej : G.Adj (false,endPt i) (true,S j.val.1 x) := by
        rw [eq,←right j]; exact edge ..
      apply OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1.NonfreeWalk.square
        (edge i.val.1 x) ei.symm ej (edge j.val.1 x).symm
      · exact fun h => diff i (congrArg Prod.snd h).symm
      · exact fun h => firstEq (inj x (congrArg Prod.snd h))
  let nodes (o : Option C) := o.elim x endPt
  have inject : Function.Injective nodes := by
    intro i j h
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact (diff j h.symm).elim
    | some i =>
      cases j with
      | none => exact (diff i h).elim
      | some j => exact congrArg some (single h)
  have count : Fintype.card (Option C)=7 := by decide
  exact count ▸ Fintype.card_le_of_injective nodes inject

/-- Transfer to the abelianization of the 2-group stabilizer detects the
stabilizer and kills every fixed-point-free element in a Frobenius action. -/
theorem frobeniusKernel : H1 := by
  classical
  intro A _ _ P hP unique
  let N : Subgroup A := P
  let X := A ⧸ N
  let base : X := QuotientGroup.mk (1 : A)
  let φ : N →* Abelianization N := Abelianization.of
  let ψ := MonoidHom.transfer φ
  let _ : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hP
  let _ : Group.IsNilpotent N := P.2.isNilpotent
  have inFix (v : A) (hv : v∈N) : v • base=base := by
    change (QuotientGroup.mk (v*1) : X)=QuotientGroup.mk 1
    apply QuotientGroup.eq.mpr; simpa using N.inv_mem hv
  have periodFix (g : A) (x : X) : g^(Function.minimalPeriod (g • ·) x) • x = x :=
    MulAction.pow_smul_eq_iff_minimalPeriod_dvd.mpr dvd_rfl
  have kills (g : A) (der : ∀ x : X, g • x ≠ x) : ψ g=1 := by
    rw [show ψ g=MonoidHom.transfer φ g from rfl,
      MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
    apply Finset.prod_eq_one
    intro q _
    let x : X := q.out
    let n := Function.minimalPeriod (g • ·) x
    have hfix : g^n • x=x := periodFix g x
    have one : g^n=1 := by
      by_contra non
      have other : g^n • (g • x)=g • x := by
        rw [← mul_smul,((Commute.refl g).pow_left n).eq,mul_smul,hfix]
      exact der x (unique (g^n) non x (g • x) hfix other).symm
    have term : (⟨q.out.out⁻¹*g^(Function.minimalPeriod (g • ·) q.out)*q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem N g q.out⟩ : N)=1 := by
      apply Subtype.ext; change q.out.out⁻¹*g^n*q.out.out=1; simp [one]
    rw [term,map_one]
  have restrict (h : N) : ψ (h:A)=φ h := by
    let g : A := h
    let T := Quotient (MulAction.orbitRel (Subgroup.zpowers g) X)
    let q₀ : T := Quotient.mk _ base
    have fx : g • base=base := inFix _ h.2
    have out0 : q₀.out=base := by
      have hr : MulAction.orbitRel (Subgroup.zpowers g) X q₀.out base :=
        Quotient.exact (Quotient.out_eq q₀)
      obtain ⟨w,hw⟩ := hr
      have hwN : (w:A)∈N := (Subgroup.zpowers_le.mpr h.2) w.2
      exact hw.symm.trans (inFix _ hwN)
    have per : Function.minimalPeriod (g • ·) q₀.out=1 := by
      rw [out0]; exact Function.minimalPeriod_eq_one_iff_isFixedPt.mpr fx
    rw [show ψ (h:A)=MonoidHom.transfer φ g from rfl,
      MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
    rw [Fintype.prod_eq_single q₀]
    · let r := q₀.out.out
      have cr : (QuotientGroup.mk r : X)=base := (QuotientGroup.out_eq' _).trans out0
      have hrN : r∈N := by simpa [base] using QuotientGroup.eq.mp cr.symm
      let w : N := ⟨r,hrN⟩
      have eq : (⟨q₀.out.out⁻¹*g^(Function.minimalPeriod (g • ·) q₀.out)*q₀.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem N g q₀.out⟩ : N)=w⁻¹*h*w := by
        apply Subtype.ext; change r⁻¹*g^_*r=r⁻¹*g*r; rw [per,pow_one]
      rw [eq,map_mul,map_mul,map_inv]; simp [mul_comm,mul_left_comm]
    · intro q hq
      let x : X := q.out
      let n := Function.minimalPeriod (g • ·) x
      have dif : x≠base := by
        intro eq; apply hq
        calc q = Quotient.mk _ x := (Quotient.out_eq q).symm
             _ = q₀ := congrArg (Quotient.mk _) eq
      have one : g^n=1 := by
        by_contra non
        exact dif (unique (g^n) non x base (periodFix g x) (inFix _ (N.pow_mem h.2 _)))
      have term : (⟨q.out.out⁻¹*g^(Function.minimalPeriod (g • ·) q.out)*q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem N g q.out⟩ : N)=1 := by
        apply Subtype.ext; change q.out.out⁻¹*g^n*q.out.out=1; simp [one]
      rw [term,map_one]
  refine ⟨ψ.ker,?_,fun g hg => kills g hg⟩
  intro eq
  have trivial : φ.ker=⊤ := by
    apply top_unique; intro h _
    have mem : (h:A)∈ψ.ker := eq ▸ Subgroup.mem_top _
    exact (restrict h).symm.trans mem
  have proper := Group.IsSolvable.commutator_lt_top_of_nontrivial N
  exact proper.ne ((Abelianization.ker_of N).symm.trans trivial)

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1.H2 := by
  classical
  intro frob residual A _ _ a b gen ha hb hab _ _ evenA _
  let P : Sylow 2 A := Classical.choice inferInstance
  let N : Subgroup A := P
  let X := A ⧸ N
  have oddIdx : Odd P.index := Nat.not_even_iff_odd.mp (fun e => P.not_dvd_index e.two_dvd)
  have nontriv : N ≠ ⊥ := by
    intro h
    have hi : P.index = Nat.card A := by change N.index=_; rw [h,Subgroup.index_bot]
    exact P.not_dvd_index (hi.symm ▸ evenA.two_dvd)
  have smaller : P.index < Nat.card A := by
    have pos : 0<N.index := by rw [N.index_eq_card]; exact Nat.card_pos
    have big := N.one_lt_card_iff_ne_bot.mpr nontriv
    rw [← N.card_mul_index]; change N.index < Nat.card N*N.index
    nlinarith
  by_contra bad
  obtain ⟨sep,down⟩ := descend N P.2 a b ⟨ha,hb,hab⟩ bad
  have nonFrob : ¬(∀ g : A, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x=y) := by
    intro h
    obtain ⟨K,proper,der⟩ := frob A P nontriv h
    have hagen : a∈K := der a (fun x => (sep x).1)
    have hbgen : b∈K := der b (fun x => (sep x).2.1)
    apply proper
    apply top_unique
    rw [← gen,Subgroup.closure_le]
    intro t ht
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl <;> assumption
  push Not at nonFrob
  obtain ⟨g,hg,x,y,hx,hy,hxy⟩ := nonFrob
  let r := Quotient.out x
  have rx : (QuotientGroup.mk r : X)=x := QuotientGroup.out_eq' _
  let d := r⁻¹*g*r
  have hd : d∈N := by
    have e : (QuotientGroup.mk r : X) = QuotientGroup.mk (g*r) := by
      change (QuotientGroup.mk r : X)=g • (QuotientGroup.mk r : X)
      rw [rx,hx]
    simpa [d,mul_assoc] using QuotientGroup.eq.mp e
  obtain ⟨m,hm⟩ := P.2.exists_orderOf_eq_pow (⟨d,hd⟩ : N)
  have semi : SemiconjBy r d g := by simp [SemiconjBy,d,mul_assoc]
  have ord : orderOf g = 2^m := (SemiconjBy.orderOf_eq r semi).symm.trans
    ((Subgroup.orderOf_mk (H:=N) d hd).symm.trans hm)
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m≠0 by
    intro h; exact hg (orderOf_eq_one_iff.mp (by simpa [h] using ord)))
  let z := g^(2^s)
  have hzinv : z^2=1 := by
    rw [show z^2=g^(2^(s+1)) by change (g^(2^s))^2=_; rw [←pow_mul,pow_succ],← ord,pow_orderOf_eq_one]
  have hnz : z≠1 := by
    intro h
    have dvd := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [ord,pow_succ] at dvd
    have hle := Nat.le_of_dvd (by positivity : 0<2^s) dvd
    have : 0<2^s := by positivity
    omega
  have fixed (v : X) (hv : g • v=v) (k : ℕ) : g^k • v=v := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ,mul_smul,hv,ih]
  let G := SimpleGraph.fromRel (fun u v : Bool × X => u.1=false ∧ v.1=true ∧
       (v.2=u.2 ∨ v.2=a • u.2 ∨ v.2=b • u.2))
  let u : Equiv.Perm X := MulAction.toPerm a
  let v : Equiv.Perm X := MulAction.toPerm b
  have noShort : ¬(cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G) := by
    rintro (c|c|c)
    · exact down ⟨2,by decide,c⟩
    · exact down ⟨3,by decide,c⟩
    · exact down ⟨4,by decide,c⟩
  have eid (w : X) : G.Adj (false,w) (true,w) := by simp [G,SimpleGraph.fromRel]
  have eu (w : X) : G.Adj (false,w) (true,u w) := by simp [G,u,SimpleGraph.fromRel]
  have ev (w : X) : G.Adj (false,w) (true,v w) := by simp [G,v,SimpleGraph.fromRel]
  have bound := OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.LocalCommutation.defectDensity G u v sep eid eu ev noShort
  have size := seven G u v sep eid eu ev (fun h => noShort (Or.inl h))
  have count : (Finset.univ.filter (fun x => u (v x) ≠ v (u x))).card =
      {x : X | a • b • x ≠ b • a • x}.ncard := by
    rw [← Set.ncard_coe_finset]; congr 1; ext; simp [u,v]
  have idx : P.index=Fintype.card X := N.index_eq_card.trans Nat.card_eq_fintype_card
  let f : Function.End X := fun w => z • w
  have hf : f^(2^1 : ℕ)=1 := by
    funext w
    change z • (z • w)=w
    rw [←mul_smul,←pow_two,hzinv,one_smul]
  have modEq := Equiv.Perm.card_fixedPoints_modEq (p:=2) (n:=1) hf
  let xx : f.fixedPoints := ⟨x,fixed x hx _⟩
  let yy : f.fixedPoints := ⟨y,fixed y hy _⟩
  have diff : xx ≠ yy := fun he => hxy (congrArg Subtype.val he)
  have twoFixed : 2 ≤ Fintype.card f.fixedPoints := by
    simpa [diff] using Finset.card_le_univ ({xx,yy} : Finset f.fixedPoints)
  have num : {w : X | z • w=w}.ncard=Fintype.card f.fixedPoints := Nat.card_eq_fintype_card
  have oddMod : P.index % 2=1 := by obtain ⟨j,hj⟩ := oddIdx; omega
  change Fintype.card X % 2 = Fintype.card f.fixedPoints % 2 at modEq
  have three : 3 ≤ {w : X | z • w=w}.ncard := by rw [num]; omega
  exact down (residual A P a b gen oddIdx (by rwa [idx]) smaller sep
    ⟨z,hnz,hzinv,three⟩ (by rwa [idx,←count]))

end Proof

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1_H2_R1
