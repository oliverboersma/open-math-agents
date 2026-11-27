import OMAStatements.S_mo_300962
import Mathlib

/-!
Zhi-Wei Sun's question on two triangular numbers and two powers of five.
Reduction by @physbuzz. Multiplication by 5 on sums of two squares gives a
descent on one residue class. In the remaining cases the class modulo 5
determines whether to double the norm to obtain the form x²+25y².
-/
namespace OMA.R_mo_300962_R1
open OMA.S_mo_300962
lemma double (k : ℕ) : 2*triangular k=k*(k+1) := by
  unfold triangular
  apply Nat.mul_div_cancel'
  rcases Nat.even_or_odd k with ⟨v,e⟩ | ⟨v,e⟩
  · exact ⟨v*(k+1),by rw [e];ring⟩
  · exact ⟨k*(v+1),by rw [e];ring⟩

lemma gaussian (m : ℕ) : (∃ a b : ℕ,m=triangular a+triangular b) ↔ ∃ u v : ℕ, 4*m+1=u^2+v^2 := by
  constructor
  · rintro ⟨a,b,rfl⟩
    wlog order : b≤a generalizing a b
    · simpa [add_comm] using this b a (by omega)
    refine ⟨a+b+1,a-b,?_⟩
    have e : a-b+b=a := by omega
    nlinarith only [double a,double b,congrArg (fun x : ℕ => x^2) e,
      congrArg (fun x : ℕ => b*x) e]
  · rintro ⟨u,v,eq⟩
    wlog le : v≤u generalizing u v
    · exact this v u (by simpa [add_comm] using eq) (by omega)
    have oe : u%2+v%2=1 := by
      have mod := congrArg (·%2) eq
      have red (t : ℕ) : t^2%2=t%2 := by
        rw [Nat.pow_mod]; rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h]
      change (4*m+1)%2=(u^2+v^2)%2 at mod
      rw [Nat.add_mod (u^2),red u,red v] at mod
      omega
    let a := (u+v-1)/2
    let b := (u-v-1)/2
    have f : u=a+b+1 := by dsimp [a,b]; omega
    have g : a=b+v := by dsimp [a,b]; omega
    refine ⟨a,b,?_⟩
    rw [f] at eq
    rw [g] at eq ⊢
    nlinarith only [eq,double (b+v),double b]

lemma criteria (m : ℕ) : (∃ a b : ℕ,m=triangular a+triangular b) ↔
    ∀ q∈(4*m+1).primeFactors,q%4=3 → Even (padicValNat q (4*m+1)) :=
  (gaussian m).trans Nat.eq_sq_add_sq_iff

lemma excludes {p m : ℕ} (pp : p.Prime) (bad : p%4=3) (one : p∣4*m+1)
    (two : ¬p^2∣4*m+1) : ¬ ∃ a b : ℕ,m=triangular a+triangular b := by
  intro rep
  have : Fact p.Prime := ⟨pp⟩
  have nz : 4*m+1≠0 := by omega
  have even := (criteria m).mp rep p (Nat.mem_primeFactors.mpr ⟨pp,one,nz⟩) bad
  have ge := (padicValNat_dvd_iff_le (p := p) (n := 1) nz).mp (by simpa using one)
  have lt := mt (padicValNat_dvd_iff_le (p := p) (n := 2) nz).mpr two
  obtain ⟨k,eq⟩ := even
  omega
/-- For any finite family of shifts, an entire arithmetic progression escapes them all. -/
lemma finite_obstruction (S : Finset ℕ) :
    ∃ r M : ℕ, 0<M ∧ ∀ n : ℕ, n ≡ r [MOD M] → ∀ s∈S,∀ a b : ℕ,n≠s+(triangular a+triangular b) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0,1,by decide,by simp⟩
  | @insert s S hs ih =>
    obtain ⟨r,M,mp,avoid⟩ := ih
    obtain ⟨p,high,pp,mod4⟩ := Nat.forall_exists_prime_gt_and_modEq (M+3)
      (q := 4) (a := 3) (by decide) (by decide)
    have bad : p%4=3 := mod4
    have dp : 0<p := pp.pos
    have co : M.Coprime (p^2) :=
      ((pp.coprime_iff_not_dvd.mpr (fun dvd => by have := Nat.le_of_dvd mp dvd; omega)).symm).pow_right _
    let delta := (3*p-1)/4
    have exactDelta : 4*delta+1=3*p := by dsimp [delta]; omega
    obtain ⟨r',first,second⟩ := Nat.chineseRemainder co r (s+delta)
    refine ⟨r',M*p^2,by positivity,?_⟩
    intro n h t ht a b
    rcases Finset.mem_insert.mp ht with rfl | old
    · intro rep
      have here := (h.of_dvd (dvd_mul_left (p^2) M)).trans second
      rw [rep] at here
      have hq := (Nat.ModEq.add_left_cancel' t here).mul_left 4 |>.add_right 1
      rw [exactDelta] at hq
      have firstQ : p∣4*(triangular a+triangular b)+1 := Nat.modEq_zero_iff_dvd.mp
        ((hq.of_dvd (by simp [pow_two])).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left p 3)))
      have secondQ : ¬p^2∣4*(triangular a+triangular b)+1 := by
        intro dv
        have wrong := Nat.modEq_zero_iff_dvd.mp (hq.symm.trans (Nat.modEq_zero_iff_dvd.mpr dv))
        have ge := Nat.le_of_dvd (show 0<3*p by positivity) wrong
        nlinarith [mul_pos dp (show 0<p-3 by omega),Nat.sub_add_cancel (show 3≤p by omega)]
      exact excludes pp bad firstQ secondQ ⟨a,b,rfl⟩
    · exact avoid n ((h.of_dvd (dvd_mul_right M (p^2))).trans first) t old a b
/-- Completing both squares, with a prescribed shift s. -/
lemma shifted (n s : ℕ) : (∃ a b : ℕ,n=s+(triangular a+triangular b)) ↔
    ∃ u v : ℕ, 4*n+1=4*s+u^2+v^2 := by
  constructor
  · rintro ⟨a,b,rfl⟩
    obtain ⟨u,v,eq⟩ := (gaussian (triangular a+triangular b)).mp ⟨a,b,rfl⟩
    exact ⟨u,v,by omega⟩
  · rintro ⟨u,v,eq⟩
    have le : s≤n := by omega
    obtain ⟨a,b,h⟩ := (gaussian (n-s)).mpr ⟨u,v,by omega⟩
    exact ⟨a,b,by omega⟩

/-- Removing a factor of 2 preserves representation as a sum of two squares. -/
lemma halve {m u v : ℕ} (eq : 2*m=u^2+v^2) : ∃ x y : ℕ,m=x^2+y^2 := by
  wlog le : v≤u generalizing u v
  · exact this (u := v) (v := u) (by simpa [add_comm] using eq) (by omega)
  have par : u%2=v%2 := by
    have q := congrArg (·%2) eq
    change (2*m)%2=(u^2+v^2)%2 at q
    rw [Nat.add_mod (u^2),Nat.pow_mod u,Nat.pow_mod v] at q
    rcases Nat.mod_two_eq_zero_or_one u with a | a <;>
      rcases Nat.mod_two_eq_zero_or_one v with b | b <;> simp_all <;> omega
  let x := (u+v)/2
  let y := (u-v)/2
  have e : u=x+y := by dsimp [x,y]; omega
  have f : x=y+v := by dsimp [x,y]; omega
  refine ⟨x,y,?_⟩
  rw [e,f] at eq
  rw [f]
  nlinarith only [eq]

/-- An integer represented by the original four summands gives another at 5n+1. -/
lemma lift5 {n a b c d : ℕ} (rep : n=triangular a+triangular b+5^c+5^d) :
    ∃ a b c d : ℕ,5*n+1=triangular a+triangular b+5^c+5^d := by
  obtain ⟨u,v,eq⟩ := (gaussian (triangular a+triangular b)).mp ⟨a,b,rfl⟩
  obtain ⟨x,y,h⟩ := Nat.sq_add_sq_mul (show 5=1^2+2^2 by decide) eq
  obtain ⟨e,f,he⟩ := (shifted (5*n+1) (5^(c+1)+5^(d+1))).mpr
    ⟨x,y,by rw [pow_succ,pow_succ,rep]; nlinarith only [h]⟩
  exact ⟨e,f,c+1,d+1,by omega⟩

/-- Square units modulo 5 force a coordinate divisible by 5. -/
lemma square_unit {u v : ℕ} (hr : (u^2+v^2)%5=1 ∨ (u^2+v^2)%5=4) :
    ∃ x y : ℕ,u^2+v^2=x^2+25*y^2 := by
  have tab : ∀ a b : Fin 5, ((a.val^2+b.val^2)%5=1 ∨ (a.val^2+b.val^2)%5=4) →
      a.val=0 ∨ b.val=0 := by decide
  have er : (u^2+v^2)%5=((u%5)^2+(v%5)^2)%5 := by
    rw [Nat.add_mod (u^2),Nat.pow_mod u,Nat.pow_mod v,←Nat.add_mod]
  rw [er] at hr
  rcases tab ⟨u%5,by omega⟩ ⟨v%5,by omega⟩ hr with a | b
  · have div : u%5=0 := a
    obtain ⟨y,e⟩ := Nat.dvd_of_mod_eq_zero div
    exact ⟨v,y,by rw [e]; ring⟩
  · have div : v%5=0 := b
    obtain ⟨y,e⟩ := Nat.dvd_of_mod_eq_zero div
    exact ⟨u,y,by rw [e]; ring⟩

/-- Doubling either nonsquare unit modulo 5 gives a square unit. -/
lemma nonsquare_unit {u v : ℕ} (hr : (u^2+v^2)%5=2 ∨ (u^2+v^2)%5=3) :
    ∃ x y : ℕ,2*(u^2+v^2)=x^2+25*y^2 := by
  obtain ⟨e,f,h⟩ := Nat.sq_add_sq_mul (show 2=1^2+1^2 by decide) (show u^2+v^2=u^2+v^2 from rfl)
  obtain ⟨x,y,eq⟩ := square_unit (u := e) (v := f) (by rw [←h]; omega)
  exact ⟨x,y,h.trans eq⟩
/-- In the square unit classes, use the form x²+25y² after factoring one 5 out of both powers. -/
def H1 : Prop := ∀ n : ℕ,1<n → ((4*n+1)%5=1 ∨ (4*n+1)%5=4) →
    (∀ j x y : ℕ,4*n+1≠4*(1+5^j)+x^2+y^2) →
    ∃ c d x y : ℕ,4*n+1=20*(5^c+5^d)+x^2+25*y^2

/-- In the nonsquare unit classes, multiply by 2 before using the same form. -/
def H2 : Prop := ∀ n : ℕ,1<n → ((4*n+1)%5=2 ∨ (4*n+1)%5=3) →
    (∀ j x y : ℕ,4*n+1≠4*(1+5^j)+x^2+y^2) →
    ∃ c d x y : ℕ,2*(4*n+1)=40*(5^c+5^d)+x^2+25*y^2

private lemma translated {n c d x y : ℕ} (eq : 4*n+1=4*(5^c+5^d)+x^2+y^2) :
    ∃ a b c d : ℕ,n=triangular a+triangular b+5^c+5^d := by
  obtain ⟨a,b,h⟩ := (shifted n (5^c+5^d)).mpr ⟨x,y,eq⟩
  exact ⟨a,b,c,d,by omega⟩

/-- Any universal representation also proves both arithmetic steps. -/
lemma necessary (all : ∀ n : ℕ,1<n → ∃ a b c d : ℕ,n=triangular a+triangular b+5^c+5^d) : H1 ∧ H2 := by
  have posShift {n : ℕ} (pos : 1<n) (none : ∀ j x y : ℕ,4*n+1≠4*(1+5^j)+x^2+y^2) :
      ∃ c d u v : ℕ,4*n+1=20*(5^c+5^d)+u^2+v^2 := by
    obtain ⟨a,b,c,d,h⟩ := all n pos
    obtain ⟨u,v,sum⟩ := (gaussian (triangular a+triangular b)).mp ⟨a,b,rfl⟩
    cases c with
    | zero => exact (none d u v (by simp only [pow_zero] at h; omega)).elim
    | succ c =>
      cases d with
      | zero => exact (none (c+1) u v (by simp only [pow_zero] at h; omega)).elim
      | succ d =>
        refine ⟨c,d,u,v,?_⟩
        rw [pow_succ 5 c,pow_succ 5 d] at h
        omega
  constructor
  · intro n pos mod none
    obtain ⟨c,d,u,v,eq⟩ := posShift pos none
    obtain ⟨x,y,xy⟩ := square_unit (u := u) (v := v) (by omega)
    exact ⟨c,d,x,y,by omega⟩
  · intro n pos mod none
    obtain ⟨c,d,u,v,eq⟩ := posShift pos none
    obtain ⟨x,y,xy⟩ := nonsquare_unit (u := u) (v := v) (by omega)
    exact ⟨c,d,x,y,by omega⟩

theorem main : H1 → H2 → type_of% @OMA.S_mo_300962.main := by
  intro h1 h2 n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro pos
    by_cases desc : n%5=1
    · let m := n/5
      have eq : n=5*m+1 := by dsimp [m]; omega
      by_cases init : m≤1
      · have six : n=6 := by omega
        exact ⟨0,0,0,1,by rw [six]; decide⟩
      · obtain ⟨a,b,c,d,rep⟩ := ih m (by omega) (by omega)
        rw [eq]
        exact lift5 rep
    by_cases has : ∃ j x y : ℕ, 4*n+1=4*(1+5^j)+x^2+y^2
    · obtain ⟨j,x,y,eq⟩ := has
      exact translated (c := 0) (d := j) (x := x) (y := y) (by simpa using eq)
    have none : ∀ j x y : ℕ,4*n+1≠4*(1+5^j)+x^2+y^2 := fun j x y eq => has ⟨j,x,y,eq⟩
    by_cases sq : (4*n+1)%5=1 ∨ (4*n+1)%5=4
    · obtain ⟨c,d,x,y,eq⟩ := h1 n pos sq none
      apply translated (c := c+1) (d := d+1) (x := x) (y := 5*y)
      rw [pow_succ 5 c,pow_succ 5 d]; nlinarith only [eq]
    · obtain ⟨c,d,x,y,eq⟩ := h2 n pos (by omega) none
      let s := 5^(c+1)+5^(d+1)
      have ss : s=5*(5^c+5^d) := by dsimp [s]; ring
      have ns : s≤n := by omega
      obtain ⟨u,v,norm⟩ := halve (m := 4*(n-s)+1) (u := x) (v := 5*y) (by
        have exactSub := Nat.sub_add_cancel ns
        nlinarith only [eq,ss,exactSub])
      apply translated (c := c+1) (d := d+1) (x := u) (y := v)
      change 4*n+1=4*s+u^2+v^2
      omega
end OMA.R_mo_300962_R1
