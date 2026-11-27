import OMAStatements.S_oeis_a120740
import Mathlib

/-!
A120740. Proof formalized by @physbuzz. Colin Barker's formulas, confirmed in
the OEIS entry by R. J. Mathar, follow from the classification of the digit sums.
For k>n the congruence modulo 9 forces n=0 or 5 mod 9. Every such n is
attained with k equal to 3 or 1 times a suitable power of ten. For k≤n,
a decimal digit-length bound leaves a finite calculation.
-/
namespace Barker120740

abbrev S (x : ℕ) := (Nat.digits 10 x).sum

lemma split (x : ℕ) : S x=x%10+S (x/10) := by
  by_cases h : x=0
  · simp [h,S]
  · unfold S; rw [Nat.digits_eq_cons_digits_div (by decide) h,List.sum_cons]

lemma complement {a b t : ℕ} (h : a+b+1=10^t) : S a+S b=9*t := by
  induction t generalizing a b with
  | zero => have aa : a=0 := by omega
            have bb : b=0 := by omega
            simp [aa,bb,S]
  | succ t ih =>
    rw [pow_succ] at h
    have lower : a%10+b%10=9 := by omega
    have upper : a/10+b/10+1=10^t := by omega
    have sm := ih upper
    rw [split a,split b]
    omega

lemma append (v t u : ℕ) (small : u<10^t) : S (v*10^t+u)=S v+S u := by
  induction t generalizing u with
  | zero =>
    have : u=0 := by omega
    simp [this,S]
  | succ t ih =>
    rw [pow_succ] at small ⊢
    let high := v*10^t
    have form : v*(10^t*10)+u = u+10*high := by dsimp [high]; ring
    rw [form,split (u+10*high),Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (by decide)]
    rw [add_comm (u/10),ih (u/10) (by omega),split u]
    omega

lemma shift (v t : ℕ) : S (v*10^t)=S v := by
  simpa [S] using append v t 0 (by positivity)

lemma bound {u t : ℕ} (h : u<10^t) : S u≤9*t := by
  have z := complement (a := u) (b := 10^t-1-u) (t := t) (by omega)
  omega

lemma sq_short {n x : ℕ} (large : 100≤n) (hx : x≤n^2) : S x<n := by
  let e := Nat.log 10 n
  have bot : 10^e≤n := Nat.pow_log_le_self 10 (by omega)
  have top : n<10^(e+1) := Nat.lt_pow_succ_log_self (by decide) _
  have ep : 2≤e := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr large
  have grow (i : ℕ) : 18*(i+2+1)<10^(i+2) := by
    induction i with
    | zero => decide
    | succ i ih =>
      rw [show i+1+2=(i+2)+1 by omega,pow_succ]
      omega
  have s := grow (e-2)
  rw [show e-2+2=e by omega] at s
  have cap : x<10^((e+1)*2) := by
    rw [pow_mul]
    exact lt_of_le_of_lt hx (Nat.pow_lt_pow_left top (by decide))
  have dig := bound cap
  omega
open OMA.S_oeis_a120740

lemma necessary {n : ℕ} (h : IsTerm n) : n=4 ∨ n%9=0 ∨ n%9=5 := by
  obtain ⟨k,h⟩ := h
  change S (k*Int.natAbs ((n:ℤ)-k))=n at h
  by_cases order : k≤n
  · have e : Int.natAbs ((n:ℤ)-k)=n-k := by omega
    rw [e] at h
    by_cases large : 100≤n
    · have bound : k*(n-k)≤n^2 := by
        rw [pow_two]; exact Nat.mul_le_mul order (by omega)
      have less := sq_short large bound
      omega
    · have tab : ∀ n k : Fin 100,k.val≤n.val → S (k.val*(n.val-k.val))=n.val →
          n.val=4 ∨ n.val%9=0 ∨ n.val%9=5 := by decide +kernel
      exact tab ⟨n,by omega⟩ ⟨k,by omega⟩ order h
  · have e : Int.natAbs ((n:ℤ)-k)=k-n := by omega
    rw [e] at h
    have congr := Nat.modEq_nine_digits_sum (k*(k-n))
    change (k*(k-n))%9=S (k*(k-n))%9 at congr
    rw [h] at congr
    have add : (k*(k-n)+k*n)%9=(n+k*n)%9 := by
      simpa only [Nat.ModEq] using (show k*(k-n) ≡ n [MOD 9] from congr).add_right (k*n)
    rw [←Nat.mul_add, Nat.sub_add_cancel (by omega)] at add
    have table : ∀ a b : Fin 9,(a.val*a.val)%9=(b.val+a.val*b.val)%9 → b.val=0 ∨ b.val=5 := by decide
    apply Or.inr
    apply table ⟨k%9,by omega⟩ ⟨n%9,by omega⟩
    change (k%9*(k%9))%9=(n%9+k%9*(n%9))%9
    calc
      _ = (k*k)%9 := (Nat.mul_mod k k 9).symm
      _ = (n+k*n)%9 := add
      _ = (n%9+(k*n)%9)%9 := Nat.add_mod .. 
      _ = _ := by rw [Nat.mul_mod k n 9,Nat.add_mod_mod]

lemma witness {n t C : ℕ} (pos : 0<C) (npositive : 0<n) (lim : C*n≤10^t)
    (target : n+S (C*n-1)=S (C*C-1)+9*t) : IsTerm n := by
  let D := 10^t
  have cp : 0<C*n := Nat.mul_pos pos npositive
  have nl : n≤C*D := by
    have dn : n≤C*n := Nat.le_mul_of_pos_left n pos
    have dc : D≤C*D := Nat.le_mul_of_pos_left D pos
    change C*n≤D at lim
    omega
  have natabs : Int.natAbs ((n:ℤ)-(C*D:ℕ))=C*D-n := by omega
  have comp := complement (a := D-C*n) (b := C*n-1) (t := t) (by change _=D; omega)
  have sm := append (C*C-1) t (D-C*n) (by change D-C*n<D; dsimp [D]; omega)
  have cp2 : 1≤C*C := Nat.mul_pos pos pos
  have form : C*D*(C*D-n)=((C*C-1)*D+(D-C*n))*D := by
    have h1 := Nat.sub_add_cancel nl
    have h2 := Nat.sub_add_cancel lim
    have h3 := Nat.sub_add_cancel cp2
    change D-C*n+C*n=D at h2
    nlinarith only [congrArg (fun v : ℕ => C*D*v) h1,
      congrArg (fun v : ℕ => v*D) h2,congrArg (fun v : ℕ => v*D^2) h3]
  refine ⟨C*D,?_⟩
  change S (C*D*Int.natAbs ((n:ℤ)-(C*D:ℕ)))=n
  rw [natabs,form,shift]
  change S ((C*C-1)*D+(D-C*n))=S (C*C-1)+S (D-C*n) at sm
  change S ((C*C-1)*D+(D-C*n))=n
  omega

lemma ample {t n : ℕ} (big : 100≤n) (lim : n≤9*t+16) : 3*n≤10^t := by
  have grow (k : ℕ) : 27*(k+3)+48≤10^(k+3) := by
    induction k with
    | zero => decide
    | succ k ih => rw [show k+1+3=(k+3)+1 by omega,pow_succ]; omega
  have := grow (t-3)
  rw [show t-3+3=t by omega] at this
  omega

lemma sufficient {n : ℕ} (h : n=4 ∨ n%9=0 ∨ n%9=5) : IsTerm n := by
  by_cases small : n<100
  · let key (m : ℕ) := if m=4 then 2 else if m=0 then 0 else
      if m%9=5 then 10^((m+S (m-1))/9) else 3*10^((m+S (3*m-1)-8)/9)
    have tab : ∀ m : Fin 100,(m.val=4 ∨ m.val%9=0 ∨ m.val%9=5) →
        S (key m.val * Int.natAbs ((m.val:ℤ)-key m.val))=m.val := by
      dsimp [key]
      decide +kernel
    exact ⟨key n,tab ⟨n,small⟩ h⟩
  rcases h with e | e | e
  · omega
  · let v := S (3*n-1)
    have mod := (Nat.modEq_nine_digits_sum (3*n-1)).symm
    change v%9=(3*n-1)%9 at mod
    let t := (n+v-8)/9
    have exactSum : n+v=8+9*t := by dsimp [t]; omega
    apply witness (C := 3) (t := t) (by decide) (by omega) (ample (by omega) (by omega))
    change n+v=8+9*t
    exact exactSum
  · let v := S (n-1)
    have mod := (Nat.modEq_nine_digits_sum (n-1)).symm
    change v%9=(n-1)%9 at mod
    let t := (n+v)/9
    have exactSum : n+v=9*t := by dsimp [t]; omega
    have cap := ample (n := n) (t := t) (by omega) (by omega)
    apply witness (C := 1) (t := t) (by decide) (by omega) (by omega)
    simpa [v,S] using exactSum
variable (P : ℕ → Prop)
def F (m : ℕ) : ℕ := if m=0 then 0 else if m=1 then 4 else
  9*((m-2)/2)+5+4*(m%2)

lemma Fe (u : ℕ) : F (2*u+2)=9*u+5 := by
  unfold F
  rw [if_neg (by omega),if_neg (by omega),show (2*u+2-2)/2=u by omega,show (2*u+2)%2=0 by omega]
lemma Fo (u : ℕ) : F (2*u+3)=9*u+9 := by
  unfold F
  rw [if_neg (by omega),if_neg (by omega),show (2*u+3-2)/2=u by omega,show (2*u+3)%2=1 by omega]
lemma casesF (i : ℕ) : i=0 ∨ i=1 ∨ ∃ u : ℕ,i=2*u+2 ∨ i=2*u+3 := by
  by_cases a : i=0
  · exact Or.inl a
  by_cases b : i=1
  · exact Or.inr (Or.inl b)
  exact Or.inr (Or.inr ⟨(i-2)/2,by omega⟩)

lemma enumerates (hp : ∀ n : ℕ,P n ↔ n=4 ∨ n%9=0 ∨ n%9=5) (m : ℕ) : Nat.nth P m=F m := by
  have all (i : ℕ) : P (F i) := by
    rw [hp]
    rcases casesF i with rfl | rfl | ⟨u,rfl | rfl⟩
    · decide
    · decide
    · rw [Fe]; omega
    · rw [Fo]; omega
  have surj (n : ℕ) (h : P n) : ∃ i,F i=n := by
    rcases (hp n).mp h with e | e | e
    · exact ⟨1,by simp [F,e]⟩
    · by_cases hz : n=0
      · exact ⟨0,by simp [F,hz]⟩
      · exact ⟨2*(n/9-1)+3,by rw [Fo]; omega⟩
    · exact ⟨2*(n/9)+2,by rw [Fe]; omega⟩
  have mono : StrictMono F := by
    apply strictMono_nat_of_lt_succ
    intro i
    rcases casesF i with rfl | rfl | ⟨u,rfl | rfl⟩
    · decide
    · decide
    · change F (2*u+2)<F (2*u+3)
      rw [Fe,Fo]; omega
    · rw [show (2*u+3)+1=2*(u+1)+2 by omega,Fo,Fe]; omega
  have sub : Set.range F ⊆ Set.ofPred P := by
    rintro n ⟨i,rfl⟩
    exact all i
  have inf : (Set.ofPred P).Infinite := (Set.infinite_range_of_injective mono.injective).mono sub
  have every (i : ℕ) (fin : (Set.ofPred P).Finite) : i<fin.toFinset.card := (inf fin).elim
  exact (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn F (fun _ h => by
    obtain ⟨i,e⟩ := surj _ h; exact ⟨i,every i,e⟩)
    (fun i _ => all i) (mono.strictMonoOn _) (every m)).symm

def val (n : ℕ) := if n=0 then 0 else F (n-1)

lemma closed (n : ℕ) (h : 2<n) : (val n : ℤ)=(18*n-(-1)^n-35)/4 := by
  rcases Nat.even_or_odd n with ⟨u,e⟩ | ⟨u,e⟩
  · have pw : (-1:ℤ)^n=1 := by rw [e,pow_add]; have := neg_one_pow_eq_or ℤ u; rcases this with eq | eq <;> rw [eq] <;> norm_num
    rw [pw]
    unfold val F; split_ifs <;> omega
  · have pw : (-1:ℤ)^n= -1 := by rw [e,pow_add,pow_mul]; norm_num
    rw [pw]
    unfold val F; split_ifs <;> omega

lemma rec (n : ℕ) (h : 5<n) : (val n : ℤ)=val (n-1)+val (n-2)-val (n-3) := by
  unfold val F; split_ifs <;> omega

open PowerSeries
lemma series : PowerSeries.mk (fun n => (val n : ℚ)) * ((1-X)^2*(1+X)) =
    X^2*(4+X+4*X^3) := by
  let f := PowerSeries.mk (fun n => (val n : ℚ))
  change f*((1-X)^2*(1+X))=X^2*(4+X+4*X^3)
  have lhs : f*((1-X)^2*(1+X))=f-f*X^1-f*X^2+f*X^3 := by ring
  have rhs : (X:PowerSeries ℚ)^2*(4+X+4*X^3)=4 • X^2+X^3+4 • X^5 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,f,coeff_mk]
  by_cases small : n≤5
  · interval_cases n <;> norm_num [val,F]
  · have r : (val n:ℚ)=val (n-1)+val (n-2)-val (n-3) := by exact_mod_cast rec n (by omega)
    simp [show 1≤n by omega,show 2≤n by omega,show 3≤n by omega,show n≠2 by omega,show n≠3 by omega,show n≠5 by omega]
    linarith

open OMA.S_oeis_a120740
lemma seq (n : ℕ) : a n=val n := by
  have hp (m : ℕ) : IsTerm m ↔ m=4 ∨ m%9=0 ∨ m%9=5 :=
    ⟨necessary,sufficient⟩
  unfold a val
  split_ifs
  · rfl
  · exact enumerates IsTerm hp _
end Barker120740

theorem OMA.solution : type_of% @OMA.S_oeis_a120740.main := by
  simp only [Barker120740.seq]
  exact ⟨Barker120740.closed,Barker120740.rec,Barker120740.series⟩
