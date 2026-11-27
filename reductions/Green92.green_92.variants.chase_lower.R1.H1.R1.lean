import OMAReductions.R_Green92_green_92_variants_chase_lower_R1

/-! Chase's lower bound at deletion probability one half. The two inputs
are single-trace estimates for the explicit pair of defect strings:
concentration of the length and number of contiguous 01 pairs, and the
quadratic discrepancy on the typical set. We derive the many-sample
testing inequality by tensorizing the Hellinger affinity. -/
namespace OMA.R_Green92_green_92_variants_chase_lower_R1_H1_R1
open Finset Real Filter
open scoped Classical

private lemma joint {α β:Type} [Fintype α] [Fintype β] [DecidableEq β] (m:ℕ)
    (f:α→β) (T:Finset (Fin m→β)) :
    ((univ.filter (fun a:Fin m→α => (fun j => f (a j))∈T)).card:ℝ)/Fintype.card (Fin m→α) =
    ∑ w∈T,∏ j,(((univ.filter (fun a => f a=w j)).card:ℝ)/Fintype.card α) := by
  classical
  have ff (w:Fin m→β) : univ.filter (fun a:Fin m→α => (fun j => f (a j))=w) =
      Fintype.piFinset (fun j => univ.filter (fun a => f a=w j)) := by
    ext a; simp [funext_iff]
  have h := sum_card_fiberwise_eq_card_filter (univ:Finset (Fin m→α)) T (fun a j => f (a j))
  simp_rw [ff,Fintype.card_piFinset] at h
  rw [←h,Nat.cast_sum,Finset.sum_div]
  apply sum_congr rfl
  intro w _
  rw [Nat.cast_prod,Finset.prod_div_distrib]
  simp

private lemma total {α β:Type} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β] (f:α→β) :
    (∑ w:β,(((univ.filter (fun a => f a=w)).card:ℝ)/Fintype.card α))=1 := by
  classical
  have e := sum_card_fiberwise_eq_card_filter (univ:Finset α) (univ:Finset β) f
  rw [←Finset.sum_div,←Nat.cast_sum,e]
  simp

private lemma independent {β:Type} [Fintype β] (m:ℕ) (F:β→ℝ) :
    ∑ w:Fin m→β,∏ j,F (w j)=(∑ u,F u)^m := by
  classical
  simpa using (sum_pow' (univ:Finset β) F m).symm

private lemma testing {α β:Type} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (f g:α→β) (m:ℕ) (T:Finset (Fin m→β))
    (successF:(9/10:ℝ)≤((univ.filter (fun a:Fin m→α => (fun j => f (a j))∈T)).card:ℝ)/Fintype.card (Fin m→α))
    (successG:(9/10:ℝ)≤((univ.filter (fun a:Fin m→α => (fun j => g (a j))∈Tᶜ)).card:ℝ)/Fintype.card (Fin m→α)) :
    let P := fun w => ((univ.filter (fun a => f a=w)).card:ℝ)/Fintype.card α
    let Q := fun w => ((univ.filter (fun a => g a=w)).card:ℝ)/Fintype.card α
    1/3 ≤ (m:ℝ)* ∑ w:β,(sqrt (P w)-sqrt (Q w))^2 := by
  classical
  intro P Q
  let U (w:Fin m→β) := ∏ j,P (w j)
  let V (w:Fin m→β) := ∏ j,Q (w j)
  let a := ∑ w:β,sqrt (P w)*sqrt (Q w)
  have p0 (w) : 0≤ P w := by dsimp [P];positivity
  have q0 (w) : 0≤ Q w := by dsimp [Q];positivity
  have u0 (w) : 0≤ U w := prod_nonneg fun j _ => p0 _
  have v0 (w) : 0≤ V w := prod_nonneg fun j _ => q0 _
  have sp : ∑ w,P w=1 := total f
  have sq : ∑ w,Q w=1 := total g
  have a0 : 0≤ a := sum_nonneg (fun _ _ => by positivity)
  have a1 : a≤1 := by
    have e := sum_sqrt_mul_sqrt_le (univ:Finset β) p0 q0
    simpa [a,sp,sq] using e
  have su : ∑ w,U w=1 := by simpa [U,sp] using independent m P
  have sv : ∑ w,V w=1 := by simpa [V,sq] using independent m Q
  have tu := Finset.sum_add_sum_compl T U
  have tv := Finset.sum_add_sum_compl T V
  rw [joint] at successF successG
  change 9/10≤∑ w∈T,U w at successF
  change 9/10≤∑ w∈Tᶜ,V w at successG
  have ut := sum_nonneg (s:=T) (fun w _ => u0 w)
  have uc := sum_nonneg (s:=Tᶜ) (fun w _ => u0 w)
  have vt := sum_nonneg (s:=T) (fun w _ => v0 w)
  have vc := sum_nonneg (s:=Tᶜ) (fun w _ => v0 w)
  have cut (L:Finset (Fin m→β)) (X Y:(Fin m→β)→ℝ) (x0:∀ w,0≤ X w) (y0:∀ w,0≤ Y w)
      (xl:∑ w∈L,X w≤1) (yl:∑ w∈L,Y w≤1/10) :
      ∑ w∈L,sqrt (X w)*sqrt (Y w)≤1/3 := by
    refine (sum_sqrt_mul_sqrt_le L x0 y0).trans ?_
    have xx : sqrt (∑ w∈L,X w)≤1 := by simpa using sqrt_le_sqrt xl
    have yy : sqrt (∑ w∈L,Y w)≤1/3 := (sqrt_le_iff).mpr ⟨by norm_num,by linarith⟩
    simpa using mul_le_mul xx yy (sqrt_nonneg _) zero_le_one
  have left := cut T U V u0 v0 (by linarith only [tu,su,uc]) (by linarith only [tv,sv,successG])
  have right := cut Tᶜ V U v0 u0 (by linarith only [tv,sv,vt]) (by linarith only [tu,su,successF])
  have tensor : (∑ w:Fin m→β,sqrt (U w)*sqrt (V w))=a^m := by
    rw [←independent m (fun w => sqrt (P w)*sqrt (Q w))]
    apply sum_congr rfl
    intro w _
    rw [Finset.prod_mul_distrib,Real.sqrt_prod univ (fun j _ => p0 _),Real.sqrt_prod univ (fun j _ => q0 _)]
  have split := sum_add_sum_compl T (fun w => sqrt (U w)*sqrt (V w))
  simp_rw [mul_comm (sqrt (V _)) (sqrt (U _))] at right
  have slack : 1/3≤1-a^m := by linarith only [split,tensor,left,right]
  have bern : ∀ j:ℕ, 1-a^j≤(j:ℝ)*(1-a) := by
    intro j;induction j with
    | zero => simp
    | succ j ih =>
      have b := pow_le_one₀ a0 a1 (n:=j)
      rw [pow_succ,Nat.cast_succ]
      nlinarith only [ih,mul_le_mul_of_nonneg_right b (sub_nonneg.mpr a1)]
  have eq : ∑ w:β,(sqrt (P w)-sqrt (Q w))^2=2*(1-a) := by
    calc _ = ∑ w:β,(P w+Q w-2*(sqrt (P w)*sqrt (Q w))) := by
           apply sum_congr rfl;intro w _;nlinarith only [sq_sqrt (p0 w),sq_sqrt (q0 w)]
         _ = _ := by rw [sum_sub_distrib,sum_add_distrib,←mul_sum,sp,sq];dsimp [a];ring
  rw [eq]
  nlinarith only [slack,bern m,mul_nonneg (Nat.cast_nonneg m (α:=ℝ)) (sub_nonneg.mpr a1)]

-- Concentration of the trace length and the number of contiguous 01 pairs.
def H1 : Prop := ∃ C:ℝ, 0< C ∧ ∀ᶠ n:ℕ in atTop,n%4=3 →
  let k := n/4
  let W (b:ℕ) (i:Fin n) : Bool := decide (i.val%2=if i.val<2*b then 1 else 0)
  let p (b:ℕ) (w:List Bool) := ((univ.filter (fun S:Finset (Fin n) => Green92.trace (W b) S=w)).card:ℝ)/Fintype.card (Finset (Fin n))
  let T := univ.image (Green92.trace (W k)) ∪ univ.image (Green92.trace (W (k+1)))
  let E (w:List Bool) := |(w.length:ℝ)-2*k|≤ sqrt k*log k ∧
    |(((w.zip w.tail).count (false,true):ℕ):ℝ)-2*k/3|≤ sqrt k*log k
  ∑ w∈T.filter (fun w => ¬E w),(p k w+p (k+1) w) ≤ C*(log n)^7/(n:ℝ)^(3/2:ℝ)

-- Chase's single-trace quadratic discrepancy estimate on the typical set.
def H2 : Prop := ∃ C:ℝ, 0< C ∧ ∀ᶠ n:ℕ in atTop,n%4=3 →
  let k := n/4
  let W (b:ℕ) (i:Fin n) : Bool := decide (i.val%2=if i.val<2*b then 1 else 0)
  let p (b:ℕ) (w:List Bool) := ((univ.filter (fun S:Finset (Fin n) => Green92.trace (W b) S=w)).card:ℝ)/Fintype.card (Finset (Fin n))
  let T := univ.image (Green92.trace (W k)) ∪ univ.image (Green92.trace (W (k+1)))
  let E (w:List Bool) := |(w.length:ℝ)-2*k|≤ sqrt k*log k ∧
    |(((w.zip w.tail).count (false,true):ℕ):ℝ)-2*k/3|≤ sqrt k*log k
  ∑ w∈T.filter E,(sqrt (p k w)-sqrt (p (k+1) w))^2 ≤ C*(log n)^7/(n:ℝ)^(3/2:ℝ)

theorem main : H1 → H2 → OMA.R_Green92_green_92_variants_chase_lower_R1.H1 := by
  classical
  rintro ⟨C,hC,tail⟩ ⟨B,hB,typ⟩
  refine ⟨1/(3*(C+B)),by positivity,?_⟩
  filter_upwards [tail,typ,eventually_ge_atTop 7] with n tail typ n7
  intro seven
  let k := n/4
  let W (b:ℕ) (i:Fin n) : Bool := decide (i.val%2=if i.val<2*b then 1 else 0)
  let p (b:ℕ) (w:List Bool) := ((univ.filter (fun S:Finset (Fin n) => Green92.trace (W b) S=w)).card:ℝ)/Fintype.card (Finset (Fin n))
  let T := univ.image (Green92.trace (W k)) ∪ univ.image (Green92.trace (W (k+1)))
  let E (w:List Bool) := |(w.length:ℝ)-2*k|≤ sqrt k*log k ∧
    |(((w.zip w.tail).count (false,true):ℕ):ℝ)-2*k/3|≤ sqrt k*log k
  have off := tail seven
  have on := typ seven
  change ∑ w∈T.filter (fun w => ¬E w),(p k w+p (k+1) w) ≤ _ at off
  change ∑ w∈T.filter E,(sqrt (p k w)-sqrt (p (k+1) w))^2 ≤ _ at on
  have p0 (b:ℕ) (w:List Bool) : 0≤ p b w := by dsimp [p];positivity
  let F (w:List Bool) := (sqrt (p k w)-sqrt (p (k+1) w))^2
  have rem := sum_le_sum (s:=T.filter (fun w => ¬E w)) (fun w _ => show F w≤ p k w+p (k+1) w by
    dsimp [F];nlinarith only [sq_sqrt (p0 k w),sq_sqrt (p0 (k+1) w),mul_nonneg (sqrt_nonneg (p k w)) (sqrt_nonneg (p (k+1) w))])
  have partition := sum_filter_add_sum_filter_not T E F
  have dist : (∑ w∈T,F w)≤(C+B)*(log n)^7/(n:ℝ)^(3/2:ℝ) := by
    change (∑ w∈T.filter E,F w) ≤ _ at on
    rw [add_mul,add_div]
    linarith only [partition,on,off,rem]
  let i : Fin n := ⟨2*k,by dsimp [k];omega⟩
  have different : W k≠W (k+1) := by
    intro eq
    have hh := congrFun eq i
    have lt : 2*k<2*(k+1) := by omega
    simp [W,i,lt] at hh
  refine ⟨W k,W (k+1),different,?_⟩
  intro m D a b
  let f (S:Finset (Fin n)) : T := ⟨Green92.trace (W k) S,mem_union_left _ (mem_image_of_mem _ (mem_univ _))⟩
  let g (S:Finset (Fin n)) : T := ⟨Green92.trace (W (k+1)) S,mem_union_right _ (mem_image_of_mem _ (mem_univ _))⟩
  let event := univ.filter (fun w:Fin m→T => D (fun j => (w j).val))
  have test := testing f g m event (by simpa [event,f] using a) (by simpa [event,g] using b)
  have fp (w:T) : (univ.filter (fun S => f S=w)).card=(univ.filter (fun S => Green92.trace (W k) S=w.val)).card := by
    congr 1;ext S;simp [f,Subtype.ext_iff]
  have gp (w:T) : (univ.filter (fun S => g S=w)).card=(univ.filter (fun S => Green92.trace (W (k+1)) S=w.val)).card := by
    congr 1;ext S;simp [g,Subtype.ext_iff]
  dsimp only at test
  simp_rw [fp,gp] at test
  change 1/3≤(m:ℝ)* ∑ w:T,F w.val at test
  rw [Finset.sum_coe_sort] at test
  have bound := test.trans (mul_le_mul_of_nonneg_left dist (Nat.cast_nonneg m (α:=ℝ)))
  have npos : 0<(n:ℝ) := by exact_mod_cast (show 0< n by omega)
  have logpos : 0< log (n:ℝ) := log_pos (by exact_mod_cast (show 1< n by omega))
  apply (div_le_iff₀ (by positivity)).mpr
  apply le_of_mul_le_mul_left (a:=3*(C+B)) _ (by positivity)
  have q : 3*(C+B)*(1/(3*(C+B))*(n:ℝ)^(3/2:ℝ))=(n:ℝ)^(3/2:ℝ) := by field_simp
  rw [q]
  have scaled := mul_le_mul_of_nonneg_right bound (rpow_pos_of_pos npos (3/2:ℝ)).le
  have cancel : (C+B)*(log (n:ℝ))^7/(n:ℝ)^(3/2:ℝ)*(n:ℝ)^(3/2:ℝ)=(C+B)*(log (n:ℝ))^7 :=
    div_mul_cancel₀ _ (rpow_pos_of_pos npos _).ne'
  rw [mul_assoc (m:ℝ),cancel] at scaled
  nlinarith only [scaled]

end OMA.R_Green92_green_92_variants_chase_lower_R1_H1_R1
