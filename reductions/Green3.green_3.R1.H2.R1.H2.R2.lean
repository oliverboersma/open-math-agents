import OMAReductions.R_Green3_green_3_R1_H2_R1

/-! Franchi, Gowers and Yip, Product-free subsets of (0,1), section 2.
In logarithmic coordinates each occupied cell is an interval. Lemma 2.1
bounds three translates of the cumulative length of a sum-free union.
The Laplace integral then gives exactly the sum of the original cell lengths. -/
namespace OMA.R_Green3_green_3_R1_H2_R1_H2_R2
open Real Finset MeasureTheory

private lemma laplace (hinge : ∀ a : ℝ, 0≤a →
    IntegrableOn (fun u : ℝ => exp (-u)*max (u-a) 0) (Set.Ioi 0) ∧
    (∫ u in Set.Ioi (0:ℝ), exp (-u)*max (u-a) 0) = exp (-a))
    (S : Finset ℕ) (a b : ℕ → ℝ) (d : ℝ) (hd : 0≤d)
    (hab : ∀ i∈S, d≤a i ∧ a i≤b i)
    (h : let F (x:ℝ) := ∑ i ∈ S, (max (x-a i) 0 - max (x-b i) 0)
         ∀ u : ℝ, 0≤u → F (u-d)+F u+F (u+d) ≤ u) :
    3*(∑ i ∈ S, (exp (-(a i))-exp (-(b i)))) ≤ 1 := by
  let F (x:ℝ) := ∑ i ∈ S, (max (x-a i) 0 - max (x-b i) 0)
  let V := ∑ i ∈ S, (exp (-(a i))-exp (-(b i)))
  change ∀ u : ℝ, 0≤u → F (u-d)+F u+F (u+d) ≤ u at h
  have trans (z : ℝ) (hz : z≤d) :
      IntegrableOn (fun u : ℝ => exp (-u)*F (u+z)) (Set.Ioi 0) ∧
      (∫ u in Set.Ioi (0:ℝ), exp (-u)*F (u+z)) = exp z*V := by
    let f (i:ℕ) (u:ℝ) := exp (-u)*max (u-(a i-z)) 0 - exp (-u)*max (u-(b i-z)) 0
    have eq (u:ℝ) : exp (-u)*F (u+z) = ∑ i ∈ S, f i u := by
      rw [show F (u+z)=∑ i∈S, (max (u+z-a i) 0-max (u+z-b i) 0) by rfl,mul_sum]
      exact sum_congr rfl fun i _ => by dsimp [f]; rw [mul_sub]; congr 3 <;> ring
    have fi (i:ℕ) (hi:i∈S) : IntegrableOn (f i) (Set.Ioi 0) :=
      ((hinge _ (sub_nonneg.mpr (hz.trans (hab i hi).1))).1).sub
        ((hinge _ (sub_nonneg.mpr ((hz.trans (hab i hi).1).trans (hab i hi).2))).1)
    simp only [eq]
    refine ⟨integrable_finsetSum _ fi,?_⟩
    rw [integral_finsetSum _ fi]
    dsimp only [V]
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    obtain ⟨aI,aV⟩ := hinge (a i-z) (by linarith [(hab i hi).1])
    obtain ⟨bI,bV⟩ := hinge (b i-z) (by linarith [(hab i hi).1,(hab i hi).2])
    dsimp only [f]
    rw [integral_sub aI bI,aV,bV,show -(a i-z)=z+(-(a i)) by ring,show -(b i-z)=z+(-(b i)) by ring,exp_add,exp_add,mul_sub]
  obtain ⟨imin,vmin⟩ := trans (-d) (by linarith)
  obtain ⟨izero,vzero⟩ := trans 0 hd
  obtain ⟨imax,vmax⟩ := trans d le_rfl
  simp only [add_zero,exp_zero,one_mul] at izero vzero
  obtain ⟨ri,rv⟩ := hinge 0 le_rfl
  have le := setIntegral_mono_on ((imin.add izero).add imax) ri measurableSet_Ioi
    (fun u hu => show exp (-u)*F (u+-d)+exp (-u)*F u+exp (-u)*F (u+d) ≤ exp (-u)*max (u-0) 0 by
      rw [sub_zero,max_eq_left (le_of_lt hu),←mul_add,←mul_add,←sub_eq_add_neg]
      exact mul_le_mul_of_nonneg_left (h u (le_of_lt hu)) (exp_pos _).le)
  have e₁ := integral_add (imin.add izero) imax
  have e₂ := integral_add imin izero
  simp only [Pi.add_apply] at le e₁ e₂
  rw [e₁,e₂,vmin,vzero,vmax,rv] at le
  have vn : 0≤V := sum_nonneg fun i hi => sub_nonneg.mpr (exp_le_exp.mpr (neg_le_neg (hab i hi).2))
  have num : 2≤exp (-d)+exp d := by linarith [Real.add_one_le_exp d,Real.add_one_le_exp (-d)]
  change 3*V≤1
  simp only [neg_zero,Real.exp_zero] at le
  nlinarith only [le, mul_nonneg (sub_nonneg.mpr num) vn,Real.exp_zero]

-- The three-translate cumulative-length inequality of FGY Lemma 2.1,
-- specialized to a disjoint finite union of open intervals. Closed
-- approximations of the intervals give the same bound at their infimum.
def H1 : Prop := ∀ (S : Finset ℕ) (a b : ℕ → ℝ) (d : ℝ), 0<d →
  (∀ i∈S, d≤a i ∧ a i<b i) → (∃ i∈S, a i=d) →
  (∀ i∈S, ∀ j∈S, i≠j → b i≤a j ∨ b j≤a i) →
  (∀ i∈S, ∀ j∈S, ∀ l∈S, b i+b j≤a l ∨ b l≤a i+a j) →
  let F (x:ℝ) := ∑ i ∈ S, (max (x-a i) 0 - max (x-b i) 0)
  ∀ u : ℝ, 0≤u → F (u-d)+F u+F (u+d) ≤ u

-- The elementary Laplace transform of one translated positive part.
def H2 : Prop := ∀ a : ℝ, 0≤a →
    IntegrableOn (fun u : ℝ => exp (-u)*max (u-a) 0) (Set.Ioi 0) ∧
    (∫ u in Set.Ioi (0:ℝ), exp (-u)*max (u-a) 0) = exp (-a)

theorem main : H1 → H2 → OMA.R_Green3_green_3_R1_H2_R1.H2 := by
  intro geom hinge k m M S hM hMN hm hmax bounds _ hcard
  let N := 2^k
  change M≤N at hMN
  change N<3*S.card at hcard
  have np : 0<N := by dsimp [N]; positivity
  have xp : (0:ℝ)<N := by exact_mod_cast np
  by_contra! no
  change ∀ i∈S, ∀ j∈S, ∀ l∈S, i*j < (l+1)*N → (i+1)*(j+1) ≤ l*N at no
  have ip (i : ℕ) (hi : i∈S) : 0 < i := by
    by_contra! hz
    have e : i=0 := by omega
    subst i
    have v := no 0 hi 0 hi 0 hi (by simpa using np)
    simp at v
  have MN : M<N := by
    by_contra! hn
    have e : M=N := by omega
    let v := M-1
    have ev : v+1=N := by dsimp [v]; omega
    have vl : v<N := by omega
    have hless : v*v<(v+1)*N := by nlinarith [Nat.mul_lt_mul_of_pos_right vl np,Nat.mul_le_mul_left v vl.le]
    have impossible := no v hmax v hmax v hmax hless
    rw [ev] at impossible
    have := Nat.mul_lt_mul_of_pos_right vl np
    omega
  let a (i:ℕ) := -(log (((i:ℝ)+1)/N))
  let b (i:ℕ) := -(log ((i:ℝ)/N))
  let d := -(log ((M:ℝ)/N))
  have ea (i : ℕ) : exp (-(a i))=((i:ℝ)+1)/N := by dsimp [a]; rw [neg_neg,exp_log (by positivity)]
  have eb (i : ℕ) (hi : i∈S) : exp (-(b i))=(i:ℝ)/N := by
    dsimp [b]; rw [neg_neg,exp_log (div_pos (by exact_mod_cast ip i hi) xp)]
  have ed : exp (-d)=(M:ℝ)/N := by dsimp [d]; rw [neg_neg,exp_log (div_pos (by exact_mod_cast hM) xp)]
  have dp : 0<d := by
    dsimp [d]; exact neg_pos.mpr (log_neg (div_pos (by exact_mod_cast hM) xp)
      ((div_lt_one xp).mpr (by exact_mod_cast MN)))
  have ab (i:ℕ) (hi:i∈S) : d≤a i ∧ a i<b i := by
    constructor
    · apply le_of_neg_le_neg
      apply exp_le_exp.mp
      rw [ea,ed]
      exact div_le_div_of_nonneg_right (by exact_mod_cast (bounds i hi).2) xp.le
    · apply lt_of_neg_lt_neg
      apply exp_lt_exp.mp
      rw [eb i hi,ea]
      exact div_lt_div_of_pos_right (by linarith) xp
  have ex : ∃ i∈S,a i=d := by
    refine ⟨M-1,hmax,?_⟩
    apply neg_injective
    apply exp_injective
    rw [ea,ed]
    congr 1
    exact_mod_cast (Nat.sub_add_cancel hM : M-1+1=M)
  have sep (i j:ℕ) (hij:i<j) (hj:j∈S) : b j≤a i := by
    apply le_of_neg_le_neg
    apply exp_le_exp.mp
    rw [ea,eb j hj]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) xp.le
  have disjoint (i:ℕ) (hi:i∈S) (j:ℕ) (hj:j∈S) (hne:i≠j) : b i≤a j ∨ b j≤a i := by
    rcases lt_or_gt_of_ne hne with h|h
    · exact Or.inr (sep _ _ h hj)
    · exact Or.inl (sep _ _ h hi)
  have avoid (i:ℕ) (hi:i∈S) (j:ℕ) (hj:j∈S) (l:ℕ) (hl:l∈S) :
      b i+b j≤a l ∨ b l≤a i+a j := by
    by_cases h : i*j<(l+1)*N
    · have he := no i hi j hj l hl h
      right
      apply le_of_neg_le_neg
      apply exp_le_exp.mp
      rw [neg_add,exp_add,ea,ea,eb l hl,div_mul_div_comm,div_le_div_iff₀ (mul_pos xp xp) xp]
      have hr : ((i:ℝ)+1)*((j:ℝ)+1) ≤ l*(N:ℝ) := by exact_mod_cast he
      nlinarith only [mul_le_mul_of_nonneg_right hr xp.le]
    · left
      apply le_of_neg_le_neg
      apply exp_le_exp.mp
      rw [neg_add,exp_add,ea,eb i hi,eb j hj,div_mul_div_comm,div_le_div_iff₀ xp (mul_pos xp xp)]
      have hr : ((l:ℝ)+1)*N ≤ (i:ℝ)*j := by exact_mod_cast (le_of_not_gt h)
      nlinarith only [mul_le_mul_of_nonneg_right hr xp.le]
  have ht := laplace hinge S a b d dp.le (fun i hi => ⟨(ab i hi).1,(ab i hi).2.le⟩)
    (geom S a b d dp ab ex disjoint avoid)
  have eq : ∑ i ∈ S, (exp (-(a i))-exp (-(b i))) = (S.card:ℝ)/N := calc
    _ = ∑ _i ∈ S, (1/(N:ℝ)) := sum_congr rfl fun i hi => by rw [ea,eb i hi]; ring
    _ = _ := by simp [div_eq_mul_inv]
  rw [eq] at ht
  have hr : (N:ℝ)<3*(S.card:ℝ) := by exact_mod_cast hcard
  nlinarith only [(div_le_iff₀ xp).mp (by simpa only [mul_div_assoc] using ht : (3*(S.card:ℝ))/(N:ℝ)≤1),hr]

end OMA.R_Green3_green_3_R1_H2_R1_H2_R2
