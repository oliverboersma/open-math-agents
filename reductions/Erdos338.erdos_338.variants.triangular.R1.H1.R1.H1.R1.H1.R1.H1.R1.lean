import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1

/-! For squarefree s = 3 mod 8 the discriminant is -s, and its real
quadratic character on positive integers is the Jacobi symbol modulo s.
Dirichlet's imaginary quadratic class number formula and Siegel's lower
bound for L(1,χ) imply the required estimate. Forgetting the sign of the
middle coefficient of a reduced form has fibers of size at most two. -/

namespace OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1
open Finset Real Filter
open scoped Topology

private lemma signs (s:ℕ) (hs:0<s) :
    let A := {v : ℤ×ℤ×ℤ | v.1>0 ∧ |v.2.1|≤v.1 ∧ v.1≤v.2.2 ∧ 4*v.1*v.2.2 = (s:ℤ)+v.2.1^2}
    let B := (((range (s+1)) ×ˢ ((range (s+1)) ×ˢ (range (s+1)))).filter
      (fun v : ℕ×ℕ×ℕ => 0<v.1 ∧ v.2.1≤v.1 ∧ v.1≤v.2.2 ∧ 4*v.1*v.2.2=s+v.2.1^2))
    A.ncard ≤ 2*B.card := by
  classical
  intro A B
  let f (v:ℤ×ℤ×ℤ) : Bool×(ℕ×ℕ×ℕ) := (decide (v.2.1<0),v.1.toNat,v.2.1.natAbs,v.2.2.toNat)
  have sub : ∀ v∈A, f v∈ ((univ:Finset Bool) ×ˢ B) := by
    rintro ⟨a,b,c⟩ ⟨ap,ba,ac,eq⟩
    change 0<a at ap
    change |b|≤a at ba
    change a≤c at ac
    change 4*a*c=(s:ℤ)+b^2 at eq
    have cp : 0<c := ap.trans_le ac
    have bb : b^2 ≤ a^2 := by nlinarith [mul_self_le_mul_self (abs_nonneg b) ba,sq_abs b]
    have A : a^2≤a*c := by nlinarith [mul_nonneg ap.le (sub_nonneg.mpr ac)]
    have cS : c ≤ (s:ℤ) := by nlinarith [mul_nonneg (show 0≤a-1 by omega) cp.le]
    have aa := Int.toNat_of_nonneg ap.le
    have cc := Int.toNat_of_nonneg cp.le
    have ab := Int.natCast_natAbs b
    change (decide (b<0),a.toNat,b.natAbs,c.toNat) ∈ (univ:Finset Bool) ×ˢ B
    apply mem_product.mpr
    refine ⟨mem_univ _,mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr ?_,mem_product.mpr ⟨mem_range.mpr ?_,mem_range.mpr ?_⟩⟩,?_,?_,?_,?_⟩⟩
    · change a.toNat<s+1; omega
    · change b.natAbs<s+1; omega
    · change c.toNat<s+1; omega
    · change 0<a.toNat; omega
    · change b.natAbs≤a.toNat; omega
    · change a.toNat≤c.toNat; omega
    · change 4*a.toNat*c.toNat=s+b.natAbs^2
      exact_mod_cast (show (4:ℤ)*(a.toNat:ℤ)*(c.toNat:ℤ)=(s:ℤ)+(b.natAbs:ℤ)^2 by rw [aa,cc,ab,sq_abs,eq])
  have inj : Set.InjOn f A := by
    rintro ⟨a,b,c⟩ ⟨ha,_,hc,_⟩ ⟨x,y,z⟩ ⟨hx,_,hz,_⟩ h
    change (decide (b<0),a.toNat,b.natAbs,c.toNat)=(decide (y<0),x.toNat,y.natAbs,z.toNat) at h
    simp only [Prod.mk.injEq] at h ⊢
    obtain ⟨sg,ax,byz,cz⟩ := h
    change 0<a at ha
    change 0<x at hx
    change a≤c at hc
    change x≤z at hz
    have sign : b<0 ↔ y<0 := by simpa using sg
    exact ⟨by omega,by omega,by omega⟩
  have h := Set.ncard_le_ncard_of_injOn f (t:=↑((univ:Finset Bool) ×ˢ B)) sub inj
  simpa using h

-- Siegel's theorem at exponent 1/8 for the negative fundamental
-- discriminants under consideration, in the Dirichlet series notation.
def H1 : Prop := ∃ c : ℝ, 0<c ∧ ∀ s : ℕ, 0<s → Squarefree s → s%8=3 →
  ∃ L:ℝ, Tendsto (fun N:ℕ => ∑ n∈Icc 1 N, (jacobiSym n s:ℝ)/(n:ℝ)) atTop (𝓝 L) ∧
    c*(s:ℝ)^(-(1/8:ℝ)) ≤ L

-- Dirichlet's class number formula followed by Gauss reduction. All
-- primitive reduced classes inject into this set of signed forms, and
-- extra boundary forms or extra units can only weaken the inequality.
def H2 : Prop := ∀ s : ℕ, 0<s → Squarefree s → s%8=3 →
  ∀ L:ℝ, Tendsto (fun N:ℕ => ∑ n∈Icc 1 N, (jacobiSym n s:ℝ)/(n:ℝ)) atTop (𝓝 L) →
  sqrt s*L ≤
    π*({v : ℤ×ℤ×ℤ | v.1>0 ∧ |v.2.1|≤v.1 ∧ v.1≤v.2.2 ∧ 4*v.1*v.2.2=(s:ℤ)+v.2.1^2}.ncard:ℝ)

theorem main : H1 → H2 → OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1.H1 := by
  rintro ⟨c,hc,hL⟩ hf
  refine ⟨c/(2*π),by positivity,?_⟩
  intro s hs hsq hm
  have p : 0<(s:ℝ) := by exact_mod_cast hs
  obtain ⟨L,lim,lower⟩ := hL s hs hsq hm
  have b := (mul_le_mul_of_nonneg_left lower (sqrt_nonneg _)).trans (hf s hs hsq hm L lim)
  have r := (Nat.cast_le (α:=ℝ)).mpr (signs s hs)
  rw [Nat.cast_mul,Nat.cast_ofNat] at r
  have upper := b.trans (mul_le_mul_of_nonneg_left r pi_pos.le)
  rw [sqrt_eq_rpow,show (s:ℝ)^(1/2:ℝ)*(c*(s:ℝ)^(-(1/8:ℝ)))=c*(s:ℝ)^(3/8:ℝ) by
    rw [mul_left_comm,←Real.rpow_add p]; norm_num] at upper
  apply (le_of_mul_le_mul_right _ (show (0:ℝ)<2*π by positivity))
  calc _ = c*(s:ℝ)^(3/8:ℝ) := by field_simp
       _ ≤ _ := by linarith only [upper]

end OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1
