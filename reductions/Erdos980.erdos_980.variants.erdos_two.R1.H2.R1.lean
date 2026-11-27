import OMAReductions.R_Erdos980_erdos_980_variants_erdos_two_R1

/-!
A reciprocal square-root bound and a growing cutoff reduce the weighted
tail to two unweighted sieve estimates. The exceptional primitive character
estimate is Lemma 2.5 of P. Pollack, The smallest inert prime in a cyclic number field of prime degree.
-/

namespace OMA.R_Erdos980_erdos_980_variants_erdos_two_R1_H2_R1

open Erdos980 Finset Filter Asymptotics
open scoped Classical Topology BigOperators

/-- A Brun–Titchmarsh upper bound for simultaneous quadratic-residue patterns,
uniform through logarithmically many prescribed primes. -/
def H1 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ j : ℕ, 16 ≤ j →
    (2:ℝ)^j ≤ (Real.log x)^10 →
    (((Nat.primesBelow ⌈x⌉₊).filter (fun p => p%2=1 ∧
      ∀ i < j, ∃ y : ZMod p, y^2=(Nat.nth Nat.Prime i : ZMod p))).card : ℝ) *
      (Real.log x/x) ≤ C/(2:ℝ)^j

/-- A special case of Pollack's multiplicative large-sieve exceptional-set
estimate with A=8: the exponent 1/3 is larger than 2/8. -/
def H2 : Prop := ∀ᶠ x : ℝ in atTop,
    (((Nat.primesBelow ⌈x⌉₊).filter (fun p => p%2=1 ∧
      (Real.log x)^8 < (leastNonresidue 2 p : ℝ))).card : ℝ) ≤ x^((1:ℝ)/3)

section Proof

private theorem smaller_square (p b : ℕ) (hb : b < leastNonresidue 2 p) :
    ∃ y : ZMod p, y^2=(b:ZMod p) := by
  by_cases h0 : b=0
  · exact ⟨0,by simp [h0]⟩
  by_contra h
  exact (not_le_of_gt hb) (Nat.sInf_le (s:={n : ℕ | 0 < n ∧ ¬∃ y : ZMod p,y^2=(n:ZMod p)})
    ⟨Nat.pos_of_ne_zero h0,h⟩)

/-- A uniform elementary bound. If a(a−1)≥p, both ceil(p/a) and
a*ceil(p/a)−p would be smaller squares, making a itself a square. -/
theorem pointwise (p : ℕ) (hp : p.Prime) :
    let a := leastNonresidue 2 p
    a*(a-1) < p := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let a := leastNonresidue 2 p
  by_cases ha : a=0
  · change a*(a-1) < p; simp [ha,hp.pos]
  let S := {v : ℕ | 0 < v ∧ ¬∃ y : ZMod p,y^2=(v:ZMod p)}
  have non : S.Nonempty := by
    by_contra empty
    have hs := Set.not_nonempty_iff_eq_empty.mp empty
    exact ha (by change sInf S=0; simp [hs])
  have haS : a∈S := Nat.sInf_mem non
  obtain ⟨apos,notSq⟩ := haS
  have ap : a < p := by
    have noMod : ¬∃ y : ZMod p, y^2=((a%p:ℕ):ZMod p) := by rwa [ZMod.natCast_mod]
    have nz : a%p≠0 := fun h => noMod ⟨0,by simp [h]⟩
    exact (Nat.sInf_le (s:=S) ⟨Nat.pos_of_ne_zero nz,noMod⟩).trans_lt (Nat.mod_lt _ hp.pos)
  change a*(a-1) < p
  by_contra! h
  let q := (p-1)/a+1
  have qa : q < a := by
    have divlt : (p-1)/a < a-1 := (Nat.div_lt_iff_lt_mul apos).mpr (by
      rw [Nat.mul_comm]; omega)
    dsimp [q]; omega
  have qp : 0 < q ∧ q < p := ⟨Nat.succ_pos _,qa.trans ap⟩
  let r := a*q-p
  have recomb : a*q=p+r ∧ r < a := by
    have er := Nat.mod_add_div (p-1) a
    have rem := Nat.mod_lt (p-1) apos
    have eq : a*q=a*((p-1)/a)+a := by dsimp [q]; ring
    dsimp [r]; omega
  obtain ⟨u,hu⟩ := smaller_square p q qa
  obtain ⟨v,hv⟩ := smaller_square p r recomb.2
  have qu : (q:ZMod p)≠0 := by
    intro e
    have hz := (ZMod.natCast_eq_zero_iff _ _).mp e
    exact (not_le_of_gt qp.2) (Nat.le_of_dvd qp.1 hz)
  have u0 : u≠0 := fun h => qu (by simpa [h] using hu.symm)
  have prod : (a:ZMod p)*q=(r:ZMod p) := by
    have eq := congrArg (fun n : ℕ => (n:ZMod p)) recomb.1
    simpa using eq
  apply notSq
  exact ⟨v/u,by rw [div_pow,hv,hu,div_eq_iff qu,prod]⟩

private theorem rootBound {p : ℕ} (hp : p.Prime) {x : ℝ} (px : (p:ℝ) ≤ x) :
    (leastNonresidue 2 p : ℝ) ≤ 2*Real.sqrt x := by
  let a := leastNonresidue 2 p
  have ht : a*(a-1) < p := pointwise p hp
  have hsq : a^2 ≤ 4*p := by
    cases h : a with
    | zero => simp
    | succ n =>
      rw [h,Nat.succ_sub_one] at ht
      nlinarith [hp.pos]
  have sqR : (a:ℝ)^2 ≤ 4*(p:ℝ) := by exact_mod_cast hsq
  have sx := Real.sq_sqrt (show 0 ≤ x from (Nat.cast_nonneg p).trans px)
  change (a:ℝ) ≤ 2*Real.sqrt x
  nlinarith [Real.sqrt_nonneg x,sq_nonneg ((a:ℝ)-2*Real.sqrt x)]

/-- Sum the middle layers and keep the two exceptional pieces unweighted. -/
private theorem weights (T : Finset ℕ) (v : ℕ → ℕ) {K J : ℕ} (hK : 1 ≤ K)
    (hKJ : K ≤ J) (starts : ∀ p∈T,K^2 ≤ v p) {w C L B : ℝ}
    (hw : 0 ≤ w) (hC : 0 ≤ C) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (point : ∀ p∈T,(v p:ℝ) ≤ B)
    (count : ∀ j ∈ Icc K J, ((T.filter fun p => j^2 ≤ v p).card:ℝ)*w ≤ C/(2:ℝ)^j) :
    (∑ p ∈ T,(v p:ℝ))*w ≤ 22*C*((K:ℝ)^2/(2:ℝ)^K) +
      L*(C/(2:ℝ)^J) + B*((T.filter fun p => L < (v p:ℝ)).card:ℝ)*w := by
  classical
  let F (j : ℕ) : ℝ := (2*(j:ℝ)^2+8*j+12)/2^j
  have telescopes (j : ℕ) : ((j:ℝ)+1)^2/(2:ℝ)^j=F j-F (j+1) := by
    simp only [F,Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp; ring
  have sumF : ∑ j ∈ Ico K J,((j:ℝ)+1)^2/(2:ℝ)^j=F K-F J := by
    clear count
    induction J, hKJ using Nat.le_induction with
    | base => simp
    | succ t ht ih => rw [sum_Ico_succ_top ht,ih,telescopes]; ring
  have FK : F K ≤ 22*((K:ℝ)^2/(2:ℝ)^K) := by
    have kR : 1 ≤ (K:ℝ) := by exact_mod_cast hK
    dsimp [F]
    rw [← mul_div_assoc,div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr kR) (show 0 ≤ (K:ℝ) by positivity), sq_nonneg ((K:ℝ)-1)]
  let layer (j p : ℕ) : ℝ := if j^2 ≤ v p then ((j:ℝ)+1)^2 else 0
  let mid (p : ℕ) : ℝ := if J^2 ≤ v p then L else 0
  let far (p : ℕ) : ℝ := if L < (v p:ℝ) then B else 0
  have cost (p) (hp:p∈T) : (v p:ℝ) ≤ (∑ j ∈ Ico K J,layer j p)+mid p+far p := by
    have nonneg (j : ℕ) : 0 ≤ layer j p := by dsimp [layer]; split <;> positivity
    have hs := sum_nonneg (s:=Ico K J) (fun j _ => nonneg j)
    have hm : 0 ≤ mid p := by dsimp [mid]; split <;> positivity
    have hf : 0 ≤ far p := by dsimp [far]; split <;> positivity
    by_cases big : L < (v p:ℝ)
    · rw [show far p=B from if_pos big]; linarith [point p hp]
    by_cases last : J^2 ≤ v p
    · rw [show mid p=L from if_pos last]; linarith
    let j := Nat.sqrt (v p)
    have low : j^2 ≤ v p := Nat.sqrt_le' _
    have high : v p < (j+1)^2 := Nat.lt_succ_sqrt' _
    have jmin : K ≤ j := by
      by_contra! h
      have fromStart := starts p hp
      have := Nat.pow_le_pow_left (show j+1 ≤ K by omega) 2
      omega
    have jmax : j < J := by
      by_contra! h; exact last ((Nat.pow_le_pow_left h 2).trans low)
    have hj : layer j p ≤ ∑ l ∈ Ico K J,layer l p :=
      single_le_sum (f:=fun l => layer l p) (fun l _ => nonneg l) (mem_Ico.mpr ⟨jmin,jmax⟩)
    rw [show layer j p=((j:ℝ)+1)^2 from if_pos low] at hj
    have vR : (v p:ℝ) ≤ ((j:ℝ)+1)^2 := by exact_mod_cast high.le
    linarith
  have indicator (pred : ℕ → Prop) [DecidablePred pred] (z : ℝ) :
      (∑ p ∈ T,if pred p then z else 0)=((T.filter pred).card:ℝ)*z := by
    rw [←sum_filter]; simp
  have avg : (∑ p ∈ T,(v p:ℝ))*w ≤ 
      (∑ j ∈ Ico K J,((T.filter fun p => j^2 ≤ v p).card:ℝ)*((j:ℝ)+1)^2)*w +
      (((T.filter fun p => J^2 ≤ v p).card:ℝ)*L)*w +
      (((T.filter fun p => L < (v p:ℝ)).card:ℝ)*B)*w := by
    have h := mul_le_mul_of_nonneg_right (sum_le_sum cost) hw
    simp only [sum_add_distrib,add_mul] at h
    rw [sum_comm (s:=T) (t:=Ico K J)] at h
    simpa only [layer,mid,far,indicator] using h
  have layers : (∑ j ∈ Ico K J,((T.filter fun p => j^2 ≤ v p).card:ℝ)*((j:ℝ)+1)^2)*w
 ≤ 22*C*((K:ℝ)^2/(2:ℝ)^K) := by
    rw [sum_mul]
    calc (∑ j ∈ Ico K J,((T.filter fun p => j^2 ≤ v p).card:ℝ)*((j:ℝ)+1)^2*w)
 ≤ ∑ j ∈ Ico K J,C*(((j:ℝ)+1)^2/2^j) := sum_le_sum <| by
            intro j hj
            have h := count j (mem_Icc.mpr ⟨(mem_Ico.mp hj).1,(mem_Ico.mp hj).2.le⟩)
            convert mul_le_mul_of_nonneg_right h (sq_nonneg ((j:ℝ)+1)) using 1 <;> ring
      _ = C*(F K-F J) := by rw [←Finset.mul_sum,sumF]
      _ ≤ C*(22*((K:ℝ)^2/2^K)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        have : 0 ≤ F J := by dsimp [F]; positivity
        linarith
      _ = _ := by ring
  have middle := mul_le_mul_of_nonneg_left (count J (mem_Icc.mpr ⟨hKJ,le_rfl⟩)) hL
  linarith only [avg,layers,middle]

theorem main : H1 → H2 → OMA.R_Erdos980_erdos_980_variants_erdos_two_R1.H2 := by
  classical
  rintro ⟨C,hC,sieve⟩ exceptional ε hε
  have vanish : Tendsto (fun j : ℕ => 22*C*((j:ℝ)^2/(2:ℝ)^j)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : 1 < (2:ℝ))).const_mul (22*C)
  obtain ⟨K,hK₀,hK⟩ := ((eventually_ge_atTop 16).and
    (vanish.eventually_lt_const (by linarith : 0<ε/3))).exists
  filter_upwards [eventually_ge_atTop (K^2)] with k hk
  have high : ∀ᶠ x : ℝ in atTop,
      2*Real.sqrt x*x^((1:ℝ)/3)*(Real.log x/x) ≤ ε/3 := by
    have little := (isLittleO_log_rpow_atTop (by norm_num : 0 < (1:ℝ)/6)).bound
      (by positivity : 0<ε/6)
    filter_upwards [little,eventually_gt_atTop (1:ℝ)] with x hl hx
    have xp : 0 < x := by linarith
    change ‖Real.log x‖ ≤ ε/6*‖x^((1:ℝ)/6)‖ at hl
    rw [Real.norm_of_nonneg (Real.log_nonneg hx.le),Real.norm_of_nonneg (Real.rpow_nonneg xp.le _)] at hl
    have mult : Real.sqrt x*x^((1:ℝ)/3)*x^((1:ℝ)/6)=x := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_add xp,←Real.rpow_add xp]
      norm_num
    rw [←mul_div_assoc,div_le_iff₀ xp]
    calc 2*Real.sqrt x*x^((1:ℝ)/3)*Real.log x
 ≤ 2*Real.sqrt x*x^((1:ℝ)/3)*(ε/6*x^((1:ℝ)/6)) :=
          mul_le_mul_of_nonneg_left hl (by positivity)
      _ = ε/3*x := by
        calc _ = ε/3*(Real.sqrt x*x^((1:ℝ)/3)*x^((1:ℝ)/6)) := by ring
             _ = _ := by rw [mult]
  filter_upwards [sieve,exceptional,high,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max ((2:ℝ)^K) (6*C/ε+1))] with x hs he hh hx hlog
  let L := Real.log x
  let w := L/x
  have xp : 0 < x := by linarith
  have lp : 0 < L := Real.log_pos hx
  have hw : 0 ≤ w := div_nonneg lp.le xp.le
  have lK : (2:ℝ)^K ≤ L := (le_max_left ..).trans hlog
  have lC : 6*C/ε+1 ≤ L := (le_max_right ..).trans hlog
  have l1 : 1 ≤ L := (one_le_pow₀ (by norm_num : 1 ≤ (2:ℝ))).trans lK
  have Lten : L ≤ L^10 := by simpa only [pow_one] using (pow_le_pow_right₀ l1 (by decide : 1 ≤ 10))
  obtain ⟨J,jlo,jhi⟩ := exists_nat_pow_near (l1.trans Lten) (by norm_num : 1 < (2:ℝ))
  have KJ : K ≤ J := by
    by_contra! h
    have h' := pow_le_pow_right₀ (by norm_num : 1 ≤ (2:ℝ)) (show J+1 ≤ K by omega)
    linarith only [h',lK,Lten,jhi]
  have mid : L^8*(C/(2:ℝ)^J) ≤ ε/3 := by
    rw [←mul_div_assoc,div_le_iff₀ (by positivity)]
    rw [pow_succ (2:ℝ) J] at jhi
    have lc : 6*C ≤ ε*L := by
      have := (div_le_iff₀ hε).mp (show 6*C/ε ≤ L by linarith); linarith
    have lc' : 6*C ≤ ε*L^2 := lc.trans (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (L-1)]) hε.le)
    have z := mul_le_mul_of_nonneg_right lc' (show 0 ≤ L^8 by positivity)
    have z' := mul_le_mul_of_nonneg_left jhi.le hε.le
    nlinarith only [z,z']
  let T := (Nat.primesBelow ⌈x⌉₊).filter fun p => p%2=1 ∧ Nat.nth Nat.Prime k ≤ leastNonresidue 2 p
  let v := leastNonresidue 2
  have starts (p) (hp:p∈T) : K^2 ≤ v p := by
    have monotone := Nat.nth_strictMono Nat.infinite_setOfPred_prime
    exact hk.trans ((monotone.id_le k).trans (mem_filter.mp hp).2.2)
  have point (p) (hp:p∈T) : (v p:ℝ) ≤ 2*Real.sqrt x := by
    have mem := Nat.mem_primesBelow.mp (mem_filter.mp hp).1
    exact rootBound mem.2 (Nat.lt_ceil.mp mem.1).le
  have count (j) (hj:j∈Icc K J) :
      ((T.filter fun p => j^2 ≤ v p).card:ℝ)*w ≤ C/(2:ℝ)^j := by
    obtain ⟨hjk,hjJ⟩ := mem_Icc.mp hj
    have j₀ : 16 ≤ j := by omega
    have hpat := hs j j₀ ((pow_le_pow_right₀ (by norm_num : 1 ≤ (2:ℝ)) hjJ).trans jlo)
    apply le_trans _ hpat
    apply mul_le_mul_of_nonneg_right _ hw
    apply Nat.cast_le.mpr
    apply card_le_card
    intro p hp
    obtain ⟨ht,hv⟩ := mem_filter.mp hp
    obtain ⟨hprime,ho,_⟩ := mem_filter.mp ht
    refine mem_filter.mpr ⟨hprime,ho,fun i hi => smaller_square p _ ?_⟩
    have lt := (Nat.nth_strictMono Nat.infinite_setOfPred_prime) hi
    exact lt.trans_le ((OMA.R_Erdos980_erdos_980_variants_erdos_two_R1.key j j₀).trans hv)
  have exSize : ((T.filter fun p => L^8 < (v p:ℝ)).card:ℝ) ≤ x^((1:ℝ)/3) := by
    apply le_trans _ he
    apply Nat.cast_le.mpr
    apply card_le_card
    intro p hp
    obtain ⟨ht,hv⟩ := mem_filter.mp hp
    obtain ⟨hprime,ho,_⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨hprime,ho,hv⟩
  have est := weights T v (by omega : 1 ≤ K) KJ starts hw hC.le
    (show 0 ≤ L^8 by positivity) (show 0 ≤ 2*Real.sqrt x by positivity) point count
  have large : 2*Real.sqrt x*((T.filter fun p => L^8 < (v p:ℝ)).card:ℝ)*w ≤ ε/3 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left exSize (by positivity)) hw).trans hh
  change (∑ p ∈ T,(v p:ℝ))*w ≤ ε
  linarith only [est,hK,mid,large]

end Proof

end OMA.R_Erdos980_erdos_980_variants_erdos_two_R1_H2_R1
