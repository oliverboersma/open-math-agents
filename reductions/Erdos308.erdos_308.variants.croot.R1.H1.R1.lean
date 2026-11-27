import OMAReductions.R_Erdos308_erdos_308_variants_croot_R1
import Mathlib

/-!
# Croot's constructive lower bound

We follow Ernest S. Croot III, On some questions of Erdős and Graham about
Egyptian fractions, Mathematika 46 (1999), 359–372, Propositions 1–3.
The cutoff removes all integers with a prime-power divisor above
N / (log N)^a. The remaining denominators are divided into disjoint classes
according to the first least common multiple that they divide.
The descent adapts @marcusbuffett's merged Erdős 297 reduction. Denominator
one survives every cancellation, so an integer one larger than the desired
floor can be reduced to that floor.
-/
namespace OMA.R_Erdos308_erdos_308_variants_croot_R1_H1_R1
open Finset Real Filter Erdos308
open scoped Classical Topology

/-- Reciprocal mass lost at the initial prime-power cutoff. -/
def H1 : Prop := ∀ a : ℝ, 3<a → ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
  let J (i : ℕ) := (Icc 1 i).lcm id
  let Q := ⌊(N:ℝ)/(log N)^a⌋₊
  (∑ n ∈ (Icc 1 N).filter (fun n => ¬n∣J Q), (1:ℝ)/n) ≤
    (a^2/2+ε)*(log (log N))^2/log N

/-- Small and medium prime powers. The small-power costs telescope to less
than one and the intermediate powers contribute a negligible tail. -/
def H2 : Prop := ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
  let J (i : ℕ) := (Icc 1 i).lcm id
  let R (i : ℕ) := (Icc 1 N).filter fun n => n∣J i ∧ ¬ n∣J (i-1)
  ∃ cost : ℕ→ℚ, ((∑ i ∈ Ioc 1 N.sqrt, cost i : ℚ):ℝ) ≤
    1 + ε*(log (log N))^2/log N ∧
    ∀ i ∈ Ioc 1 N.sqrt, ∀ z : ℤ, ∃ V ⊆ R i,
      (∑ n ∈ V,(1:ℚ)/n) ≤ cost i ∧ ∃ b : ℤ,
        (b:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V,(1:ℚ)/n

/-- The modular subset sums for the large prime powers, in the range for
which logarithmically many denominators are available. -/
def H3 : Prop := ∀ a : ℝ, 3<a → ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
  let J (i : ℕ) := (Icc 1 i).lcm id
  let Q := ⌊(N:ℝ)/(log N)^a⌋₊
  let R (i : ℕ) := (Icc 1 N).filter fun n => n∣J i ∧ ¬ n∣J (i-1)
  ∃ cost : ℕ→ℚ, ((∑ i ∈ Ioc N.sqrt Q, cost i : ℚ):ℝ) ≤
    ε*(log (log N))^2/log N ∧
    ∀ i ∈ Ioc N.sqrt Q, ∀ z : ℤ, ∃ V ⊆ R i,
      (∑ n ∈ V,(1:ℚ)/n) ≤ cost i ∧ ∃ b : ℤ,
        (b:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V,(1:ℚ)/n

lemma descend (J : ℕ → ℕ) (R : ℕ → Finset ℕ) (cost : ℕ → ℚ)
    (L B : ℕ) (hB : L ≤ B) (step : ∀ i ∈ Ioc L B, ∀ z : ℤ, ∃ V ⊆ R i,
      (∑ n ∈ V, (1:ℚ)/n) ≤ cost i ∧ ∃ a : ℤ,
        (a:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V, (1:ℚ)/n)
    (apart : ∀ i ∈ Ioc L B, ∀ j ∈ Ioc L B,
      i < j → Disjoint (R i) (R j)) (z : ℤ) :
    ∃ P ⊆ (Ioc L B).biUnion R, (∑ n ∈ P, (1:ℚ)/n) ≤ ∑ i ∈ Ioc L B, cost i ∧
    ∃ a : ℤ, (a:ℚ)/J L = (z:ℚ)/J B - ∑ n ∈ P, (1:ℚ)/n := by
  induction B,hB using Nat.le_induction generalizing z with
  | base => exact ⟨∅,empty_subset _,by simp,z,by simp⟩
  | succ b hb ih =>
    have last : b+1 ∈ Ioc L (b+1) := mem_Ioc.mpr ⟨by omega,le_rfl⟩
    have sub : Ioc L b ⊆ Ioc L (b+1) := fun i hi => mem_Ioc.mpr
      ⟨(mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2.trans (Nat.le_succ _)⟩
    obtain ⟨V,hV,hv,a,ha⟩ := step (b+1) last z
    obtain ⟨P,hP,hp,j,hj⟩ := ih (fun i hi => step i (sub hi)) (fun i hi k hk => apart i (sub hi) k (sub hk)) a
    have dj : Disjoint P V := by
      apply disjoint_left.mpr
      intro n hn hnV
      obtain ⟨i,hi,hnR⟩ := mem_biUnion.mp (hP hn)
      exact disjoint_left.mp (apart i (sub hi) _ last (Nat.lt_succ_of_le (mem_Ioc.mp hi).2)) hnR (hV hnV)
    have eq : Ioc L (b+1) = insert (b+1) (Ioc L b) := by
      ext i; simp only [mem_Ioc,mem_insert]; omega
    refine ⟨P∪V,union_subset (fun n hn => ?_) (fun n hn => mem_biUnion.mpr ⟨_,last,hV hn⟩),?_,j,?_⟩
    · obtain ⟨i,hi,hh⟩ := mem_biUnion.mp (hP hn)
      exact mem_biUnion.mpr ⟨_,sub hi,hh⟩
    · rw [sum_union dj,eq,sum_insert (by simp)]
      linarith
    · simp only [Nat.add_sub_cancel] at ha
      rw [sum_union dj,hj,ha]
      ring




lemma assemble (N Q : ℕ) (hN : 1≤N) (hQ : 1≤Q) (cost : ℕ→ℚ) :
  let J (i : ℕ) := (Icc 1 i).lcm id
  let R (i : ℕ) := (Icc 1 N).filter fun n => n∣J i ∧ ¬ n∣J (i-1)
  (∀ i ∈ Ioc 1 Q, ∀ z : ℤ, ∃ V ⊆ R i,
      (∑ n ∈ V,(1:ℚ)/n) ≤ cost i ∧ ∃ b : ℤ,
        (b:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V,(1:ℚ)/n) →
  ∃ S ⊆ Icc 1 N, 1∈S ∧ ∃ z : ℕ, (∑ n ∈ S,(1:ℚ)/n) = z ∧
    (harmonic N:ℝ)-z ≤
      (∑ n ∈ (Icc 1 N).filter (fun n => ¬n∣J Q),(1:ℝ)/n) +
      ((∑ i ∈ Ioc 1 Q,cost i:ℚ):ℝ) := by
  intro J R step
  let G := (Icc 1 N).filter fun n => n∣J Q
  have Jpos (i : ℕ) : 0<J i := by
    apply Nat.pos_of_ne_zero
    apply Finset.lcm_ne_zero_iff.mpr
    intro n hn
    exact Nat.ne_of_gt (mem_Icc.mp hn).1
  have Jdvd {i j : ℕ} (h : i≤j) : J i∣J j :=
    Finset.lcm_dvd (fun n hn => Finset.dvd_lcm (f:=id) (mem_Icc.mpr
      ⟨(mem_Icc.mp hn).1,(mem_Icc.mp hn).2.trans h⟩))
  have part (i j : ℕ) (h : i<j) : Disjoint (R i) (R j) := by
    apply disjoint_left.mpr
    intro n hi hj
    have d := (mem_filter.mp hi).2.1
    exact (mem_filter.mp hj).2.2 (dvd_trans d (Jdvd (by omega)))
  let t : ℤ := ∑ n ∈ G, (J Q/n : ℕ)
  have grid : (t:ℚ)/J Q=∑ n ∈ G,(1:ℚ)/n := by
    dsimp only [t]
    push_cast
    rw [sum_div]
    apply sum_congr rfl
    intro n hn
    have dv := (mem_filter.mp hn).2
    have np := (mem_Icc.mp (mem_filter.mp hn).1).1
    apply (div_eq_div_iff (by exact_mod_cast (Jpos Q).ne') (by exact_mod_cast (Nat.ne_of_gt np))).mpr
    rw [one_mul]
    exact_mod_cast Nat.div_mul_cancel dv
  obtain ⟨P,sub,hcost,b,hb⟩ := descend J R cost 1 Q hQ step (fun i _ j _ => part i j) t
  have good : P⊆G := by
    intro n hn
    obtain ⟨i,hi,hr⟩ := mem_biUnion.mp (sub hn)
    exact mem_filter.mpr ⟨(mem_filter.mp hr).1,dvd_trans (mem_filter.mp hr).2.1 (Jdvd (mem_Ioc.mp hi).2)⟩
  have untouched : 1∉P := by
    intro hp
    obtain ⟨i,hi,hr⟩ := mem_biUnion.mp (sub hp)
    exact (mem_filter.mp hr).2.2 (one_dvd _)
  have jone : J 1=1 := by simp [J]
  rw [jone,Nat.cast_one,div_one,grid,←Finset.sum_sdiff_eq_sub good] at hb
  have nonneg : 0≤b := by
    have h : 0≤(b:ℚ) := by rw [hb]; positivity
    exact_mod_cast h
  lift b to ℕ using nonneg
  refine ⟨G \ P,fun n hn => (mem_filter.mp (mem_sdiff.mp hn).1).1,
    mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,hN⟩,one_dvd _⟩,untouched⟩,b,?_,?_⟩
  · exact_mod_cast hb.symm
  have hp : (∑ n ∈ P,(1:ℝ)/n) ≤ ((∑ i ∈ Ioc 1 Q,cost i:ℚ):ℝ) := by
    have t : ((∑ n ∈ P, (1:ℚ)/n):ℝ) ≤ ((∑ i ∈ Ioc 1 Q,cost i:ℚ):ℝ) := by exact_mod_cast hcost
    simpa using t
  have bb : (b:ℝ) = ∑ n ∈ G \ P,(1:ℝ)/n := by simpa using congrArg (fun t : ℚ => (t:ℝ)) hb
  have split := Finset.sum_sdiff good (f:=fun n : ℕ => (1:ℝ)/n)
  have both := Finset.sum_filter_add_sum_filter_not (Icc 1 N) (fun n => n∣J Q) (fun n : ℕ => (1:ℝ)/n)
  rw [harmonic_eq_sum_Icc]
  push_cast
  change (∑ n ∈ G, (1:ℝ)/n) + _ = _ at both
  simp only [one_div,Rat.cast_sum] at hp bb split both ⊢
  linarith only [hp,bb,split,both]



lemma floor_rep {N z : ℕ} {S : Finset ℕ} (sub : S⊆Icc 1 N) (one : 1∈S)
    (eq : (∑ n ∈ S,(1:ℚ)/n) = z) {u : ℝ} (hu : u≤1)
    (low : (harmonic N:ℝ)-z < 1+u) : IsRepresentable N ⌊(harmonic N:ℝ)-u⌋₊ := by
  let k := ⌊(harmonic N:ℝ)-u⌋₊
  have hz : IsRepresentable N z := ⟨S,sub,eq⟩
  have hi := OMA.R_Erdos308_erdos_308_variants_croot_R1.mass_le hz
  have om : 0≤∑ n ∈ (Icc 1 N).filter (fun n => ∃ p ∈ n.primeFactors, (N/p)*(N/p).factorial < p), (1:ℝ)/n := by positivity
  have hzle : z≤k+1 := by
    have h := Nat.lt_floor_add_one ((harmonic N:ℝ)-u)
    change (harmonic N:ℝ)-u < (k:ℝ)+1 at h
    have zlt : z<k+2 := by exact_mod_cast (show (z:ℝ)<(k:ℝ)+2 by linarith)
    omega
  have hkz : k≤z := by
    apply Nat.le_of_lt_succ
    exact (Nat.floor_lt' (Nat.succ_ne_zero z)).mpr (by push_cast; linarith)
  rcases Nat.eq_or_lt_of_le hkz with hk|hk
  · change IsRepresentable N k
    exact hk ▸ hz
  have e : z=k+1 := by omega
  refine ⟨S.erase 1,(erase_subset _ _).trans sub,?_⟩
  have h := Finset.sum_erase_add (f:=fun n : ℕ => (1:ℚ)/n) S one
  rw [eq,e] at h
  push_cast at h
  change _ = (k:ℚ)
  norm_num at h
  simpa only [one_div] using h


lemma fixed (cut : H1) (small : H2) (large : H3) (η : ℝ) (η0 : 0<η) (η1 : η≤1) :
    ∀ᶠ N : ℕ in atTop, IsRepresentable N
      ⌊(harmonic N:ℝ)-9/2*(1+η)*(log (log N))^2/log N⌋₊ := by
  let a := 3+η/2
  let b := 9/2*(1+η)
  have a3 : 3<a := by dsimp [a]; linarith
  have δ : 0<η/4 := by positivity
  have gap : a^2/2+3*(η/4)<b := by
    dsimp [a,b]
    nlinarith [mul_nonneg η0.le (sub_nonneg.mpr η1)]
  have lc := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have grow := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    ((isLittleO_log_rpow_rpow_atTop a (show 0<(1/2:ℝ) by norm_num)).bound zero_lt_one)
  have sc := ((isLittleO_log_rpow_rpow_atTop (2:ℝ) (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero.comp lc).const_mul b
  rw [mul_zero] at sc
  filter_upwards [cut a a3 (η/4) δ,small (η/4) δ,large a a3 (η/4) δ,
      sc.eventually_lt_const zero_lt_one,grow,
      lc.eventually_gt_atTop 1,eventually_ge_atTop 2] with N hc hs hl hcst hg hn hN
  let J (i : ℕ) := (Icc 1 i).lcm id
  let Q := ⌊(N:ℝ)/(log N)^a⌋₊
  let R (i : ℕ) := (Icc 1 N).filter fun n => n∣J i ∧ ¬n∣J (i-1)
  let s := (log (log N))^2/log N
  have np : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  change 1<log (N:ℝ) at hn
  have lp : 0<log (N:ℝ) := by linarith
  have sp : 0<s := div_pos (sq_pos_of_pos (log_pos hn)) lp
  have un : b*s≤1 := by
    apply le_of_lt
    simpa [Function.comp_def,s,Real.rpow_two,Real.rpow_one] using hcst
  have hlp := rpow_pos_of_pos lp a
  have rad : (log (N:ℝ))^a ≤ sqrt N := by
    change ‖(log (N:ℝ))^a‖ ≤ 1*‖(N:ℝ)^(1/2:ℝ)‖ at hg
    rw [sqrt_eq_rpow]
    simpa only [Real.norm_eq_abs,abs_of_pos hlp,abs_of_pos (rpow_pos_of_pos np _),one_mul] using hg
  have sqQ : N.sqrt≤Q := by
    apply Nat.le_floor
    apply (le_div_iff₀ hlp).mpr
    exact (mul_le_mul Real.nat_sqrt_le_real_sqrt rad hlp.le (sqrt_nonneg _)).trans_eq
      (by rw [←sq,Real.sq_sqrt np.le])
  have s1 : 1≤N.sqrt := Nat.le_sqrt.mpr (by omega)
  obtain ⟨lo,lcost,low⟩ := hs
  obtain ⟨hi,hcost,high⟩ := hl
  let cost (i:ℕ) := if i≤N.sqrt then lo i else hi i
  have merge : (∑ i ∈ Ioc 1 Q,cost i) = (∑ i ∈ Ioc 1 N.sqrt,lo i)+(∑ i ∈ Ioc N.sqrt Q,hi i) := by
    rw [←Finset.Ioc_union_Ioc_eq_Ioc s1 sqQ,Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
    congr 1
    · exact sum_congr rfl (fun i h => if_pos (mem_Ioc.mp h).2)
    · exact sum_congr rfl (fun i h => if_neg (not_le.mpr (mem_Ioc.mp h).1))
  obtain ⟨S,sub,one,z,eq,loss⟩ := assemble N Q (by omega) (s1.trans sqQ) cost (by
    intro i hi z
    by_cases ht : i≤N.sqrt
    · simpa only [cost,if_pos ht] using low i (mem_Ioc.mpr ⟨(mem_Ioc.mp hi).1,ht⟩) z
    · simpa only [cost,if_neg ht] using high i (mem_Ioc.mpr ⟨not_le.mp ht,(mem_Ioc.mp hi).2⟩) z)
  dsimp only at hc lcost hcost
  rw [merge,Rat.cast_add] at loss
  have cle : (∑ n ∈ (Icc 1 N).filter (fun n => ¬n∣J Q),(1:ℝ)/n) ≤ (a^2/2+η/4)*s := by
    simpa only [J,Q,s,mul_div_assoc] using hc
  have ll : ((∑ i ∈ Ioc 1 N.sqrt,lo i:ℚ):ℝ) ≤ 1+(η/4)*s := by simpa only [s,mul_div_assoc] using lcost
  have hh : ((∑ i ∈ Ioc N.sqrt Q,hi i:ℚ):ℝ) ≤ (η/4)*s := by simpa only [Q,s,mul_div_assoc] using hcost
  have rep := floor_rep sub one eq un (by
    change (harmonic N:ℝ)-z < 1+b*s
    linarith only [loss,cle,ll,hh,mul_lt_mul_of_pos_right gap sp])
  simpa only [b,s,mul_div_assoc] using rep


theorem main : H1 → H2 → H3 → OMA.R_Erdos308_erdos_308_variants_croot_R1.H1 := by
  intro cut small large
  let d (k : ℕ) : ℝ := 1/((k:ℝ)+1)
  let P (N k : ℕ) := IsRepresentable N
    ⌊(harmonic N:ℝ)-9/2*(1+d k)*(log (log N))^2/log N⌋₊
  have row (k : ℕ) : ∀ᶠ N : ℕ in atTop, P N k :=
    fixed cut small large (d k) (by dsimp [d]; positivity)
      (by dsimp [d]; apply (div_le_one (by positivity)).mpr; linarith [Nat.cast_nonneg (α:=ℝ) k])
  let j (N : ℕ) := Nat.findGreatest (P N) N
  have top : Tendsto j atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [row k,eventually_ge_atTop k] with N hp hn
    exact Nat.le_findGreatest hn hp
  refine ⟨fun N => d (j N),tendsto_one_div_add_atTop_nhds_zero_nat.comp top,?_⟩
  filter_upwards [row 0] with N hN
  exact Nat.findGreatest_spec (Nat.zero_le N) hN
end OMA.R_Erdos308_erdos_308_variants_croot_R1_H1_R1
