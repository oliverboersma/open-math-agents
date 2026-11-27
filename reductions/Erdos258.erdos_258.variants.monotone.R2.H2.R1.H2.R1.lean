import OMAReductions.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1
import Mathlib

/-! Erdős and Straus, Some number theoretic results, Section 2. A congruence
class forces the initial divisor digits and stays coprime to its modulus
for a long sequence of subsequent shifts. A first moment over that class
then bounds the weighted tail at a representative in the given interval. -/
namespace OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1_H2_R1

open Finset Filter Real
open scoped Topology

/-- A CRT construction with an explicit small modulus. The first k divisor
digits are divisible by successive powers of t, and the following H shifts
are units modulo the modulus. -/
def H1 : Prop := ∀ k t H : ℕ, 1≤k → 2≤t → ∃ A r : ℕ, 0<A ∧ r<A ∧
  log (A:ℝ) ≤ 4*(t:ℝ)*(k:ℝ)^2*((k:ℝ)^2+log (H+k+2:ℕ)) ∧
  (∀ N : ℕ, N ≡ r [MOD A] → ∀ j ∈ Icc 1 k, t^j ∣ (N+j).divisors.card) ∧
  ∀ i < H, Nat.Coprime (r+k+i+1) A

/-- Divisor hyperbola bound for a reduced residue class. -/
def H2 : Prop := ∀ X A r : ℕ, 1≤A → Nat.Coprime r A →
  (∑ n ∈ (Icc 1 X).filter (fun n => n ≡ r [MOD A]), (n.divisors.card:ℝ)) ≤
    2*((X:ℝ)/A*(1+log X)+sqrt X)

lemma geometric : ∃ B : ℝ, 0≤B ∧ ∀ n : ℕ,
    Summable (fun k : ℕ => ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k) ∧
    (∑' k : ℕ, ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k) ≤ ((n:ℝ)+1)*B := by
  let b (k : ℕ) := ((k:ℝ)+1)*((1:ℝ)/2)^k
  have sm : Summable b := by
    have h : Summable (fun k : ℕ => (k:ℝ)*((1:ℝ)/2)^k) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R:=ℝ) 1 (r:=1/2) (by norm_num)
    simpa [b,add_mul] using h.add (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num))
  refine ⟨∑' k,b k,tsum_nonneg (fun k => by dsimp [b]; positivity),?_⟩
  intro n
  have dom (k : ℕ) : ((k+n+1).divisors.card:ℝ)/(2:ℝ)^k ≤ ((n:ℝ)+1)*b k := by
    have h : ((k+n+1).divisors.card:ℝ) ≤ ((k+n+1:ℕ):ℝ) := by exact_mod_cast Nat.card_divisors_le_self _
    push_cast at h
    dsimp [b]
    rw [div_pow,one_pow,←mul_assoc,mul_one_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [h,mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) (Nat.cast_nonneg k : (0:ℝ)≤k)]
  have s := Summable.of_nonneg_of_le (fun k => by positivity) dom (sm.mul_left _)
  refine ⟨s,?_⟩
  rw [←tsum_mul_left]
  exact s.tsum_le_tsum dom (sm.mul_left _)

lemma progression_mean (estimate : H2) : ∃ C : ℝ, 0<C ∧ ∀ X A r k H : ℕ,
    1≤X → 1≤A → (A:ℝ) ≤ sqrt X → k≤X → H≤X → (X:ℝ)^2 ≤ (2:ℝ)^H →
    (∀ i < H, Nat.Coprime (r+k+i+1) A) →
    let S := (Icc 0 X).filter (fun N => N ≡ r [MOD A])
    (∑ N ∈ S, ∑' i : ℕ, ((i+(N+k)+1).divisors.card:ℝ)/(2:ℝ)^i) ≤
      C*((X:ℝ)/A)*(1+log X) := by
  classical
  obtain ⟨B,b0,bs⟩ := geometric
  refine ⟨80+8*B,by linarith,?_⟩
  intro X A r k H X1 A1 aX kX HX grow cop S
  have xp : 0<(X:ℝ) := by exact_mod_cast X1
  have x1 : 1≤(X:ℝ) := by exact_mod_cast X1
  have ap : 0<(A:ℝ) := by exact_mod_cast A1
  have lx : 0 ≤ log (X:ℝ) := log_nonneg x1
  have sqX := sq_sqrt (Nat.cast_nonneg X : (0:ℝ)≤X)
  have rt : sqrt X ≤ (X:ℝ)/A := by
    apply (le_div_iff₀ ap).mpr
    nlinarith only [sqX,mul_le_mul_of_nonneg_left aX (sqrt_nonneg (X:ℝ))]
  have ax : 1≤(X:ℝ)/A := (one_le_sqrt.mpr x1).trans rt
  let d (N i : ℕ) : ℝ := (i+(N+k)+1).divisors.card
  have row (i : ℕ) (hi : i<H) : (∑ N ∈ S,d N i) ≤ 40*((X:ℝ)/A)*(1+log X) := by
    let f (N : ℕ) := i+(N+k)+1
    let U := (Icc 1 (4*X)).filter (fun n => n ≡ r+k+i+1 [MOD A])
    have sub : S.image f ⊆ U := by
      intro n hn
      obtain ⟨N,hN,rfl⟩ := mem_image.mp hn
      obtain ⟨rangeN,cong⟩ := mem_filter.mp hN
      have nX := (mem_Icc.mp rangeN).2
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by dsimp [f]; omega,by dsimp [f]; omega⟩,?_⟩
      simpa [f,Nat.add_comm,Nat.add_assoc,Nat.add_left_comm] using cong.add_right (k+i+1)
    have inc := Finset.sum_le_sum_of_subset_of_nonneg (f:=fun n : ℕ => (n.divisors.card:ℝ)) sub
      (fun _ _ _ => Nat.cast_nonneg _)
    rw [sum_image (fun N _ M _ eq => by dsimp [f] at eq; omega)] at inc
    have bd := inc.trans (estimate (4*X) A (r+k+i+1) A1 (cop i hi))
    change (∑ N ∈ S,d N i) ≤ _ at bd
    push_cast at bd
    rw [log_mul (by norm_num) xp.ne',sqrt_mul (by norm_num : (0:ℝ)≤4)] at bd
    norm_num at bd
    have log4 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    rw [mul_div_assoc] at bd
    nlinarith only [bd,rt,ax,mul_le_mul_of_nonneg_left log4 (div_nonneg xp.le ap.le),
      mul_nonneg (div_nonneg xp.le ap.le) lx]
  let G (n : ℕ) := ∑' i : ℕ, ((i+n+1).divisors.card:ℝ)/(2:ℝ)^i
  have split (N : ℕ) : G (N+k) = (∑ i ∈ range H, d N i/(2:ℝ)^i) + G (N+k+H)/(2:ℝ)^H := by
    change (∑' i : ℕ, d N i/(2:ℝ)^i) = _
    rw [←(bs (N+k)).1.sum_add_tsum_nat_add H]
    congr 1
    change _ = (∑' i : ℕ, ((i+(N+k+H)+1).divisors.card:ℝ)/(2:ℝ)^i)/(2:ℝ)^H
    rw [←tsum_div_const]
    apply tsum_congr
    intro i
    rw [show i+H+(N+k)+1=i+(N+k+H)+1 by omega,pow_add]
    ring
  have finite : (∑ N ∈ S,∑ i ∈ range H,d N i/(2:ℝ)^i) ≤ 80*((X:ℝ)/A)*(1+log X) := by
    rw [sum_comm]
    simp_rw [←sum_div]
    have R := sum_le_sum (s:=range H) (fun i hi => div_le_div_of_nonneg_right (row i (mem_range.mp hi)) (by positivity : 0≤(2:ℝ)^i))
    have eq : (∑ i ∈ range H,40*((X:ℝ)/A)*(1+log X)/(2:ℝ)^i) =
        (40*((X:ℝ)/A)*(1+log X))*(∑ i ∈ range H,(1/2:ℝ)^i) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [div_pow,one_pow,mul_one_div]
    rw [eq] at R
    have geom := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).sum_le_tsum (range H)
      (fun i _ => pow_nonneg (by norm_num : (0:ℝ)≤1/2) i)
    rw [tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)] at geom
    norm_num at geom
    nlinarith only [R,mul_le_mul_of_nonneg_left geom (show 0≤40*((X:ℝ)/A)*(1+log X) by positivity)]
  have tail : (∑ N ∈ S,G (N+k+H)/(2:ℝ)^H) ≤ 8*B := by
    have point (N : ℕ) (hN : N∈S) : G (N+k+H)/(2:ℝ)^H ≤ 4*X*B/(2:ℝ)^H := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply (bs _).2.trans
      apply mul_le_mul_of_nonneg_right _ b0
      have nX := (mem_Icc.mp (mem_filter.mp hN).1).2
      exact_mod_cast (show N+k+H+1 ≤ 4*X by omega)
    have sum := sum_le_sum point
    rw [sum_const,nsmul_eq_mul] at sum
    have c : (S.card:ℝ)≤2*X := by
      have := card_le_card (show S ⊆ Icc 0 X from filter_subset _ _)
      rw [Nat.card_Icc] at this
      exact_mod_cast (show S.card≤2*X by omega)
    apply sum.trans
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right c (show 0≤4*(X:ℝ)*B by positivity),
      mul_le_mul_of_nonneg_left grow (show 0≤8*B by positivity)]
  change (∑ N ∈ S,G (N+k)) ≤ _
  simp_rw [split,sum_add_distrib]
  have scale : 1 ≤ ((X:ℝ)/A)*(1+log X) := one_le_mul_of_one_le_of_one_le ax (by linarith)
  nlinarith only [finite,tail,mul_le_mul_of_nonneg_left scale (show 0≤8*B by positivity)]

lemma pack (X k h A r : ℕ) (hk : 1≤k) (hh : 0<h) (ha : 0<A) (hr : r<A)
    (long : (4*A+2*k+2)*h≤X) (I : Finset ℕ) (incl : I ⊆ Icc 1 X)
    (convex : ∀ x ∈ I, ∀ y ∈ I, Icc x y ⊆ I) (many : X/h≤I.card) :
    ∃ J : Finset ℕ, J ⊆ (Icc 0 X).filter (fun N => N ≡ r [MOD A]) ∧
      (∀ N ∈ J,Icc (N+1) (N+k) ⊆ I) ∧ X ≤ 8*h*A*J.card := by
  classical
  have size : 4*A+2*k+2≤I.card := ((Nat.le_div_iff_mul_le hh).mpr long).trans many
  have ne : I.Nonempty := card_pos.mp (by omega)
  let a := I.min' ne
  let b := I.max' ne
  have ami : a∈I := min'_mem _ _
  have bma : b∈I := max'_mem _ _
  have convex' : Icc a b ⊆ I := convex a ami b bma
  have rep : I = Icc a b := Subset.antisymm (fun i hi => mem_Icc.mpr ⟨min'_le _ _ hi,le_max' _ _ hi⟩) convex'
  have ab : a≤b := min'_le _ _ bma
  have len : I.card+a=b+1 := by rw [rep,Nat.card_Icc]; omega
  let T := I.card/(2*A)
  have twoA : 0<2*A := by omega
  have T1 : 1≤T := (Nat.le_div_iff_mul_le twoA).mpr (by omega)
  have lower : 2*A*T ≤ I.card := Nat.mul_div_le _ _
  have upper : I.card < (T+1)*(2*A) := by simpa [T,Nat.mul_comm] using Nat.lt_mul_div_succ I.card twoA
  let start := A*(a/A+1)+r
  let f (i : ℕ) := start + A*i
  have little := Nat.mul_div_le a A
  have next := Nat.lt_mul_div_succ a ha
  have startLo : a ≤ start := by dsimp [start]; nlinarith only [next]
  have startHi : start≤a+2*A := by dsimp [start]; nlinarith only [little,hr]
  have bounds (i : ℕ) (hi : i<T) : a≤f i+1 ∧ f i+k≤b := by
    have iT := Nat.mul_le_mul_left A (show i+1≤T by omega)
    dsimp [f]
    constructor
    · omega
    · nlinarith only [iT,lower,startHi,size,len]
  let J := (range T).image f
  have cj : J.card=T := by
    rw [show J=(range T).image f from rfl,card_image_of_injective,card_range]
    intro i j eq
    apply Nat.eq_of_mul_eq_mul_left ha
    exact Nat.add_left_cancel eq
  refine ⟨J,?_,?_,?_⟩
  · intro N hn
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hn
    have xb := (mem_Icc.mp (incl bma)).2
    have ub := (bounds i (mem_range.mp hi)).2
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,by omega⟩,?_⟩
    simp [f,start,Nat.ModEq,Nat.add_mod]
  · intro N hn z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hn
    obtain ⟨lo,up⟩ := bounds i (mem_range.mp hi)
    exact convex' (mem_Icc.mpr ⟨lo.trans (mem_Icc.mp hz).1,(mem_Icc.mp hz).2.trans up⟩)
  · rw [cj]
    have xl := Nat.lt_mul_div_succ X hh
    have step : X ≤ 2*h*I.card := by
      have plus := Nat.mul_le_mul_left h (show X/h+1≤2*I.card by omega)
      nlinarith only [xl,plus]
    have step2 : I.card ≤ 4*A*T := by
      have hh' := Nat.mul_le_mul_left (2*A) (show T+1≤2*T by omega)
      nlinarith only [upper,hh']
    nlinarith only [step,Nat.mul_le_mul_left (2*h) step2]

lemma scale (D : ℝ) (dpos : 0<D) : ∀ᶠ X : ℕ in atTop, ∃ k : ℕ, 256≤k ∧
    (k:ℝ)^63 ≤ log X ∧ log X ≤ (k:ℝ)^64 ∧
    D*(k:ℝ)^128 < (2:ℝ)^k ∧ (2:ℝ)^k ≤ sqrt X := by
  let w (X : ℕ) := (log (X:ℝ))^(1/64:ℝ)
  have logtop := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have wt : Tendsto w atTop atTop := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/64)).comp logtop
  have kt : Tendsto (fun X : ℕ => ⌈w X⌉₊) atTop atTop := tendsto_nat_ceil_atTop.comp wt
  have decay := (tendsto_pow_const_div_const_pow_of_one_lt 128 (by norm_num : (1:ℝ)<2)).comp kt
  filter_upwards [wt.eventually_ge_atTop ((2:ℝ)^63),kt.eventually_ge_atTop 256,
    decay.eventually_lt_const (one_div_pos.mpr dpos),eventually_ge_atTop 1] with X wh kh sm X1
  let k := ⌈w X⌉₊
  change 256≤k at kh
  have x1 : 1≤(X:ℝ) := by exact_mod_cast X1
  have xp := zero_lt_one.trans_le x1
  have w1 : 1≤w X := (by norm_num : (1:ℝ)≤2^63).trans wh
  have kp : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
  have above : w X ≤ (k:ℝ) := Nat.le_ceil _
  have below : (k:ℝ) ≤ 2*w X := by
    have h := Nat.ceil_lt_add_one (by linarith : 0≤w X)
    change (k:ℝ)<w X+1 at h
    linarith
  have idw : (w X)^64 = log X := by
    dsimp [w]; rw [←rpow_natCast,←rpow_mul (log_nonneg x1)]; norm_num
  have lo : (k:ℝ)^63 ≤ log X := calc
    _ ≤ (2*w X)^63 := pow_le_pow_left₀ (Nat.cast_nonneg _) below _
    _ = (2:ℝ)^63*(w X)^63 := mul_pow _ _ _
    _ ≤ (w X)*(w X)^63 := mul_le_mul_of_nonneg_right wh (by positivity)
    _ = _ := by rw [←idw]; ring
  have hi : log (X:ℝ) ≤ (k:ℝ)^64 := idw.symm.le.trans (pow_le_pow_left₀ (by linarith) above _)
  have eq : D*(k:ℝ)^128 < (2:ℝ)^k := by
    change (k:ℝ)^128/(2:ℝ)^k<1/D at sm
    have := (div_lt_div_iff₀ (by positivity : 0<(2:ℝ)^k) dpos).mp sm
    linarith only [this]
  refine ⟨k,kh,lo,hi,eq,?_⟩
  apply (log_le_log_iff (by positivity) (sqrt_pos.mpr xp)).mp
  rw [log_pow,log_sqrt xp.le]
  have k2 : (2:ℝ)≤k := by exact_mod_cast (show 2≤k by omega)
  have kl : (k:ℝ)^2 ≤ (k:ℝ)^63 := pow_le_pow_right₀ kp (by decide)
  nlinarith only [lo,kl,mul_le_mul_of_nonneg_left k2 (Nat.cast_nonneg k : (0:ℝ)≤k),
    mul_le_mul_of_nonneg_left (show log (2:ℝ)≤1 by linarith [log_two_lt_d9]) (Nat.cast_nonneg k)]

lemma modulus {X k t A : ℕ} (large : 256≤k) (a0 : 0<A)
    (lo : (k:ℝ)^63 ≤ log X) (tcap : (t:ℝ) ≤ (k:ℝ)^56)
    (size : log A ≤ 4*(t:ℝ)*(k:ℝ)^2*((k:ℝ)^2+log ((k^128+k+2:ℕ):ℝ)))
    (Xpos : 0 < (X:ℝ)) : (A:ℝ) ≤ sqrt X := by
  let z := (k:ℝ)
  have z1 : 1≤z := by dsimp [z]; exact_mod_cast (show 1≤k by omega)
  have zp := zero_lt_one.trans_le z1
  have z256 : (256:ℝ)≤z := by dsimp [z]; exact_mod_cast large
  have cover : ((k^128+k+2:ℕ):ℝ) ≤ 4*z^128 := by
    push_cast
    have h : z ≤ z^128 := by simpa using pow_le_pow_right₀ z1 (by decide : 1≤128)
    have h' := one_le_pow₀ z1 (n:=128)
    change z^128+z+2 ≤ _
    linarith
  have bound := log_le_log (by positivity : 0<((k^128+k+2:ℕ):ℝ)) cover
  rw [log_mul (by norm_num) (pow_pos zp _).ne',log_pow] at bound
  have logs : log ((k^128+k+2:ℕ):ℝ) ≤ z^2 := by
    have log4 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    push_cast
    norm_num at bound
    have logz := log_le_sub_one_of_pos zp
    nlinarith only [log4,logz,bound,mul_le_mul_of_nonneg_right z256 zp.le,z256]
  have logs0 : 0 ≤ log ((k^128+k+2:ℕ):ℝ) := log_nonneg (by exact_mod_cast (show 1≤k^128+k+2 by omega))
  have small : log A ≤ 8*z^60 := by
    apply size.trans
    calc
      _ ≤ 4*z^56*z^2*(z^2+z^2) := by gcongr
      _ = _ := by ring
  have extra : 16 ≤ z^3 := by
    have t : z ≤ z^3 := by simpa using pow_le_pow_right₀ z1 (by decide : 1≤3)
    linarith
  have product := mul_le_mul_of_nonneg_left extra (pow_nonneg zp.le 60)
  apply (log_le_log_iff (by exact_mod_cast a0) (sqrt_pos.mpr Xpos)).mp
  rw [log_sqrt Xpos.le]
  change z^63 ≤ _ at lo
  nlinarith only [lo,small,product]

theorem main : H1 → H2 → OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1.H2 := by
  classical
  intro crt estimate q hq
  obtain ⟨C,cpos,avg⟩ := progression_mean estimate
  have qp : (0:ℝ)<q := by exact_mod_cast hq
  let D := 16+16*(q:ℝ)*C
  have dpos : 0<D := by dsimp [D]; positivity
  filter_upwards [scale D dpos,eventually_ge_atTop 2] with X parameters X2
  obtain ⟨k,kl,lo,hi,expensive,root⟩ := parameters
  intro t t2 tlim I incl convex cardI
  let H := k^128
  let h := ⌊(log X)^(7/8:ℝ)⌋₊
  let z := (k:ℝ)
  have x1 : (1:ℝ) ≤ X := by exact_mod_cast (show 1≤X by omega)
  have xp := zero_lt_one.trans_le x1
  have w0 := log_nonneg x1
  have z1 : 1 ≤ z := by dsimp [z]; exact_mod_cast (show 1≤k by omega)
  have zp := zero_lt_one.trans_le z1
  have power : (log X)^(7/8:ℝ) ≤ z^56 := calc
    _ ≤ (z^64)^(7/8:ℝ) := rpow_le_rpow w0 hi (by norm_num)
    _ = _ := by rw [←rpow_natCast z 64,←rpow_mul zp.le]; norm_num
  have hcap : (h:ℝ) ≤ z^56 := (Nat.floor_le (rpow_nonneg w0 _)).trans power
  have hpos : 0<h := by
    have tt : t ≤ h := (Nat.le_floor_iff (rpow_nonneg w0 _)).mpr tlim
    omega
  obtain ⟨A,r,ap,rA,sz,initial,cop⟩ := crt k t H (by omega) t2
  have ar := modulus kl ap lo (tlim.trans power) sz xp
  have arpos : 0 < (A:ℝ) := by exact_mod_cast ap
  have Hbig : 16*z^128 ≤ sqrt X := calc
    _ ≤ D*z^128 := mul_le_mul_of_nonneg_right (by dsimp [D]; linarith [mul_nonneg qp.le cpos.le]) (pow_nonneg zp.le _)
    _ ≤ _ := expensive.le.trans root
  have hroot : 16*(h:ℝ) ≤ sqrt X := by
    apply le_trans _ Hbig
    exact mul_le_mul_of_nonneg_left (hcap.trans (pow_le_pow_right₀ z1 (by decide))) (by norm_num)
  have Hp : (H:ℝ) = z^128 := by dsimp [H,z]; norm_cast
  have small : (H:ℝ) ≤ sqrt X := by rw [Hp]; linarith [pow_nonneg zp.le 128]
  have kH : k≤H := by
    simpa [H] using Nat.pow_le_pow_right (show 0<k by omega) (by decide : 1≤128)
  have HX : H≤X := by
    have rt := Real.sqrt_le_self_iff.mpr (Or.inr x1)
    exact_mod_cast small.trans rt
  have kroot : (k:ℝ)≤ sqrt X := (by exact_mod_cast kH : (k:ℝ)≤H).trans small
  have rtone : 1≤ sqrt X := one_le_sqrt.mpr x1
  have long : (4*A+2*k+2)*h ≤ X := by
    have e : 4*(A:ℝ)+2*(k:ℝ)+2 ≤ 8*sqrt X := by linarith
    have e' : (h:ℝ) ≤ sqrt X/8 := by linarith [Nat.cast_nonneg h (α:=ℝ)]
    have mult := mul_le_mul e e' (Nat.cast_nonneg h) (by positivity)
    have sq := sq_sqrt xp.le
    exact_mod_cast (by nlinarith only [sq,mult] : (4*(A:ℝ)+2*(k:ℝ)+2)*h≤X)
  have grow : (X:ℝ)^2 ≤ (2:ℝ)^H := by
    apply (log_le_log_iff (pow_pos xp _) (by positivity)).mp
    rw [log_pow,log_pow,Hp]
    norm_num only [Nat.cast_ofNat]
    have h64 : 4≤z^64 := by
      have he := pow_le_pow_right₀ z1 (by decide : 1≤64)
      have zl : (256:ℝ)≤z := by dsimp [z]; exact_mod_cast kl
      simp only [pow_one] at he
      linarith
    have hl2 : (1/2:ℝ) ≤ log 2 := by linarith [Real.log_two_gt_d9]
    change log (X:ℝ) ≤ z^64 at hi
    have mult := mul_le_mul_of_nonneg_left h64 (pow_nonneg zp.le 64)
    nlinarith only [hi,mult,mul_le_mul_of_nonneg_left hl2 (pow_nonneg zp.le 128)]
  obtain ⟨J,hJ,inter,count⟩ := pack X k h A r (by omega) hpos ap rA long I incl convex cardI
  let G (n : ℕ) := ∑' i : ℕ, ((i+n+1).divisors.card:ℝ)/(2:ℝ)^i
  have ub := (Finset.sum_le_sum_of_subset_of_nonneg (f:=fun N => G (N+k)) hJ
      (fun i _ _ => tsum_nonneg fun j => by positivity)).trans
    (avg X A r k H (by omega) ap ar (kH.trans HX) HX grow cop)
  have price : 8*(h:ℝ)*(q:ℝ)*C*(1+log X) < (2:ℝ)^k := by
    apply lt_of_le_of_lt _ expensive
    have p : 1+log X ≤ 2*z^64 := by linarith [one_le_pow₀ z1 (n:=64)]
    have s : (h:ℝ)*(1+log X) ≤ z^56*(2*z^64) := mul_le_mul hcap p (by linarith) (pow_nonneg zp.le _)
    have e : z^120 ≤ z^128 := pow_le_pow_right₀ z1 (by decide)
    dsimp [D]
    nlinarith only [mul_le_mul_of_nonneg_left s (show 0≤8*(q:ℝ)*C by positivity),
      mul_le_mul_of_nonneg_left e (show 0≤16*(q:ℝ)*C by positivity),pow_nonneg zp.le 128]
  have existsN : ∃ N∈J, (q:ℝ)*G (N+k)<(2:ℝ)^k := by
    by_contra! bad
    have sum := sum_le_sum (s:=J) (fun N hN => bad N hN)
    rw [sum_const,nsmul_eq_mul,←mul_sum] at sum
    have cost := sum.trans (mul_le_mul_of_nonneg_left ub qp.le)
    have jpos : 0<J.card := by
      by_contra! hh
      rw [show J.card=0 by omega,mul_zero] at count
      omega
    have jr : 0<(J.card:ℝ) := by exact_mod_cast jpos
    have cap : (X:ℝ)/A ≤ 8*h*J.card := by
      apply (div_le_iff₀ arpos).mpr
      have cnt : (X:ℝ) ≤ 8*(h:ℝ)*A*J.card := by exact_mod_cast count
      linarith only [cnt]
    have weighted := mul_le_mul_of_nonneg_right cap (show 0 ≤ (q:ℝ)*C*(1+log X) by positivity)
    have imposs := mul_lt_mul_of_pos_right price jr
    linarith only [cost,weighted,imposs]
  obtain ⟨N,nJ,good⟩ := existsN
  exact ⟨N,k,inter N nJ,initial N (mem_filter.mp (hJ nJ)).2,
    good.trans_le (pow_le_pow_left₀ (by norm_num) (by exact_mod_cast t2) _)⟩

end OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1_H2_R1
