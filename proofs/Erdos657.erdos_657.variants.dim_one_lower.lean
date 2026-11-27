import FormalConjectures.ErdosProblems.«657»
import Mathlib
-- Credit: R1 reduction by Javi Soto (PR 3885), as credited in the H2 header.
-- Credit: H1 leaf, author not named in its piece header.
-- Credit: H2 leaf, Javi Soto (PR 3885), Kelley-Meka estimate from LeanAPAP (Yael Dillies and contributors), Adam Carter (PR 3227), PanPapag (PR 3553).
-- Credit: @LordMike (assembly)
section OMA.R1Piece
namespace OMA.R1
open Finset Filter
open scoped Pointwise Classical
def H1 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (K : ℝ), 1 ≤ K → 0 < A.card →
    ((A - A).card : ℝ) ≤ K * A.card →
    ∃ (N : ℕ) (B : Finset ℕ) (g : ℕ → ℝ), B ⊆ range N ∧ A.card ≤ 4 * B.card ∧
      (N : ℝ) ≤ C * K ^ 8 * A.card ∧ Set.MapsTo g (B : Set ℕ) (A : Set ℝ) ∧
      Set.InjOn g (B : Set ℕ) ∧
      ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, a + c = b + b → g a + g c = g b + g b
def H2 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (B : Finset ℕ), B ⊆ range N →
    ThreeAPFree (B : Set ℕ) → (B.card : ℝ) * Real.log (4 * (N : ℝ)) ≤ C * N
private theorem diffs (A : Finset ℝ) :
    (A - A).card ≤ 2 * (distinctDistances A + 1) := by
  classical
  let D := insert 0 (distanceSet A)
  let signed : Bool × ℝ → ℝ := fun v => if v.1 then v.2 else -v.2
  have hs : A - A ⊆ (univ ×ˢ D).image signed := by
    intro t ht
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_sub.mp ht
    have hab : |x-y| ∈ D := by
      by_cases he : x=y
      · simp [D,he]
      · apply mem_insert_of_mem
        exact mem_image.mpr ⟨(x,y),mem_offDiag.mpr ⟨hx,hy,he⟩,Real.dist_eq ..⟩
    rcases le_total y x with h|h
    · exact mem_image.mpr ⟨(true,|x-y|),mem_product.mpr ⟨mem_univ _,hab⟩,
        by simp [signed,abs_of_nonneg (sub_nonneg.mpr h)]⟩
    · exact mem_image.mpr ⟨(false,|x-y|),mem_product.mpr ⟨mem_univ _,hab⟩,
        by simp [signed,abs_of_nonpos (sub_nonpos.mpr h)]⟩
  calc
    _ ≤ _ := card_le_card hs
    _ ≤ (univ ×ˢ D : Finset (Bool × ℝ)).card := card_image_le
    _ = 2*D.card := by simp
    _ ≤ _ := Nat.mul_le_mul_left 2 (card_insert_le _ _)
private theorem Zq {A : Finset ℝ} (h : (A : Set ℝ).IsIsoscelesFree) :
    ThreeAPFree (A : Set ℝ) := by
  intro a ha b hb c hc he
  by_contra hab
  have hac : a ≠ c := by intro e; apply hab; linarith
  have hbc : b ≠ c := by intro e; apply hab; linarith
  apply h ha hb hc hab hbc hac
  left
  rw [Real.dist_eq, Real.dist_eq, show a - b = b - c by linarith]
theorem main : H1 → H2 → type_of% @Erdos657.erdos_657.variants.dim_one_lower := by
  rintro ⟨C,hC,hmodel⟩ ⟨T,hT,hroth⟩
  let e : ℝ := 1 / 16
  have he : 0 < e := by norm_num [e]
  refine ⟨e,he,?_⟩
  have hg : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ e) atTop atTop :=
    (tendsto_rpow_atTop he).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hg.eventually_gt_atTop (1 + 4*T*C*3^8),eventually_ge_atTop 2] with n hn hn2
  intro A hA hiso
  let L := (Real.log (n : ℝ)) ^ e
  have hn' : 0 < (n : ℝ) := by positivity
  have hL : 1 ≤ L := by
    change 1 + 4*T*C*3^8 < L at hn
    linarith [show 0 < 4*T*C*3^8 by positivity]
  have hp : L ^ 16 = Real.log (n : ℝ) := by
    dsimp [L]
    rw [← Real.rpow_mul_natCast (Real.log_nonneg (x := (n : ℝ)) (by exact_mod_cast (show 1 ≤ n by omega)))]
    norm_num [e]
  by_contra! small
  have hD : ((A - A).card : ℝ) ≤ 3*L*A.card := by
    have hd : ((A - A).card : ℝ) ≤ 2 * ((distinctDistances A : ℝ) + 1) := by
      exact_mod_cast diffs A
    rw [hA]
    change (distinctDistances A : ℝ) < (n : ℝ)*L at small
    nlinarith [mul_le_mul_of_nonneg_left hL hn'.le, show (2:ℝ) ≤ n by exact_mod_cast hn2]
  obtain ⟨N,B,g,hsub,hcard,hsz,hm,hi,hap⟩ :=
    hmodel A (3*L) (by linarith) (by omega) hD
  have hb : ThreeAPFree (B : Set ℕ) := by
    intro a ha b hbb c hc habc
    exact hi ha hbb (Zq hiso (hm ha) (hm hbb) (hm hc) (hap a ha b hbb c hc habc))
  rw [hA] at hsz hcard
  have hBN : B.card ≤ N := by simpa using card_le_card hsub
  have hlog : Real.log (n : ℝ) ≤ Real.log (4 * (N : ℝ)) :=
    Real.log_le_log hn' (by exact_mod_cast (show n ≤ 4*N by omega))
  have hsum : (n : ℝ)*Real.log n ≤ 4*T*C*(3*L)^8*n := calc
    _ ≤ (4*(B.card : ℝ))*Real.log (4*(N : ℝ)) :=
      mul_le_mul (by exact_mod_cast hcard) hlog (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) (by positivity)
    _ ≤ 4*(T*N) := by linarith [hroth N B hsub hb]
    _ ≤ 4*T*(C*(3*L)^8*n) := by nlinarith [mul_le_mul_of_nonneg_left hsz hT.le]
    _ = _ := by ring
  have hcancel : L^16 ≤ (4*T*C*3^8)*L^8 := by
    apply (le_of_mul_le_mul_right (a := (n : ℝ)) · hn')
    rw [hp]
    linarith only [show (n : ℝ)*Real.log n ≤ 4*T*C*(3*L)^8*n from hsum]
  have hpow : L ≤ L^8 := le_self_pow₀ hL (by decide)
  have h8 : 0 < L^8 := by positivity
  have hcoef : L^8 ≤ 4*T*C*3^8 := by
    apply (le_of_mul_le_mul_right (a := L^8) · h8)
    nlinarith only [hcancel, show L^8*L^8 = L^16 by ring]
  change 1 + 4*T*C*3^8 < L at hn
  linarith
end OMA.R1
end OMA.R1Piece
namespace OMA.L1
open Finset Set MeasureTheory
namespace OMA.Avoid657
theorem avoid (D : Finset ℝ) : ∃ t : ℝ, ∀ d ∈ D, d ≠ 0 → ∀ z : ℤ,
    2 ≤ |((16*(D.card+1):ℕ):ℝ)*(t*d-z)| := by
  classical
  let N : ℝ := ((16*(D.card+1):ℕ):ℝ)
  let ε : ℝ := 2/N
  let T : ℝ := 1 + ∑ d ∈ D, 2/|d|
  have hN : 0<N := by dsimp [N]; positivity
  have eps : 0<ε := div_pos (by norm_num) hN
  have eps1 : ε≤1 := by
    apply (div_le_one hN).2
    dsimp [N]; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) D.card]
  have hT : 0<T := by dsimp [T]; positivity
  have large {d} (hd : d∈D) (ne:d≠0) : 2≤T*|d| := by
    have hs := single_le_sum (f:=fun x:ℝ ↦ 2/|x|) (fun _ _ ↦ by positivity) hd
    apply (div_le_iff₀ (abs_pos.mpr ne)).1
    exact hs.trans (by dsimp [T]; linarith)
  let J (d:ℝ) := ⌊T*|d|⌋₊+2
  let I (d:ℝ) (j:ℕ) := Icc (((j:ℝ)-ε)/|d|) (((j:ℝ)+ε)/|d|)
  let Bad (d:ℝ) := ⋃ j ∈ range (J d), I d j
  let U := ⋃ d ∈ D.erase 0, Bad d
  have size {d} (hd:d∈D.erase 0) : volume.real (Bad d) ≤ 4*ε*T := by
    obtain ⟨ne, mem⟩ := mem_erase.mp hd
    have dp := abs_pos.mpr ne
    have hj : (J d:ℝ) ≤ 2*(T*|d|) := by
      dsimp [J]; push_cast
      linarith [Nat.floor_le (mul_nonneg hT.le dp.le),large mem ne]
    have vol (j:ℕ) : volume.real (I d j)=2*ε/|d| := by
      dsimp [I]
      rw [Real.volume_real_Icc_of_le (div_le_div_of_nonneg_right (by linarith) dp.le)]
      ring
    calc _ ≤ ∑ j ∈ range (J d), volume.real (I d j) := measureReal_biUnion_finset_le ..
         _ = (J d:ℝ)*(2*ε/|d|) := by simp [vol]
         _ ≤ (2*(T*|d|))*(2*ε/|d|) := mul_le_mul_of_nonneg_right hj (by positivity)
         _ = _ := by field_simp; ring
  have total : volume.real U < T := by
    calc _ ≤ ∑ d ∈ D.erase 0, volume.real (Bad d) := measureReal_biUnion_finset_le ..
         _ ≤ ∑ _d ∈ D.erase 0, 4*ε*T := sum_le_sum fun _ h ↦ size h
         _ ≤ (D.card:ℝ)*(4*ε*T) := by
           simp only [sum_const,nsmul_eq_mul]
           gcongr
           exact erase_subset _ _
         _ < T := by
           dsimp [ε,N]
           push_cast
           have hd : 0≤(D.card:ℝ) := Nat.cast_nonneg _
           field_simp
           nlinarith only [hT, mul_nonneg hd hT.le]
  have comp : IsCompact U := (D.erase 0).isCompact_biUnion fun d _ ↦
    (range (J d)).isCompact_biUnion fun _ _ ↦ isCompact_Icc
  obtain ⟨t, ta, tout⟩ : ∃ t ∈ Icc 0 T, t ∉ U := by
    by_contra! h
    have vv := measureReal_mono (μ:=volume) (s₁:=Icc 0 T) (s₂:=U)
      (fun t ht ↦ h t ht) comp.measure_lt_top.ne
    rw [Real.volume_real_Icc_of_le hT.le, sub_zero] at vv
    exact (not_lt_of_ge vv) total
  refine ⟨t, ?_⟩
  intro d hd ne z
  by_contra! h
  change |N*(t*d-z)|<2 at h
  rw [abs_mul, abs_of_pos hN, mul_comm] at h
  have near := (lt_div_iff₀ hN).2 h
  change |t*d-z|<ε at near
  have near' := (abs_abs_sub_abs_le_abs_sub (t*d) (z:ℝ)).trans_lt near
  have zn : (z.natAbs:ℝ)=|(z:ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [abs_mul,abs_of_nonneg ta.1,←zn] at near'
  obtain ⟨lo,hi⟩ := abs_lt.mp near'
  have dp := abs_pos.mpr ne
  have index : z.natAbs < J d := by
    have htd := mul_le_mul_of_nonneg_right ta.2 dp.le
    apply Nat.cast_lt (α:=ℝ) |>.mp
    dsimp [J]; push_cast
    linarith [Nat.lt_floor_add_one (T*|d|)]
  apply tout
  simp only [U,Bad,Set.mem_iUnion,exists_prop]
  exact ⟨d, mem_erase.mpr ⟨ne,hd⟩,z.natAbs,mem_range.mpr index,
    (div_le_iff₀ dp).2 (by linarith), (le_div_iff₀ dp).2 (by linarith)⟩
end OMA.Avoid657
open Finset
open scoped Pointwise
namespace OMA.Model657
theorem build
    (avoid : ∀ D : Finset ℝ, ∃ t : ℝ, ∀ d ∈ D, d ≠ 0 → ∀ z : ℤ,
      2 ≤ |((16*(D.card+1):ℕ):ℝ)*(t*d-z)|) :
    ∃ C : ℝ, 0<C ∧ ∀ (A : Finset ℝ) (K : ℝ), 1≤K → 0<A.card →
      ((A-A).card:ℝ) ≤ K*A.card →
      ∃ (N : ℕ) (B : Finset ℕ) (g : ℕ → ℝ), B⊆range N ∧ A.card≤4*B.card ∧
        (N:ℝ)≤C*K^8*A.card ∧ Set.MapsTo g (B:Set ℕ) (A:Set ℝ) ∧
        Set.InjOn g (B:Set ℕ) ∧
        (∀ a∈B, ∀ b∈B, ∀ c∈B, a+c=b+b → g a+g c=g b+g b) := by
  classical
  refine ⟨32, by norm_num, ?_⟩
  intro A K hK hA hd
  let D := (A+A)-(A+A)
  let N := 16*(D.card+1)
  have npos : 0<N := by dsimp [N]; omega
  obtain ⟨t, ht⟩ := avoid D
  let f (x : ℝ) : ℕ := ⌊(N:ℝ)*Int.fract (t*x)⌋₊
  have err (x : ℝ) :
      (f x:ℝ) ≤ (N:ℝ)*(t*x-(⌊t*x⌋:ℤ)) ∧ (N:ℝ)*(t*x-(⌊t*x⌋:ℤ)) < (f x:ℝ)+1 :=
    ⟨Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (Int.fract_nonneg _)), Nat.lt_floor_add_one _⟩
  have reflect {a b c d : ℝ} (ha:a∈A) (hb:b∈A) (hc:c∈A) (hd':d∈A)
      (eq : f a+f b=f c+f d) : a+b=c+d := by
    by_contra ne
    have hm : (a+b)-(c+d) ∈ D := sub_mem_sub (add_mem_add ha hb) (add_mem_add hc hd')
    have h := ht _ hm (sub_ne_zero.mpr ne) (⌊t*a⌋+⌊t*b⌋-(⌊t*c⌋+⌊t*d⌋))
    change 2 ≤ |(N:ℝ)*_| at h
    push_cast at h
    have heq : (f a:ℝ)+f b=(f c:ℝ)+f d := by exact_mod_cast eq
    apply (not_lt_of_ge h)
    apply abs_lt.mpr
    constructor <;> nlinarith only [heq, (err a).1, (err a).2, (err b).1, (err b).2,
      (err c).1, (err c).2, (err d).1, (err d).2]
  have inj : Set.InjOn f (A : Set ℝ) := by
    intro a ha b hb eq
    exact add_right_cancel (reflect ha ha hb ha (congrArg (·+f a) eq))
  let B := A.image f
  let g := Function.invFunOn f (A:Set ℝ)
  have left {a} (ha:a∈A) : g (f a)=a := inj.leftInvOn_invFunOn ha
  have right {b} (hb:b∈B) : g b ∈ A ∧ f (g b)=b := by
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    rw [left ha]
    exact ⟨ha,rfl⟩
  have size : (D.card:ℝ) ≤ K^4*A.card := by
    have h := pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub (card_pos.mp hA) A 2 2
    have h' : (D.card:ℝ) ≤ (((A-A).card:ℝ)/A.card)^4*A.card := by
      dsimp [D]
      simpa only [two_nsmul, NNRat.cast_natCast, NNRat.cast_mul, NNRat.cast_pow,
        NNRat.cast_div] using (NNRat.cast_le (K:=ℝ)).mpr h
    apply h'.trans
    gcongr
    exact (div_le_iff₀ (by exact_mod_cast hA)).mpr hd
  refine ⟨N,B,g,?_,?_,?_,fun _ hb ↦ (right hb).1,?_,?_⟩
  · intro b hb
    obtain ⟨a, _, rfl⟩ := mem_image.mp hb
    apply Finset.mem_range.mpr
    apply (Nat.floor_lt' npos.ne').2
    simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one (t*a)) (by exact_mod_cast npos : 0<(N:ℝ))
  · rw [show B.card=A.card from card_image_of_injOn inj]; omega
  · have h4 : 1≤K^4 := one_le_pow₀ hK
    have h8 : K^4≤K^8 := pow_le_pow_right₀ hK (by norm_num)
    have ha : 1≤(A.card:ℝ) := by exact_mod_cast hA
    have s1 := one_le_mul_of_one_le_of_one_le h4 ha
    have s2 := mul_le_mul_of_nonneg_right h8 (Nat.cast_nonneg A.card)
    dsimp [N]
    push_cast
    nlinarith only [size,s1,s2]
  · intro b hb c hc eq
    rw [←(right hb).2,←(right hc).2,eq]
  · intro a ha b hb c hc eq
    apply reflect (right ha).1 (right hc).1 (right hb).1 (right hb).1
    simpa only [(right ha).2,(right hb).2,(right hc).2] using eq
end OMA.Model657
theorem solve : OMA.R1.H1 :=
  OMA.Model657.build OMA.Avoid657.avoid
end OMA.L1
noncomputable section
abbrev Io := @Finset.sum_congr
abbrev Q0 := @AddChar.norm_apply
abbrev Q1 := @Real.exp_pos
abbrev Q2 := @smul_eq_mul
abbrev Q3 := @mul_one
abbrev Q4 := @Nat.le_mul_of_pos_right
abbrev Q5 := @Nat.cast_nonneg
abbrev Q6 := @mul_left_comm
abbrev Q7 := @mul_mul_mul_comm
abbrev Q8 := @abs_nonneg
abbrev Q9 := @div_le_one
abbrev QA := @congrArg
abbrev QB := @Real.log_pow
abbrev QC := @abs_of_nonneg
abbrev QD := @Finset.sum_comm
abbrev QE := @Finset.sum_filter
abbrev QF := @div_le_iff₀
abbrev QG := @Real.log_le_log
abbrev QH := @pow_nonneg
abbrev QI := @Finset.sum_le_sum
abbrev QJ := @Finset.sum_sub_distrib
abbrev QK := @Real.norm_eq_abs
abbrev QL := @mul_pow
abbrev QM := @mul_pos
abbrev QN := @mul_right_comm
abbrev QO := @norm_mul
abbrev QP := @Nat.mul_pos
abbrev QQ := @Nat.mul_le_mul_right
abbrev QR := @Nat.pow_le_pow_right
abbrev QS := @nsmul_eq_mul
abbrev QT := @one_mul
abbrev QU := @pow_mul
abbrev QV := @lt_of_not_ge
abbrev QW := @mul_le_mul
abbrev QX := @Real.log_le_sub_one_of_pos
abbrev QY := @AddCircle.homeomorphCircle_apply
abbrev QZ := @translate_apply
abbrev Qi := @mul_le_mul_of_nonneg_right
abbrev Qj := @Finset.mul_sum
abbrev Qk := @Fintype.sum_equiv
abbrev Ql := @Real.log_mul
abbrev Qm := @Set.indicator_apply
abbrev Qn := @mul_nonneg
abbrev Qo := @mul_assoc
abbrev Qp := @pow_le_pow_left₀
abbrev Qr := @Nat.mul_le_mul_left
abbrev Qs := @le_div_iff₀
abbrev Qt := @Finset.sum_mul
abbrev Qu := @Finset.card_le_card
abbrev Qv := @Real.log_nonneg
abbrev Qw := @div_eq_mul_inv
abbrev Qx := @mul_comm
abbrev Qy := @sub_eq_add_neg
abbrev Qz := @div_le_div_of_nonneg_right
abbrev R0 := @pow_sub_one_mul
abbrev R1 := @Fintype.card_le_of_injective
abbrev R2 := @ENNReal.some_eq_coe
abbrev R3 := @RCLike.conj_to_real
abbrev R4 := @Nat.pow_le_pow_left
abbrev R5 := @two_mul
abbrev R6 := @one_div
abbrev R7 := @Real.exp_add
abbrev R8 := @Nat.mul_comm
abbrev R9 := @div_le_div_iff_of_pos_right
abbrev RA := @Real.norm_of_nonneg
abbrev RB := @pow_succ
abbrev RD := @Pi.smul_apply
abbrev RF := @pow_pos
abbrev RG := @NNReal.smul_def
abbrev RH := @one_le_pow₀
abbrev RI := @Subtype.ext
abbrev RJ := @inv_le_inv₀
abbrev RK := @map_sum
abbrev RL := @pow_add
abbrev RM := @Pi.add_apply
abbrev RN := @Real.rpow_natCast
abbrev RO := @AddChar.sub_apply
abbrev RP := @if_pos
abbrev RQ := @mul_le_of_le_one_left
abbrev RR := @nonempty_fintype
abbrev RS := @div_nonneg
abbrev RT := @abs_of_pos
abbrev RU := @map_mul
abbrev RV := @add_comm
abbrev RW := @Fintype.expect_equiv
abbrev RX := @Fintype.mem_piFinset
abbrev RY := @Nat.lt_floor_add_one
abbrev RZ := @Nat.add_le_add_right
abbrev Ra := @Nat.mul_le_mul
abbrev Rb := @div_le_div_of_nonneg_left
abbrev Rc := @starRingEnd_apply
abbrev Rd := @not_lt_of_ge
abbrev Re := @norm_nonneg
abbrev Rf := @Complex.norm_real
abbrev Rg := @pow_ne_zero
abbrev Rh := @Function.comp_apply
abbrev Ri := @div_eq_inv_mul
abbrev Rj := @Fintype.expect_eq_sum_div_card
abbrev Rk := @Fintype.exists_lt_card_fiber_of_mul_lt_card
abbrev Rl := @mul_ne_zero
abbrev Rm := @Nat.cast_mul
abbrev Rn := @div_pos
abbrev Ro := @Finset.sum_subset
abbrev Rp := @Finset.mem_insert
abbrev Rq := @norm_sum_le
abbrev Rr := @Nat.le_ceil
abbrev Rs := @sub_add_cancel
abbrev Rt := @Pi.one_apply
abbrev Ru := @Nat.cast_ne_zero
abbrev Rv := @Nat.cast_pow
abbrev Rw := @Pi.sub_apply
abbrev Rx := @Fintype.card_coe
abbrev Ry := @Finset.sum_le_sum_of_subset_of_nonneg
abbrev Rz := @AddChar.inv_apply_eq_conj
abbrev S0 := @Real.rpow_mul
abbrev S2 := @NNReal.HolderConjugate.conjExponent
abbrev S3 := @Nat.ceil_mono
abbrev S4 := @Real.rpow_inv_rpow
abbrev S5 := @mul_div_right_comm
abbrev S6 := @DFunLike.congr_fun
abbrev S7 := @Finset.subset_univ
abbrev S8 := @sub_left_injective
abbrev S9 := @NNReal.coe_natCast
abbrev SA := @Finite.bddAbove_range
abbrev SB := @Fintype.piFinset_univ
abbrev SC := @le_antisymm
abbrev SD := @two_ne_zero
abbrev SE := @NNReal.coe_inv
abbrev SF := @le_rfl
abbrev SG := @le_abs_self
abbrev SH := @mul_div_cancel_left₀
abbrev SI := @lt_of_lt_of_le
abbrev SJ := @pow_le_pow_of_le_one
abbrev SK := @NNReal.coe_mul
abbrev SL := @Fintype.card_subtype
abbrev SM := @lt_of_le_of_ne
abbrev SN := @Fintype.card_ne_zero
abbrev SO := @Finset.sum_erase_add
abbrev SP := @lt_div_iff₀
abbrev SQ := @Real.rpow_pos_of_pos
abbrev SR := @congr_fun
abbrev SS := @boole_mul
abbrev SU := @abs_mul
abbrev SV := @RCLike.inner_apply'
abbrev SW := @Real.log_le_log_iff
abbrev SX := @Equiv.subLeft_apply
abbrev SY := @sq_pos_of_pos
abbrev SZ := @Nat.mul_assoc
abbrev Sa := @tendsto_natCast_atTop_atTop
abbrev Sb := @RCLike.inner_apply
abbrev Sc := @Real.pow_rpow_inv_natCast
abbrev Sd := @Finset.inter_subset_right
abbrev Se := @pow_le_pow_right₀
abbrev Sf := @Real.rpow_le_rpow
abbrev Sg := @RCLike.wInner_one_eq_sum
abbrev Sh := @Finset.inter_subset_left
abbrev Si := @Finset.sum_apply
abbrev Sj := @le_trans
abbrev Sk := @mul_lt_mul_of_pos_right
abbrev Sl := @Nat.mod_eq_of_lt
abbrev Sm := @Finset.mem_of_mem_erase
abbrev Sn := @max_le_max_right
abbrev So := @Nat.cast_two
abbrev Sp := @Nat.cast_pos
abbrev Sq := @mul_le_of_le_one_right
abbrev Sr := @add_le_add
abbrev Ss := @le_add_of_nonneg_right
abbrev St := @AddChar.map_add_eq_mul
abbrev Su := @abs_sub_comm
abbrev Sv := @Real.log_pos
abbrev Sw := @Finset.ne_of_mem_erase
abbrev Sx := @ENNReal.HolderConjugate.eq_top_iff_eq_one
abbrev Sy := @div_le_div_iff₀
abbrev Sz := @Finset.mem_univ
abbrev T0 := @starRingEnd_self_apply
abbrev T2 := @even_two_mul
abbrev T3 := @Nat.cast_add
abbrev T4 := @tsub_le_self
abbrev T6 := @mul_lt_mul_of_pos_left
abbrev T7 := @Finset.sum_add_distrib
abbrev T8 := @Real.closedBall_eq_Icc
abbrev T9 := @Nat.le_mul_of_pos_left
abbrev TA := @inv_mul_le_iff₀
abbrev TB := @ZMod.natCast_eq_natCast_iff'
abbrev TC := @Fintype.card_pi
abbrev TD := @AddCircle.injective_toCircle
abbrev TE := @abs_div
abbrev TF := @pow_sum_div_card_le_sum_pow
abbrev TG := @Fintype.card_piFinset_const
abbrev TH := @AddChar.expect_apply_eq_ite
abbrev TI := @pow_two
abbrev TJ := @smul_mul_assoc
abbrev TK := @inv_mul_eq_div
abbrev TL := @add_sub_cancel
abbrev TM := @true_and
abbrev TN := @NNReal.coe_one
abbrev TO := @neg_le_neg
abbrev TP := @Finset.sum_div
abbrev TQ := @Finset.abs_sum_le_sum_abs
abbrev TR := @Pi.conj_apply
abbrev TS := @Real.rpow_neg
abbrev TT := @Real.sqrt_pos
abbrev TU := @apply_ite
abbrev TV := @AddChar.map_neg_eq_conj
abbrev TW := @Finset.prod_mul_distrib
abbrev TX := @Finset.exists_max_image
abbrev TY := @div_pow
abbrev TZ := @le_of_mul_le_mul_right
abbrev Ta := @Real.mul_self_sqrt
abbrev Tb := @Set.mem_vadd_set_iff_neg_vadd_mem
abbrev Tc := @mul_add
abbrev Td := @mul_ite
abbrev Te := @inv_pow
abbrev Tf := @eq_or_ne
abbrev Tg := @Real.coe_toNNReal
abbrev Th := @Real.rpow_le_rpow_of_exponent_ge
abbrev Ti := @Nat.floor_le
abbrev Tj := @Finset.sum_le_univ_sum_of_nonneg
abbrev Tk := @ENNReal.HolderConjugate.ne_zero
abbrev Tl := @RCLike.conj_conj
abbrev Tm := @and_assoc
abbrev Tn := @Real.rpow_nonneg
abbrev To := @not_nonempty_iff
abbrev Tp := @Finset.sum_sub_sum_mem_addSpan
abbrev Tq := @Finset.sum_const
abbrev Tr := @Nat.lt_succ_self
abbrev Ts := @AddCircle.norm_coe_eq_abs_iff
abbrev Tt := @Finset.sum_lt_sum_of_nonempty
abbrev Tu := @le_max_left
abbrev Tv := @div_lt_iff₀
abbrev Tw := @mul_inv_cancel₀
abbrev Tx := @pos_iff_ne_zero
abbrev Ty := @Nat.succ_le_iff
abbrev Tz := @div_mul_cancel₀
abbrev U0 := @NNReal.coe_le_coe
abbrev U1 := @one_pos
abbrev U2 := @AddChar.neg_apply
abbrev U3 := @AddChar.add_apply
abbrev U4 := @Real.sqrt_eq_rpow
abbrev U5 := @Nat.zero_lt_of_lt
abbrev U6 := @Nat.mul_left_comm
abbrev UA := @Complex.norm_natCast
abbrev UB := @Fintype.sum_mul_sum
abbrev UC := @isEmpty_or_nonempty
abbrev UD := @ENNReal.none_eq_top
abbrev UE := @translate_sub_right
abbrev UF := @Finset.mem_symmDiff
abbrev UG := @addRothNumber_spec
abbrev UH := @CharP.cast_eq_zero
abbrev UI := @algebraMap.coe_pow
abbrev UJ := @ENNReal.toReal_pos
abbrev UK := @ENNReal.toReal_mul
abbrev UL := @Fintype.sum_ite_eq
abbrev UM := @one_add_mul_le_pow
abbrev UN := @Finset.sum_eq_zero
abbrev UO := @Finset.prod_le_one
abbrev UP := @abs_add_le
abbrev UQ := @not_ne_iff
abbrev UR := @tendsto_rpow_atTop
abbrev US := @add_mul
abbrev UT := @sub_div
abbrev UU := @Finset.mem_filter
abbrev UW := @div_le_one_of_le₀
abbrev UX := @Complex.conj_mul'
abbrev UY := @mul_sub
abbrev UZ := @Finset.sum_nonneg
abbrev Ua := @Finset.mem_union_right
abbrev Ub := @AddCircle.toCircle_add
abbrev Uc := @Nat.floor_lt
abbrev Ud := @AddChar.map_neg_eq_inv
abbrev Ue := @ENNReal.toReal_natCast
abbrev Uf := @Real.sq_sqrt
abbrev Ug := @Finset.mem_vadd_finset
abbrev Uh := @Real.exp_neg
abbrev Ui := @Real.log_div
abbrev Uj := @le_of_mul_le_mul_left
abbrev Uk := @Complex.normSq_nonneg
abbrev Ul := @Fintype.sum_prod_type
abbrev Um := @Finset.mem_union_left
abbrev Un := @Complex.re_ofReal_mul
abbrev Uo := @Classical.choose_spec
abbrev Up := @norm_inv
abbrev Uq := @ne_of_gt
abbrev Ur := @Function.mem_support
abbrev Us := @zero_le_one
abbrev Ut := @Equiv.subRight_apply
abbrev Uu := @congrFun
abbrev Uv := @min_le_left
abbrev Uw := @one_le_inv₀
abbrev Ux := @Finset.card_powerset
abbrev Uy := @pow_le_one₀
abbrev Uz := @vadd_eq_add
abbrev iO := @mul_le_mul_of_nonneg_left
end
open MeasureTheory
section
open Finset Function
namespace ay
section z8
variable {α:Type*} [AddCommMonoid α] [DecidableEq α]
def dL (A:Finset α):ℕ :=
 #(((A ×ˢ A) ×ˢ A).filter fun x↦x.1.1+x.2=x.1.2+x.1.2)
variable [IsCancelAdd α]
lemma uH {A:Finset α} (hA:ThreeAPFree (A:Set α)) :
  dL A= #A:=by
 classical
 let D:Finset ((α × α) × α):=A.image fun a↦((a,a),a)
 have eI :
   (((A ×ˢ A) ×ˢ A).filter fun x↦x.1.1+x.2=x.1.2+x.1.2)=D:=by
  ext x
  rcases x with ⟨⟨a,b⟩,c⟩
  simp only[mem_filter,mem_product,D,mem_image]
  constructor
  ·rintro ⟨⟨⟨ha,hb⟩,hc⟩,pG⟩
   have hab:a=b:=hA ha hb hc pG
   have NZ:b=c:=hA.eq_right ha hb hc pG
   exact ⟨b,hb,by simp[hab,NZ]⟩
  ·rintro ⟨d,hd,Cw⟩
   have PR:d=a:=QA (fun x↦x.1.1) Cw
   have N0:d=b:=QA (fun x↦x.1.2) Cw
   have PS:d=c:=QA (fun x↦x.2) Cw
   subst a
   subst b
   subst c
   simp[hd]
 change #(((A ×ˢ A) ×ˢ A).filter fun x↦x.1.1+x.2=x.1.2+x.1.2)= #A
 rw[eI]
 change #(A.image fun a↦((a,a),a))= #A
 rw[card_image_of_injective]
 intro a b hab
 exact QA (fun x↦x.1.1) hab
end z8
section xQ
abbrev aD (N:ℕ):ℕ:=2*N+1
abbrev cn (N:ℕ) (a:ℕ):ZMod (aD N):=a
lemma gz (N:ℕ) :
  Set.InjOn (cn N) (Set.Iic N):=by
 intro a ha b hb hab
 change a≤N at ha
 change b≤N at hb
 have KX:a<aD N:=by
  change a<2*N+1
  omega
 have KY:b<aD N:=by
  change b<2*N+1
  omega
 have yE :=
  (TB a b (aD N)).mp hab
 rwa[Sl KX,Sl KY] at yE
lemma iS {N a b c d:ℕ}
  (ha:a≤N) (hb:b≤N) (hc:c≤N) (hd:d≤N) :
  cn N a+cn N c =
    cn N b+cn N d ↔
   a+c=b+d:=by
 constructor
 ·intro h
  have hcast:((a+c:ℕ):ZMod (aD N)) =
    ((b+d:ℕ):ZMod (aD N)):=by
   simpa only[T3] using h
  have IY:a+c<aD N:=by
   change a+c<2*N+1
   omega
  have IZ:b+d<aD N:=by
   change b+d<2*N+1
   omega
  have yE :=
   (TB (a+c) (b+d) (aD N)).mp hcast
  rwa[Sl IY,Sl IZ] at yE
 ·intro h
  simpa only[T3] using
   QA (fun n:ℕ↦(n:ZMod (aD N))) h
def cY (N:ℕ) (A:Finset ℕ):Finset (ZMod (aD N)) :=
 A.image (cn N)
@[simp] lemma fh {N:ℕ} {A:Finset ℕ} {x:ZMod (aD N)} :
  x∈cY N A↔ ∃ a∈A,cn N a=x:=by
 simp[cY]
lemma vF {N:ℕ} {A:Finset ℕ}
  (hA: ∀ a∈A,a≤N): #(cY N A)= #A:=by
 rw[cY,card_image_iff]
 exact fun a ha b hb h↦gz N (hA a ha) (hA b hb) h
lemma qR {N:ℕ} {A:Finset ℕ}
  (hA: ∀ a∈A,a≤N) :
  dL (cY N A)=dL A:=by
 classical
 let f:((ℕ × ℕ) × ℕ)→((ZMod (aD N) × ZMod (aD N)) ×
   ZMod (aD N)):=fun x ↦
  ((cn N x.1.1,cn N x.1.2),cn N x.2)
 let T:Finset ((ℕ × ℕ) × ℕ) :=
  ((A ×ˢ A) ×ˢ A).filter fun x↦x.1.1+x.2=x.1.2+x.1.2
 let U:Finset ((ZMod (aD N) × ZMod (aD N)) ×
   ZMod (aD N)) :=
  (((cY N A ×ˢ cY N A) ×ˢ cY N A).filter fun x ↦
   x.1.1+x.2=x.1.2+x.1.2)
 have N1:U=T.image f:=by
  ext x
  rcases x with ⟨⟨x,y⟩,z⟩
  constructor
  ·intro FK
   have KZ :
     x∈cY N A∧y∈cY N A∧z∈cY N A ∧
      x+z=y+y:=by
    simpa[U,Tm] using FK
   rcases KZ with ⟨hx,hy,hz,uI⟩
   obtain ⟨a,ha,rfl⟩:=fh.mp hx
   obtain ⟨b,hb,rfl⟩:=fh.mp hy
   obtain ⟨c,hc,rfl⟩:=fh.mp hz
   refine mem_image.mpr ⟨((a,b),c), ?_,rfl⟩
   have pG:a+c=b+b :=
    (iS (hA a ha) (hA b hb) (hA c hc) (hA b hb)).1 uI
   simp[T,ha,hb,hc,pG]
  ·intro FK
   obtain ⟨⟨⟨a,b⟩,c⟩,xg,Hl⟩:=mem_image.mp FK
   have Cx:a∈A∧b∈A∧c∈A∧a+c=b+b:=by
    simpa[T,Tm] using xg
   rcases Cx with ⟨ha,hb,hc,pG⟩
   have hx:cn N a∈cY N A :=
    fh.mpr ⟨a,ha,rfl⟩
   have hy:cn N b∈cY N A :=
    fh.mpr ⟨b,hb,rfl⟩
   have hz:cn N c∈cY N A :=
    fh.mpr ⟨c,hc,rfl⟩
   have uI:cn N a+cn N c =
     cn N b+cn N b :=
    (iS (hA a ha) (hA b hb) (hA c hc) (hA b hb)).2 pG
   rw[←Hl]
   simp[U,f,hx,hy,hz,uI]
 have hf:Set.InjOn f T:=by
  rintro ⟨⟨a,b⟩,c⟩ pG ⟨⟨a',b'⟩,c'⟩ Cx heq
  have xg:a∈A∧b∈A∧c∈A∧a+c=b+b:=by
   simpa[T,Tm] using pG
  have D1:a'∈A∧b'∈A∧c'∈A∧a'+c'=b'+b':=by
   simpa[T,Tm] using Cx
  rcases xg with ⟨ha,hb,hc, -⟩
  rcases D1 with ⟨mM,N2,hc', -⟩
  have N3:a=a':=gz N (hA a ha) (hA a' mM)<|
   QA (fun x↦x.1.1) heq
  have N4:b=b':=gz N (hA b hb) (hA b' N2)<|
   QA (fun x↦x.1.2) heq
  have N5:c=c':=gz N (hA c hc) (hA c' hc')<|
   QA (fun x↦x.2) heq
  simp[N3,N4,N5]
 change #U= #T
 rw[N1,card_image_of_injOn hf]
end xQ
end ay
end
section
open Filter Finset
open scoped Topology
namespace ay
noncomputable def r3 (N:ℕ):ℕ :=
 addRothNumber (Finset.Icc 1 N)
lemma vt (N:ℕ):r3 N=rothNumberNat N:=by
 rw[r3, ←Finset.Ico_add_one_right_eq_Icc,addRothNumber_Ico]
 simp
end ay
end
section
open Filter Finset
open scoped Topology
namespace ay
def dX (K:ℝ) (nJ:ℕ):Prop :=
 0<K ∧
  ∀ (N:ℕ),nJ≤N →
   ∀ (A:Finset ℕ),A⊆Finset.Icc 1 N→ A.Nonempty →
    ∀ d:ℕ,
     1≤d →
     Real.log ((N:ℝ)/(#A:ℝ))≤(d:ℝ)*Real.log 2 →
      Real.exp (-K*(d:ℝ)^12)*(N:ℝ)^2 ≤
       (dL A:ℝ)
lemma fo
  {K:ℝ} {nJ:ℕ} (z9:dX K nJ) :
  ∀ᶠ N:ℕ in atTop,
   (r3 N:ℝ) ≤
    (N:ℝ)*Real.exp
     (-(Real.log 2/(2*K^(1/12:ℝ))) *
      (Real.log (N:ℝ))^(1/12:ℝ)):=by
 have hK:0<K:=z9.1
 have eu:Tendsto (fun N:ℕ=>Real.log (N:ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp Sa
 have FM:Tendsto (fun N:ℕ=>Real.log (N:ℝ)/K) atTop atTop :=
  Tendsto.atTop_div_const hK eu
 have wG :
   Tendsto
    (fun N:ℕ=>(Real.log (N:ℝ)/K)^(1/12:ℝ))
    atTop atTop :=
  (UR (by norm_num:(0:ℝ)<1/12)).comp FM
 filter_upwards[eventually_ge_atTop nJ,eventually_gt_atTop 3,
   wG.eventually_ge_atTop 2] with N I0 hN KO
 obtain ⟨A,zZ,r0,D3⟩:=UG (Finset.Icc 1 N)
 have wH: #A=r3 N:=by simpa[r3] using r0
 have xR:r3 N≤N:=by
  rw[vt]
  exact rothNumberNat_le N
 have B8:0<r3 N:=by
  have Cy:({1}:Finset ℕ)⊆Finset.Icc 1 N:=by
   simpa using(show 1≤N by omega)
  have xS:=addRothNumber.mono Cy
  have N6:1≤addRothNumber (Finset.Icc 1 N):=by simpa using xS
  have:0<addRothNumber (Finset.Icc 1 N):=by omega
  simpa[r3] using this
 have uJ:A.Nonempty:=by
  apply Finset.card_pos.mp
  simpa[wH] using B8
 have xT:(0:ℝ)<N:=by exact_mod_cast(U5 hN)
 have ov:(0:ℝ)<r3 N:=by exact_mod_cast B8
 have w1:(r3 N:ℝ)≤N:=by exact_mod_cast xR
 have Cz:(1:ℝ)≤(N:ℝ)/(r3 N:ℝ):=by
  rw[one_le_div ov]
  exact w1
 have CA:(0:ℝ)<(N:ℝ)/(r3 N:ℝ) :=
  Rn xT ov
 let q:ℝ:=Real.log ((N:ℝ)/(r3 N:ℝ))/Real.log 2
 let d:ℕ:=Nat.ceil q
 have r2:0<Real.log 2:=Sv (by norm_num)
 have D4:0≤q:=by
  exact RS (Qv Cz) r2.le
 have Aa :
   Real.log ((N:ℝ)/(#A:ℝ))≤(d:ℝ)*Real.log 2:=by
  rw[wH]
  rw[←QF r2]
  simpa[q,d] using Rr q
 have CB:r3 N<N:=by
  apply SM xR
  intro heq
  have D5: #(Finset.Icc 1 N)=N:=by
   rw[Nat.card_Icc]
   omega
  have MW:A=Finset.Icc 1 N:=by
   apply Finset.eq_of_subset_of_card_le zZ
   rw[D5,wH,heq]
  have D6:ThreeAPFree (Finset.Icc 1 N:Set ℕ):=by
   simpa[MW] using D3
  have ow:=D6 (a:=1) (b:=2) (c:=3)
   (by simp[show 1≤N by omega]) (by simp[show 2≤N by omega])
   (by simp[show 3≤N by omega]) (by norm_num)
  omega
 have I1:0<q:=by
  have D7:(1:ℝ)<(N:ℝ)/(r3 N:ℝ):=by
   rw[SP ov]
   norm_num
   exact_mod_cast CB
  exact Rn (Sv D7) r2
 have D8:1≤d:=by
  exact(Nat.ceil_pos.mpr I1)
 have ox:=z9.2 N I0 A zZ uJ d D8 Aa
 rw[uH D3,wH] at ox
 have Ho :
   Real.exp (-K*(d:ℝ)^12)*(N:ℝ)^2≤(N:ℝ) :=
  ox.trans w1
 have Ac :
   Real.exp (-K*(d:ℝ)^12)*(N:ℝ)≤1:=by
  have pH :
    (Real.exp (-K*(d:ℝ)^12)*(N:ℝ))*(N:ℝ) ≤
     1*(N:ℝ):=by
   simpa[TI,Qo] using Ho
  exact(TZ pH xT)
 have CD:Real.log (N:ℝ)≤K*(d:ℝ)^12:=by
  have D9 :=
   QG
    (QM (Q1 _) xT)
    Ac
  rw[Ql (Real.exp_ne_zero _) xT.ne',Real.log_exp,
   Real.log_one] at D9
  linarith
 have qg:0≤Real.log (N:ℝ) :=
  Qv (by exact_mod_cast(show 1≤N by omega))
 have Bt:0≤Real.log (N:ℝ)/K :=
  RS qg hK.le
 have Bu:Real.log (N:ℝ)/K≤(d:ℝ)^12:=by
  rw[QF hK]
  simpa[Qx] using CD
 have K0 :
   (Real.log (N:ℝ)/K)^(1/12:ℝ)≤(d:ℝ):=by
  calc
   (Real.log (N:ℝ)/K)^(1/12:ℝ) ≤
     ((d:ℝ)^12)^(1/12:ℝ) :=
    Sf Bt Bu (by norm_num)
   _=(d:ℝ):=by
    convert Sc (show(0:ℝ)≤d by positivity)
     (by norm_num:(12:ℕ)≠0) using 1
    all_goals norm_num
 have KP:(d:ℝ)<q+1:=by
  simpa[d] using Nat.ceil_lt_add_one D4
 have xU :
   (Real.log (N:ℝ)/K)^(1/12:ℝ)/2≤q:=by
  linarith
 have xh :
   (Real.log 2/2) *
     (Real.log (N:ℝ)/K)^(1/12:ℝ) ≤
    Real.log ((N:ℝ)/(r3 N:ℝ)):=by
  calc
   (Real.log 2/2) *
     (Real.log (N:ℝ)/K)^(1/12:ℝ) =
     ((Real.log (N:ℝ)/K)^(1/12:ℝ)/2)*Real.log 2:=by ring
   _≤q*Real.log 2 :=
    Qi xU r2.le
   _=Real.log ((N:ℝ)/(r3 N:ℝ)):=by
    simp[q,r2.ne']
 have CE:0<K^(1/12:ℝ) :=
  SQ hK _
 have Ad :
   (Real.log 2/(2*K^(1/12:ℝ))) *
     (Real.log (N:ℝ))^(1/12:ℝ) =
    (Real.log 2/2) *
     (Real.log (N:ℝ)/K)^(1/12:ℝ):=by
  rw[Real.div_rpow qg hK.le]
  field_simp[CE.ne']
 have zG :
   Real.exp
     ((Real.log 2/(2*K^(1/12:ℝ))) *
      (Real.log (N:ℝ))^(1/12:ℝ)) ≤
    (N:ℝ)/(r3 N:ℝ):=by
  rw[←Real.le_log_iff_exp_le CA]
  rw[Ad]
  exact xh
 have Bv :
   (r3 N:ℝ) *
     Real.exp
      ((Real.log 2/(2*K^(1/12:ℝ))) *
       (Real.log (N:ℝ))^(1/12:ℝ)) ≤
    (N:ℝ):=by
  have:=(Qs ov).mp zG
  simpa[Qx] using this
 calc
  (r3 N:ℝ) ≤
    (N:ℝ) /
     Real.exp
      ((Real.log 2/(2*K^(1/12:ℝ))) *
       (Real.log (N:ℝ))^(1/12:ℝ)) :=
   (Qs (Q1 _)).2 Bv
  _=(N:ℝ) *
    Real.exp
     (-((Real.log 2/(2*K^(1/12:ℝ))) *
      (Real.log (N:ℝ))^(1/12:ℝ))):=by
   rw[Uh,Qw]
  _=(N:ℝ)*Real.exp
    (-(Real.log 2/(2*K^(1/12:ℝ))) *
     (Real.log (N:ℝ))^(1/12:ℝ)):=by
   congr 2
   ring
end ay
end
section
open Finset Function
section
variable {ι α ip:Type*}
section CommMonoidWithZero
variable [CommMonoidWithZero ip] [DecidableEq α]
lemma mN [Fintype α] (s:Finset ι) (t:ι→Finset α) (x:α) :
  (Set.indicator (↑(s.inf t)) fun _↦(1:ip)) x= ∏ i∈s,(Set.indicator (t i) fun _↦(1:_)) x:=by simp[Qm,mem_inf,prod_boole]
end CommMonoidWithZero
end
end
section
open scoped Pointwise
section
variable {α G ip:Type*}
section yF
variable [One ip] [Zero ip] [AddGroup G] [AddAction G α]
@[simp] lemma Ea (g:G) (s:Set α) (a:α):(Set.indicator (g+ᵥ s) fun _↦(1:ip)) a=(Set.indicator s fun _↦(1:_)) (-g+ᵥ a):=by
 classical simp[Qm,Tb]
end yF
end
end
section
open scoped Pointwise
section
variable {G ip:Type*}
section yF
variable [One ip] [Zero ip] [AddGroup G]
@[simp] lemma FF (s:Set G) (a:G):(Set.indicator (-s) fun _↦(1:ip)) a=(Set.indicator s fun _↦(1:_)) (-a):=by
 classical simp[Qm]
end yF
end
end
section
section
variable {F α β ip nJ:Type*}
namespace Set
variable [MonoidWithZero ip] [MonoidWithZero nJ] {s:Set α}
lemma iq (s t:Set α) (x:α):(Set.indicator (s∩t) fun _↦(1:ip)) x=(Set.indicator s fun _↦(1:_)) x*(Set.indicator t fun _↦(1:_)) x:=by
 classical simp[indicator_apply, ←ite_and,and_comm]
lemma rf [FunLike F ip nJ] [MonoidWithZeroHomClass F ip nJ] (f:F) (s:Set α)
  (x:α):f ((Set.indicator s fun _↦(1:_)) x)=(Set.indicator s fun _↦(1:_)) x:=by classical exact MonoidWithZeroHom.map_ite_one_zero ..
variable [Nontrivial ip] {a:α}
lemma qk:(Set.indicator s fun _↦(1:ip)) a≠0↔a∈s:=by
 classical exact one_ne_zero.ite_ne_right_iff
variable (ip) in
@[simp] lemma jY:(Set.indicator s fun _↦(1:ip)).support=s:=by
 ext; exact qk
end Set
end
end
section
section
open scoped Pointwise translate
variable {G ip:Type*}
section Semiring
variable [One ip] [Zero ip] [AddCommGroup G]
variable (ip) in
lemma sR (a:G) (s:Set G):τ a (Set.indicator s fun _↦(1:ip))=(Set.indicator (a+ᵥ s) fun _↦(1:_)):=by
 classical ext; simp[Qm,Tb,sub_eq_neg_add]
end Semiring
end
end
section
section
open scoped ComplexConjugate
variable {G R:Type*}
section CommSemiring
variable [CommSemiring R] [StarRing R] [AddCommGroup G]
end CommSemiring
end
end
section
section
namespace ZMod
variable {M:Type*} {q:ℕ}
end ZMod
end
end
section
section
open scoped Finset BigOperators
namespace AddChar
variable {ι G:Type*} {q:ℕ} [AddCommGroup G]
section
variable {Δ:Set (AddChar G ℂ)} {ψ:AddChar G ℂ} {x:G}
variable [Finite G]
variable {V:AddSubgroup G} [Fintype V]
end
variable [Module (ZMod q) G] {γ:AddChar G ℂ} {r:ZMod q} {x:G}
variable [Fact q.Prime] [FiniteDimensional (ZMod q) G] {γ:ι→ AddChar G ℂ}
 {s:Finset ι}
end AddChar
end
end
section
section
namespace RCLike
variable {K:Type*} [RCLike K]
end RCLike
end
end
section
section
open ENNReal
namespace MeasureTheory
variable {𝕜 α:Type*} {m:MeasurableSpace α} {μ:Measure α} [NormedRing 𝕜]
lemma qS {p q r:ℝ≥0∞} {f g:α→𝕜} (hf:AEStronglyMeasurable f μ)
  (hg:AEStronglyMeasurable g μ) [HolderTriple p q r] :
  eLpNorm (f*g) r μ≤eLpNorm f p μ*eLpNorm g q μ:=by
 simpa using eLpNorm_smul_le_mul_eLpNorm hg hf
end MeasureTheory
end
end
section
section
open Finset Fintype Function
open scoped ComplexConjugate NNReal Pointwise translate
variable {G H R S:Type*} [DecidableEq G] [AddCommGroup G]
section CommSemiring
variable [CommSemiring R]
def uK:G→R:=fun a↦if a=0 then 1 else 0
@[simp] lemma yG (a:G):(uK a:R)=if a=0 then 1 else 0:=rfl
variable [StarRing R]
end CommSemiring
variable [Fintype G]
section CommSemiring
variable [CommSemiring R] {f g:G→R}
def aC (f g:G→R):G→R:=fun a↦ ∑ x:G × G with x.1+x.2=a ,f x.1*g x.2
lemma f7 (f g:G→R) (a:G) :
  ((aC f g)) a= ∑ x:G × G with x.1+x.2=a,f x.1*g x.2:=rfl
lemma CF (f g h:G→R):(aC ((f+g)) h)=(aC f h)+(aC g h):=by
 ext; simp[f7,US,sum_add_distrib]
lemma tj [DistribSMul H R] [IsScalarTower H R R] (c:H) (f g:G→R) :
  (aC (c•f) g)=c•((aC f g)):=by ext a; simp[f7,smul_sum,TJ]
lemma Bw [DistribSMul H R] [SMulCommClass H R R] (c:H) (f g:G→R) :
  (aC f (c•g))=c•((aC f g)):=by ext a; simp[f7,smul_sum,mul_smul_comm]
@[simp] lemma FN (a:G) (f g:G→R):(aC (τ a f) g)=τ a ((aC f g)) :=
 funext fun b↦sum_equiv ((Equiv.subRight a).prodCongr<| Equiv.refl _)
  (by simp[sub_add_eq_add_sub]) (by simp)
lemma fA (f g:G→R):(aC f g)=(aC g f) :=
 funext fun a↦sum_equiv (Equiv.prodComm _ _) (by simp[RV])<| by simp[Qx]
lemma uL [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
  [SMulCommClass H R R] (c d:H) (f g:G→R):(c*d)•((aC f g))=(aC (c•f) (d•g)):=by
 rw[tj,Bw,mul_smul]
lemma iT (f g h:G→R):(aC ((aC f g)) h)=(aC f (((aC g h)))):=by
 ext a
 simp only[sum_mul,mul_sum,f7,Finset.sum_sigma']
 apply sum_nbij' (fun ⟨(_b,c),(d,e)⟩↦⟨(d,e+c),(e,c)⟩)
  (fun ⟨(b,_c),(d,e)⟩↦⟨(b+d,e),(b,d)⟩)<;>aesop (add simp[add_assoc,Qo])
lemma xi (f g h:G→R):(aC f (((aC g h))))=(aC g (((aC f h)))):=by
 rw[←iT, ←iT,fA g]
lemma ir (f g h i:G→R):(aC ((aC f g)) (((aC h i))))=(aC ((aC f h)) (((aC g i)))):=by
 rw[iT,iT,xi g]
lemma xV [CommSemiring S] (m:R→+* S) (f g:G→R) (a:G) :
  m (((aC f g)) a)=((aC (m ∘ f) (m ∘ g))) a:=by simp[f7,RK,RU]
lemma rg (f g:G→R) (a:G):((aC f g)) a= ∑ t,f (a-t)*g t:=by
 rw[f7]; apply sum_nbij' Prod.snd (fun b↦(a-b,b))<;>aesop
lemma cR (f g:G→R) (a:G):((aC f g)) a= ∑ t,f t*g (a-t):=by
 rw[fA,rg]; simp_rw[Qx]
lemma r4 (f g:G→R) (a b:G):((aC f g)) (a+b)= ∑ t,f (a+t)*g (b-t) :=
 (rg _ _ _).trans<| Qk (Equiv.subLeft b) _ _ fun t↦by
  simp[add_sub_assoc]
lemma tP (f g h:G→R): ∑ a,((aC f g)) a*h a= ∑ a, ∑ b,f a*g b*h (a+b):=by
 simp_rw[cR,sum_mul]
 rw[sum_comm]
 exact sum_congr rfl fun x _↦Qk (Equiv.subRight x) _ _ fun y↦by simp
lemma uM (f g:G→R): ∑ a,((aC f g)) a=(∑ a,f a)* ∑ a,g a:=by
 simpa only[UB,Rt,Q3] using tP f g 1
lemma tQ (f g:G→R):support ((aC f g))⊆support f+support g:=by
 rintro a ha
 obtain ⟨x,hx,h⟩:=exists_ne_zero_of_sum_ne_zero ha
 exact ⟨_,left_ne_zero_of_mul h,_,right_ne_zero_of_mul h,(mem_filter.1 hx).2⟩
variable [StarRing R]
def al (f g:G→R):G→R:=fun a↦ ∑ x:G × G with x.1-x.2=a,f x.1*conj g x.2
lemma el (f g:G→R) (a:G) :
  ((al f g)) a= ∑ x:G × G with x.1-x.2=a ,f x.1*conj g x.2:=rfl
@[simp] lemma I2 (f:G→R):(al f 0)=0:=by ext; simp[el]
@[simp] lemma I3 (f:G→R):(al 0 f)=0:=by ext; simp[el]
@[simp] lemma FO (f:G→R):(al f ((fun _↦0)))=0:=by ext; simp[el]
lemma Bx (f g h:G→R):(al f ((g+h)))=(al f g)+(al f h):=by
 ext; simp[el,Tc,sum_add_distrib]
lemma By (f g h:G→R):(al ((f+g)) h)=(al f h)+(al g h):=by
 ext; simp[el,US,sum_add_distrib]
lemma oy [DistribSMul H R] [IsScalarTower H R R] (c:H) (f g:G→R) :
  (al (c•f) g)=c•((al f g)):=by ext; simp[el,smul_sum,TJ]
lemma oz [Star H] [DistribSMul H R] [SMulCommClass H R R] [StarModule H R] (c:H)
  (f g:G→R):(al f (c•g))=star c•((al f g)):=by
 ext; simp[el,smul_sum,mul_smul_comm,Rc,star_smul]
@[simp] lemma rh (a:G) (f g:G→R):(al (τ a f) g)=τ a ((al f g)) :=
 funext fun b↦sum_equiv ((Equiv.subRight a).prodCongr<| Equiv.refl _)
  (by simp[sub_right_comm _ a]) (by simp)
@[simp] lemma iM (f g:G→R):(aC f (conjneg g))=(al f g) :=
 funext fun a↦sum_equiv ((Equiv.refl _).prodCongr<| Equiv.neg _) (by simp) (by simp)
@[simp] lemma FH (f g:G→R) (a:G):conj (((aC f g)) a)=((aC (conj f) (conj g))) a:=by
 simp only[TR,f7,RK,RU]
@[simp] lemma pI (f g:G→R):conjneg ((aC f g))=(aC (conjneg f) (conjneg g)):=by
 funext a
 simp only[f7,conjneg_apply,RK,RU]
 exact sum_equiv (Equiv.neg _) (by simp[←neg_eq_iff_eq_neg,RV]) (by simp)
@[simp] lemma xW (f g:G→R):conjneg ((al f g))=(al g f):=by
 simp_rw[←iM,pI,conjneg_conjneg,fA]
lemma kp (f g h i:G→R):(aC ((al f g)) (((al h i))))=(al ((aC f h)) (((aC g i)))):=by
 simp_rw[←iM,pI,ir]
lemma eL (f g:G→R) (a:G):((al f g)) a= ∑ t,f t*conj (g (t-a)):=by
 simp[←iM,cR]
lemma wR (f g:G→R) (a:G):((al f g)) (-a)=conj (((al g f)) a):=by
 rw[←xW f,conjneg_apply,Complex.conj_conj]
lemma ri (f g:G→R) (a b:G) :
  ((al f g)) (a-b)= ∑ t,f (a+t)*conj (g (b+t)):=by
 simp[←iM,Qy,r4,RV]
lemma lJ (f g h:G→R) :
  ∑ a,((al f g)) a*h a= ∑ a, ∑ b,f a*conj (g b)*h (a-b):=by
 simp_rw[eL,sum_mul]
 rw[sum_comm]
 exact Fintype.sum_congr _ _ fun x↦Qk (Equiv.subLeft x) _ _ fun y↦by simp
lemma jI (f g:G→R): ∑ a,((al f g)) a=(∑ a,f a)* ∑ a,conj (g a):=by
 simpa only[UB,Rt,Q3] using lJ f g 1
end CommSemiring
section CommRing
variable [CommRing R]
@[simp] lemma CI (f g:G→R):(aC (-f) g)= -((aC f g)):=by ext; simp[f7]
lemma CJ (f g h:G→R):(aC ((f-g)) h)=(aC f h)-(aC g h):=by
 simp only[Qy,CF,CI]
variable [StarRing R]
@[simp] lemma Bz (f g:G→R):(al f (-g))= -((al f g)):=by ext; simp[el]
@[simp] lemma BA (f g:G→R):(al (-f) g)= -((al f g)):=by ext; simp[el]
lemma BB (f g h:G→R):(al f ((g-h)))=(al f g)-(al f h):=by
 simp only[Qy,Bx,Bz]
lemma BC (f g h:G→R):(al ((f-g)) h)=(al f h)-(al g h):=by
 simp only[Qy,By,BA]
end CommRing
namespace RCLike
variable {𝕜:Type} [RCLike 𝕜] (f g:G→ℝ) (a:G)
@[simp] lemma rt:(↑(((aC f g)) a):𝕜)=((aC ((↑) ∘ f) ((↑) ∘ g))) a :=
 xV (algebraMap ℝ 𝕜) _ _ _
@[simp] lemma lb:(↑(((al f g)) a):𝕜)=((al ((↑) ∘ f) ((↑) ∘ g))) a:=by simp[el]
@[simp] lemma oA:((↑):ℝ→𝕜) ∘ ((aC f g))=(aC ((↑) ∘ f) ((↑) ∘ g)):=funext<| rt _ _
@[simp] lemma gF:((↑):ℝ→𝕜) ∘ ((al f g))=(al ((↑) ∘ f) ((↑) ∘ g)):=funext<| lb _ _
end RCLike
namespace Complex
variable (f g:G→ℝ) (n:ℕ) (a:G)
@[simp] lemma zH:(↑(((aC f g)) a):ℂ)=((aC ((↑) ∘ f) ((↑) ∘ g))) a:=RCLike.rt _ _ _
@[simp] lemma yH:(↑(((al f g)) a):ℂ)=((al ((↑) ∘ f) ((↑) ∘ g))) a:=RCLike.lb _ _ _
@[simp] lemma ql:((↑):ℝ→ℂ) ∘ ((aC f g))=(aC ((↑) ∘ f) ((↑) ∘ g)) :=
 funext<| zH _ _
@[simp] lemma px:((↑):ℝ→ℂ) ∘ ((al f g))=(al ((↑) ∘ f) ((↑) ∘ g)) :=
 funext<| yH _ _
end Complex
namespace NNReal
variable (f g:G→ℝ≥0) (a:G)
@[simp] lemma rt:(↑(((aC f g)) a):ℝ)=((aC ((↑) ∘ f) ((↑) ∘ g))) a:=xV NNReal.toRealHom _ _ _
@[simp] lemma lb:(↑(((al f g)) a):ℝ)=((al ((↑) ∘ f) ((↑) ∘ g))) a:=by simp[el,coe_sum]
@[simp] lemma oA:((↑):_→ℝ) ∘ ((aC f g))=(aC ((↑) ∘ f) ((↑) ∘ g)) :=
 funext<| rt _ _
@[simp] lemma gF:((↑):_→ℝ) ∘ ((al f g))=(al ((↑) ∘ f) ((↑) ∘ g)) :=
 funext<| lb _ _
end NNReal
section CommSemiring
variable [CommSemiring R] {f g:G→R} {n:ℕ}
def eo (f:G→R):ℕ→G→R
 | 0=>uK
 | n+1=>(aC (eo f n) f)
@[simp] lemma IV (f:G→R):(eo f 0)=uK:=rfl
lemma vi (f:G→R) (n:ℕ):(eo f ((n+1)))=(aC ((eo f n)) f):=rfl
lemma yI (f:G→R) (n:ℕ):(eo f ((n+1)))=(aC f ((eo f n))):=fA _ _
@[simp] lemma vj [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
  [SMulCommClass H R R] (c:H) (f:G→R): ∀ n,(eo ((c•f)) n)=c^n•(eo f n)
 | 0=>by simp
 | n+1=>by simp_rw[vi,vj _ _ n,RB,uL]
variable [StarRing R]
end CommSemiring
namespace NNReal
end NNReal
namespace Complex
end Complex
end
end
section
open scoped ComplexConjugate
section
namespace Set
variable {α R:Type*} [CommSemiring R] [StarRing R]
end Set
end
end
section
open Finset Function
open Fintype (card)
open scoped BigOperators ComplexConjugate Pointwise translate
section
variable {K L α G:Type*}
section DivisionSemiring
variable [DivisionSemiring K] [DivisionSemiring L] {s:Finset α}
noncomputable def mu (s:Finset α):α→K:=(#s:K)⁻¹ •(Set.indicator s fun _↦(1:_))
lemma mu_apply [DecidableEq α] (x:α):mu s x=(#s:K)⁻¹ *ite (x∈s) 1 0:=by
 simp[mu,Qm]
@[simp] lemma FQ:(mu ∅:α→K)=0:=by ext; simp[mu]
lemma xX (f:K→+* L) (s:Finset α) (x:α):f (mu s x)=mu s x:=by
 simp_rw[mu,RD,Q2,RU,Set.rf,map_inv₀,map_natCast]
section Nontrivial
variable [CharZero K] {a:α}
@[simp] lemma FR:(@mu K _ _) s a=0↔a∉s:=by
 classical
 simp only[mu_apply,mul_boole,ite_eq_right_iff,inv_eq_zero,Nat.cast_eq_zero,card_eq_zero]
 refine imp_congr_right fun ha↦ ?_
 simp only[ne_empty_of_mem ha]
variable (K)
@[simp] lemma jo (s:Finset α):support ((@mu K _ _) s)=s:=by ext; simp
end Nontrivial
variable (K)
lemma l1 [CharZero K] (s:Finset α): #s•(@mu K _ _) s=(Set.indicator s fun _↦(1:_)):=by
 classical
 ext x:1
 simp only[RD,mu_apply,Td,Q3,mul_zero,smul_ite,QS,
  Qm,SetLike.mem_coe]
 split_ifs with h
 ·have:s.Nonempty:=⟨_,h⟩
  simp[this.ne_empty]
 ·simp
lemma qm [CharZero K] (s:Finset α) (x:α): #s•(@mu K _ _) s x=(Set.indicator s fun _↦(1:_)) x :=
 SR (l1 K _) _
@[simp] lemma kU [CharZero K] [Fintype α] (hs:s.Nonempty): ∑ x,(@mu K _ _) s x=1:=by
 classical
 simpa[mu_apply] using Tw (Nat.cast_ne_zero.2 hs.card_pos.ne')
section Group
variable [AddGroup G] [AddAction G α] [DecidableEq α]
@[simp] lemma ND (g:G) (s:Finset α) (a:α):(@mu K _ _) (g+ᵥ s) a=mu s (-g+ᵥ a):=by
 simp[mu_apply,neg_vadd_mem_iff]
end Group
section Group
variable [AddGroup α] [DecidableEq α]
@[simp] lemma N7 (s:Finset α) (a:α):(@mu K _ _) (-s) a=mu s (-a):=by simp[mu]
end Group
lemma vH [AddCommGroup G] [DecidableEq G] (a:G) (s:Finset G) :
  τ a ((@mu K _ _) s)=mu (a+ᵥ s):=by
 ext; simp[mu_apply, ←neg_vadd_mem_iff,sub_eq_neg_add]
end DivisionSemiring
section Semifield
variable (K) [Semifield K] {s:Finset G}
variable [StarRing K]
@[simp] lemma CK [AddCommGroup G] [DecidableEq G] (s:Finset G) :
  conjneg ((@mu K _ _) s)=mu (-s):=by ext; simp[mu_apply]; split_ifs<;>simp
end Semifield
section Semifield
variable (K) [Semifield K] [StarRing K] {s:Finset α}
end Semifield
section LinearOrderedSemifield
variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] {s:Finset α}
@[simp] lemma cC:0≤(@mu K _ _) s:=fun a↦by classical rw[mu_apply]; split_ifs<;>simp
end LinearOrderedSemifield
namespace Complex
variable (s:Finset α) (a:α)
@[simp] lemma Eb: ↑((@mu (ℝ) _ _) s a)=(@mu (ℂ) _ _) s a:=xX (algebraMap ℝ ℂ) ..
@[simp] lemma yJ:(↑) ∘ (@mu (ℝ) _ _) s=(@mu (ℂ) _ _) s:=funext<| Eb _
end Complex
namespace RCLike
variable {𝕜:Type*} [RCLike 𝕜] (s:Finset α) (a:α)
@[simp] lemma Ae: ↑((@mu (ℝ) _ _) s a)=(@mu 𝕜 _ _) s a:=xX (algebraMap ℝ 𝕜) _ _
@[simp] lemma iF:(↑) ∘ (@mu (ℝ) _ _) s=(@mu 𝕜 _ _) s:=funext<| Ae _
end RCLike
namespace NNReal
open scoped NNReal
@[simp] lemma Ae (s:Finset α) (x:α): ↑((@mu (ℝ≥0) _ _) s x)=(@mu (ℝ) _ _) s x:=xX NNReal.toRealHom _ _
@[simp] lemma iF (s:Finset α):(↑) ∘ (@mu (ℝ≥0) _ _) s=(@mu (ℝ) _ _) s:=funext<| Ae _
end NNReal
namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function
end Mathlib.Meta.Positivity
end
end
section
section
open Finset Fintype Function
open scoped BigOperators ComplexConjugate NNReal Pointwise translate
variable {G R γ:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
section CommSemiring
variable [CommSemiring R] {f g:G→R}
variable [StarRing R]
end CommSemiring
section Semifield
variable [Semifield R]
variable [StarRing R]
end Semifield
section Semifield
variable [Semifield R] [CharZero R]
variable [StarRing R]
end Semifield
section Field
variable [Field R] [CharZero R]
variable [StarRing R]
end Field
section CommSemiring
variable [CommSemiring R] {f g:G→R} {n:ℕ}
lemma jZ (s:Finset G) :
  ∀ (n:ℕ) (a:G),((eo ((Set.indicator s fun _↦(1:R))) n)) a= #{x∈(Fintype.piFinset fun _:Fin n↦s) | ∑ i,x i=a}
 | 0,a=>by simp[TU card,eq_comm]
 | n+1,a=>by
  simp_rw[yI,cR,jZ,Qm,
   SS,sum_ite,mem_coe,filter_univ_mem,sum_const_zero,add_zero, ←Nat.cast_sum,
   ←Finset.card_sigma]
  congr 1
  refine card_equiv ((Equiv.sigmaEquivProd ..).trans<| Fin.consEquiv fun _↦G) ?_
  aesop (add simp[Fin.sum_cons,Fin.forall_fin_succ])
lemma ph (s:Finset G) (n:ℕ) (f:G→R) :
  (aC ((eo ((Set.indicator s fun _↦(1:_))) n)) f)= ∑ a∈(Fintype.piFinset fun _:Fin n↦s),τ (∑ i,a i) f:=by
 ext b
 simp only[cR,jZ,Si,QZ,
  ←QS, ←sum_const,Finset.sum_fiberwise']
variable [StarRing R]
end CommSemiring
section Semifield
variable [Semifield R] [CharZero R]
lemma vI (s:Finset G) (n:ℕ) (f:G→R) :
  (aC ((eo (mu s) n)) f)=𝔼 a∈piFinset (fun _:Fin n↦s),τ (∑ i,a i) f:=by
 simp only[mu,vj,Te,tj,ph,expect,
  card_piFinset_const,Rv]
 rw[←NNRat.cast_smul_eq_nnqsmul R]
 push_cast
 rfl
variable [StarRing R]
end Semifield
section Field
variable [Field R] [CharZero R]
end Field
end
end
section
section
open Finset hiding card
open Function ProbabilityTheory Real
open Fintype (card)
open scoped BigOperators ComplexConjugate ENNReal NNReal translate
variable {α 𝕜 R E:Type*} [MeasurableSpace α]
namespace MeasureTheory
section NormedAddCommGroup
variable [NormedAddCommGroup E] {p q:ℝ≥0∞} {f g h:α→E}
noncomputable def c2 (p:ℝ≥0∞) (f:α→E):ℝ:=lpNorm f p (uniformOn .univ)
@[simp] lemma yK:0≤(c2 p f):=by simp[c2]
section NormedField
variable [NormedField 𝕜] {p:ℝ≥0∞} {f g:α→𝕜}
variable [NormedSpace ℝ 𝕜]
end NormedField
section RCLike
variable {p:ℝ≥0∞}
end RCLike
section DiscreteMeasurableSpace
variable [DiscreteMeasurableSpace α] [Finite α]
end DiscreteMeasurableSpace
variable [Finite α]
section NormedField
variable [NormedField 𝕜] {p:ℝ≥0∞} {f g:α→𝕜}
end NormedField
omit [Finite α]
variable [DiscreteMeasurableSpace α] [Fintype α]
lemma mO (iu:p≠0) (hp:p≠∞) (f:α→E) :
  (c2 p f)=(𝔼 i, ‖f i‖ ^p.toReal)^p.toReal⁻¹ :=by
 simp[c2,uniformOn,lpNorm_eq_integral_norm_rpow_toReal iu hp .of_discrete,
  integral_fintype,cond_apply,expect_eq_sum_div_card,Ri, ←mul_sum,Measure.real]
lemma tk {p:ℝ≥0} (hp:p≠0) (f:α→E) :
  (c2 p f)=(𝔼 i, ‖f i‖ ^(p:ℝ))^(p⁻¹ :ℝ) :=
 mO (by simpa using hp) (by simp) _
lemma qn {p:ℝ≥0} (hp:p≠0) (f:α→E) :
  (c2 p f)^(p:ℝ)=𝔼 i, ‖f i‖ ^(p:ℝ):=by
 rw[tk hp,S4]<;>positivity
lemma qT {p:ℕ} (hp:p≠0) (f:α→E) :
  (c2 p f)^p=𝔼 i, ‖f i‖ ^p:=by
 simpa using qn (Nat.cast_ne_zero.2 hp) f
lemma ru (f:α→E):(c2 2 f)^2=𝔼 i, ‖f i‖ ^2:=by
 simpa using qT SD _
lemma tl (f:α→E):(c2 1 f)=𝔼 i, ‖f i‖ :=by
 simp[mO]
omit [Fintype α]
variable [Finite α]
lemma oB (f:α→E):(c2 (∞) f)= ⨆ i, ‖f i‖ :=by
 cases UC α<;>simp[c2,lpNorm_exponent_top_eq_essSup]
omit [Finite α]
end NormedAddCommGroup
end MeasureTheory
namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function MeasureTheory
section Examples
section NormedAddCommGroup
variable [Fintype α] [DiscreteMeasurableSpace α] [NormedAddCommGroup E] [PartialOrder E] {f:α→E}
end NormedAddCommGroup
section Complex
variable [Fintype α] [DiscreteMeasurableSpace α] {w:α→ℝ≥0} {f:α→ℂ}
end Complex
end Examples
end Mathlib.Meta.Positivity
namespace MeasureTheory
section Real
variable {α:Type*} {w2:MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] {p q:ℝ≥0}
 {f g:α→ℝ}
end Real
section mn
variable {α:Type*} {w2:MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] [RCLike 𝕜]
 {p q:ℝ≥0} {f g:α→𝕜}
end mn
section
variable {α:Type*} {w2:MeasurableSpace α}
end
end MeasureTheory
namespace MeasureTheory
variable {ι G 𝕜 E R:Type*} [Fintype ι] {I4:MeasurableSpace ι} [DiscreteMeasurableSpace ι]
section Indicator
variable [RCLike R] {s:Finset ι} {p:ℝ≥0}
end Indicator
section c2
variable {mG:MeasurableSpace G} [DiscreteMeasurableSpace G] [AddCommGroup G] [Finite G]
 {p:ℝ≥0∞}
end c2
end MeasureTheory
end
end
section
section
open Finset Function Real
open scoped BigOperators ComplexConjugate ENNReal NNReal NNRat
variable {α 𝕜 R E:Type*} [MeasurableSpace α]
namespace MeasureTheory
variable [NormedAddCommGroup E] {p q:ℝ≥0∞} {f g h:α→E}
noncomputable def aJ (p:ℝ≥0∞) (f:α→E):ℝ:=lpNorm f p .count
@[simp] lemma d8:0≤(aJ p f):=by simp[aJ]
@[simp] lemma n1 (f:α→E):(aJ 0 f)=0:=by simp[aJ]
@[simp] lemma Af (p:ℝ≥0∞):(aJ p ((0:α→E)))=0:=by simp[aJ]
lemma r5 (f g:α→E) (p:ℝ≥0∞):(aJ p (f-g))=(aJ p (g-f)):=by
 simp[aJ,lpNorm_sub_comm]
@[simp] lemma Ag (hf:StronglyMeasurable f) (p:ℝ≥0∞):(aJ p (fun i↦ ‖f i‖))=(aJ p f) :=
 lpNorm_norm hf.aestronglyMeasurable _
section NormedField
variable [NormedField 𝕜] {p:ℝ≥0∞} {f g:α→𝕜}
lemma vJ [Module 𝕜 E] [NormSMulClass 𝕜 E] (c:𝕜) (f:α→E) :
  (aJ p (c•f))= ‖c‖ *(aJ p f):=by simp[aJ,lpNorm_const_smul]
lemma zI [NormedSpace ℝ E] (n:ℕ) (f:α→E) (p:ℝ≥0∞) :
  (aJ p (n•f))=n•(aJ p f):=by simp[aJ,lpNorm_nsmul]
variable [NormedSpace ℝ 𝕜]
end NormedField
section RCLike
variable {p:ℝ≥0∞}
@[simp] lemma Ah [RCLike R] (f:α→R):(aJ p (conj f))=(aJ p f):=lpNorm_conj ..
end RCLike
section DiscreteMeasurableSpace
variable [DiscreteMeasurableSpace α] [Finite α]
lemma yL (hp:1≤p):(aJ p (f+g))≤(aJ p f)+(aJ p g) :=
 lpNorm_add_le .of_discrete hp
lemma yM (hp:1≤p):(aJ p (f-g))≤(aJ p f)+(aJ p g) :=
 lpNorm_sub_le .of_discrete hp
lemma wS [Module ℚ≥0 E] [NormedSpace ℝ E] {ι:Type*} {s:Finset ι} {f:ι→α→E}
  (hp:1≤p):(aJ p (𝔼 i∈s,f i))≤𝔼 i∈s,(aJ p (f i)) :=
 lpNorm_expect_le (fun _ _↦ .of_discrete) hp
lemma ep (hp:1≤p) :
  (aJ p (f-h))≤(aJ p (f-g))+(aJ p (g-h)) :=
 lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub .of_discrete .of_discrete hp
end DiscreteMeasurableSpace
variable [Fintype α]
section NormedField
variable [NormedField 𝕜] {p:ℝ≥0∞} {f g:α→𝕜}
end NormedField
variable [DiscreteMeasurableSpace α]
lemma iv (iu:p≠0) (hp:p≠∞) (f:α→E) :
  (aJ p f)=(∑ i, ‖f i‖ ^p.toReal)^p.toReal⁻¹ :=by
 simp[aJ,lpNorm_eq_integral_norm_rpow_toReal iu hp .of_discrete,integral_fintype]
lemma lj {p:ℝ≥0} (hp:p≠0) (f:α→E) :
  (aJ p f)=(∑ i, ‖f i‖ ^(p:ℝ))^(p⁻¹ :ℝ) :=
 iv (by simpa using hp) (by simp) _
lemma iU {p:ℝ≥0} (hp:p≠0) (f:α→E) :
  (aJ p f)^(p:ℝ)= ∑ i, ‖f i‖ ^(p:ℝ):=by
 rw[lj hp,S4 (by positivity) (mod_cast hp)]
lemma gA {p:ℕ} (hp:p≠0) (f:α→E):(aJ p f)^p= ∑ i, ‖f i‖ ^p:=by
 simpa using iU (Nat.cast_ne_zero.2 hp) f
lemma tn (f:α→E):(aJ 2 f)^2= ∑ i, ‖f i‖ ^2:=by
 simpa using gA SD _
lemma ej (f:α→E):(aJ 1 f)= ∑ i, ‖f i‖ :=by simp[iv]
omit [Fintype α]
variable [Finite α]
lemma dw (f:α→E):(aJ (∞) f)= ⨆ i, ‖f i‖ :=by
 cases UC α<;>simp[aJ,lpNorm_exponent_top_eq_essSup]
lemma vu {i:α}: ‖f i‖ ≤(aJ (∞) f):=by
 rw[dw]; exact le_ciSup (f:=fun i↦ ‖f i‖) (SA _) i
omit [Finite α]
variable [Fintype α]
end MeasureTheory
namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function MeasureTheory
section Examples
section NormedAddCommGroup
variable [Fintype α] [DiscreteMeasurableSpace α] [NormedAddCommGroup E] [PartialOrder E] {f:α→E}
end NormedAddCommGroup
section Complex
variable [Fintype α] [DiscreteMeasurableSpace α] {f:α→ℂ}
end Complex
end Examples
end Mathlib.Meta.Positivity
namespace MeasureTheory
section Real
variable {α:Type*} {w2:MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] {p q:ℝ≥0}
 {f g:α→ℝ}
end Real
section mn
variable {α:Type*} {w2:MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] [RCLike 𝕜]
 {p q:ℝ≥0} {f g:α→𝕜}
end mn
section
variable {α:Type*} {w2:MeasurableSpace α}
end
end MeasureTheory
end
end
section
section
open Finset Function Real
open scoped BigOperators ComplexConjugate ENNReal NNReal translate
namespace MeasureTheory
variable {ι G 𝕜 E R:Type*} [Finite ι] {I4:MeasurableSpace ι} [DiscreteMeasurableSpace ι]
section Indicator
variable [RCLike R] {s:Finset ι} {p:ℝ≥0}
lemma kV (hp:p≠0) (s:Finset ι) :
  (aJ p ((Set.indicator ((s:Set ι)) fun _↦(1:R))))^(p:ℝ)= #s:=by
 classical
 cases RR ι
 have: ∀ x,(ite (x∈s) 1 0:ℝ)^(p:ℝ) =
  ite (x∈s) (1^(p:ℝ)) (0^(p:ℝ)):=fun x↦by split_ifs<;>simp
 simp[iU,hp,Qm,TU norm, -sum_const,
  card_eq_sum_ones]
lemma n2 (hp:p≠0) (s:Finset ι) :
  (aJ p ((Set.indicator ((s:Set ι)) fun _↦(1:R))))= #s^(p⁻¹ :ℝ):=by
 refine(eq_rpow_inv ?_ ?_ ?_).2 (kV ?_ _)<;>first | positivity | exact d8
lemma rv {p:ℕ} (hp:p≠0) (s:Finset ι) :
  (aJ p ((Set.indicator ((s:Set ι)) fun _↦(1:R))))^(p:ℝ)= #s:=by
 simpa using kV (Nat.cast_ne_zero.2 hp) s
lemma r6 (s:Finset ι):(aJ 2 ((Set.indicator ((s:Set ι)) fun _↦(1:R))))^2= #s:=by
 simpa using rv SD s
@[simp] lemma tR (s:Finset ι):(aJ 2 ((Set.indicator ((s:Set ι)) fun _↦(1:R))))=Real.sqrt #s:=by
 rw[eq_comm,sqrt_eq_iff_eq_sq,r6]<;>first | positivity | exact d8
lemma rx (hp:1≤p) (hs:s.Nonempty):(aJ p ((@mu R _ _) s))= #s^((p:ℝ)⁻¹ -1):=by
 rw[mu,vJ ((#s)⁻¹ :R) ((Set.indicator ((s:Set ι)) fun _↦(1:R))),n2,Up,
  RCLike.norm_natCast,TK, ←Real.rpow_sub_one]<;>positivity
lemma zJ (hp:1≤p):(aJ p ((@mu R _ _) s))≤ #s^(p⁻¹ -1:ℝ):=by
 obtain rfl | hs:=s.eq_empty_or_nonempty
 ·simp only[FQ,Af,card_empty,UH,SE]
  positivity
 ·exact(rx hp hs).le
@[simp] lemma uN (hs:s.Nonempty):(aJ 1 ((@mu R _ _) s))=1:=by
 simpa using rx SF hs
lemma rj:(aJ 1 ((@mu R _ _) s))≤1:=by simpa using zJ SF
@[simp] lemma CL (hs:s.Nonempty):(aJ 2 ((@mu R _ _) s))= #s^(-2⁻¹ :ℝ):=by
 have:(2⁻¹ -1:ℝ)= -2⁻¹ :=by norm_num
 simpa[sqrt_eq_rpow,this] using rx one_le_two (R:=R) hs
end Indicator
section aJ
variable {mG:MeasurableSpace G} [DiscreteMeasurableSpace G] [AddCommGroup G] [Finite G]
 {p:ℝ≥0∞}
@[simp] lemma jX [NormedAddCommGroup E] (a:G) (f:G→E):(aJ p (τ a f))=(aJ p f):=by
 cases RR G
 obtain p | p:=p
 ·simp only[dw,UD,QZ]
  exact(Equiv.subRight _).iSup_congr fun _↦rfl
 obtain rfl | hp:=Tf p 0
 ·simp only[n1,R2,ENNReal.coe_zero]
 ·simp only[lj hp,R2,QZ]
  congr 1
  exact Qk (Equiv.subRight _) _ _ fun _↦rfl
@[simp] lemma G0 [RCLike E] (f:G→E):(aJ p (conjneg f))=(aJ p f):=by
 cases RR G
 simp only[conjneg,Ah]
 obtain p | p:=p
 ·simp only[dw,UD]
  exact(Equiv.neg _).iSup_congr fun _↦rfl
 obtain rfl | hp:=Tf p 0
 ·simp only[n1,R2,ENNReal.coe_zero]
 ·simp only[lj hp,R2]
  congr 1
  exact Qk (Equiv.neg _) _ _ fun _↦rfl
lemma pJ [NormedAddCommGroup E] (hp:1≤p) {ι:Type*} (s:Finset ι)
  (a:ι→G) (f:G→E):(aJ p (τ (∑ i∈s,a i) f-f))≤ ∑ i∈s,(aJ p (τ (a i) f-f)):=by
 induction s using Finset.cons_induction with
 | empty=>simp
 | cons i s ih hs =>
 calc
  _=(aJ p (τ (∑ j∈s,a j) (τ (a i) f-f)+(τ (∑ j∈s,a j) f-f))):=by
   rw[sum_cons,translate_add',UE,sub_add_sub_cancel]
  _≤(aJ p (τ (∑ j∈s,a j) (τ (a i) f-f)))+ ∑ j∈s,(aJ p ((τ (a j) f-f))):=by
   grw[yL hp,hs]
  _=_:=by rw[jX,sum_cons]
end aJ
end MeasureTheory
end
end
section
section
open Finset Function MeasureTheory RCLike Real
open scoped ComplexConjugate ENNReal NNReal Pointwise translate
variable {G 𝕜:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
section RCLike
variable [RCLike 𝕜] {p:ℝ≥0∞}
lemma tS (f g:G→𝕜) (a:G):((al f g)) a=conj ⟪f,τ a g⟫_[𝕜]:=by
 simp[wInner_one_eq_sum,eL,RK,Qx]
lemma qo (f g h:G→𝕜):⟪f,(al g h)⟫_[𝕜]=⟪conj g,(aC (conj f) (conj h))⟫_[𝕜]:=by
 calc
  _= ∑ b, ∑ a,g a*conj (h b)*conj (f (a-b)):=by
   simp_rw[wInner_one_eq_sum,Sb,lJ]
   exact sum_comm
  _= ∑ b, ∑ a,conj (f a)*conj (h b)*g (a+b):=by
   simp_rw[←Fintype.sum_prod_type']
   exact Qk ((Equiv.refl _).prodShear Equiv.subRight) _ _
    (by simp[mul_rotate,QN])
  _=_:=by
   simp_rw[wInner_one_eq_sum,Sb,tP,TR,
    Tl]
   exact sum_comm
lemma wT (f g h:G→𝕜):⟪f,(aC g h)⟫_[𝕜]=⟪conj g,(al (conj f) (conj h))⟫_[𝕜]:=by
 simp_rw[qo,Tl]
lemma vK (f g h:G→𝕜):⟪(al f g),h⟫_[𝕜]=⟪(aC (conj h) (conj g)),conj f⟫_[𝕜]:=by
 rw[←conj_wInner_symm,qo,conj_wInner_symm]
lemma rk (f g h:G→𝕜):⟪(aC f g),h⟫_[𝕜]=⟪(al (conj h) (conj g)),conj f⟫_[𝕜]:=by
 rw[←conj_wInner_symm,wT,conj_wInner_symm]
lemma kW (f g h:G→𝕜) :
  ⟪(al f g),h⟫_[𝕜]=⟪f,(aC h g)⟫_[𝕜]:=by
 rw[vK]; simp[wInner_one_eq_sum,Qx]
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
lemma wU {p:ℝ≥0} (hp:1≤p) (f g:G→𝕜) :
  (aJ p ((aC f g)))≤(aJ p f)*(aJ 1 g):=by
 obtain rfl | hp:=hp.eq_or_lt
 ·simp_rw[ENNReal.coe_one,ej,sum_mul_sum,cR]
  calc
   ∑ x, ‖∑ y,f y*g (x-y)‖ ≤ ∑ x, ∑ y, ‖f y*g (x-y)‖ :=
    sum_le_sum fun x _↦Rq _ _
   _=_:= ?_
  rw[sum_comm]
  simp_rw[QO]
  exact sum_congr rfl fun x _↦Qk (Equiv.subRight x) _ _ fun _↦rfl
 have iu:=zero_lt_one.trans hp
 have h1:=d8 (p:=(p:ℝ≥0∞)) (f:=aC f g)
 have h2:=d8 (p:=(p:ℝ≥0∞)) (f:=f)
 have h3:=d8 (p:=1) (f:=g)
 rw[←rpow_le_rpow_iff _ _ iu,mul_rpow]
 any_goals positivity
 dsimp
 simp_rw[iU iu.ne',cR]
 have I5:(p:ℝ).HolderConjugate (1-(p:ℝ)⁻¹)⁻¹ :=
  ⟨by simp,mod_cast iu,by bound⟩
 have (x:G): ‖∑ y,f y*g (x-y)‖ ^(p:ℝ) ≤
   (∑ y, ‖f y‖ ^(p:ℝ)* ‖g (x-y)‖)*(∑ y, ‖g (x-y)‖)^(p-1:ℝ):=by
  rw[←le_rpow_inv_iff_of_pos,mul_rpow, ←rpow_mul,sub_one_mul,Tw]
  any_goals positivity
  calc
   _≤ ∑ y, ‖f y*g (x-y)‖ :=Rq _ _
   _= ∑ y, ‖f y‖ * ‖g (x-y)‖ ^(p:ℝ)⁻¹ * ‖g (x-y)‖ ^(1-(p:ℝ)⁻¹):= ?_
   _≤_:=inner_le_Lp_mul_Lq _ _ _ I5
   _=_:= ?_
  ·congr with t
   rw[QO,Qo, ←rpow_add' (by positivity),TL,rpow_one]
   simp
  ·have:1-(p:ℝ)⁻¹ ≠0:=sub_ne_zero.2 (inv_ne_one.2<| NNReal.coe_ne_one.2 hp.ne').symm
   simp[mul_rpow,rpow_nonneg,iu.ne',this,abs_rpow_of_nonneg]
 calc
  ∑ x, ‖∑ y,f y*g (x-y)‖ ^(p:ℝ) ≤
    ∑ x,(∑ y, ‖f y‖ ^(p:ℝ)* ‖g (x-y)‖)*(∑ y, ‖g (x-y)‖)^(p-1:ℝ) :=
   sum_le_sum fun i _↦this _
  _=_:= ?_
 have hg: ∀ x, ∑ y, ‖g (x-y)‖ =(aJ 1 g):=by
  simp_rw[ej]
  exact fun x↦Qk (Equiv.subLeft _) _ _ fun _↦rfl
 have hg': ∀ y, ∑ x, ‖g (x-y)‖ =(aJ 1 g):=by
  simp_rw[ej]
  exact fun x↦Qk (Equiv.subRight _) _ _ fun _↦rfl
 simp_rw[hg]
 rw[←sum_mul,sum_comm]
 simp_rw[←mul_sum,hg']
 rw[←sum_mul,Qo, ←rpow_one_add' (by positivity),TL]
 rw[TL]
 positivity
end RCLike
section Real
variable [MeasurableSpace G] [DiscreteMeasurableSpace G] {f g:G→ℝ} {n:ℕ}
lemma yN (hf:0≤f) (hg:0≤g):(aJ 1 ((aC f g)))=(aJ 1 f)*(aJ 1 g):=by
 have: ∀ x,0≤ ∑ y,f y*g (x-y):=fun x↦sum_nonneg fun y _↦Qn (hf _) (hg _)
 simp[ej, ←uM,cR,norm_of_nonneg (this _),
  norm_of_nonneg (hf _),norm_of_nonneg (hg _)]
lemma xY (hf:0≤f) (hg:0≤g):(aJ 1 ((al f g)))=(aJ 1 f)*(aJ 1 g):=by
 simpa using yN hf (conjneg_nonneg.2 hg)
end Real
end
end
section
section
open Finset Function MeasureTheory RCLike Real
open scoped ComplexConjugate ENNReal NNReal NNRat
variable {ι 𝕜 S:Type*} [Fintype ι]
namespace RCLike
variable [RCLike 𝕜] {I4:MeasurableSpace ι} [DiscreteMeasurableSpace ι] {f:ι→𝕜}
@[simp] lemma xZ {_:MeasurableSpace ι} [DiscreteMeasurableSpace ι] (f:ι→𝕜) :
  ⟪f,f⟫_[𝕜]=(((aJ 2 f):ℝ):𝕜)^2:=by
 simp_rw[←UI]
 simp[tn,wInner_one_eq_sum]
end RCLike
namespace MeasureTheory
section Real
variable {α:Type*} {w2:MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] {p q:ℝ≥0∞}
 {f g:α→ℝ}
lemma nb (p q:ℝ≥0∞) [p.HolderConjugate q] :
  ⟪f,g⟫_[ℝ]≤(aJ p f)*(aJ q g):=by
 have x0:p≠0:=Tk p q
 have x1:q≠0:=Tk q p
 have yO:⟪f,g⟫_[ℝ]= ∑ i,f i*g i:=by simp[wInner_one_eq_sum,Qx]
 have N8 i:f i*g i≤ ‖f i‖ * ‖g i‖ :=
  (SG _).trans_eq (by rw[SU]; simp[QK])
 obtain rfl | Ai:=Tf p ∞
 ·obtain rfl:q=1:=(Sx ∞ q).mp rfl
  simp only[yO,ej,norm_eq_abs,dw,mul_sum]
  gcongr ∑ _, ?_ with i
  grw[SG (_*_),SU, ←le_ciSup (SA _)]
 obtain rfl | MA:=Tf q ∞
 ·obtain rfl:p=1:=(Sx ∞ p).mp rfl
  simp only[yO,ej,norm_eq_abs,dw,sum_mul]
  gcongr ∑ _, ?_ with i
  grw[SG (_*_),SU, ←le_ciSup (SA _)]
 have N9:0<p.toReal:=UJ x0 Ai
 have Oa:0<q.toReal:=UJ x1 MA
 have uO:Real.HolderConjugate p.toReal q.toReal:=by
  simpa using ENNReal.HolderTriple.toReal (p:=p) (q:=q) (r:=1) N9 Oa
 rw[yO,iv x0 Ai,iv x1 MA]
 simpa using Real.inner_le_Lp_mul_Lq Finset.univ f g uO
end Real
section mn
variable {α:Type*} {w2:MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
 {p q r:ℝ≥0∞} {f g:α→𝕜}
lemma vL (f g:α→𝕜): ‖⟪f,g⟫_[𝕜]‖ ≤⟪fun a↦ ‖f a‖,fun a↦ ‖g a‖⟫_[ℝ]:=by
 grw[wInner_one_eq_sum,Rq]; simp[wInner_one_eq_sum]
lemma lk (p q:ℝ≥0∞) [p.HolderConjugate q] :
  ‖⟪f,g⟫_[𝕜]‖ ≤(aJ p f)*(aJ q g) :=
 calc
  _≤⟪fun a↦ ‖f a‖,fun a↦ ‖g a‖⟫_[ℝ]:=vL _ _
  _≤(aJ p (fun a↦ ‖f a‖))*(aJ q (fun a↦ ‖g a‖)):=nb _ _
  _=(aJ p f)*(aJ q g):=by simp_rw[Ag .of_discrete]
omit [Fintype α]
variable [Finite α]
lemma yP (p q:ℝ≥0∞) [p.HolderTriple q r]:(aJ r (f*g))≤(aJ p f)*(aJ q g):=by
 cases RR α
 change lpNorm (f*g) r .count≤lpNorm f p .count*lpNorm g q .count
 have N8:AEStronglyMeasurable (f*g) .count:= .of_discrete
 grw[←toReal_eLpNorm .of_discrete, ←toReal_eLpNorm .of_discrete, ←toReal_eLpNorm .of_discrete,
  ←UK, ←qS (r:=r) .of_discrete .of_discrete]
 exact(ENNReal.mul_lt_top eLpNorm_lt_top_of_finite eLpNorm_lt_top_of_finite).ne
end mn
end MeasureTheory
end
end
section
open Finset Fintype Nat Real
variable {ι:Type*} {A:Finset ι} {m n:ℕ}
lemma step_one (hA:A.Nonempty) (f:ι→ℝ) (a:Fin n→ι)
  (hf: ∀ i, ∑ a∈(Fintype.piFinset fun _:Fin n↦A),f (a i)=0) :
  |∑ i,f (a i)| ^(m+1) ≤
   (∑ b∈(Fintype.piFinset fun _:Fin n↦A), |∑ i,(f (a i)-f (b i))| ^(m+1))/ #A^n:=by
 let B:=(Fintype.piFinset fun _:Fin n↦A)
 calc
  |∑ i,f (a i)| ^(m+1)
   = |∑ i,(f (a i)-(∑ b∈B,f (b i))/ #B)| ^(m+1):=by
   simp only[B,hf,sub_zero,zero_div]
  _= |(∑ b∈B, ∑ i,(f (a i)-f (b i)))/ #B| ^(m+1):=by
   simp only[sum_sub_distrib]
   rw[sum_const,UT,sum_comm,sum_div,QS,card_piFinset,prod_const,
    Finset.card_univ,Fintype.card_fin,Rv,SH]
   positivity
  _= |∑ b∈B, ∑ i,(f (a i)-f (b i))| ^(m+1)/ #B^(m+1):=by
   rw[TE,TY,Nat.abs_cast]
  _≤(∑ b∈B, |∑ i,(f (a i)-f (b i))|)^(m+1)/ #B^(m+1):=by
   gcongr; exact IsAbsoluteValue.abv_sum _ _ _
  _=(∑ b∈B, |∑ i,(f (a i)-f (b i))|)^(m+1)/ #B^m/ #B:=by
   rw[div_div, ←pow_succ]
  _≤(∑ b∈B, |∑ i,(f (a i)-f (b i))| ^(m+1))/ #B:=by
   gcongr; exact TF (fun _ _↦Q8 _) _
  _=_:=by simp[B]
lemma Ec (hA:A.Nonempty) (f:ι→ℝ) (hf: ∀ i, ∑ a∈(Fintype.piFinset fun _:Fin n↦A),f (a i)=0) (m:ℕ)
  (a:Fin n→ι) :
  |∑ i,f (a i)| ^m≤(∑ b∈(Fintype.piFinset fun _:Fin n↦A), |∑ i,(f (a i)-f (b i))| ^m)/ #A^n:=by
 cases m
 ·simp only[pow_zero,sum_const,prod_const,Nat.smul_one_eq_cast,Finset.card_fin,
   card_piFinset, ←Rv]
  rw[div_self]
  rw[Ru, ←Tx]
  exact RF (Finset.card_pos.2 hA) _
 exact step_one hA f a hf
lemma Aj (A:Finset ι) (f:ι→ℝ) (ε:Fin n→ℝ)
  (hε:ε∈(Fintype.piFinset fun _:Fin n↦(({-1,1}:Finset ℝ)))) (g:(Fin n→ℝ)→ℝ) :
  ∑ a∈(Fintype.piFinset fun _:Fin n↦A), ∑ b∈(Fintype.piFinset fun _:Fin n↦A),g (ε*(f ∘ a-f ∘ b)) =
   ∑ a∈(Fintype.piFinset fun _:Fin n↦A), ∑ b∈(Fintype.piFinset fun _:Fin n↦A),g (f ∘ a-f ∘ b):=by
 rw[←sum_product', ←sum_product']
 let n3:(Fin n→ι) × (Fin n→ι)→(Fin n→ι) × (Fin n→ι):=by
  intro xy
  exact(fun i↦if ε i=1 then xy.1 i else xy.2 i,fun i↦if ε i=1 then xy.2 i else xy.1 i)
 have h₁: ∀ a∈((Fintype.piFinset fun _:Fin n↦A)) ×ˢ ((Fintype.piFinset fun _:Fin n↦A)),n3 a∈((Fintype.piFinset fun _:Fin n↦A)) ×ˢ ((Fintype.piFinset fun _:Fin n↦A)):=by
  simp only[mem_product,mem_piFinset, ←forall_and,n3]
  intro a h i
  split_ifs
  ·exact h i
  ·exact(h i).symm
 have h₂: ∀ a∈((Fintype.piFinset fun _:Fin n↦A)) ×ˢ ((Fintype.piFinset fun _:Fin n↦A)),n3 (n3 a)=a:=fun a _↦by
  ext<;>simp only[n3]<;>split_ifs<;>rfl
 refine sum_nbij' n3 n3 h₁ h₁ h₂ h₂ ?_
 ·rintro ⟨a,b⟩ _
  congr with i:1
  simp only[mem_piFinset,mem_insert,mem_singleton] at hε
  simp only[Pi.mul_apply,Rw,Rh,n3]
  split_ifs with h
  ·simp[h]
  rw[(hε i).resolve_right h]
  ring
lemma FT (f:ι→ℝ) :
  ∑ a∈(Fintype.piFinset fun _:Fin n↦A), ∑ b∈(Fintype.piFinset fun _:Fin n↦A),(∑ i,(f (a i)-f (b i)))^(2*m) =
   2⁻¹ ^n* ∑ ε∈(Fintype.piFinset fun _:Fin n↦(({-1,1}:Finset ℝ))),
    ∑ a∈(Fintype.piFinset fun _:Fin n↦A), ∑ b∈(Fintype.piFinset fun _:Fin n↦A),(∑ i,ε i*(f (a i)-f (b i)))^(2*m):=by
 let B:=(Fintype.piFinset fun _:Fin n↦A)
 have: ∀ ε∈(Fintype.piFinset fun _:Fin n↦(({-1,1}:Finset ℝ))),
  ∑ a∈B, ∑ b∈B,(∑ i,ε i*(f (a i)-f (b i)))^(2*m) =
   ∑ a∈B, ∑ b∈B,(∑ i,(f (a i)-f (b i)))^(2*m) :=
  fun ε hε↦Aj A f _ hε fun z:Fin n→ℝ↦univ.sum z^(2*m)
 rw[Io rfl this,sum_const,card_piFinset_const,card_pair,QS,
  Rv,So,Te,inv_mul_cancel_left₀]
 ·positivity
 ·norm_num
lemma CM (f:ι→ℝ) :
  ∑ ε∈(Fintype.piFinset fun _:Fin n↦(({-1,1}:Finset ℝ))),
   ∑ a∈(Fintype.piFinset fun _:Fin n↦A), ∑ b∈(Fintype.piFinset fun _:Fin n↦A),(∑ i,ε i*(f (a i)-f (b i)))^(2*m) =
   ∑ a∈(Fintype.piFinset fun _:Fin n↦A), ∑ b∈(Fintype.piFinset fun _:Fin n↦A), ∑ k∈piAntidiag univ (2*m),
     (multinomial univ k* ∏ t,(f (a t)-f (b t))^k t) *
      ∑ ε∈(Fintype.piFinset fun _:Fin n↦(({-1,1}:Finset ℝ))), ∏ t,ε t^k t:=by
 simp only[@sum_comm _ _ (Fin n→ℝ) _ _ ((Fintype.piFinset fun _:Fin n↦A)),sum_pow_eq_sum_piAntidiag]
 refine sum_congr rfl fun a _↦ ?_
 refine sum_congr rfl fun b _↦ ?_
 simp only[QL,prod_mul_distrib, @sum_comm _ _ (Fin n→ℝ), ←mul_sum, ←sum_mul]
 refine sum_congr rfl fun k _↦ ?_
 rw[←Qo,QN]
lemma Ed {k:Fin n→ℕ} :
  ∑ ε∈(Fintype.piFinset fun _:Fin n↦(({-1,1}:Finset ℝ))), ∏ t,ε t^k t=2^n*ite (∀ i,Even (k i)) 1 0:=by
 calc
  _= ∏ i, ∑ j∈({-1,1}:Finset ℝ),j^k i:=by rw[←sum_prod_piFinset]
  _= ∏ i,if Even (k i) then 2 else 0:=by
   congr with i
   split_ifs<;>simp_all[sum_pair (show(-1:ℝ)≠1 by norm_num),one_add_one_eq_two]
  _=_:=by simp[Fintype.prod_ite_zero]
lemma FU {f:ι→ℝ} {a b:Fin n→ι} :
  ∑ k∈piAntidiag univ m,
    (multinomial univ fun a↦2*k a:ℝ)* ∏ i,(f (a i)-f (b i))^(2*k i) ≤
   m^m*(∑ i,(f (a i)-f (b i))^2)^m:=by
 rw[sum_pow_eq_sum_piAntidiag,mul_sum]
 refine sum_le_sum fun k hk↦ ?_
 rw[mem_piAntidiag] at hk
 simp only[←Qo,QU]
 gcongr
 norm_cast
 refine multinomial_two_mul_le_mul_multinomial.trans ?_
 rw[hk.1]
lemma CN {f:ι→ℝ} {a b:Fin n→ι} :
  m^m*(∑ i,(f (a i)-f (b i))^2:ℝ)^m ≤
   m^m*2^m*(∑ i,(f (a i)^2+f (b i)^2))^m:=by
 rw[←QL, ←QL, ←QL,Qo,mul_sum _ _ (2:ℝ)]
 gcongr with i
 exact add_sq_le.trans_eq (by simp)
lemma CO {f:ι→ℝ} {a b:Fin n→ι} :
  m^m*2^m*(∑ i,(f (a i)^2+f (b i)^2))^m ≤
   m^m*2^(m+(m-1)) *
    ((∑ i,f (a i)^2)^m+(∑ i,f (b i)^2)^m):=by
 rw[RL, ←Qo _ _ (2^_),Qo _ (2^(m-1)),sum_add_distrib]
 gcongr
 refine add_pow_le ?_ ?_ m<;>positivity
lemma FV {f : ι → ℝ} (hm : 1 ≤ m) (hA : A.Nonempty) :
    (∑ a ∈ (Fintype.piFinset fun _ : Fin n ↦ A), ∑ b ∈ (Fintype.piFinset fun _ : Fin n ↦ A), ∑ k ∈ piAntidiag univ m,
      ↑(multinomial univ fun i ↦ 2 * k i) * ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n
        ≤ (4 * m) ^ m * ∑ a ∈ (Fintype.piFinset fun _ : Fin n ↦ A), (∑ i, f (a i) ^ 2) ^ m := by
  let B := (Fintype.piFinset fun _ : Fin n ↦ A)
  calc
    (∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ piAntidiag univ m,
      (multinomial univ fun i ↦ 2 * k i : ℝ) * ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n
    _ ≤ (∑ a ∈ B, ∑ b ∈ B, m ^ m * 2 ^ (m + (m - 1)) *
          ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) : ℝ) / #A ^ n := by
      gcongr; exact FU.trans <| CN.trans CO
    _ = _ := by
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      rw [← mul_add, ← two_mul, ← mul_assoc 2, ← mul_assoc 2, mul_right_comm 2, ← _root_.pow_succ',
        add_assoc, Nat.sub_add_cancel hm, pow_add, ← mul_pow, ← mul_pow, card_piFinset, prod_const,
        Finset.card_univ, Fintype.card_fin, Nat.cast_pow, mul_div_cancel_left₀]
      · norm_num
        dsimp [B]
      · positivity
section
namespace Real
lemma tp (m:ℕ) (f:ι→ℝ) (hf: ∀ i, ∑ a∈(Fintype.piFinset fun _:Fin n↦A),f (a i)=0) :
  ∑ a∈(Fintype.piFinset fun _:Fin n↦A),(∑ i,f (a i))^(2*m) ≤
   (4*m)^m* ∑ a∈(Fintype.piFinset fun _:Fin n↦A),(∑ i,f (a i)^2)^m:=by
 obtain rfl | hm:=m.eq_zero_or_pos
 ·simp
 have w3:1≤ m:=by rwa[Ty]
 obtain rfl | hA:=A.eq_empty_or_nonempty
 ·cases n<;>cases m<;>simp
 let B:=(Fintype.piFinset fun _:Fin n↦A)
 calc
  ∑ a∈B,(∑ i,f (a i))^(2*m)
   ≤ ∑ a∈(Fintype.piFinset fun _:Fin n↦A),(∑ b∈B, |∑ i,(f (a i)-f (b i))| ^(2*m))/ #A^n:=by
   gcongr; simpa[QU,sq_abs] using Ec hA f hf (2*m) _
  _=(∑ a∈(Fintype.piFinset fun _:Fin n↦A), ∑ b∈(Fintype.piFinset fun _:Fin n↦A), ∑ k∈piAntidiag univ (2*m) with ∀ i,2∣k i,
    multinomial univ (fun i↦k i)* ∏ t,(f (a t)-f (b t))^k t)/ #A^n:=by
   rw[←sum_div]
   simp only[QU,sq_abs]
   simp only[←QU]
   rw[FT,CM,Qx,Te, ←Qw,div_div]
   simp only[Ed,Td,mul_zero,Q3, ←sum_filter, ←sum_mul,even_iff_two_dvd]
   rw[Qx,mul_div_mul_left]
   positivity
  _=(∑ a∈(Fintype.piFinset fun _:Fin n↦A), ∑ b∈(Fintype.piFinset fun _:Fin n↦A), ∑ k∈(piAntidiag univ m).map
     ⟨(2•·),fun _ _ h↦funext fun i↦mul_right_injective₀ SD (SR h i)⟩,
    multinomial univ (fun i↦k i)* ∏ t,(f (a t)-f (b t))^k t)/ #A^n:=by
   rw[map_nsmul_piAntidiag_univ m (ι:=Fin n) (n:=2) SD]; congr!
  _=(∑ a∈(Fintype.piFinset fun _:Fin n↦A), ∑ b∈(Fintype.piFinset fun _:Fin n↦A), ∑ k∈piAntidiag univ m,
    multinomial univ (fun i↦2*k i)* ∏ t,(f (a t)-f (b t))^(2*k t))/ #A^n:=by
   simp
  _≤_:=FV w3 hA
lemma g9 (hm:m≠0) (f:ι→ℝ) (hf: ∀ i, ∑ a∈(Fintype.piFinset fun _:Fin n↦A),f (a i)=0) :
  ∑ a∈(Fintype.piFinset fun _:Fin n↦A),(∑ i,f (a i))^(2*m) ≤
   (4*m)^m*n^(m-1)* ∑ a∈(Fintype.piFinset fun _:Fin n↦A), ∑ i,f (a i)^(2*m):=by
 obtain _ | m:=m
 ·simp at hm
 obtain rfl | hn:=n.eq_zero_or_pos
 ·simp
 calc
  ∑ a∈(Fintype.piFinset fun _:Fin n↦A),(∑ i,f (a i))^(2*(m+1))
   ≤ (4* ↑(m+1))^(m+1)* ∑ a∈(Fintype.piFinset fun _:Fin n↦A),(∑ i,f (a i)^2)^(m+1) :=
   tp _ f hf
  _≤(4* ↑(m+1))^(m+1)*(∑ a∈(Fintype.piFinset fun _:Fin n↦A),n^m* ∑ i,f (a i)^(2*(m+1))):= ?_
  _≤(4* ↑(m+1))^(m+1)*n^m* ∑ a∈(Fintype.piFinset fun _:Fin n↦A), ∑ i,f (a i)^(2*(m+1)):=by
   simp_rw[Qo,mul_sum]; rfl
 gcongr with a
 rw[←div_le_iff₀' (by positivity)]
 simpa only[Finset.card_fin,QU] using
  TF (f:=fun i↦f (a i)^2) (s:=univ) (fun i _↦by positivity) m
end Real
namespace RCLike
variable {𝕜:Type*} [RCLike 𝕜]
lemma g9 (hm:m≠0) (f:ι→𝕜) (hf: ∀ i, ∑ a∈(Fintype.piFinset fun _:Fin n↦A),f (a i)=0) :
  ∑ a∈(Fintype.piFinset fun _:Fin n↦A), ‖∑ i,f (a i)‖ ^(2*m) ≤
   (8*m)^m*n^(m-1)* ∑ a∈(Fintype.piFinset fun _:Fin n↦A), ∑ i, ‖f (a i)‖ ^(2*m):=by
 let f₁ x:ℝ:=re (f x)
 let f₂ x:ℝ:=im (f x)
 let B:=(Fintype.piFinset fun _:Fin n↦A)
 have K1 i: ∑ a∈B,f₁ (a i)=0:=by rw[←RK,hf,map_zero]
 have K2 i: ∑ a∈B,f₂ (a i)=0:=by rw[←RK,hf,map_zero]
 have h₁:=Real.g9 hm _ K1
 have h₂:=Real.g9 hm _ K2
 simp only[QU,RCLike.norm_sq_eq_def]
 simp only[←sq,RK,RK]
 calc
  ∑ a∈B,((∑ i,re (f (a i)))^2+(∑ i,im (f (a i)))^2)^m ≤
    ∑ a∈B,
     2^(m-1)*(((∑ i,re (f (a i)))^2)^m+((∑ i,im (f (a i)))^2)^m):=by
   gcongr with a; apply add_pow_le<;>positivity
  _=2^(m-1)*(∑ a∈B,(∑ i,re (f (a i)))^(2*m) +
     ∑ a∈B,(∑ i,im (f (a i)))^(2*m)):=by
   simp only[←sum_add_distrib,mul_sum,QU]
  _≤2^(m-1)*((4*m)^m*n^(m-1) *
     ∑ a∈B, ∑ i,re (f (a i))^(2*m)+(4*m)^m*n^(m-1) *
     ∑ a∈B, ∑ i,im (f (a i))^(2*m)):=by gcongr
  _=2^(m-1)*((4*m)^m*n^(m-1) *
     ∑ a∈B, ∑ i,(re (f (a i))^(2*m)+im (f (a i))^(2*m))):=by
   simp_rw[sum_add_distrib,Tc]
  _≤2^(m-1)*((4*m)^m*n^(m-1) *
     ∑ a∈B, ∑ i,2*(re (f (a i))^2+im (f (a i))^2)^m):=by
   simp_rw[QU]; gcongr; apply pow_add_pow_le'<;>positivity
  _=(8*m)^m*n^(m-1)* ∑ a∈B, ∑ i,(re (f (a i))^2+im (f (a i))^2)^m:=by
   simp_rw[←mul_sum,show(8:ℝ)=2*4 by norm_num,QL, ←R0 hm (2:ℝ)]
   ring
end RCLike
end
end
section
open scoped Pointwise Combinatorics.Additive translate
namespace Finset
variable {α:Type*} [DecidableEq α] {s:Finset α} {k:ℕ}
section Add
variable [Add α]
end Add
variable [AddCommGroup α] [Fintype α]
end Finset
section
variable {α:Type*} {g:α→ℝ} {c ε:ℝ} {A:Finset α}
open Finset
lemma Ee (hc:0<c) (hg: ∀ a∈A,0≤g a) (h: ∑ a∈A,g a≤ε*c* #A) :
  (1-ε)* #A≤ #{a∈A | g a≤c}:=by
 classical
 have:=h.trans'
  (sum_le_sum_of_subset_of_nonneg (filter_subset (¬g ·≤c) A) fun i hi _↦hg _ hi)
 have :=
  (card_nsmul_le_sum _ _ c (by simp+contextual [le_of_lt])).trans this
 rw[QS,QN] at this
 have:=TZ this hc
 rw[filter_not,cast_card_sdiff (filter_subset _ _)] at this
 linarith only[this]
lemma x2 (hc:0≤c) (hε:0≤ε) (hg: ∀ a∈A,0≤g a)
  (h: ∑ a∈A,g a≤ε*c* #A):(1-ε)* #A≤ #{a∈A | g a≤c}:=by
 rcases hc.lt_or_eq with (hc | rfl)
 ·exact Ee hc hg h
 simp only[mul_zero,zero_mul] at h
 classical
 rw[one_sub_mul,sub_le_comm, ←cast_card_sdiff (filter_subset _ A), ←filter_not,
  filter_false_of_mem]
 ·simp only[card_empty,UH]; positivity
 intro i hi
 rw[(sum_eq_zero_iff_of_nonneg hg).1 (h.antisymm (sum_nonneg hg)) i hi]
 simp
end
open Finset Real
open scoped BigOperators Pointwise NNReal ENNReal
variable {G:Type*} [Fintype G] {A S:Finset G} {f:G→ℂ} {x ε K:ℝ} {k m:ℕ}
section
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
open MeasureTheory in
lemma BD (hε:0<ε) (hm:1≤ m) (hk:64*m/ε^2≤k) :
  (8*m)^m*k^(m-1)* #A^k*k*(2*(aJ (2*m) f):ℝ)^(2*m) ≤
   1/2*((k*ε)^(2*m)* ∑ i:G, ‖f i‖ ^(2*m))* #A^k:=by
 have yQ:((2*m:ℕ):ℝ≥0∞)=2*m:=by rw[Rm,So]
 have w3:2*m≠0:=by
  refine Rl two_pos.ne' ?_
  rw[←Tx, ←Ty]
  exact hm
 rw[QL (2:ℝ), ←yQ, ←gA w3 f, ←Qo, ←Qo,
  QN _ (#A^k:ℝ),QN _ (#A^k:ℝ),
  QN _ (#A^k:ℝ)]
 rw[div_le_iff₀' (by positivity)] at hk
 have Ob:=d8 (p:=((2*m:ℕ):ℝ≥0∞)) (f:=f)
 gcongr ?_*_*_
 calc
  (8*m:ℝ)^m*k^(m-1)*k*2^(2*m)
   = (8*m)^m*2^(2*m)*(k^(m-1)*k):=by ring
  _=(64*m*k/2)^m:=by rw[R0 (by omega),QU, ←QL]; ring
  _≤(ε^2*k*k/2)^m:=by gcongr
  _=(k*ε)^(2*m)/2^m:=by ring_nf; simp_rw[R6]
  _≤(k*ε)^(2*m)/2^1:=by gcongr; norm_num
  _=1/2*(k*ε)^(2*m):=by ring
end
variable [DecidableEq G] [AddCommGroup G]
lemma xj (hm:1≤ m) (x:G) :
  ∑ a∈(Fintype.piFinset fun _:Fin k↦A), ‖∑ i,f (x-a i)-(k•((aC (mu A) f))) x‖ ^(2*m) ≤
   (8*m)^m*k^(m-1) *
    ∑ a∈(Fintype.piFinset fun _:Fin k↦A), ∑ i, ‖f (x-a i)-((aC (mu A) f)) x‖ ^(2*m):=by
 let f':G→ℂ:=fun a↦f (x-a)-((aC (mu A) f)) x
 refine(RCLike.g9 (by linarith only[hm]) f' ?_).trans_eq' ?_
 ·intro i
  rw[Fintype.sum_piFinset_apply,sum_sub_distrib]
  simp only[sum_const]
  rw[←RD (card A), ←tj,l1,cR]
  simp only[SS,Qm,mem_coe]
  rw[←sum_filter,filter_mem_eq_inter,univ_inter,sub_self,smul_zero]
 congr with a:1
 simp only[sum_sub_distrib,RD,sum_const,card_fin,f']
variable [MeasurableSpace G]
namespace gl
def CP (k m:ℕ) (ε:ℝ) (f:G→ℂ) (A:Finset G) (a:Fin k→G):Prop :=
 (aJ (2*m) (fun x:G↦ ∑ i,f (x-a i)-(k•((aC (mu A) f))) x))≤k*ε*(aJ (2*m) f)
noncomputable instance:DecidablePred (CP k m ε f A):=Classical.decPred _
noncomputable def l (k m:ℕ) (ε:ℝ) (f:G→ℂ) (A:Finset G):Finset (Fin k→G) :=
 {x∈(Fintype.piFinset fun _:Fin k↦A) | CP k m ε f A x}
lemma yR (hε:0<ε) (hm:1≤ m)
  (h: ∑ a∈(Fintype.piFinset fun _:Fin k↦A),
    ((aJ (2*m) (fun x:G↦ ∑ i:Fin k,f (x-a i)-(k•((aC (mu A) f))) x))^(2*m):ℝ) ≤
   1/2*(k*ε*(aJ (2*m) f))^(2*m)* #A^k) :
  (#A^k:ℝ)/2≤ #(l k m ε f A):=by
 rw[←Rv, ←TG] at h
 have Ob:=d8 (p:=2*m) (f:=f)
 have:=x2 (by positivity) (by norm_num)
  (fun _ _↦QH d8 _) h
 norm_num1 at this
 rw[TG,Qx,mul_one_div,Rv] at this
 refine this.trans_eq ?_
 rw[l]
 congr with a:3
 refine pow_le_pow_iff_left₀ ?_ ?_ ?_<;>first | positivity | exact d8
variable [DiscreteMeasurableSpace G]
open MeasureTheory in
lemma xk (hm:1≤ m) (hA:A.Nonempty) :
  (8*m)^m*k^(m-1)* ∑ a∈(Fintype.piFinset fun _:Fin k↦A), ∑ i,(aJ (2*m) (τ (a i) f-(aC (mu A) f)))^(2*m) ≤
   (8*m)^m*k^(m-1)* ∑ _a∈(Fintype.piFinset fun _:Fin k↦A), ∑ _i:Fin k,(2*(aJ (2*m) f))^(2*m):=by
 have yQ:((2*m:ℕ):ℝ≥0∞)=2*m:=by rw[Rm,So]
 have w3:1<2*m:=(Qr 2 hm).trans_lt'<| by norm_num1
 have MX:(1:ℝ≥0∞)≤2*m:=by rw[←yQ,Nat.one_le_cast]; exact w3.le
 gcongr
 ·exact d8
 refine(yM MX).trans ?_
 rw[jX,R5 (aJ (2*m) f),add_le_add_iff_left]
 have K3:((2*m:ℝ≥0):ℝ≥0∞)=2*m:=by
  rw[ENNReal.coe_mul,ENNReal.coe_two,ENNReal.coe_natCast]
 have:(1:ℝ≥0)<2*m:=by
  rw[←So, ←Rm,Nat.one_lt_cast]
  exact w3
 rw[←K3,fA]
 refine(wU this.le _ _).trans ?_
 rw[uN hA,Q3]
open MeasureTheory in
lemma Hp (hε:0<ε) (hm:1≤ m) (hk:(64:ℝ)*m/ε^2≤k) :
  (#A^k:ℝ)/2≤ #(l k m ε f A):=by
 have:0<k:=by
  rw[← @Nat.cast_pos ℝ]
  refine hk.trans_lt' ?_
  refine Rn (QM (by norm_num1) ?_) (RF hε _)
  rw[Sp, ←Ty]
  exact hm
 rcases A.eq_empty_or_nonempty with (rfl | hA)
 ·simp[zero_pow this.ne']
 refine yR hε hm ?_
 have w3:2*m≠0:=by linarith
 have yQ:((2*m:ℕ):ℝ≥0∞)=2*m:=by rw[Rm,So]
 rw[←yQ,QL]
 simp only[gA w3]
 rw[sum_comm]
 have: ∀ x:G, ∑ a∈(Fintype.piFinset fun _:Fin k↦A),
   ‖∑ i,f (x-a i)-(k•((aC (mu A) f))) x‖ ^(2*m) ≤
  (8*m)^m*k^(m-1) *
   ∑ a∈(Fintype.piFinset fun _:Fin k↦A), ∑ i, ‖f (x-a i)-((aC (mu A) f)) x‖ ^(2*m) :=
  xj hm
 refine(sum_le_sum fun x _↦this x).trans ?_
 rw[←mul_sum]
 simp only[@sum_comm _ _ G]
 have (a:Fin k→G) (i:Fin k) :
   ∑ x, ‖f (x-a i)-((aC (mu A) f)) x‖ ^(2*m)=(aJ (2*m) (τ (a i) f-(aC (mu A) f)))^(2*m):=by
  rw[←yQ,gA w3]
  simp only[Rw,QZ]
 simp only[this]
 have :
  (8*m)^m*k^(m-1)* ∑ a∈(Fintype.piFinset fun _:Fin k↦A), ∑ i,(aJ (2*m) (τ (a i) f-(aC (mu A) f)))^(2*m) ≤
   (8*m)^m*k^(m-1)* ∑ a∈(Fintype.piFinset fun _:Fin k↦A), ∑ i,(2*(aJ (2*m) f))^(2*m) :=
  xk hm hA
 refine Sj (mod_cast this) ?_
 simpa[Qo] using BD hε hm hk
open MeasureTheory in
lemma pK {t:G} {a:Fin k→G} (ha:a∈l k m ε f A)
  (mM:(a+fun _↦t)∈l k m ε f A) (hk:0<k) (hm:1≤ m) :
  (aJ (2*m) (τ (-t) ((aC (mu A) f))-(aC (mu A) f)))≤2*ε*(aJ (2*m) f):=by
 let f₁:G→ℂ:=fun x↦ ∑ i,f (x-a i)
 let f₂:G→ℂ:=fun x↦ ∑ i,f (x-a i-t)
 have hp:(1:ℝ≥0∞)≤2*m:=by norm_cast; linarith
 have h₁:(aJ (2*m) (f₁-k•((aC (mu A) f))))≤k*ε*(aJ (2*m) f):=by
  rw[l,UU] at ha ; exact ha.2
 have h₂:(aJ (2*m) (f₂-k•((aC (mu A) f))))≤k*ε*(aJ (2*m) f):=by
  rw[l,UU,CP] at mM
  refine mM.2.trans_eq' ?_
  congr with i:1
  simp[sub_sub,f₂]
 have h₃:f₂=τ t f₁:=by
  ext i:1
  rw[QZ]
  refine Io rfl fun j _↦ ?_
  rw[sub_right_comm]
 have Hq:(aJ (2*m) (τ t f₁-k•((aC (mu A) f))))=(aJ (2*m) (τ (-t) (τ t f₁-k•((aC (mu A) f))))):=by
  rw[jX]
 have MY:(aJ (2*m) (τ t f₁-k•((aC (mu A) f))))=(aJ (2*m) (f₁-τ (-t) (k•((aC (mu A) f))))):=by
  rw[Hq,UE,translate_translate]
  simp
 have NH:(aJ (2*m) (τ (-t) (k•((aC (mu A) f)))-f₁))≤k*ε*(aJ (2*m) f):=by
  rwa[r5, ←MY, ←h₃]
 have:(0:ℝ)<k:=by positivity
 refine Uj ?_ this
 rw[←QS, ←zI _ (_-(aC (mu A) f)),nsmul_sub, ←
  translate_smul_right (-t) ((aC (mu A) f)) k,Qo,Q6,R5 ((k:ℝ)*_), ←
  Qo]
 calc
  (aJ (2*m) (τ (-t) (k•((aC (mu A) f)))-k•((aC (mu A) f))))
   ≤ (aJ (2*m) (τ (-t) (k•((aC (mu A) f)))-f₁))+(aJ (2*m) (f₁-k•((aC (mu A) f)))) :=
   ep (mod_cast hp)
  _≤k*ε*(aJ (2*m) f)+k*ε*(aJ (2*m) f):=by gcongr
end gl
end
section
section
open Finset Function Real
open scoped ComplexConjugate NNReal Pointwise
variable {G R:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
section ll
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g:G→R}
lemma zK (hf:0≤f) (hg:0≤g):0≤(aC f g) :=
 fun _a↦sum_nonneg fun _x _↦Qn (hf _) (hg _)
lemma py (hf:0≤f) (hg:0≤g) (a:G):0≤((aC f g)) a :=
 zK hf hg _
variable [StarRing R] [StarOrderedRing R]
lemma iN (hf:0≤f) (hg:0≤g):0≤(al f g) :=
 fun _a↦sum_nonneg fun _x _↦Qn (hf _)<| star_nonneg_iff.2<| hg _
lemma dM (hf:0≤f) (hg:0≤g) (a:G):0≤((al f g)) a :=
 iN hf hg _
end ll
section iw
variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] {f g:G→R}
@[simp] lemma tT (hf:0≤f) (hg:0≤g) :
  support ((aC f g))=support f+support g:=by
 refine(tQ _ _).antisymm ?_
 rintro _ ⟨a,ha,b,hb,rfl⟩
 rw[mem_support,r4]
 exact Uq<| sum_pos' (fun c _↦Qn (hf _)<| hg _) ⟨0,mem_univ _,
  QM ((hf _).lt_of_ne'<| by simpa using ha)<| (hg _).lt_of_ne'<| by simpa using hb⟩
variable [StarRing R] [StarOrderedRing R]
@[simp] lemma f8 (hf:0≤f) (hg:0≤g):support ((al f g))=support f-support g:=by
 simpa[Qy] using tT hf (conjneg_nonneg.2 hg)
end iw
section ll
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g:G→R} {n:ℕ}
end ll
section iw
variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] [StarRing R] [StarOrderedRing R]
 {f g:G→R} {n:ℕ}
end iw
namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function
section
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g:G→R}
variable [StarRing R] [StarOrderedRing R]
end
end Mathlib.Meta.Positivity
end
end
section
section
open Finset Function Real MeasureTheory
open scoped ComplexConjugate ENNReal NNReal translate
variable {α 𝕜 E:Type*} [MeasurableSpace α]
section NormedAddCommGroup
variable [NormedAddCommGroup E] {p q:ℝ≥0∞} {w:α→ℝ≥0} {f g h:α→E}
noncomputable def b0 (p:ℝ≥0∞) (w:α→ℝ≥0) (f:α→E):ℝ :=
 lpNorm f p<| .sum fun i↦w i• .dirac i
@[simp] lemma tU:0≤(b0 p w f):=by simp[b0]
@[simp] lemma I6 (w:α→ℝ≥0):(b0 p w ((0:α→E)))=0:=by simp[b0]
@[simp] lemma KQ (w:α→ℝ≥0) (f:α→E):(b0 p w (-f))=(b0 p w f):=by
 simp[b0]
lemma Ak [NormedField 𝕜] [NormedSpace 𝕜 E] (c:𝕜) (f:α→E) (p:ℝ≥0∞) (w:α→ℝ≥0) :
  (b0 p w (c•f))= ‖c‖₊*(b0 p w f):=lpNorm_const_smul ..
lemma zL [NormedSpace ℝ E] (n:ℕ) (f:α→E) (p:ℝ≥0∞) (w:α→ℝ≥0) :
  (b0 p w (n•f))=n•(b0 p w f):=lpNorm_nsmul ..
section RCLike
variable {K:Type*} [RCLike K]
end RCLike
variable [Finite α]
variable [Fintype α] [DiscreteMeasurableSpace α]
lemma ln (iu:p≠0) (hp:p≠∞) (w:α→ℝ≥0) (f:α→E) :
  (b0 p w f)=(∑ i,w i• ‖f i‖ ^p.toReal)^p.toReal⁻¹ :=by
 simp[b0,lpNorm_eq_integral_norm_rpow_toReal iu hp .of_discrete,RG,
  integral_finsetSum_measure]
lemma r7 {p:ℝ≥0} (hp:p≠0) (w:α→ℝ≥0) (f:α→E) :
  (b0 p w f)^(p:ℝ)= ∑ i,w i• ‖f i‖ ^(p:ℝ):=by
 rw[ln (mod_cast hp) (by simp),ENNReal.coe_toReal,
  S4 _ (mod_cast hp)]
 simp only[RG,Q2]
 positivity
lemma jd {p:ℕ} (hp:p≠0) (w:α→ℝ≥0) (f:α→E) :
  (b0 p w f)^p= ∑ i,w i• ‖f i‖ ^p:=by
 simpa using r7 (Nat.cast_ne_zero.2 hp) w f
omit [Fintype α]
section one_le
lemma yS (hp:1≤p) (w:α→ℝ≥0) (f g:α→E) :
  (b0 p w (f+g))≤(b0 p w f)+(b0 p w g):=lpNorm_add_le .of_discrete hp
lemma qU (hp:1≤p) (w:α→ℝ≥0) (f g:α→E) :
  (b0 p w f)≤(b0 p w (f+g))+(b0 p w g):=by simpa using yS hp w (f+g) (-g)
end one_le
end NormedAddCommGroup
section Real
variable [DiscreteMeasurableSpace α] {p:ℝ≥0∞} {w:α→ℝ≥0} {f g:α→ℝ}
end Real
section b0
variable [Finite α] [DiscreteMeasurableSpace α] {p:ℝ≥0} {w:α→ℝ≥0}
variable [AddCommGroup α]
end b0
namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function MeasureTheory
end Mathlib.Meta.Positivity
end
end
section
section
namespace Finset
variable {α R:Type*} [Fintype α] [Semiring R]
@[simp] lemma rl (s:Finset α): ∑ x,(Set.indicator ((s:Set α)) fun _↦(1:R)) x= #s:=by
 classical simp[Qm]
lemma lK (s:Finset α): #s= ∑ x,(Set.indicator ((s:Set α)) fun _↦(1:_)) x :=
 (rl _).symm
end Finset
end
end
section
section
namespace Set
variable {α M:Type*} [Zero M] [One M]
section Preorder
variable [Preorder M] [ZeroLEOneClass M] {s:Set α}
@[simp] lemma cZ:0≤ s.indicator (fun _↦(1:M)) :=
 indicator_nonneg (by simp)
end Preorder
section PartialOrder
variable [PartialOrder M] [ZeroLEOneClass M] [NeZero (1:M)] {s:Set α}
end PartialOrder
end Set
end
end
section
section
open Finset Fintype Function MeasureTheory RCLike Real
open scoped ENNReal NNReal Pointwise
variable {G:Type*} [DecidableEq G] [Fintype G] [AddCommGroup G] {p:ℕ} {aL a0 A:Finset G}
 {ε δ:ℝ}
private def c (p:ℕ) (A:Finset G) (s:Fin p→G):Finset G:=univ.inf fun i↦s i+ᵥ A
private lemma B9 (p:ℕ) (aL a0 A:Finset G) (f:G→ℝ) :
  ∑ s,⟪(al ((Set.indicator (↑(aL∩c p A s)) fun _↦(1:(ℝ)))) ((Set.indicator (↑(a0∩c p A s)) fun _↦(1:_)))),f⟫_[ℝ] =
   (#aL* #a0)• ∑ x,((al ((@mu (ℝ) _ _) aL) (mu a0))) x*((al ((Set.indicator A fun _↦(1:_))) ((Set.indicator A fun _↦(1:_))))) x^p*f x:=by
 simp_rw[Qo]
 simp only[wInner_one_eq_sum,inner_apply',R3,mul_sum,sum_mul,smul_sum,
  @sum_comm _ _ (Fin p→G),lJ,ri,Fintype.sum_pow,
  Set.rf]
 congr with ey
 congr with b₂
 refine Qk (Equiv.neg _) _ _ fun s↦ ?_
 rw[←TJ,mul_smul_mul_comm,qm,qm,
  coe_inter,coe_inter,Set.iq,Set.iq,
  Q7,prod_mul_distrib]
 simp[c,mN,Qy,Qo,RV]
private lemma K4 (p:ℕ) (B A:Finset G): ∑ s, #(B∩c p A s)= #A^p* #B:=by
 simp only[lK,Set.iq,c,mN,
  mul_sum,sum_mul,coe_inter,coe_vadd_finset,sum_pow', @sum_comm G,SB,
  ←sR,QZ]
 congr with x
 exact Qk (Equiv.subLeft fun _↦x) _ _ fun s↦Qx _ _
private lemma x3 (p:ℕ) (B A:Finset G) :
  ∑ s,(#(B∩c p A s):ℝ)= #A^p* #B:=by
 rw[←Nat.cast_sum,K4]; norm_cast
variable [MeasurableSpace G]
noncomputable def s (p:ℝ≥0) (ε:ℝ) (aL a0 A:Finset G):Finset G :=
 {x | (1-ε)*(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator ((A:Set G)) fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))<((al ((Set.indicator A fun _↦(1:_))) ((Set.indicator A fun _↦(1:_))))) x}
@[simp] lemma K5 {p:ℝ≥0} {ε:ℝ} {aL a0 A:Finset G} {x:G} :
  x∈s p ε aL a0 A ↔
   (1-ε)*(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator ((A:Set G)) fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))<((al ((Set.indicator A fun _↦(1:_))) ((Set.indicator A fun _↦(1:_))))) x:=by simp[s]
lemma I7 {p : ℝ≥0} {ε : ℝ} {aL a0 A : Finset G} {x : G} :
    x ∈ s p ε aL a0 A ↔ (1 - ε) * (_root_.b0 p ((_root_.al (_root_.mu aL) (_root_.mu a0))) ((_root_.al ((@_root_.mu (ℝ) _ _) A) (_root_.mu A)))) < ((_root_.al (_root_.mu A) (_root_.mu A))) x := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  · simp [← l1, -nsmul_eq_mul, oy, oz, zL, hA.card_pos]
variable [DiscreteMeasurableSpace G]
private lemma jq (hp:p≠0) (hB:(aL∩a0).Nonempty) (hA:A.Nonempty) :
  (0:ℝ)<(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))^p:=by
 rw[jd (by positivity)]
 refine sum_pos' (fun x _↦by positivity) ⟨0,mem_univ _,smul_pos ?_<| RF ?_ _⟩
 ·rwa[Tx, ←Ur,f8,jo,jo,
   ←coe_sub,mem_coe,zero_mem_sub_iff,not_disjoint_iff_nonempty_inter]<;>exact cC
 ·rw[norm_pos_iff, ←Ur,f8,Set.jY]
  any_goals exact Set.cZ
  exact hA.to_set.zero_mem_sub
lemma Oc (hp₂:2≤p) (f:G→ℝ≥0) (hf: ∃ x,x∈aL-a0∧x∈A-A∧x∈f.support)
  (hB:(aL∩a0).Nonempty) (hA:A.Nonempty) :
  ∃ aX,aX⊆aL∧ ∃ a3,a3⊆a0 ∧
   ⟪(al ((@mu (ℝ) _ _) aX) (mu a3)),(↑) ∘ f⟫_[ℝ]*(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))^p
    ≤ 2* ∑ x,((al (mu aL) (mu a0))) x*((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))) x^p*f x ∧
   (4:ℝ) ⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p)
    ≤ #aX/ #aL ∧
   (4:ℝ) ⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p)
    ≤ #a3/ #a0:=by
 have:=hB.mono inter_subset_left
 have:=hB.mono inter_subset_right
 have iu:p≠0:=by positivity
 have:=jq iu hB hA
 set M:ℝ :=
  2 ⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))^p*(sqrt #aL*sqrt #a0)/ #A^p
   with Al
 have hM:0<M:=by rw[Al]; positivity
 replace hf:0< ∑ x,((al ((@mu (ℝ) _ _) aL) (mu a0))) x*((al ((Set.indicator A fun _↦(1:_))) ((Set.indicator A fun _↦(1:_))))) x^p*f x:=by
  have:0≤(al ((@mu (ℝ) _ _) aL) (mu a0))*((al ((Set.indicator A fun _↦(1:_))) ((Set.indicator A fun _↦(1:_)))))^p*(↑) ∘ f :=
   Qn (Qn (iN cC cC)<| QH
    (iN Set.cZ Set.cZ) _) fun _↦by simp
  refine Fintype.sum_pos<| this.lt_iff_ne'.2<| support_nonempty_iff.1 ?_
  simp only[support_comp_eq,Set.Nonempty,Tm,support_mul',f8,
   Set.cZ,cC,Set.jY,jo,
   NNReal.coe_eq_zero,iff_self,forall_const,Set.mem_inter_iff, ←coe_sub,mem_coe,
   support_pow' _ iu,hf]
 set aX:=fun s↦aL∩c p A s
 set a3:=fun s↦a0∩c p A s
 set g:(Fin p→G)→ℝ:=fun s↦ #(aX s)* #(a3 s) with Ef
 have hg: ∀ s,0≤g s:=fun s↦by rw[Ef]; dsimp; positivity
 have Am: ∑ s,g s= #aL* #a0*(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))^p:=by
  have Eg:0≤(al ((Set.indicator ((A:Set G)) fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_)))) :=
   iN Set.cZ Set.cZ
  simpa only[jd iu,norm_of_nonneg (Eg _),RG,
   NNReal.lb,NNReal.iF,wInner_one_eq_sum,Rt,inner_apply',
   ←coe_inter,conj_to_real,Q3,jI,rl,QS,
   Rm,g,aX,a3] using! B9 p aL a0 A 1
 suffices ∑ s,⟪(al ((Set.indicator (aX s) fun _↦(1:(ℝ)))) ((Set.indicator (a3 s) fun _↦(1:_)))),(↑) ∘ f⟫_[ℝ]*(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))^p
  < ∑ s,(Set.indicator (({s | M^2≤g s}:Finset _)) fun _↦(1:_)) s*g s *
    (2* ∑ x,((al (mu aL) (mu a0))) x*((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))) x^p*f x) by
  obtain ⟨s, -,hs⟩:=exists_lt_of_sum_lt this
  refine ⟨_,inter_subset_left (s₂:=c p A s),_,inter_subset_left (s₂:=c p A s), ?_⟩
  simp only[Qm,SS] at hs
  split_ifs at hs with h; swap
  ·simp only[zero_mul,wInner_one_eq_sum,Rh,SV,
    R3] at hs
   have:0≤(al ((Set.indicator ((aX s:Set G)) fun _↦(1:(ℝ)))) ((Set.indicator (a3 s) fun _↦(1:_)))) :=
    iN Set.cZ Set.cZ
   cases hs.not_ge<|
    Qn (sum_nonneg fun x _↦Qn (this _)<| by positivity)<| by positivity
  have:(4:ℝ) ⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p)
   ≤ #(aX s)/ #aL*(#(a3 s)/ #a0):=by
   rw[div_mul_div_comm,Qs (by positivity)]
   simpa[Ef,Al,QL,TY,pow_mul',show(2:ℝ)^2=4 by norm_num,
    S5] using h
  refine ⟨(lt_of_mul_lt_mul_left (hs.trans_eq' ?_)<| hg s).le,this.trans<|
   Sq ?_<| UW ?_ ?_,this.trans<|
   RQ ?_<| UW ?_ ?_⟩
  ·simp_rw[aX,a3,g, ←l1,oy,oz, ←Nat.cast_smul_eq_nsmul ℝ,
    wInner_smul_left,Q2,star_trivial,Qo,aX,a3]
  any_goals positivity
  all_goals exact Nat.cast_le.2<| card_mono inter_subset_left
 rw[←sum_mul,B9,QS,Rm, ←sum_mul,QN, ←Am,
  Q6, ←Qo]
 simp only[Qm,SS,mem_coe,mem_filter,mem_univ,TM, ←sum_filter,
  mul_lt_mul_iff_left₀ hf,Rh]
 by_cases h: ∀ s,g s≠0→M^2≤g s
 ·rw[←sum_filter_ne_zero (s:=filter _ _),Finset.filter_comm,
   filter_true_of_mem fun s hs↦h s (mem_filter.1 hs).2, ←sum_filter_ne_zero]
  refine lt_mul_of_one_lt_left (sum_pos (fun s hs↦(h _ (mem_filter.1 hs).2).trans_lt'<|
   by positivity) ?_) one_lt_two
  rw[←sum_filter_ne_zero] at Am
  exact nonempty_of_sum_ne_zero<| Am.trans_ne<| by positivity
 push Not at h
 obtain ⟨s,hs⟩:=h
 suffices h:(2:ℝ)* ∑ s with g s<M^2,g s< ∑ s,g s by
  refine(le_or_lt_of_add_le_add ?_).resolve_left h.not_ge
  simp_rw[←not_le, ←compl_filter, ←R5, ←Tc,sum_compl_add_sum]
  rfl
 rw[←lt_div_iff₀' (zero_lt_two' ℝ),Ri]
 calc
  ∑ s with g s<M^2,g s= ∑ s with g s<M^2∧g s≠0,Real.sqrt (g s)*Real.sqrt (g s)
     := by simp_rw[mul_self_sqrt (hg _), ←filter_filter,sum_filter_ne_zero]
  _< ∑ s with g s<M^2∧g s≠0,M*Real.sqrt (g s)
    := sum_lt_sum_of_nonempty ⟨s,mem_filter.2 ⟨mem_univ _,hs.symm⟩⟩ ?_
  _≤ ∑ s,M*Real.sqrt (g s):=sum_le_univ_sum_of_nonneg fun s↦by positivity
  _=M*(∑ s,Real.sqrt #(aX s)*Real.sqrt #(a3 s))
    := by simp_rw[mul_sum,g,sqrt_mul<| Q5 _]
  _≤M*(Real.sqrt (∑ s, #(aX s))*Real.sqrt (∑ s, #(a3 s))):=by
   gcongr; exact sum_sqrt_mul_sqrt_le _ fun i↦by positivity fun i↦by positivity
  _=_:= ?_
 ·simp only[mem_filter,mem_univ,TM,and_imp]
  exact fun s Od hs↦Sk ((sqrt_lt' hM).2 Od)<|
   sqrt_pos.2<| (hg _).lt_of_ne' hs
 rw[x3,x3,sqrt_mul',sqrt_mul',Q7 (Real.sqrt _),mul_self_sqrt,
  ←Qo,Al,Tz, ←sqrt_mul,Qo,mul_self_sqrt,Am,QN,
  Qo]
 all_goals positivity
lemma Hr (aL a0:Finset G) (hε:0<ε) (An:ε≤1) (Ca:0<δ) (hp:Even p)
  (hp₂:2≤p) (FW:ε⁻¹ *log (2/δ)≤p) (hB:(aL∩a0).Nonempty) (hA:A.Nonempty)
  (hf: ∃ x,x∈aL-a0∧x∈A-A∧x∉s p ε aL a0 A) :
  ∃ aX,aX⊆aL∧ ∃ a3,a3⊆a0∧1-δ≤ ∑ x∈s p ε aL a0 A,((al (mu aX) (mu a3))) x ∧
    (4:ℝ)⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p) ≤
      #aX/ #aL ∧
     (4:ℝ)⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p) ≤
      #a3/ #a0:=by
 obtain ⟨aX,I8,a3,I9,h,r8,r9⟩ :=
  Oc hp₂ (Set.indicator ((s p ε aL a0 A)ᶜ) fun _↦(1:_))
   (by simpa only[Set.jY,coe_compl,Set.mem_compl_iff,mem_coe]) hB hA
 refine ⟨aX,I8,a3,I9, ?_,r8,r9⟩
 have iu:0<p:=by positivity
 have aux (c:Finset G) (r)
  (h:(4:ℝ)⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p)≤ #c/r) :
  c.Nonempty:=by
  simp_rw[nonempty_iff_ne_empty]
  rintro rfl
  simp[pow_mul',TA (zero_lt_four' ℝ),div_nonpos_iff,
   (RF (jq iu.ne' hB hA) 2).not_ge,iu.ne',hA.ne_empty] at h
 have fY:aX.Nonempty:=aux _ _ r8
 have ho:a3.Nonempty:=aux _ _ r9
 clear r8 r9 aux
 rw[sub_le_comm]
 calc
  _= ∑ x∈(s p ε aL a0 A)ᶜ,((al (mu aX) (mu a3))) x:= ?_
  _=⟪(al ((@mu (ℝ) _ _) aX) (mu a3)),(↑) ∘ (Set.indicator ((s (↑p) ε aL a0 A)ᶜ) fun _↦(1:(ℝ≥0)))⟫_[ℝ]:=by
   simp[wInner_one_eq_sum, -mem_compl, -K5,Qm]
   simp only[←ite_not (_∈s p ε aL a0 A), ←mem_compl,TU]
   simp[-mem_compl]
  _≤_:=(Qs<| jq iu.ne' hB hA).2 h
  _≤_:= ?_
 ·simp_rw[sub_eq_iff_eq_add',sum_add_sum_compl,jI,xX]
  rw[kU _ fY,kU _ ho,QT]
 rw[QF (jq iu.ne' hB hA), ←le_div_iff₀' (zero_lt_two' ℝ)]
 simp only[TU NNReal.toReal,Qm,TN,NNReal.coe_zero,
  mul_boole,Fintype.sum_ite_mem,S5, ←coe_compl,mem_coe]
 calc
  ∑ x∈(s p ε aL a0 A)ᶜ,((al (mu aL) (mu a0))) x*((al ((Set.indicator A fun _↦(1:_))) ((Set.indicator A fun _↦(1:_))))) x^p ≤
    ∑ x∈(s p ε aL a0 A)ᶜ,
     ((al (mu aL) (mu a0))) x*((1-ε)*(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_)))))))^p:=by
   gcongr with x hx
   ·exact dM cC cC x
   ·exact dM Set.cZ Set.cZ _
   ·simpa using hx
  _≤ ∑ x,((al (mu aL) (mu a0))) x*((1-ε)*(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_)))))))^p:=by
   gcongr
   ·intros
    exact Qn (dM cC cC _)<| hp.pow_nonneg _
   ·exact subset_univ _
  _=(aJ 1 ((@mu (ℝ) _ _) aL))*(aJ 1 ((@mu (ℝ) _ _) a0))*((1-ε)^p*(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))^p)
    := ?_
  _≤_ :=
   RQ (Qn (hp.pow_nonneg _)<| hp.pow_nonneg _)<|
    mul_le_one₀ rj d8 rj
  _≤_:=Qi ?_<| hp.pow_nonneg _
 ·have:0≤(al ((@mu (ℝ) _ _) aL) (mu a0)):=iN cC cC
  simp_rw[←xY cC cC,ej,
   RA (this _),sum_mul,QL]
 calc
  (1-ε)^p≤exp (-ε)^p:=by gcongr; exact one_sub_le_exp_neg _
  _=exp (-(ε*p)):=by rw[←neg_mul,exp_mul,rpow_natCast]
  _≤exp (-log (2/δ)) :=
   (exp_monotone<| TO<| (TA<| by positivity).1 FW)
  _=δ/2:=by rw[exp_neg,exp_log,inv_div]; positivity
end
end
section
section
open Finset hiding card
open Fintype (card)
open Function MeasureTheory RCLike Real
open scoped ComplexConjugate ComplexOrder NNReal ENNReal
variable {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
 {ν:G→ℝ≥0} {f:G→ℝ} {g h:G→ℂ} {ε:ℝ} {p:ℕ}
lemma wV {f:G→ℂ} (hf:(al g g)=f) (f9:(al h h)=(↑) ∘ ν) (k:ℕ) :
  0≤⟪f^k,(↑) ∘ ν⟫_[ℂ]:=by
 calc
  0≤ ∑ z:Fin k→G,(‖∑ x,(∏ i,conj (g (x+z i)))*h x‖ :ℂ)^2:=by positivity
  _= ∑ x:G, ∑ yz:G × G with yz.1-yz.2=x,
     h yz.1*conj h yz.2*conj (((al g g)) (yz.1-yz.2))^k:= ?_
  _= ∑ x:G, ∑ yz:G × G with yz.1-yz.2=x,
     h yz.1*conj h yz.2*conj (((al g g)) x)^k:=by
    congr! with x _ yz Oe
    simpa using Oe
  _=_:=by
   rw[←hf, ←f9,wInner_one_eq_sum]
   simp only[Pi.pow_apply,Sb,map_pow]
   simp_rw[el h,sum_mul]
 simp_rw[ri,sum_fiberwise, ←univ_product_univ,sum_product]
 simp only[sum_pow',sum_mul_sum,RU,T0,SB,
  ←UX,RK,map_prod]
 simp only[mul_sum, @sum_comm _ _ (Fin k→G),Qx (conj _),prod_mul_distrib,TR]
 rw[sum_comm]
 congr with x
 congr with y
 congr with z
 group
lemma xl {f:G→ℝ} (hf:(al g g)=(↑) ∘ f) (f9:(al h h)=(↑) ∘ ν) (k:ℕ) :
  (0:ℝ)≤⟪(↑) ∘ ν,f^k⟫_[ℝ]:=by
 simpa[←Complex.zero_le_real,wInner_one_eq_sum,Qx] using wV hf f9 k
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
end
end
section
section
open Finset hiding card
open Fintype (card)
open Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ENNReal NNReal NNRat
variable {ι κ 𝕜:Type*} [Fintype ι]
namespace RCLike
variable [RCLike 𝕜] {I4:MeasurableSpace ι} [DiscreteMeasurableSpace ι] {f:ι→𝕜}
@[simp] lemma wInner_cWeight_self (f:ι→𝕜) :
  ⟪f,f⟫ₙ_[𝕜]=(((c2 2 f):ℝ):𝕜)^2:=by
 simp_rw[←UI]
 simp[ru,wInner_cWeight_eq_expect]
end RCLike
namespace MeasureTheory
section mn
variable {α:Type*} {w2:MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
 {p q r:ℝ≥0∞} {f g:α→𝕜}
omit [Fintype α]
variable [Finite α]
lemma yT (p q:ℝ≥0∞) (_hr₀:r≠0) [PL:ENNReal.HolderTriple p q r] :
  (c2 r (f*g))≤(c2 p f)*(c2 q g):=by
 cases RR α
 set μ:=ProbabilityTheory.uniformOn (Set.univ:Set α) with Hs
 have Of:IsFiniteMeasure μ:=by rw[Hs]; infer_instance
 have MZ:MemLp (f*g) r μ:=MemLp.of_discrete
 have FX:MemLp f p μ:=MemLp.of_discrete
 have FY:MemLp g q μ:=MemLp.of_discrete
 have Og: ∀ᵐ x ∂μ, ‖f x*g x‖₊≤(1:NNReal)* ‖f x‖₊* ‖g x‖₊ :=
  .of_forall fun x↦by rw[QT]; exact nnnorm_mul_le _ _
 have key:eLpNorm (fun x↦f x*g x) r μ
   ≤ ((1:NNReal):ℝ≥0∞)*eLpNorm f p μ*eLpNorm g q μ :=
  eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p:=p) (q:=q) (r:=r)
   FX.aestronglyMeasurable FY.aestronglyMeasurable (·*·) 1 Og
 change lpNorm _ _ μ≤lpNorm _ _ μ*lpNorm _ _ μ
 rw[←toReal_eLpNorm MZ.aestronglyMeasurable,
   ←toReal_eLpNorm FX.aestronglyMeasurable,
   ←toReal_eLpNorm FY.aestronglyMeasurable,
   ←UK]
 apply ENNReal.toReal_mono
 ·exact ENNReal.mul_ne_top FX.eLpNorm_ne_top FY.eLpNorm_ne_top
 ·simpa[Pi.mul_def] using key
end mn
section Real
variable {α:Type*} {w2:MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] {p q:ℝ≥0}
 {f g:α→ℝ}
end Real
section mn
variable {α:Type*} {w2:MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
 {p q r:ℝ≥0∞} {f g:α→𝕜}
omit [Fintype α] in
lemma tV [Finite α] (p q:ℝ≥0∞) [hpq:ENNReal.HolderConjugate p q] :
  (c2 1 (f*g))≤(c2 p f)*(c2 q g):=yT _ _ one_ne_zero
end mn
end MeasureTheory
end
end
section
section
open AddChar Finset Fintype Function MeasureTheory RCLike
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal translate
variable {G:Type*} [AddCommGroup G] [Fintype G] {f:G→ℂ} {ψ:AddChar G ℂ} {n:ℕ}
noncomputable def dft (f:G→ℂ):AddChar G ℂ→ℂ:=fun ψ↦⟪ψ,f⟫_[ℂ]
lemma dft_apply (f:G→ℂ) (ψ:AddChar G ℂ):dft f ψ=⟪ψ,f⟫_[ℂ]:=rfl
lemma pz [MeasurableSpace G] [DiscreteMeasurableSpace G] (f:G→ℂ)
  (ψ:AddChar G ℂ): ‖dft f ψ‖ ≤(aJ 1 f):=by
 grw[dft_apply,lk ∞ 1,dw]
 simp[Q0]
lemma qV [MeasurableSpace G] [DiscreteMeasurableSpace G] (f:G→ℂ) :
  (c2 (∞) (dft f))≤(aJ 1 f):=by
 rw[oB]; exact ciSup_le fun ψ↦pz f ψ
@[simp] lemma vM (f g:G→ℂ):⟪dft f,dft g⟫ₙ_[ℂ]=⟪f,g⟫_[ℂ]:=by
 classical
 unfold dft
 simp_rw[wInner_one_eq_sum,wInner_cWeight_eq_expect,inner_apply',RK,RU,
  T0,sum_mul,mul_sum,expect_sum_comm,Q7 _ (conj<| f _),
  ←expect_mul, ←Rz, ←map_neg_eq_inv, ←map_add_eq_mul,
  TH,add_neg_eq_zero,SS,UL]
@[simp] lemma w4 [MeasurableSpace G] [DiscreteMeasurableSpace G] (f:G→ℂ) :
  (c2 2 (dft f))=(aJ 2 f):=by
 refine(sq_eq_sq₀ lpNorm_nonneg lpNorm_nonneg).1<| Complex.ofReal_injective ?_
 push_cast
 simpa[c2,aJ,RCLike.wInner_cWeight_self,xZ] using vM f f
lemma vk (f:G→ℂ) (a:G):𝔼 ψ,dft f ψ*ψ a=f a:=by
 classical
 simp_rw[dft,wInner_one_eq_sum,inner_apply',sum_mul,expect_sum_comm,QN _ (f _),
  ←expect_mul, ←Rz,TK, ←map_sub_eq_div,
  TH,sub_eq_zero,SS,UL]
@[simp] lemma Ao [DecidableEq G]:dft (uK:G→ℂ)=1:=by
 ext; simp[yG,dft_apply,wInner_one_eq_sum]
variable [DecidableEq G]
lemma sa (f g:G→ℂ) (ψ:AddChar G ℂ):dft ((aC f g)) ψ=dft f ψ*dft g ψ:=by
 simp_rw[dft,wInner_one_eq_sum,inner_apply,cR,mul_sum,sum_mul,
  ←sum_product',univ_product_univ]
 refine Qk ((Equiv.prodComm _ _).trans<|
  ((Equiv.refl _).prodShear Equiv.subRight).trans<| Equiv.prodComm _ _)  _ _ fun (a,b)↦ ?_
 simp[Q7, ←RU, ←map_add_eq_mul]
@[simp] lemma x4 (f g:G→ℂ):dft ((aC f g))=dft f*dft g:=funext<| sa _ _
@[simp] lemma vN (f:G→ℂ): ∀ n,dft ((eo f n))=dft f^n
 | 0=>Ao
 | n+1=>by simp[vi,RB,vN]
@[simp] lemma vO (f:G→ℂ) (n:ℕ) (ψ:AddChar G ℂ) :
  dft ((eo f n)) ψ=dft f ψ^n:=SR (vN _ _) _
end
end
section
open scoped BigOperators
namespace ay
open Finset
abbrev Zg (G:Type*) [AddCommGroup G]:=G→+ AddCircle (1:ℝ)
structure aj (G:Type*) [AddCommGroup G] where
 eX:Finset (Zg G)
 width:Zg G→NNReal
namespace aj
variable {G H:Type*} [AddCommGroup G] [AddCommGroup H]
def rank (B:aj G):ℕ:=B.eX.card
def ai (B:aj G) (t:NNReal):aj G where
 eX:=B.eX
 width γ:=t*B.width γ
@[simp] lemma KR (B:aj G) (t:NNReal) :
  (B.ai t).eX=B.eX:=rfl
@[simp] lemma oC (B:aj G) (t:NNReal) (γ:Zg G) :
  (B.ai t).width γ=t*B.width γ:=rfl
@[simp] lemma f6 (B:aj G) (t:NNReal) :
  (B.ai t).rank=B.rank:=rfl
@[simp] lemma oD (B:aj G):B.ai 1=B:=by
 cases B
 simp[ai]
@[simp] lemma vl (B:aj G) (s t:NNReal) :
  (B.ai s).ai t=B.ai (t*s):=by
 cases B
 simp[ai,Qo]
noncomputable def Zc [Fintype G] (B:aj G):Finset G:=by
 classical
 exact Finset.univ.filter fun x ↦
  ∀ γ∈B.eX, ‖γ x‖ ≤(B.width γ:ℝ)
@[simp] lemma Zm [Fintype G] (B:aj G) (x:G) :
  x∈B.Zc↔ ∀ γ∈B.eX, ‖γ x‖ ≤(B.width γ:ℝ):=by
 classical
 simp[Zc]
lemma sb [Fintype G] (B:aj G):0∈B.Zc:=by
 rw[Zm]
 intro γ n4
 simp
lemma aE [Fintype G] (B:aj G):B.Zc.Nonempty :=
 ⟨0,B.sb⟩
lemma ec [Fintype G] {B:aj G} {x:G} :
  -x∈B.Zc↔x∈B.Zc:=by
 simp only[Zm]
 constructor<;>intro hx γ n4
 ·simpa only[map_neg,norm_neg] using hx γ n4
 ·simpa only[map_neg,norm_neg] using hx γ n4
lemma b5 [Fintype G] {B:aj G} {s t:NNReal} (pA:s≤t) :
  (B.ai s).Zc⊆(B.ai t).Zc:=by
 intro x hx
 rw[Zm] at hx ⊢
 intro γ n4
 have d5:(s:ℝ)*(B.width γ:ℝ) ≤
   (t:ℝ)*(B.width γ:ℝ):=by
  gcongr
 exact(hx γ n4).trans d5
lemma e7 [Fintype G] {B:aj G} {s t:NNReal} {x y:G}
  (hx:x∈(B.ai s).Zc) (hy:y∈(B.ai t).Zc) :
  x+y∈(B.ai (s+t)).Zc:=by
 rw[Zm] at hx hy ⊢
 intro γ n4
 rw[map_add]
 calc
  ‖γ x+γ y‖ ≤ ‖γ x‖ + ‖γ y‖ :=norm_add_le _ _
  _≤(s:ℝ)*(B.width γ:ℝ)+(t:ℝ)*(B.width γ:ℝ) :=
   Sr (hx γ n4) (hy γ n4)
  _=((s+t:NNReal):ℝ)*(B.width γ:ℝ):=by
   push_cast
   ring
lemma j0 [Fintype G] {B:aj G} {s t:NNReal} {x y:G}
  (hx:x∈(B.ai s).Zc) (hy:y∈(B.ai t).Zc) :
  x-y∈(B.ai (s+t)).Zc:=by
 rw[Qy]
 exact e7 hx (ec.mpr hy)
noncomputable def map (B:aj G) (e:G ≃+ H):aj H:=by
  classical
  exact
    { eX:=B.eX.image fun γ↦γ.comp e.symm.toAddMonoidHom
      width:=fun δ↦B.width (δ.comp e.toAddMonoidHom) }
@[simp] lemma MB (B:aj G) (e:G ≃+ H) (δ:Zg H) :
    (B.map e).width δ=B.width (δ.comp e.toAddMonoidHom):=by
  classical
  simp[map]
@[simp] lemma vP (B:aj G) (e:G ≃+ H) (δ:Zg H) :
  δ∈(B.map e).eX ↔
   ∃ γ∈B.eX,γ.comp e.symm.toAddMonoidHom=δ:=by
 classical
 simp[map]
private lemma vv (e:G ≃+ H) :
  Function.Injective (fun γ:Zg G↦γ.comp e.symm.toAddMonoidHom):=by
 intro γ δ h
 ext x
 have hx:=S6 h (e x)
 simpa using hx
@[simp] lemma Ap (B:aj G) (e:G ≃+ H) :
  (B.map e).rank=B.rank:=by
 classical
 rw[rank,rank,map]
 exact Finset.card_image_iff.mpr (vv e).injOn
private lemma se (B:aj G) (e:G ≃+ H)
  (γ:Zg G) :
  (B.map e).width (γ.comp e.symm.toAddMonoidHom)=B.width γ:=by
 change B.width ((γ.comp e.symm.toAddMonoidHom).comp e.toAddMonoidHom)=B.width γ
 apply QA B.width
 ext x
 simp
@[simp] lemma oE [Fintype G] [Fintype H]
  (B:aj G) (e:G ≃+ H) (x:G) :
  e x∈(B.map e).Zc↔x∈B.Zc:=by
 classical
 rw[Zm,Zm]
 constructor
 ·intro hx γ n4
  have CQ:γ.comp e.symm.toAddMonoidHom∈(B.map e).eX:=by
   exact vP B e _ |>.mpr ⟨γ,n4,rfl⟩
  have hh:=hx (γ.comp e.symm.toAddMonoidHom) CQ
  rw[se] at hh
  have Aq:(γ.comp e.symm.toAddMonoidHom) (e x)=γ x:=by simp
  rwa[Aq] at hh
 ·intro hx δ Ca
  rcases (vP B e δ).mp Ca with ⟨γ,n4,rfl⟩
  rw[se]
  have Aq:(γ.comp e.symm.toAddMonoidHom) (e x)=γ x:=by simp
  rw[Aq]
  exact hx γ n4
@[simp] lemma ky [Fintype G] [Fintype H]
  (B:aj G) (e:G ≃+ H) :
  (B.map e).Zc.card=B.Zc.card:=by
 classical
 symm
 apply Finset.card_bijective e e.bijective
 intro x
 exact(oE B e x).symm
noncomputable def eK (N:ℕ) (hN:Odd N):ZMod N ≃+ ZMod N:=by
  let f:ZMod N→+ ZMod N :=
    { toFun:=fun x↦x+x
      map_zero':=by simp
      map_add':=by
        intro x y
        abel }
  have K6:IsUnit (2:ZMod N) :=
    (ZMod.isUnit_iff_coprime 2 N).2 (Nat.coprime_two_left.mpr hN)
  have Ht:Function.Bijective (fun x:ZMod N↦(2:ZMod N)*x) :=
    IsUnit.isUnit_iff_mulLeft_bijective.mp K6
  have M0:Function.Bijective f:=by
    simpa only[f,AddMonoidHom.coe_mk,ZeroHom.coe_mk,R5] using Ht
  exact AddEquiv.ofBijective f M0
@[simp] lemma sS (N:ℕ) (hN:Odd N) (x:ZMod N) :
  eK N hN x=x+x:=by
 simp[eK]
@[simp] lemma tW (N:ℕ) [NeZero N] (hN:Odd N)
  (B:aj (ZMod N)) :
  (B.map (eK N hN)).Zc.card=B.Zc.card :=
 ky B (eK N hN)
end aj
end ay
end
section
open Finset
open scoped NNReal
namespace ay.br
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
structure aY (G:Type*) [AddCommGroup G] [Fintype G]
  [DecidableEq G] where
 ba:aj G
 outer:ℝ≥0
 inner:ℝ≥0
 regular:0< inner∧inner≤outer ∧
  (ba.ai (outer+inner)).Zc.card ≤
   2*(ba.ai (outer-inner)).Zc.card
 set:Finset G
 nonempty:set.Nonempty
 mo:set⊆(ba.ai outer).Zc
namespace aY
def e8 (s:aY G):Finset G :=
 (s.ba.ai s.outer).Zc
def Zd (s:aY G):ℝ :=
 (s.set.card:ℝ)/s.e8.card
def rank (s:aY G):ℕ:=s.ba.rank
def card (s:aY G):ℕ:=s.e8.card
lemma sf (s:aY G):s.e8.Nonempty :=
 (s.ba.ai s.outer).aE
lemma dI (s:aY G):0<s.Zd:=by
 exact Rn (by exact_mod_cast s.nonempty.card_pos)
  (by exact_mod_cast s.sf.card_pos)
lemma Zn (s:aY G):s.Zd≤1:=by
 rw[Zd,Q9 (by exact_mod_cast s.sf.card_pos)]
 exact_mod_cast Qu s.mo
end aY
def dk (q:ℝ) (aq:ℕ) (aU:ℝ)
  (s t:aY G):Prop :=
 q*s.Zd≤t.Zd ∧
  t.rank≤ s.rank+aq ∧
  Real.exp (-aU)*(s.card:ℝ)≤(t.card:ℝ)
inductive et (q:ℝ) (aq:ℕ) (aU:ℝ) :
  ℕ→aY G→aY G→Prop
 | nil (s:aY G):et q aq aU 0 s s
 | cons {n:ℕ} {s t u:aY G}
   (pA:dk q aq aU s t)
   (x5:et q aq aU n t u) :
   et q aq aU (n+1) s u
namespace et
lemma qW {q:ℝ} {aq:ℕ} {aU:ℝ}
  (hq:0≤q) {n:ℕ} {s t:aY G}
  (h:et q aq aU n s t) :
  q^n*s.Zd≤t.Zd:=by
 induction h with
 | nil s=>simp
 | @cons n s t u pA x5 ih =>
   have uP:0≤q^n:=QH hq n
   calc
    q^(n+1)*s.Zd=q^n*(q*s.Zd):=by
     rw[RB]
     ring
    _≤q^n*t.Zd :=
     iO pA.1 uP
    _≤u.Zd:=ih
lemma Zb {q:ℝ} {aq:ℕ} {aU:ℝ}
  {n:ℕ} {s t:aY G}
  (h:et q aq aU n s t) :
  Real.exp (-(n:ℝ)*aU)*(s.card:ℝ)≤(t.card:ℝ):=by
 induction h with
 | nil s=>simp
 | @cons n s t u pA x5 ih =>
   have BE:0≤Real.exp (-(n:ℝ)*aU) :=
    (Q1 _).le
   calc
    Real.exp (-((n+1:ℕ):ℝ)*aU)*(s.card:ℝ) =
      Real.exp (-(n:ℝ)*aU) *
       (Real.exp (-aU)*(s.card:ℝ)):=by
     rw[show-((n+1:ℕ):ℝ)*aU =
       (-(n:ℝ)*aU)+(-aU) by
      push_cast
      ring,
      R7]
     ring
    _≤Real.exp (-(n:ℝ)*aU)*(t.card:ℝ) :=
     iO pA.2.2 BE
    _≤(u.card:ℝ):=ih
end et
def nF (L:ℕ) (Zd:ℝ):Prop :=
 1/(2:ℝ)^L≤Zd
end
end ay.br
end
section
open Finset Function
open scoped BigOperators NNReal
namespace ay
section Moments
variable {X:Type*} [Fintype X] [DecidableEq X]
def iP (ν f:X→ℝ) (k:ℕ):ℝ :=
 ∑ x:X,ν x*f x^k
def aK (ν f:X→ℝ) (k:ℕ):ℝ :=
 ∑ x:X,ν x* |f x| ^k
omit [DecidableEq X] in
lemma dx {ν f:X→ℝ} (f9: ∀ x,0≤ν x) (k:ℕ) :
  0≤aK ν f k:=by
 exact sum_nonneg fun x _↦Qn (f9 x) (QH (Q8 _) _)
noncomputable def cP (ε:ℝ):ℕ :=
 Nat.ceil (60/ε^2)
noncomputable def dJ (ε:ℝ) (p:ℕ):ℕ :=
 2*p*cP ε
lemma ix {ε:ℝ} (hε:0<ε) :
  0<cP ε:=by
 rw[cP,Nat.ceil_pos]
 positivity
lemma sg (ε:ℝ) (p:ℕ) :
  Even (dJ ε p):=by
 refine ⟨p*cP ε, ?_⟩
 simp[dJ,R5,US]
lemma sT {ε:ℝ} {p:ℕ} (hε:0<ε) (hp:p≠0) :
  0<dJ ε p:=by
 simp[dJ,ix hε,Nat.pos_of_ne_zero hp]
lemma qX {ε:ℝ} (_hε:0<ε) :
  60/ε^2≤cP ε:=by
 simpa[cP] using Rr (60/ε^2)
private lemma oF {a b:ℝ} {n:ℕ}
  (ha:0≤a) (hb:0≤b) (hn:1≤n) :
  (a+b)^n≤2^(n-1)*(a^n+b^n):=by
 let a':ℝ≥0:=⟨a,ha⟩
 let b':ℝ≥0:=⟨b,hb⟩
 have h:=NNReal.rpow_add_le_mul_rpow_add_rpow a' b'
  (p:=(n:ℝ)) (by exact_mod_cast hn)
 exact_mod_cast h
omit [DecidableEq X] in
lemma mS
  {ν f:X→ℝ} {ε:ℝ} {p:ℕ}
  (f9: ∀ x,0≤ν x) (n5: ∑ x:X,ν x=1)
  (Ar: ∀ k:ℕ,0≤ iP ν f k)
  (qr:0<ε) (An:ε≤1) (hp:5≤p) (CR:Odd p)
  (iV:ε^p≤aK ν f p) :
  ∃ p':ℕ,0<p'∧Even p'∧p'≤dJ ε p ∧
   (1+ε/2)^p'≤aK ν (f+1) p':=by
 classical
 have x0:p≠0:=Uq (SI (by norm_num) hp)
 have FZ:Even (p-1):=Nat.Odd.sub_odd CR odd_one
 have Eh :
   ε^p≤2* ∑ i:X,ν i*((f^(p-1)) i*(f i)⁺):=by
  calc
   ε^p≤aK ν f p:=iV
   _= ∑ i:X,ν i*((f^(p-1)) i* |f i|):=by
    unfold aK
    apply sum_congr rfl
    intro i _
    congr 1
    change |f i| ^p=f i^(p-1)* |f i|
    rw[←QC (FZ.pow_nonneg (f i)),abs_pow,
     R0 x0]
   _≤ iP ν f p +
     ∑ i:X,ν i*((f^(p-1)) i* |f i|) :=
    le_add_of_nonneg_left (Ar p)
   _= ∑ i:X,ν i*((f^(p-1)) i*(f i+ |f i|)):=by
    simp[iP,Tc,sum_add_distrib,R0 x0]
   _= ∑ i:X,ν i*((f^(p-1)) i*(2•(f i)⁺)):=by
    simp[add_abs_eq_two_nsmul_posPart]
   _=2* ∑ i:X,ν i*((f^(p-1)) i*(f i)⁺):=by
    simp[mul_sum]
    ring_nf
 let P:Finset X:=Finset.univ.filter fun i↦0≤f i
 let T:Finset X:=Finset.univ.filter fun i↦3/4*ε≤f i
 have Oh:T⊆P:=by
  intro i hi
  simp only[P,T,mem_filter,mem_univ,TM] at hi ⊢
  exact Sj (by positivity) hi
 have hP :
   (2:ℝ)⁻¹ *ε^p≤ ∑ i∈P,ν i*(f^p) i:=by
  rw[TA (by norm_num:(0:ℝ)<2),sum_filter]
  simpa[P,Pi.posPart_apply,posPart_eq_ite,R0 x0] using Eh
 have As :
   ∑ i∈P \ T,ν i*(f^p) i≤(4:ℝ)⁻¹ *ε^p:=by
  calc
   _≤ ∑ i∈P \ T,ν i*(3/4*ε)^p:=by
    apply sum_le_sum
    intro i hi
    have G1:=hi
    simp only[mem_sdiff,P,T,mem_filter,mem_univ,TM,not_le] at G1
    exact iO (Qp G1.1 G1.2.le p) (f9 i)
   _=(3/4)^p*ε^p* ∑ i∈P \ T,ν i:=by
    rw[←sum_mul]
    simp[QL]
    ring
   _≤(4:ℝ)⁻¹ *ε^p* ∑ i:X,ν i:=by
    have hpow:(3/4:ℝ)^p≤(4:ℝ)⁻¹ :=by
     calc
      (3/4:ℝ)^p≤(3/4:ℝ)^5:=by
       exact SJ (by norm_num) (by norm_num) hp
      _≤(4:ℝ)⁻¹ :=by norm_num
    calc
     (3/4)^p*ε^p* ∑ i∈P \ T,ν i ≤
       (4:ℝ)⁻¹ *ε^p* ∑ i∈P \ T,ν i :=
      Qi
       (Qi hpow (QH qr.le p))
       (sum_nonneg fun i _↦f9 i)
     _≤(4:ℝ)⁻¹ *ε^p* ∑ i:X,ν i :=
      iO
       (sum_le_univ_sum_of_nonneg fun i↦f9 i)
       (Qn (by norm_num) (QH qr.le p))
   _=(4:ℝ)⁻¹ *ε^p:=by rw[n5,Q3]
 have At :
   (4:ℝ)⁻¹ *ε^p≤ ∑ i∈T,ν i*(f^p) i:=by
  calc
   (4:ℝ)⁻¹ *ε^p =
     (2:ℝ)⁻¹ *ε^p-(4:ℝ)⁻¹ *ε^p:=by ring
   _≤(∑ i∈P,ν i*(f^p) i) -
     ∑ i∈P \ T,ν i*(f^p) i:=sub_le_sub hP As
   _= ∑ i∈T,ν i*(f^p) i:=by
    rw[sum_sdiff_eq_sub Oh]
    ring
 have G3:0≤ ∑ i∈T,ν i*(f^p) i :=
  (Qn (by norm_num) (QH qr.le p)).trans At
 have Oi :
   (∑ i∈T,ν i*(f^p) i)^2 ≤
    (∑ i∈T,ν i)* ∑ i∈T,ν i*(f^(2*p)) i:=by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul T
  ·intro i _
   exact f9 i
  ·intro i _
   exact Qn (f9 i) ((T2 p).pow_nonneg (f i))
  ·intro i _
   dsimp
   rw[show 2*p=p*2 by omega,QU,QL]
   ring_nf
   exact SF
 have Ja :
   ((4:ℝ)⁻¹ *ε^p)^2 ≤
    (∑ i∈T,ν i)*aK ν f (2*p):=by
  calc
   _≤(∑ i∈T,ν i*(f^p) i)^2 :=
    Qp (Qn (by norm_num) (QH qr.le p)) At 2
   _≤(∑ i∈T,ν i)* ∑ i∈T,ν i*(f^(2*p)) i:= Oi
   _≤(∑ i∈T,ν i)*aK ν f (2*p):=by
    apply iO _ (sum_nonneg fun i _↦f9 i)
    unfold aK
    have heq :
      (∑ i∈T,ν i*(f^(2*p)) i) =
       ∑ i∈T,ν i* |f i| ^(2*p):=by
     apply sum_congr rfl
     intro i _
     simp only[Pi.pow_apply]
     rw[(T2 p).pow_abs]
    rw[heq]
    apply sum_le_sum_of_subset_of_nonneg (subset_univ T)
    intro i _ _
    exact Qn (f9 i) (QH (Q8 _) _)
 let q:ℕ:=2*p
 by_cases F0:(2:ℝ)^q≤aK ν (f+1) q
 ·refine ⟨q,by dsimp[q]; omega,T2 p, ?_, ?_⟩
  ·dsimp[q,dJ]
   exact Q4 _ (ix qr)
  ·exact(Qp (by positivity) (by linarith) q).trans F0
 ·have dV:aK ν (f+1) q<(2:ℝ)^q:=QV F0
  have hq:1≤q:=by dsimp[q]; omega
  have Oj:aK ν f q≤(2:ℝ)^(2*q):=by
   calc
    aK ν f q ≤
      (2:ℝ)^(q-1)*(aK ν (f+1) q+1):=by
     unfold aK
     calc
      (∑ x:X,ν x* |f x| ^q) ≤
        ∑ x:X,ν x *
         ((2:ℝ)^(q-1)*(|f x+1| ^q+1^q)):=by
       apply sum_le_sum
       intro i _
       apply iO _ (f9 i)
       calc
        |f i| ^q≤(|f i+1| +1)^q:=by
         apply Qp (Q8 _) _ q
         calc
          |f i| = |(f i+1)-1| :=by ring_nf
          _≤ |f i+1| + |(1:ℝ)| :=abs_sub _ _
          _= |f i+1| +1:=by norm_num
        _≤(2:ℝ)^(q-1)*(|f i+1| ^q+1^q) :=
         oF (Q8 _) (by norm_num) hq
      _=(2:ℝ)^(q-1) *
        (∑ x:X,ν x* |(f+1) x| ^q+1):=by
       simp only[RM,Rt,one_pow]
       calc
        (∑ x:X,ν x*(2^(q-1)*(|f x+1| ^q+1))) =
          2^(q-1)*(∑ x:X,ν x* |f x+1| ^q) +
           2^(q-1)* ∑ x:X,ν x:=by
         simp_rw[Tc]
         rw[sum_add_distrib]
         congr 1
         ·rw[mul_sum]
          apply sum_congr rfl
          intro i _
          ring
         ·rw[mul_sum]
          apply sum_congr rfl
          intro i _
          ring
        _=2^(q-1)*((∑ x:X,ν x* |f x+1| ^q)+1):=by
         rw[n5]
         ring
    _≤(2:ℝ)^(q-1)*((2:ℝ)^q+1):=by
     gcongr
    _≤(2:ℝ)^(q-1)*(2:ℝ)^(q+1):=by
     gcongr
     calc
      (2:ℝ)^q+1≤(2:ℝ)^q+(2:ℝ)^q:=by
       gcongr
       exact RH (by norm_num:(1:ℝ)≤2)
      _=(2:ℝ)^(q+1):=by rw[RB]; ring
    _=(2:ℝ)^(2*q):=by rw[←RL]; congr 1; omega
  have Jb:(ε/8)^(2*p)≤ ∑ i∈T,ν i:=by
   have M1:aK ν f (2*p)≤(2:ℝ)^(4*p):=by
    convert Oj using 1; simp[q]; omega
   have M3 :
     ((4:ℝ)⁻¹ *ε^p)^2 ≤
      (∑ i∈T,ν i)*(2:ℝ)^(4*p) :=
    Ja.trans (iO M1 (sum_nonneg fun i _↦f9 i))
   have sh:(16:ℝ)*(2:ℝ)^(4*p)≤(8:ℝ)^(2*p):=by
    have Ol:(16:ℝ)≤4^p:=by
     calc
      (16:ℝ)=4^2:=by norm_num
      _≤4^p:=Se (by norm_num:(1:ℝ)≤4) (by omega)
    rw[show(2:ℝ)^(4*p)=16^p by rw[QU]; norm_num,
     show(8:ℝ)^(2*p)=64^p by rw[QU]; norm_num]
    calc
     (16:ℝ)*16^p≤4^p*16^p :=
      Qi Ol (QH (by norm_num) p)
     _=64^p:=by rw[←QL]; norm_num
   rw[TY]
   apply(QF (RF (by norm_num:(0:ℝ)<8) (2*p))).2
   have pH:=iO M3 (by norm_num:(0:ℝ)≤16)
   calc
    ε^(2*p)=16*((4:ℝ)⁻¹ *ε^p)^2:=by
     rw[show 2*p=p+p by omega,RL,TI]
     ring
    _≤16*((∑ i∈T,ν i)*(2:ℝ)^(4*p)):=pH
    _=(∑ i∈T,ν i)*(16*(2:ℝ)^(4*p)):=by ring
    _≤(∑ i∈T,ν i)*(8:ℝ)^(2*p) :=
     iO sh (sum_nonneg fun i _↦f9 i)
  let m:ℕ:=cP ε
  have G4:0< m:=ix qr
  have Hu:60/ε^2≤(m:ℝ):=by
   simpa[m] using qX qr
  have eO :
    1+ε/6≤(1+3*ε/4)/(1+ε/2):=by
   apply(Qs (by positivity:0<1+ε/2)).2
   nlinarith
  have x6 :
    8/ε≤((1+3*ε/4)/(1+ε/2))^m:=by
   calc
    8/ε≤1+(m:ℝ)*(ε/6):=by
     have:=Qi Hu (by positivity:0≤ε/6)
     field_simp at this ⊢
     nlinarith[SY qr]
    _≤(1+ε/6)^m:=UM (by linarith) m
    _≤((1+3*ε/4)/(1+ε/2))^m :=
     Qp (by positivity) eO m
  have CS :
    (1+ε/2)^m≤(ε/8)*(1+3*ε/4)^m:=by
   have Hv:0<(1+ε/2)^m:=RF (by positivity) m
   rw[TY] at x6
   have Jc:=(Qs Hv).1 x6
   calc
    (1+ε/2)^m =
      (ε/8)*((8/ε)*(1+ε/2)^m):=by field_simp
    _≤(ε/8)*(1+3*ε/4)^m :=
     iO Jc (by positivity)
  have Au :
    (1+ε/2)^(2*p*m) ≤
     (ε/8)^(2*p)*(1+3*ε/4)^(2*p*m):=by
   calc
    (1+ε/2)^(2*p*m)=((1+ε/2)^m)^(2*p):=by
     rw[←QU,R8 m (2*p)]
    _≤((ε/8)*(1+3*ε/4)^m)^(2*p) :=
     Qp (by positivity) CS (2*p)
    _=(ε/8)^(2*p)*(1+3*ε/4)^(2*p*m):=by
     rw[QL, ←QU,R8 m (2*p)]
  have mq:Even (2*p*m):=by
   simp[SZ]
  refine ⟨2*p*m,by positivity,mq, ?_, ?_⟩
  ·simp[dJ,m]
  ·calc
    (1+ε/2)^(2*p*m) ≤
      (ε/8)^(2*p)*(1+3*ε/4)^(2*p*m):=Au
    _≤(∑ i∈T,ν i)*(1+3*ε/4)^(2*p*m) :=
     Qi Jb (QH (by positivity) _)
    _= ∑ i∈T,ν i*(1+3*ε/4)^(2*p*m):=by
     rw[←sum_mul]
    _≤ ∑ i∈T,ν i* |(f+1) i| ^(2*p*m):=by
     apply sum_le_sum
     intro i hi
     apply iO _ (f9 i)
     apply Qp (by positivity) _ _
     have G1:3/4*ε≤f i:=by simpa[T] using hi
     have Jd:0≤(f+1) i:=by
      simp only[RM,Rt]
      nlinarith
     rw[QC Jd]
     simp only[RM,Rt]
     nlinarith
    _≤aK ν (f+1) (2*p*m):=by
     unfold aK
     apply sum_le_sum_of_subset_of_nonneg (subset_univ T)
     intro i _ _
     exact Qn (f9 i) (QH (Q8 _) _)
end Moments
section vw
open Fintype MeasureTheory RCLike Real
open scoped ComplexConjugate ComplexOrder ENNReal
variable {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
 [MeasurableSpace G] [DiscreteMeasurableSpace G]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma ry {ν:G→ℝ≥0} {f:G→ℝ} {g h:G→ℂ}
  (hf:(al g g)=(↑) ∘ f) (f9:(al h h)=(↑) ∘ ν) (k:ℕ) :
  (0:ℝ)≤⟪(↑) ∘ ν,f^k⟫_[ℝ] :=
 xl hf f9 k
end vw
end ay
end
section
open Finset
open scoped BigOperators
namespace ay
namespace an
variable {X:Type*} [Fintype X] [DecidableEq X]
structure cw (ν:X→ℝ):Prop where
 nonneg: ∀ x,0≤ν x
 sum_eq_one: ∑ x,ν x=1
noncomputable def aM (ν f:X→ℝ) (p:ℕ):ℝ :=
 if p=0 then 0 else
  (aK ν f p)^(1/(p:ℝ))
omit [DecidableEq X] in
lemma dG (ν f:X→ℝ) {p:ℕ} (hp:0<p) :
  aM ν f p =
   (aK ν f p)^(1/(p:ℝ)):=by
 simp[aM,hp.ne']
omit [DecidableEq X] in
lemma j1 {ν:X→ℝ} (f9:cw ν)
  (f:X→ℝ) (p:ℕ) :
  0≤aM ν f p:=by
 classical
 unfold aM
 split
 ·exact SF
 ·exact Tn (dx f9.nonneg p) _
omit [DecidableEq X] in
lemma jr {ν f:X→ℝ} (f9:cw ν)
  {p:ℕ} (hp:0<p) :
  aM ν f p^p=aK ν f p:=by
 classical
 rw[dG _ _ hp, ←RN,
  ←S0 (dx f9.nonneg p)]
 have Ei:(p:ℝ)≠0:=by exact_mod_cast hp.ne'
 field_simp
 simp
private lemma xm {x:ℝ} {p q:ℕ} (hp:0<p) :
  (|x| ^p)^((q:ℝ)/(p:ℝ))= |x| ^q:=by
 rw[←RN]
 rw[←S0 (Q8 x)]
 rw[←RN]
 congr 1
 have Ei:(p:ℝ)≠0:=by exact_mod_cast hp.ne'
 field_simp
omit [DecidableEq X] in
lemma gG
  {ν f:X→ℝ} (f9:cw ν)
  {p q:ℕ} (hp:0<p) (hpq:p≤q) :
  aM ν f p≤aM ν f q:=by
 classical
 have hq:0<q:=hp.trans_le hpq
 have Ei:(0:ℝ)<p:=by exact_mod_cast hp
 have Je:(0:ℝ)<q:=by exact_mod_cast hq
 have M4:(p:ℝ)≤q:=by exact_mod_cast hpq
 have eO:(1:ℝ)≤(q:ℝ)/(p:ℝ):=by
  exact(Qs Ei).2 (by simpa using M4)
 have Av:0≤aK ν f p :=
  dx f9.nonneg p
 have M5:0≤aK ν f q :=
  dx f9.nonneg q
 have Hw :
   (aK ν f p)^((q:ℝ)/(p:ℝ)) ≤
    aK ν f q:=by
  have h:=Real.rpow_arith_mean_le_arith_mean_rpow
   (Finset.univ:Finset X) ν (fun x↦ |f x| ^p)
   (fun x _↦f9.nonneg x) (by simpa using f9.sum_eq_one)
   (fun x _↦QH (Q8 _) _) eO
  simpa only[aK,mem_univ,xm hp] using h
 rw[dG _ _ hp,dG _ _ hq]
 have kz :
   0≤(aK ν f p)^((q:ℝ)/(p:ℝ)) :=
  Tn Av _
 have wG:=Sf kz Hw
  (RS Us Je.le)
 calc
  (aK ν f p)^(1/(p:ℝ)) =
    ((aK ν f p)^((q:ℝ)/(p:ℝ))) ^
     (1/(q:ℝ)):=by
   rw[←S0 Av]
   congr 1
   field_simp
  _≤(aK ν f q)^(1/(q:ℝ)):=wG
omit [DecidableEq X] in
lemma lq
  {μ ν f g:X→ℝ} (Jf:cw μ) (f9:cw ν)
  {p:ℕ} (hp:0<p)
  (yU:aK μ f p≤2*aK ν g p) :
  aM μ f p≤2*aM ν g p:=by
 classical
 have Ei:(0:ℝ)<p:=by exact_mod_cast hp
 have ha:0≤(1/(p:ℝ)):=by positivity
 have K7:(1/(p:ℝ))≤1:=by
  rw[Q9 Ei]
  exact_mod_cast hp
 have Ej:0≤aK μ f p :=
  dx Jf.nonneg p
 have zi:0≤aK ν g p :=
  dx f9.nonneg p
 rw[dG _ _ hp,dG _ _ hp]
 calc
  (aK μ f p)^(1/(p:ℝ)) ≤
    (2*aK ν g p)^(1/(p:ℝ)) :=
   Sf Ej yU ha
  _=(2:ℝ)^(1/(p:ℝ)) *
    (aK ν g p)^(1/(p:ℝ)):=by
   rw[Real.mul_rpow (by norm_num:(0:ℝ)≤2) zi]
  _≤2*(aK ν g p)^(1/(p:ℝ)):=by
   apply Qi _ (Tn zi _)
   simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num:(1:ℝ)≤2) K7
def bS (p:ℕ):ℕ:=2*p
lemma sU (p:ℕ):Even (bS p):=by
 exact ⟨p,by simp[bS,R5]⟩
lemma tX {p:ℕ} (hp:0<p) :
  p≤bS p:=by
 simp only[bS]
 omega
def cF (p:ℕ):ℕ :=
 2*bS p+3
lemma pL (p:ℕ) :
  Odd (cF p):=by
 simp[cF,bS,Nat.odd_iff]
lemma fK {p:ℕ} (hp:0<p) :
  5≤cF p:=by
 simp only[cF,bS]
 omega
lemma je (p:ℕ) :
  bS p≤cF p:=by
 simp only[cF]
 omega
omit [DecidableEq X] in
lemma js
  {ν f:X→ℝ} (f9:cw ν) {p:ℕ} (hp:0<p) :
  aM ν f (bS p) ≤
   aM ν f (cF p):=by
 classical
 apply gG f9
 ·exact QP (by norm_num) hp
 ·exact je p
noncomputable def cz (ε:ℝ) (p:ℕ):ℕ :=
 dJ (ε/2) (cF p)
lemma tY (ε:ℝ) (p:ℕ) :
  Even (cz ε p):=by
 exact sg _ _
lemma uQ {ε:ℝ} {p:ℕ}
  (hε:0<ε) (hp:0<p) :
  0<cz ε p:=by
 apply sT (p:=cF p)
 ·positivity
 ·have Pq:=fK hp
  omega
lemma pB (ε:ℝ) (p:ℕ) :
  cz ε p =
   (8*p+6)*cP (ε/2):=by
 unfold cz dJ cF
  bS
 ring
lemma pj {ε:ℝ} {p:ℕ} (hp:0<p) :
  cz ε p ≤
   14*cP (ε/2)*p:=by
 rw[pB]
 have Cc:8*p+6≤14*p:=by omega
 have h:=QQ (cP (ε/2)) Cc
 simpa[Qo,Qx,Q6] using h
omit [DecidableEq X] in
lemma pM
  {ν:X→ℝ} (f9:cw ν)
  {f fB:X→ℝ} {η bo:ℝ}
  (Jg:0<η) (Jh:η≤1) (fF:0<bo)
  {p:ℕ} (hp:5≤p) (CR:Odd p)
  (Ar: ∀ k:ℕ,0≤ iP ν f k)
  (iV:η^p≤aK ν f p)
  (c3: ∀ x,fB x=bo*(1+f x)) :
  ∃ r:ℕ,0<r∧Even r∧r≤dJ η p ∧
   (1+η/2)*bo≤aM ν fB r:=by
 classical
 obtain ⟨r,hr,Aw,yV,tq⟩ :=
  mS f9.nonneg f9.sum_eq_one Ar
   Jg Jh hp CR iV
 refine ⟨r,hr,Aw,yV, ?_⟩
 have Ax :
   aK ν fB r =
    bo^r*aK ν (f+1) r:=by
  unfold aK
  rw[Qj]
  apply sum_congr rfl
  intro x _
  rw[c3 x,SU,RT fF,QL]
  simp only[RM,Rt]
  ring_nf
 have Au :
   ((1+η/2)*bo)^r ≤
    aK ν fB r:=by
  rw[Ax,QL]
  simpa[Qx] using
   (Qi tq (QH fF.le r))
 rw[dG _ _ hr]
 have dc:0≤(1+η/2)*bo:=by positivity
 have wG:=Sf (QH dc r) Au
  (by positivity:0≤(r:ℝ)⁻¹)
 rw[Sc dc hr.ne'] at wG
 simpa[R6] using wG
omit [DecidableEq X] in
lemma nK
  {μ ν:X→ℝ} (Jf:cw μ) (f9:cw ν)
  {balanced gH fB:X→ℝ}
  {ε bo:ℝ} (hε:0<ε) (fF:0<bo)
  {p:ℕ} (hp:0<p)
  (ld :
   aM μ balanced (bS p) ≤
    2*aM ν gH (bS p))
  (CT :
   ε*bo/2<aM ν gH (bS p) →
    ∃ r:ℕ,0<r∧r≤cz ε p ∧
     (1+ε/8)*bo≤aM ν fB r)
  (qs :
   aM ν fB (cz ε p) <
    (1+ε/8)*bo) :
  aM μ balanced p≤ε*bo:=by
 classical
 have Hx:0<ε*bo:=QM hε fF
 by_contra hbound
 have K8:ε*bo<aM μ balanced p:=QV hbound
 have xo :
   aM μ balanced p ≤
    aM μ balanced (bS p) :=
  gG Jf hp (tX hp)
 have CV :
   ε*bo/2<aM ν gH (bS p):=by
  nlinarith[Hx,K8.trans_le xo,ld,
   j1 f9 gH (bS p)]
 obtain ⟨r,hr,Ji,tq⟩:=CT CV
 have xp :
   aM ν fB r ≤
    aM ν fB (cz ε p) :=
  gG f9 hr Ji
 exact(Rd (tq.trans xp)) qs
end an
end ay
end
section
open Finset Function
open scoped BigOperators translate
namespace ay
noncomputable section
section BF
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def af (A:Finset G) (x:G):ℝ :=
 if x∈A then (#A:ℝ)⁻¹ else 0
def ao (f g:G→ℝ) (x:G):ℝ :=
 ∑ y:G,f y*g (x-y)
def aZ (f g:G→ℝ) (x:G):ℝ :=
 ∑ y:G,f y*g (y-x)
def qh (f g:G→ℝ):ℝ :=
 ∑ x:G,f x*g x
omit [AddCommGroup G] [Fintype G] in
@[simp] lemma dj {A:Finset G} {x:G} (hx:x∈A) :
  af A x=(#A:ℝ)⁻¹ :=by
 simp[af,hx]
omit [AddCommGroup G] [Fintype G] in
@[simp] lemma dO {A:Finset G} {x:G} (hx:x∉A) :
  af A x=0:=by
 simp[af,hx]
omit [AddCommGroup G] [Fintype G] in
lemma bO (A:Finset G) (x:G) :
  0≤af A x:=by
 unfold af
 split_ifs
 ·exact inv_nonneg.mpr (Q5 _)
 ·exact SF
omit [AddCommGroup G] [Fintype G] in
lemma qt {A:Finset G} (hA:A.Nonempty) (x:G) :
  0<af A x↔x∈A:=by
 unfold af
 split_ifs with hx
 ·simp only[hx,iff_true]
  exact inv_pos.mpr (Nat.cast_pos.mpr hA.card_pos)
 ·simp[hx]
omit [AddCommGroup G] [Fintype G] in
lemma d6 {A:Finset G} (hA:A.Nonempty) (x:G) :
  af A x≠0↔x∈A:=by
 unfold af
 split_ifs with hx
 ·simp[hx,hA.card_ne_zero]
 ·simp[hx]
omit [AddCommGroup G] in
lemma cf {A:Finset G} (hA:A.Nonempty) :
  ∑ x:G,af A x=1:=by
 change(∑ x∈(univ:Finset G),if x∈A then (#A:ℝ)⁻¹ else 0)=1
 rw[←QE]
 have eI:univ.filter (fun x:G↦x∈A)=A:=by ext; simp
 rw[eI]
 simp[hA.card_ne_zero]
omit [DecidableEq G] in
lemma e9 {f g:G→ℝ}
  (hf: ∀ x,0≤f x) (hg: ∀ x,0≤g x) (z:G) :
  0≤ao f g z:=by
 exact sum_nonneg fun x _↦Qn (hf x) (hg (z-x))
omit [DecidableEq G] in
lemma gB {f g:G→ℝ}
  (hf: ∀ x,0≤f x) (hg: ∀ x,0≤g x) (z:G) :
  0≤aZ f g z:=by
 exact sum_nonneg fun x _↦Qn (hf x) (hg (x-z))
lemma kA (A B:Finset G) (x:G) :
  ao (af A) (af B) x =
   (#(A.filter fun y↦x-y∈B):ℝ)*(#A:ℝ)⁻¹ *(#B:ℝ)⁻¹ :=by
 have eI:(univ.filter fun y:G↦x-y∈B)∩A =
   A.filter fun y↦x-y∈B:=by
  ext y
  simp[and_comm]
 simp[ao,af, ←QE,
  Qo,Q6,eI]
omit [Fintype G] in
lemma lQ (A B:Finset G) (x:G) :
  #(A.filter fun y↦x-y∈B)=A.addConvolution B x:=by
 unfold Finset.addConvolution
 refine Finset.card_nbij' (fun y↦(y,x-y)) (fun ab↦ab.1) ?_ ?_ ?_ ?_
 ·intro y hy
  change y∈A.filter (fun y↦x-y∈B) at hy
  change(y,x-y)∈(A ×ˢ B).filter (fun ab↦ab.1+ab.2=x)
  rw[mem_filter] at hy ⊢
  exact ⟨mem_product.mpr hy,by simp⟩
 ·rintro ⟨a,b⟩ hab
  change(a,b)∈(A ×ˢ B).filter (fun ab↦ab.1+ab.2=x) at hab
  change a∈A.filter (fun y↦x-y∈B)
  simp only[mem_filter,mem_product] at hab ⊢
  rcases hab with ⟨⟨ha,hb⟩,hsum⟩
  refine ⟨ha, ?_⟩
  have Ek:x-a=b:=by
   rw[←hsum]
   simp
  simpa[Ek] using hb
 ·intro y _
  rfl
 ·rintro ⟨a,b⟩ hab
  change(a,b)∈(A ×ˢ B).filter (fun ab↦ab.1+ab.2=x) at hab
  simp only[mem_filter,mem_product] at hab
  rcases hab with ⟨-,hsum⟩
  have Ek:x-a=b:=by
   rw[←hsum]
   simp
  simp[Ek]
lemma iy (A B:Finset G) (x:G) :
  ao (af A) (af B) x =
   (A.addConvolution B x:ℝ)*(#A:ℝ)⁻¹ *(#B:ℝ)⁻¹ :=by
 rw[kA,lQ]
end BF
section Algebra
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
omit [DecidableEq G] in
lemma fG (f g:G→ℝ) :
  ao f g=ao g f:=by
 funext x
 rw[ao,ao]
 refine Qk (Equiv.subLeft x) _ _ fun y↦ ?_
 simp[Qx]
omit [DecidableEq G] in
lemma iz (f g:G→ℝ) :
  ∑ x:G,ao f g x=(∑ x:G,f x)* ∑ x:G,g x:=by
 simp_rw[ao,Qt]
 rw[QD]
 apply Io rfl
 intro y _
 rw[←Qj]
 congr 1
 exact Qk (Equiv.subRight y) _ _ fun x↦by simp
omit [DecidableEq G] in
lemma hH (f g:G→ℝ) :
  ∑ x:G,aZ f g x =
   (∑ x:G,f x)* ∑ x:G,g x:=by
 simp_rw[aZ,Qt]
 rw[QD]
 apply Io rfl
 intro y _
 rw[←Qj]
 congr 1
 exact Qk (Equiv.subLeft y) _ _ fun x↦by simp
end Algebra
section CW
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def df (A C:Finset G):ℕ :=
 #(((A ×ˢ A) ×ˢ C).filter fun x↦x.1.1+x.1.2=x.2+x.2)
omit [Fintype G] in
lemma kX (A C:Finset G) :
  df A C= ∑ c∈C,A.addConvolution A (c+c):=by
 unfold df Finset.addConvolution
 simp only[Finset.card_eq_sum_ones,QE,Finset.sum_product]
 calc
  (∑ a∈A, ∑ b∈A, ∑ c∈C,if a+b=c+c then 1 else 0) =
    ∑ a∈A, ∑ c∈C, ∑ b∈A,if a+b=c+c then 1 else 0:=by
   apply Io rfl
   intro a _
   rw[QD]
  _= ∑ c∈C, ∑ a∈A, ∑ b∈A,if a+b=c+c then 1 else 0:=by
   rw[QD]
lemma jJ {A C:Finset G}
  (eU:Function.Injective (fun x:G↦x+x)) :
  qh (ao (af A) (af A))
    (af (C.image fun x↦x+x)) =
   (df A C:ℝ)*(#A:ℝ)⁻¹ ^2*(#C:ℝ)⁻¹ :=by
 let D:Finset G:=C.image fun x↦x+x
 have Jj: #D= #C:=by
  dsimp[D]
  exact card_image_of_injective _ eU
 have vQ (F:G→ℝ) :
   (∑ z:G,F z*af D z) =
    ∑ z∈D,F z*(#D:ℝ)⁻¹ :=by
  change(∑ z:G,F z*(if z∈D then (#D:ℝ)⁻¹ else 0))=_
  simp only[Td,mul_zero]
  rw[←QE]
  have eI:univ.filter (fun z:G↦z∈D)=D:=by ext; simp
  rw[eI]
 have yW: ∑ z∈D,A.addConvolution A z=df A C:=by
  rw[kX]
  dsimp[D]
  rw[Finset.sum_image]
  intro a _ b _ hab
  exact eU hab
 have F1: ∑ z∈D,(A.addConvolution A z:ℝ)=(df A C:ℝ):=by
  exact_mod_cast yW
 rw[qh,vQ]
 simp_rw[iy]
 rw[Jj]
 have gX (z:G) :
   ((A.addConvolution A z:ℝ)*(#A:ℝ)⁻¹ *(#A:ℝ)⁻¹)*(#C:ℝ)⁻¹ =
    (A.addConvolution A z:ℝ) *
     ((#A:ℝ)⁻¹ *(#A:ℝ)⁻¹ *(#C:ℝ)⁻¹):=by ac_rfl
 simp_rw[gX]
 rw[←Qt,F1]
 simp only[TI]
 ac_rfl
omit [Fintype G] in
lemma iA {A A' C:Finset G} (t:G)
  (hA: ∀ x∈A',x-t∈A) (hC: ∀ x∈C,x-t∈A) :
  df A' C≤dL A:=by
 unfold df dL
 let f:((G × G) × G)→((G × G) × G):=fun x ↦
  ((x.1.1-t,x.2-t),x.1.2-t)
 apply Finset.card_le_card_of_injOn f
 ·rintro ⟨⟨a,c⟩,b⟩ pG
  change((a,c),b)∈(((A' ×ˢ A') ×ˢ C).filter fun x ↦
   x.1.1+x.1.2=x.2+x.2) at pG
  change((a-t,b-t),c-t)∈(((A ×ˢ A) ×ˢ A).filter fun x ↦
   x.1.1+x.2=x.1.2+x.1.2)
  simp only[mem_filter,mem_product] at pG ⊢
  rcases pG with ⟨⟨⟨ha,hc⟩,hb⟩,uI⟩
  refine ⟨⟨⟨hA a ha,hC b hb⟩,hA c hc⟩, ?_⟩
  calc
   (a-t)+(c-t)=(a+c)-(t+t):=by
    simp only[Qy,neg_add_rev]
    ac_rfl
   _=(b+b)-(t+t):=QA (fun x↦x-(t+t)) uI
   _=(b-t)+(b-t):=by
    simp only[Qy,neg_add_rev]
    ac_rfl
 ·rintro ⟨⟨a,c⟩,b⟩ _ ⟨⟨a',c'⟩,b'⟩ _ heq
  have K9:a-t=a'-t:=QA (fun x↦x.1.1) heq
  have La:b-t=b'-t:=QA (fun x↦x.1.2) heq
  have Lb:c-t=c'-t:=QA (fun x↦x.2) heq
  have ha:a=a':=calc
   a=(a-t)+t:=(Rs a t).symm
   _=(a'-t)+t:=QA (fun x↦x+t) K9
   _=a':=Rs a' t
  have hb:b=b':=calc
   b=(b-t)+t:=(Rs b t).symm
   _=(b'-t)+t:=QA (fun x↦x+t) La
   _=b':=Rs b' t
  have hc:c=c':=calc
   c=(c-t)+t:=(Rs c t).symm
   _=(c'-t)+t:=QA (fun x↦x+t) Lb
   _=c':=Rs c' t
  simp[ha,hb,hc]
end CW
end
end ay
end
section
open Finset
open scoped BigOperators NNReal symmDiff
namespace ay
namespace aj
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def vR (B:aj G) (a8 eta:ℝ≥0):Prop :=
 0<eta ∧
  ∀ aF:ℝ≥0,aF≤eta →
   (B.ai (a8-aF)).Zc=(B.ai a8).Zc ∧
   (B.ai (a8+aF)).Zc=(B.ai a8).Zc
def pC (B:aj G) (a8 eta:ℝ≥0):Prop :=
 0<eta∧eta≤a8 ∧
  (B.ai (a8+eta)).Zc.card ≤
   2*(B.ai (a8-eta)).Zc.card
def a1 (B:aj G):Prop :=
 let d:ℕ:=max B.rank 1
 ∀ aF:ℝ≥0,
  aF≤1/(100*(d:ℝ≥0)) →
   (1-100*(d:ℝ)*(aF:ℝ))*(B.Zc.card:ℝ) ≤
     ((B.ai (1-aF)).Zc.card:ℝ) ∧
   ((B.ai (1+aF)).Zc.card:ℝ) ≤
     (1+100*(d:ℝ)*(aF:ℝ))*(B.Zc.card:ℝ)
omit [DecidableEq G] in
lemma si (B:aj G) (a8:ℝ≥0) :
  (B.ai a8).a1 ↔
   let d:ℕ:=max B.rank 1
   ∀ aF:ℝ≥0,
    aF≤1/(100*(d:ℝ≥0)) →
     (1-100*(d:ℝ)*(aF:ℝ)) *
        ((B.ai a8).Zc.card:ℝ) ≤
       ((B.ai ((1-aF)*a8)).Zc.card:ℝ) ∧
     ((B.ai ((1+aF)*a8)).Zc.card:ℝ) ≤
       (1+100*(d:ℝ)*(aF:ℝ)) *
        ((B.ai a8).Zc.card:ℝ):=by
 simp[a1,Qx]
noncomputable def fp (A:Finset G) (t:G):Finset G :=
 A.map (Equiv.addRight t).toEmbedding
omit [DecidableEq G] [Fintype G] in
@[simp] lemma lr {A:Finset G} {t x:G} :
  x∈fp A t↔x-t∈A:=by
 simp[fp,Qy]
lemma kY
  {B:aj G} {a8 eta:ℝ≥0} (fC:eta≤a8) {t:G}
  (ht:t∈(B.ai eta).Zc) :
  (fp (B.ai a8).Zc t) ∆ (B.ai a8).Zc ⊆
   (B.ai (a8+eta)).Zc \ (B.ai (a8-eta)).Zc:=by
 intro x hx
 rw[UF] at hx
 rw[Finset.mem_sdiff]
 constructor
 ·rcases hx with hx | hx
  ·rw[lr] at hx
   have Ay:=e7 hx.1 ht
   simpa using Ay
  ·exact b5 (Ss (by positivity)) hx.1
 ·intro oG
  have zM:x∈(B.ai a8).Zc:=by
   exact b5 (T4) oG
  have Jk:x-t∈(B.ai a8).Zc:=by
   have eY: -t∈(B.ai eta).Zc:=ec.mpr ht
   have xq:=e7 oG eY
   simpa[Qy,tsub_add_cancel_of_le fC] using xq
  have xr:x∈fp (B.ai a8).Zc t:=by
   rwa[lr]
  rcases hx with hx | hx
  ·exact hx.2 zM
  ·exact hx.2 xr
lemma kB
  {B:aj G} {a8 eta:ℝ≥0} (fC:eta≤a8) {t:G}
  (ht:t∈(B.ai eta).Zc) :
  ((fp (B.ai a8).Zc t) ∆
    (B.ai a8).Zc).card ≤
   (B.ai (a8+eta)).Zc.card -
    (B.ai (a8-eta)).Zc.card:=by
 have sj :
   (B.ai (a8-eta)).Zc ⊆
    (B.ai (a8+eta)).Zc :=
  b5 ((T4).trans (Ss (by positivity)))
 calc
  ((fp (B.ai a8).Zc t) ∆
    (B.ai a8).Zc).card ≤
    ((B.ai (a8+eta)).Zc \
     (B.ai (a8-eta)).Zc).card :=
   Qu (kY fC ht)
  _=(B.ai (a8+eta)).Zc.card -
    (B.ai (a8-eta)).Zc.card :=
   Finset.card_sdiff_of_subset sj
lemma gY
  (A:Finset G) (t:G) :
  ∑ x:G, |af A (x-t)-af A x| =
   (((fp A t) ∆ A).card:ℝ)/(A.card:ℝ):=by
 have gX (x:G) :
   |af A (x-t)-af A x| =
    if x∈(fp A t) ∆ A then (A.card:ℝ)⁻¹ else 0:=by
  by_cases Ay:x-t∈A<;>by_cases hx:x∈A <;>
   simp[af,UF,lr,
    Ay,hx,QC]
 simp_rw[gX]
 rw[←QE]
 simp[Qw]
lemma jf
  {B:aj G} {a8 eta:ℝ≥0} (fC:eta≤a8) {t:G}
  (ht:t∈(B.ai eta).Zc) :
  ∑ x:G,
    |af (B.ai a8).Zc (x-t) -
     af (B.ai a8).Zc x| ≤
   (((B.ai (a8+eta)).Zc.card -
    (B.ai (a8-eta)).Zc.card:ℕ):ℝ) /
     ((B.ai a8).Zc.card:ℝ):=by
 rw[gY]
 rw[Qw,Qw]
 gcongr
 exact_mod_cast kB fC ht
lemma cN
  {B:aj G} (dF:B.a1) {aF:ℝ≥0}
  (dy:aF≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  {t:G} (ht:t∈(B.ai aF).Zc) :
  ∑ x:G,
    |af B.Zc (x-t) -
     af B.Zc x| ≤
   200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ):=by
 let d:ℕ:=max B.rank 1
 have hd:0<d:=by simp[d]
 have Cd:aF≤1/(100*(d:ℝ≥0)):=by
  simpa[d] using dy
 have oH:aF≤1:=by
  apply Cd.trans
  rw[Q9]
  ·exact_mod_cast(show 1≤100*d by omega)
  ·positivity
 have El :=
  jf
   (B:=B) (a8:=(1:ℝ≥0)) (eta:=aF) oH ht
 simp only[oD] at El
 simp only[a1] at dF
 have jt:=dF aF (by simpa[d] using Cd)
 have sj :
   (B.ai (1-aF)).Zc.card ≤
    (B.ai (1+aF)).Zc.card :=
  Qu
   (b5
    (tsub_le_self.trans (Ss (show 0≤aF by exact bot_le))))
 have BG:(0:ℝ)<B.Zc.card:=by
  exact_mod_cast B.aE.card_pos
 apply El.trans
 rw[Nat.cast_sub sj]
 rw[QF BG]
 nlinarith[jt.1,jt.2]
end aj
end ay
end
section
open Finset
open scoped BigOperators NNReal
namespace ay
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
lemma g7
  {B:aj G} (dF:B.a1) {κ:ℝ≥0}
  (qu:κ≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  (ν:G→ℝ) (kq: ∀ t,0≤ν t)
  (pN: ∀ t,ν t≠0→t∈(B.ai κ).Zc) :
  ∑ x:G,
    |ao (af B.Zc) ν x -
     (∑ t:G,ν t)*af B.Zc x| ≤
   200*((max B.rank 1:ℕ):ℝ)*(κ:ℝ)* ∑ t:G,ν t:=by
 let E:ℝ:=200*((max B.rank 1:ℕ):ℝ)*(κ:ℝ)
 have gX (x:G) :
   |ao (af B.Zc) ν x -
     (∑ t:G,ν t)*af B.Zc x| ≤
    ∑ t:G,ν t *
     |af B.Zc (x-t)-af B.Zc x| :=by
  rw[fG]
  simp only[ao]
  rw[Qt, ←QJ]
  simp_rw[←UY]
  calc
   |∑ t:G,ν t *
     (af B.Zc (x-t)-af B.Zc x)| ≤
     ∑ t:G, |ν t *
      (af B.Zc (x-t)-af B.Zc x)| :=
    abs_sum_le_sum_abs _ _
   _= ∑ t:G,ν t *
     |af B.Zc (x-t)-af B.Zc x| :=by
    apply Io rfl
    intro t _
    rw[SU,QC (kq t)]
 calc
  ∑ x:G,
    |ao (af B.Zc) ν x -
     (∑ t:G,ν t)*af B.Zc x| ≤
    ∑ x:G, ∑ t:G,ν t *
     |af B.Zc (x-t)-af B.Zc x| :=by
   exact QI fun x _↦gX x
  _= ∑ t:G,ν t* ∑ x:G,
     |af B.Zc (x-t)-af B.Zc x| :=by
   rw[QD]
   apply Io rfl
   intro t _
   rw[Qj]
  _≤ ∑ t:G,ν t*E:=by
   apply QI
   intro t _
   by_cases ht:ν t=0
   ·simp[ht]
   ·exact iO
     (aj.cN
      dF qu (pN t ht)) (kq t)
  _=(∑ t:G,ν t)*E:=by rw[Qt]
  _=E* ∑ t:G,ν t:=by ring
  _=200*((max B.rank 1:ℕ):ℝ)*(κ:ℝ)* ∑ t:G,ν t:=rfl
lemma f4
  {B:aj G} {a8 eta:ℝ≥0}
  (dF:B.pC a8 eta)
  (ν:G→ℝ)
  (kq: ∀ t,0≤ν t)
  (n5: ∑ t:G,ν t=1)
  (pN: ∀ t,ν t≠0→t∈(B.ai eta).Zc)
  (x:G) :
  af (B.ai a8).Zc x ≤
   2*ao
    (af (B.ai (a8+eta)).Zc) ν x:=by
 let Jl:=(B.ai (a8-eta)).Zc
 let K:=(B.ai a8).Zc
 let mr:=(B.ai (a8+eta)).Zc
 have oG:Jl.card≤K.card:=by
  apply Qu
  exact aj.b5 (T4:a8-eta≤a8)
 have ch:mr.card≤2*K.card :=
  dF.2.2.trans (Qr 2 oG)
 have x7:(0:ℝ)<K.card:=by
  exact_mod_cast(B.ai a8).aE.card_pos
 have Em:(0:ℝ)< mr.card:=by
  exact_mod_cast(B.ai (a8+eta)).aE.card_pos
 have x8 (hx:x∈K) :
   ao (af mr) ν x =
    (mr.card:ℝ)⁻¹ :=by
  rw[fG]
  simp only[ao]
  calc
   ∑ t:G,ν t*af mr (x-t) =
     ∑ t:G,ν t*(mr.card:ℝ)⁻¹ :=by
    apply Io rfl
    intro t _
    by_cases ht:ν t=0
    ·simp[ht]
    ·have Ay:x-t∈mr :=
      aj.j0 hx (pN t ht)
     rw[dj Ay]
   _=(∑ t:G,ν t)*(mr.card:ℝ)⁻¹ :=by
    rw[Qt]
   _=(mr.card:ℝ)⁻¹ :=by rw[n5,QT]
 by_cases hx:x∈K
 ·rw[show(B.ai a8).Zc=K by rfl,
   dj hx,x8 hx]
  calc
   (K.card:ℝ)⁻¹ =1/(K.card:ℝ):=by rw[R6]
   _≤2/(mr.card:ℝ):=by
    rw[Sy x7 Em]
    simpa only[QT] using(show(mr.card:ℝ)≤2*K.card by
     exact_mod_cast ch)
   _=2*(mr.card:ℝ)⁻¹ :=by rw[Qw]
 ·rw[show(B.ai a8).Zc=K by rfl,
   dO hx]
  exact Qn (by norm_num)
   (e9
    (bO mr) kq x)
lemma gC
  {B:aj G} (dF:B.a1) {κ:ℝ≥0} (Jm:0<κ)
  (qu:κ≤1/(400*(max B.rank 1:ℕ):ℝ≥0))
  (ν:G→ℝ) (kq: ∀ t,0≤ν t)
  (n5: ∑ t:G,ν t=1)
  (pN: ∀ t,ν t≠0→t∈(B.ai κ).Zc)
  (x:G) :
  af B.Zc x ≤
   2*ao
    (af (B.ai (1+κ)).Zc) ν x:=by
 let d:ℕ:=max B.rank 1
 have hd:0<d:=by simp[d]
 have Jn:κ≤1/(400*(d:ℝ≥0)):=by simpa[d] using qu
 have En:κ≤1/(100*(d:ℝ≥0)):=by
  apply Jn.trans
  apply Rb (by positivity) (by positivity)
  exact Qi (by norm_num:(100:ℝ≥0)≤400) (by positivity)
 have Jo:κ≤1:=by
  apply En.trans
  rw[Q9]
  ·exact_mod_cast(show 1≤100*d by omega)
  ·positivity
 have jt:=dF κ (by simpa[d] using En)
 have Az:(100:ℝ)*d*(κ:ℝ)≤1/4:=by
  have NI:(κ:ℝ)≤1/(400*(d:ℝ)):=by
   exact_mod_cast Jn
  have Om:(0:ℝ)<d:=by exact_mod_cast hd
  calc
   (100:ℝ)*d*(κ:ℝ)≤100*d*(1/(400*(d:ℝ))):=by gcongr
   _=1/4:=by field_simp; ring
 have Eo :
   ((B.ai (1+κ)).Zc.card:ℝ) ≤
    2*((B.ai (1-κ)).Zc.card:ℝ):=by
  nlinarith[jt.1,jt.2,
   show(0:ℝ)<B.Zc.card by exact_mod_cast B.aE.card_pos]
 have ch :
   (B.ai (1+κ)).Zc.card ≤
    2*(B.ai (1-κ)).Zc.card:=by
  exact_mod_cast Eo
 have Hy:B.pC 1 κ:=⟨Jm,Jo,ch⟩
 simpa only[aj.oD] using
  f4
   Hy ν kq n5 pN x
def bs (A:Finset G) (x:G):ℝ :=
 if x∈A then 1 else 0
omit [AddCommGroup G] [Fintype G] in
@[simp] lemma rA {A:Finset G} {x:G} (hx:x∈A) :
  bs A x=1:=by simp[bs,hx]
def cp (A K:Finset G):ℝ :=
 (A.card:ℝ)/K.card
def a9 (A C:Finset G) (x:G):ℝ :=
 ao (bs A) (af C) x
omit [AddCommGroup G] in
lemma jU
  {A K:Finset G} (lL:A⊆K) (_hK:K.Nonempty) :
  ∑ x:G,bs A x*af K x =
   cp A K:=by
 have hsum :
   ∑ x∈A,bs A x*af K x =
    ∑ x:G,bs A x*af K x:=by
  apply Ro (S7 A)
  intro x _ Ep
  simp[bs,Ep]
 rw[←hsum]
 calc
  ∑ x∈A,bs A x*af K x =
    ∑ _x∈A,(K.card:ℝ)⁻¹ :=by
   apply Io rfl
   intro x hx
   rw[rA hx,
    dj (lL hx),QT]
  _=cp A K:=by
   simp[cp,Qw]
lemma dP
  {B:aj G} (dF:B.a1) {κ:ℝ≥0}
  (qu:κ≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  {A C:Finset G} (lL:A⊆B.Zc) (hC:C.Nonempty)
  (fN:C⊆(B.ai κ).Zc) :
  |(∑ x:G,af B.Zc x*a9 A C x) -
    cp A B.Zc| ≤
   200*((max B.rank 1:ℕ):ℝ)*(κ:ℝ):=by
 let ν:G→ℝ:=fun t↦af C (-t)
 have kq: ∀ t,0≤ν t:=fun t↦bO C (-t)
 have n5: ∑ t:G,ν t=1:=by
  calc
   ∑ t:G,ν t= ∑ t:G,af C t:=by
    exact Qk (Equiv.neg G) _ _ (fun _↦rfl)
   _=1:=cf hC
 have pN: ∀ t,ν t≠0→t∈(B.ai κ).Zc:=by
  intro t ht
  have eY: -t∈C:=(d6 hC (-t)).mp ht
  exact aj.ec.mp (fN eY)
 have x8 :
   ∑ y:G,
     |ao (af B.Zc) ν y -
      af B.Zc y| ≤
    200*((max B.rank 1:ℕ):ℝ)*(κ:ℝ):=by
  simpa[n5] using
   g7
    dF qu ν kq pN
 have AA :
   ∑ x:G,af B.Zc x*a9 A C x =
    ∑ y:G,bs A y *
     ao (af B.Zc) ν y:=by
  simp only[a9,ao,Qj]
  rw[QD]
  apply Io rfl
  intro y _
  apply Io rfl
  intro x _
  dsimp[ν]
  rw[neg_sub]
  ring
 have dc :
   ∑ y:G,bs A y*af B.Zc y =
    cp A B.Zc :=
  jU lL B.aE
 rw[AA, ←dc, ←QJ]
 simp_rw[←UY]
 calc
  |∑ y:G,bs A y *
    (ao (af B.Zc) ν y -
     af B.Zc y)| ≤
    ∑ y:G, |bs A y *
     (ao (af B.Zc) ν y -
      af B.Zc y)| :=abs_sum_le_sum_abs _ _
  _≤ ∑ y:G,
    |ao (af B.Zc) ν y -
     af B.Zc y| :=by
   apply QI
   intro y _
   by_cases hy:y∈A<;>simp[bs,hy]
  _≤200*((max B.rank 1:ℕ):ℝ)*(κ:ℝ):=x8
lemma ki
  {B:aj G} (dF:B.a1) {κ:ℝ≥0}
  (qu:κ≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  {A pO qY:Finset G}
  (hA:A.Nonempty) (lL:A⊆B.Zc)
  (Lc:pO.Nonempty) (Ld:qY.Nonempty)
  (CX:pO⊆(B.ai κ).Zc)
  (CY:qY⊆(B.ai κ).Zc)
  {ε:ℝ} (_hε:0<ε)
  (dV :
   400*((max B.rank 1:ℕ):ℝ)*(κ:ℝ) ≤
    ε*cp A B.Zc/4) :
  (∃ x∈B.Zc,
    (1-ε)*cp A B.Zc≤a9 A pO x ∧
    (1-ε)*cp A B.Zc≤a9 A qY x) ∨
   (∃ x:G,
    (1+ε/2)*cp A B.Zc≤a9 A pO x) ∨
   (∃ x:G,
    (1+ε/2)*cp A B.Zc≤a9 A qY x):=by
 let K:=B.Zc
 let α:ℝ:=cp A K
 let E:ℝ:=200*((max B.rank 1:ℕ):ℝ)*(κ:ℝ)
 let yX:ℝ:= ∑ x:G,af K x*a9 A pO x
 let yY:ℝ:= ∑ x:G,af K x*a9 A qY x
 have hK:K.Nonempty:=B.aE
 have PU:0<α:=by
  dsimp[α,K,cp]
  exact Rn (by exact_mod_cast hA.card_pos) (by exact_mod_cast hK.card_pos)
 have Hz: |yX-α| ≤E:=by
  simpa[yX,α,E,K] using
   dP
    dF qu lL Lc CX
 have HA: |yY-α| ≤E:=by
  simpa[yY,α,E,K] using
   dP
    dF qu lL Ld CY
 have z0:α-E≤yX:=by
  have:=(abs_le.mp Hz).1
  linarith
 have Pr:α-E≤yY:=by
  have:=(abs_le.mp HA).1
  linarith
 have NJ:2*E≤ε*α/4:=by
  calc
   2*E=400*((max B.rank 1:ℕ):ℝ)*(κ:ℝ):=by
    dsimp[E]
    ring
   _≤ε*cp A B.Zc/4:=dV
   _=ε*α/4:=by rfl
 by_cases rB :
   ∃ x∈K,
    (1-ε)*α≤a9 A pO x ∧
    (1-ε)*α≤a9 A qY x
 ·exact Or.inl rB
 by_cases Ce: ∃ x:G,(1+ε/2)*α≤a9 A pO x
 ·exact Or.inr (Or.inl Ce)
 by_cases Cf: ∃ x:G,(1+ε/2)*α≤a9 A qY x
 ·exact Or.inr (Or.inr Cf)
 exfalso
 let T:ℝ:=2*α-ε*α/2
 have gX: ∀ x∈K,
   a9 A pO x+a9 A qY x<T:=by
  intro x hx
  have Ps:a9 A pO x<(1+ε/2)*α :=
   QV (fun h↦Ce ⟨x,h⟩)
  have Pt:a9 A qY x<(1+ε/2)*α :=
   QV (fun h↦Cf ⟨x,h⟩)
  have As :
    a9 A pO x<(1-ε)*α ∨
     a9 A qY x<(1-ε)*α:=by
   by_cases h₁:(1-ε)*α≤a9 A pO x
   ·right
    exact QV (fun h₂↦rB ⟨x,hx,h₁,h₂⟩)
   ·left
    exact QV h₁
  rcases As with NK | NL
  ·dsimp[T]
   nlinarith
  ·dsimp[T]
   nlinarith
 have qv :
   ∑ x:G,af K x *
     (a9 A pO x+a9 A qY x) <
    ∑ x:G,af K x*T:=by
  apply Finset.sum_lt_sum
  ·intro x _
   by_cases hx:x∈K
   ·exact iO (gX x hx).le
     (bO K x)
   ·simp[dO hx]
  ·refine ⟨0,Sz 0, ?_⟩
   have hz:0∈K:=B.sb
   exact T6 (gX 0 hz)
    ((qt hK 0).2 hz)
 have CZ:yX+yY<T:=by
  calc
   yX+yY= ∑ x:G,af K x *
     (a9 A pO x+a9 A qY x):=by
    dsimp[yX,yY]
    rw[←T7]
    apply Io rfl
    intro x _
    ring
   _< ∑ x:G,af K x*T:=qv
   _=(∑ x:G,af K x)*T:=by rw[Qt]
   _=T:=by rw[cf hK,QT]
 dsimp[T] at CZ
 nlinarith
end
end ay
end
section
open Finset Function Real
open Complex (re)
open scoped BigOperators ComplexConjugate
namespace ay
namespace c5
variable {G:Type*} [Fintype G] [AddCommGroup G]
noncomputable def c6 (A:Finset G) (psi:AddChar G ℂ):ℂ :=
 ∑ x∈A,psi x
noncomputable def cj (A:Finset G) (eta:ℝ):Finset (AddChar G ℂ) :=
 Finset.univ.filter fun psi↦eta*A.card≤ ‖c6 A psi‖
@[simp] lemma gm {A:Finset G} {eta:ℝ} {psi:AddChar G ℂ} :
  psi∈cj A eta↔eta*A.card≤ ‖c6 A psi‖ :=by
 simp[cj]
end c5
end ay
end
section
open Finset
open scoped BigOperators NNReal
namespace ay
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def dd (f:G→ℝ):ℕ→G→ℝ
 | 0=>af {0}
 | n+1=>ao (dd f n) f
@[simp] lemma Cg (f:G→ℝ) :
  dd f 0=af {0}:=rfl
@[simp] lemma j2 (f:G→ℝ) (n:ℕ) :
  dd f (n+1) =
   ao (dd f n) f:=rfl
lemma sV {f:G→ℝ} (hf: ∀ x,0≤f x) :
  ∀ n x,0≤dd f n x:=by
 intro n
 induction n with
 | zero =>
   exact bO {0}
 | succ n AD =>
   exact e9 AD hf
lemma oI {f:G→ℝ} (hf: ∑ x:G,f x=1) :
  ∀ n, ∑ x:G,dd f n x=1:=by
 intro n
 induction n with
 | zero =>
   exact cf (singleton_nonempty 0)
 | succ n AD =>
   rw[j2,iz,AD,hf,QT]
lemma jK
  (B:aj G) (σ:ℝ≥0) :
  ∀ n x,dd (af (B.ai σ).Zc) n x≠0 →
   x∈(B.ai ((n:ℝ≥0)*σ)).Zc:=by
 intro n
 induction n with
 | zero =>
   intro x hx
   have PV:x=0:=by
    simpa using
     (d6 (singleton_nonempty 0) x).mp hx
   subst x
   simp
 | succ n AD =>
   intro x hx
   rw[j2,ao] at hx
   obtain ⟨y, -,hy⟩:=Finset.exists_ne_zero_of_sum_ne_zero hx
   have Lf:dd (af (B.ai σ).Zc) n y≠0 :=
    (mul_ne_zero_iff.mp hy).1
   have HB:af (B.ai σ).Zc (x-y)≠0 :=
    (mul_ne_zero_iff.mp hy).2
   have Jp:=AD y Lf
   have F2:x-y∈(B.ai σ).Zc :=
    (d6
     (B.ai σ).aE (x-y)).mp HB
   have xq:=aj.e7 Jp F2
   have Lg:y+(x-y)=x:=by simp
   rw[Lg] at xq
   simpa[T3,Nat.cast_one,US] using xq
def cG (w:G→ℝ) (ψ:AddChar G ℂ):ℂ :=
 ∑ x:G,(w x:ℂ)*ψ x
lemma jT (A:Finset G) (ψ:AddChar G ℂ) :
  cG (af A) ψ =
   ((A.card:ℝ)⁻¹ :ℂ)*c5.c6 A ψ:=by
 calc
  cG (af A) ψ =
    ∑ x∈A,((A.card:ℝ)⁻¹ :ℂ)*ψ x:=by
   rw[cG, ←Ro (s₁:=A) (s₂:=Finset.univ)]
   ·apply Io rfl
    intro x hx
    simp[af,hx]
   ·simp
   ·intro x MC Ep
    simp[af,Ep]
  _=((A.card:ℝ)⁻¹ :ℂ)*c5.c6 A ψ:=by
   rw[c5.c6,Qj]
lemma fy
  (C:aj G) (ψ:AddChar G ℂ)
  (Jq:ψ∉c5.cj C.Zc (1/2)) :
  ‖cG (af C.Zc) ψ‖ <1/2:=by
 have ch:(0:ℝ)<C.Zc.card:=by
  exact_mod_cast C.aE.card_pos
 have Er :
   ‖c5.c6 C.Zc ψ‖ <(1/2:ℝ)*C.Zc.card:=by
  apply QV
  intro h
  exact Jq (c5.gm.mpr h)
 calc
  ‖cG (af C.Zc) ψ‖ =
    (C.Zc.card:ℝ)⁻¹ * ‖c5.c6 C.Zc ψ‖ :=by
   rw[jT,QO]
   simp[Up]
  _<(C.Zc.card:ℝ)⁻¹ *
    ((1/2:ℝ)*C.Zc.card) :=
   T6 Er (inv_pos.mpr ch)
  _=1/2:=by field_simp
omit [DecidableEq G] in
lemma jb (f g:G→ℝ) (ψ:AddChar G ℂ) :
  cG (ao f g) ψ=cG f ψ*cG g ψ:=by
 unfold cG ao
 push_cast
 calc
  ∑ x:G,(∑ y:G,(f y:ℂ)*(g (x-y):ℂ))*ψ x =
    ∑ x:G, ∑ y:G,(f y:ℂ)*(g (x-y):ℂ)*ψ x:=by
   apply Io rfl
   intro x hx
   rw[Qt]
  _= ∑ y:G, ∑ x:G,(f y:ℂ)*(g (x-y):ℂ)*ψ x :=
   QD
  _ =
    ∑ y:G,((f y:ℂ)*ψ y) *
     ∑ z:G,(g z:ℂ)*ψ z:=by
   apply Io rfl
   intro y hy
   rw[Qj]
   refine Qk (Equiv.subRight y) _ _ fun z↦ ?_
   have Jq:ψ z=ψ y*ψ (z-y):=by
    calc
     ψ z=ψ (y+(z-y)):=QA ψ (by simp)
     _=ψ y*ψ (z-y):=St ψ y (z-y)
   simp only[Ut]
   rw[Jq]
   ring
  _=(∑ y:G,(f y:ℂ)*ψ y) *
    ∑ z:G,(g z:ℂ)*ψ z:=by
   simpa using
    (Qt (univ:Finset G) (fun y↦(f y:ℂ)*ψ y)
     (∑ z:G,(g z:ℂ)*ψ z)).symm
lemma qZ (f:G→ℝ) (ψ:AddChar G ℂ) :
  ∀ n,cG (dd f n) ψ=cG f ψ^n:=by
 intro n
 induction n with
 | zero =>
   unfold cG
   rw[Fintype.sum_eq_single 0]
   ·simp[af]
   ·intro y hy
    simp[af,hy]
 | succ n AD =>
   rw[j2,jb,AD,RB]
omit [DecidableEq G] in
lemma tZ {w:G→ℝ} (hw: ∀ x,0≤w x)
  (ψ:AddChar G ℂ) :
  ‖cG w ψ‖ ≤ ∑ x:G,w x:=by
 unfold cG
 calc
  ‖∑ x:G,(w x:ℂ)*ψ x‖ ≤
    ∑ x:G, ‖(w x:ℂ)*ψ x‖ :=Rq _ _
  _= ∑ x:G,w x:=by
   apply Io rfl
   intro x hx
   simp[hw x]
def ed (B:aj G) (σ:ℝ≥0) (n:ℕ):G→ℝ :=
 ao
  (af (B.ai (1+(n:ℝ≥0)*σ)).Zc)
  (dd (af (B.ai σ).Zc) n)
lemma qw (B:aj G) (σ:ℝ≥0) (n:ℕ) (x:G) :
  0≤ed B σ n x:=by
 exact e9
  (bO _)
  (sV (bO _) n) x
lemma sm (B:aj G) (σ:ℝ≥0) (n:ℕ) :
  ∑ x:G,ed B σ n x=1:=by
 rw[ed,iz,
  cf (B.ai (1+(n:ℝ≥0)*σ)).aE,
  oI
   (cf (B.ai σ).aE),QT]
lemma nc
  (B:aj G) (σ:ℝ≥0) (n:ℕ) {x:G} (hx:x∈B.Zc) :
  ed B σ n x =
   (((B.ai (1+(n:ℝ≥0)*σ)).Zc.card:ℝ)⁻¹):=by
 rw[ed,fG]
 simp only[ao]
 calc
  ∑ t:G,dd (af (B.ai σ).Zc) n t *
     af (B.ai (1+(n:ℝ≥0)*σ)).Zc (x-t) =
    ∑ t:G,dd (af (B.ai σ).Zc) n t *
     (((B.ai (1+(n:ℝ≥0)*σ)).Zc.card:ℝ)⁻¹):=by
   apply Io rfl
   intro t ht
   by_cases Jr :
     dd (af (B.ai σ).Zc) n t=0
   ·simp[Jr]
   ·have On:t∈(B.ai ((n:ℝ≥0)*σ)).Zc :=
     jK B σ n t Jr
    have Ay:x-t ∈
      (B.ai (1+(n:ℝ≥0)*σ)).Zc:=by
     exact aj.j0
      (B:=B) (s:=1) (t:=(n:ℝ≥0)*σ)
      (by simpa using hx) On
    rw[dj Ay]
  _=(∑ t:G,
     dd (af (B.ai σ).Zc) n t) *
    (((B.ai (1+(n:ℝ≥0)*σ)).Zc.card:ℝ)⁻¹):=by
   rw[Qt]
  _=(((B.ai (1+(n:ℝ≥0)*σ)).Zc.card:ℝ)⁻¹):=by
   rw[oI
    (cf (B.ai σ).aE)]
   simp
omit [DecidableEq G] in
lemma oJ
  {B:aj G} (dF:B.a1) {σ:ℝ≥0} (n:ℕ)
  (dV:(n:ℝ≥0)*σ ≤
   1/(100*(max B.rank 1:ℕ):ℝ≥0)) :
  (B.ai (1+(n:ℝ≥0)*σ)).Zc.card ≤
   2*B.Zc.card:=by
 let κ:ℝ≥0:=(n:ℝ≥0)*σ
 let d:ℕ:=max B.rank 1
 have jt:=dF κ (by simpa[κ,d] using dV)
 have n6:(1+100*(d:ℝ)*(κ:ℝ))≤2:=by
  have NM:(κ:ℝ)≤1/(100*(d:ℝ)):=by
   exact_mod_cast(show κ≤1/(100*(d:ℝ≥0)) by
    simpa[κ,d] using dV)
  have hd:(0:ℝ)<d:=by exact_mod_cast(show 0<d by simp[d])
  calc
   1+100*(d:ℝ)*(κ:ℝ) ≤
     1+100*(d:ℝ)*(1/(100*(d:ℝ))):=by gcongr
   _=2:=by field_simp; ring
 have Js :
   ((B.ai (1+κ)).Zc.card:ℝ) ≤
    2*(B.Zc.card:ℝ):=by
  calc
   ((B.ai (1+κ)).Zc.card:ℝ) ≤
     (1+100*(d:ℝ)*(κ:ℝ))*(B.Zc.card:ℝ):=by
    simpa[κ,d] using jt.2
   _≤2*(B.Zc.card:ℝ):=by gcongr
 exact_mod_cast Js
lemma lu
  (B:aj G) (σ:ℝ≥0) (n:ℕ) (ψ:AddChar G ℂ) :
  ‖cG (ed B σ n) ψ‖ ≤
   ‖cG (af (B.ai σ).Zc) ψ‖ ^n:=by
 rw[ed,jb,
  qZ,QO,norm_pow]
 have ju :
   ‖cG (af
    (B.ai (1+(n:ℝ≥0)*σ)).Zc) ψ‖ ≤1:=by
  simpa[cf
   (B.ai (1+(n:ℝ≥0)*σ)).aE] using
   tZ
    (w:=af
     (B.ai (1+(n:ℝ≥0)*σ)).Zc)
    (bO _) ψ
 exact RQ (by positivity) ju
end
end ay
end
section
open Finset
open scoped BigOperators NNReal
namespace ay
noncomputable section
namespace aj
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def cx (z:AddCircle (1:ℝ)):ℝ :=
 (QuotientAddGroup.equivIcoMod (p:=(1:ℝ)) (by norm_num) (-1/2) z).1
lemma kZ (z:AddCircle (1:ℝ)) :
  cx z∈Set.Ico (-1/2:ℝ) (1/2):=by
 let e:=QuotientAddGroup.equivIcoMod (p:=(1:ℝ)) (by norm_num) (-1/2)
 change-1/2≤cx z∧cx z<1/2
 constructor
 ·exact(e z).2.1
 ·have hz:=(e z).2.2
  norm_num at hz ⊢
  exact hz
@[simp] lemma zN (z:AddCircle (1:ℝ)) :
  ((cx z:ℝ):AddCircle (1:ℝ))=z:=by
 let e:=QuotientAddGroup.equivIcoMod (p:=(1:ℝ)) (by norm_num) (-1/2)
 have h:=e.symm_apply_apply z
 change((cx z:ℝ):AddCircle (1:ℝ))=z
 simpa only[e,cx,QuotientAddGroup.equivIcoMod_symm_apply] using h
lemma t3 (z:AddCircle (1:ℝ)): |cx z| ≤1/2:=by
 have hz:=kZ z
 rw[Set.mem_Ico] at hz
 rw[abs_le]
 constructor<;>linarith
lemma hJ (z:AddCircle (1:ℝ)): ‖z‖ = |cx z| :=by
 calc
  ‖z‖ = ‖((cx z:ℝ):AddCircle (1:ℝ))‖ :=by rw[zN]
  _= |cx z| :=
   (Ts (1:ℝ) (by norm_num)).2
    (by simpa using t3 z)
lemma gu (z w:AddCircle (1:ℝ)) :
  ‖z-w‖ ≤ |cx z-cx w| :=by
 have ts :
   (((cx z-cx w:ℝ):ℝ):AddCircle (1:ℝ))=z-w:=by
  simp
 rw[←ts]
 simpa only[QK] using
  (QuotientAddGroup.norm_mk_le_norm
   (S:=AddSubgroup.zmultiples (1:ℝ)) :
    ‖((cx z-cx w:ℝ):AddCircle (1:ℝ))‖ ≤
     ‖cx z-cx w‖)
def uR (w r:ℝ):Fin 4 :=
 if r< -(w/2) then 0
 else if r<0 then 1
 else if r<w/2 then 2
 else 3
lemma oK {w r s:ℝ}
  (_hw:0≤w) (hr: |r| ≤w) (hs: |s| ≤w)
  (lM:uR w r=uR w s) :
  |r-s| ≤w/2:=by
 rw[abs_le] at hr hs ⊢
 unfold uR at lM
 split_ifs at lM
 all_goals try { omega }
 all_goals constructor<;>linarith
def gr (B:aj G) (x:↥(B.ai 1).Zc) :
  B.eX→Fin 4 :=
 fun γ↦uR (B.width γ.1:ℝ) (cx (γ.1 x.1))
omit [DecidableEq G] in
private lemma nL (B:aj G)
  {x y:↥(B.ai 1).Zc}
  (nd:B.gr x=B.gr y) :
  x.1-y.1∈(B.ai (1/2)).Zc:=by
 rw[Zm]
 intro γ n4
 have hx:=(Zm (B.ai 1) x.1).mp x.2 γ n4
 have hy:=(Zm (B.ai 1) y.1).mp y.2 γ n4
 simp only[oC,QT,SK] at hx hy ⊢
 rw[map_sub]
 have C2: |cx (γ x.1)| ≤(B.width γ:ℝ):=by
  rwa[←hJ]
 have C3: |cx (γ y.1)| ≤(B.width γ:ℝ):=by
  rwa[←hJ]
 have vS:=Uu nd ⟨γ,n4⟩
 calc
  ‖γ x.1-γ y.1‖ ≤ |cx (γ x.1)-cx (γ y.1)| :=
   gu _ _
  _≤(B.width γ:ℝ)/2 :=
   oK (by positivity) C2 C3 vS
  _=((1/2:NNReal):ℝ)*(B.width γ:ℝ):=by
   norm_num
   ring
omit [DecidableEq G] in
private lemma qx (B:aj G)
  (a:B.eX→Fin 4) :
  Fintype.card {x:↥(B.ai 1).Zc// B.gr x=a} ≤
   (B.ai (1/2)).Zc.card:=by
 classical
 by_cases jv:Nonempty
   {x:↥(B.ai 1).Zc// B.gr x=a}
 ·let x₀:{x:↥(B.ai 1).Zc// B.gr x=a} :=
   Classical.choice jv
  let f:{x:↥(B.ai 1).Zc// B.gr x=a} →
    ↥(B.ai (1/2)).Zc :=
   fun x↦⟨x.1.1-x₀.1.1,nL B
    (x.2.trans x₀.2.symm)⟩
  have hf:Function.Injective f:=by
   intro x y nd
   apply RI
   apply RI
   have q0:=congr_arg (fun z↦z.1) nd
   dsimp[f] at q0
   exact S8 q0
  calc
   Fintype.card {x:↥(B.ai 1).Zc// B.gr x=a} ≤
     Fintype.card ↥(B.ai (1/2)).Zc :=
    R1 f hf
   _=(B.ai (1/2)).Zc.card:=Rx _
 ·simp only[To] at jv
  simp
omit [DecidableEq G] in
lemma de (B:aj G) :
  (B.ai 1).Zc.card ≤
   4^B.rank*(B.ai (1/2)).Zc.card:=by
 classical
 let S:=B.eX→Fin 4
 let q:↥(B.ai 1).Zc→ S:=B.gr
 have jv: ∀ a:S,
   Fintype.card {x:↥(B.ai 1).Zc// q x=a} ≤
    (B.ai (1/2)).Zc.card:=by
  intro a
  exact qx B a
 have AF:Fintype.card S=4^B.rank:=by
  dsimp[S,rank]
  rw[TC]
  simp
 rw[←Rx (B.ai 1).Zc, ←AF]
 by_contra h
 have xP :
   Fintype.card S*(B.ai (1/2)).Zc.card <
    Fintype.card ↥(B.ai 1).Zc:=by omega
 obtain ⟨a,ha⟩:=Rk (f:=q) xP
 have Es: #{x | q x=a}≤(B.ai (1/2)).Zc.card:=by
  rw[←SL]
  exact jv a
 exact(Rd Es) ha
omit [DecidableEq G] in
lemma iW (B:aj G) :
  (B.ai 2).Zc.card ≤
   4^(3*B.rank)*(B.ai (1/4)).Zc.card:=by
 classical
 have h₂:=de (B.ai 2)
 have h₁:=de B
 have iB:=de (B.ai (1/2))
 simp only[f6,vl] at h₂ iB
 norm_num at h₂ iB
 calc
  (B.ai 2).Zc.card≤4^B.rank*B.Zc.card:=h₂
  _≤4^B.rank*(4^B.rank*(B.ai (1/2)).Zc.card):=by
   gcongr
   simpa using h₁
  _≤4^B.rank *
    (4^B.rank*(4^B.rank*(B.ai (1/4)).Zc.card)):=by
   gcongr
  _=4^(3*B.rank)*(B.ai (1/4)).Zc.card:=by
   rw[←Qo, ←RL, ←Qo, ←RL]
   congr 2
   omega
private lemma nM
  (f:ℝ→ℝ) (hf:Monotone f)
  (rT:f (5/4)-f (1/4)<5) :
  ∃ x∈Set.Icc (1/2:ℝ) 1,
   ∀ y∈Set.Icc (1/4:ℝ) (5/4),
    |f y-f x| ≤60* |y-x| :=by
 classical
 by_contra! xt
 let zj:Set (ℝ × ℝ):={p |
  1/4≤p.1∧p.1<p.2∧p.2≤5/4 ∧
   60*(p.2-p.1)<f p.2-f p.1}
 let center:(ℝ × ℝ)→ℝ:=fun p↦(p.1+p.2)/2
 let radius:(ℝ × ℝ)→ℝ:=fun p↦(p.2-p.1)/2
 have tu {p:ℝ × ℝ} (hp:p∈zj):0<radius p:=by
  dsimp[zj] at hp
  dsimp[radius]
  linarith
 have C4 (p:ℝ × ℝ) (hp:p∈zj):radius p≤1/2:=by
  dsimp[zj] at hp
  dsimp[radius]
  linarith
 obtain ⟨u,x9,C5,HC⟩ :=
  Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
   zj center radius (1/2) C4 5 (by norm_num)
 have zO:Set.Icc (1/2:ℝ) 1 ⊆
   ⋃ b:↥u,Metric.ball (center b.1) (6*radius b.1):=by
  intro x hx
  obtain ⟨y,G5,nd⟩:=xt x hx
  let p:ℝ × ℝ:=(min x y,max x y)
  have Lh:p∈zj:=by
   dsimp[zj,p]
   have G6:x∈Set.Icc (1/4:ℝ) (5/4):=by
    constructor<;>linarith[hx.1,hx.2]
   rcases le_total x y with hle | hle
   ·simp only[min_eq_left hle,max_eq_right hle]
    have xu: |f y-f x| =f y-f x :=
     QC (sub_nonneg.mpr (hf hle))
    have C6: |y-x| =y-x:=QC (sub_nonneg.mpr hle)
    rw[xu,C6] at nd
    exact ⟨G6.1,QV (fun heq↦by
     have:y=x:=SC heq hle
     subst y
     norm_num at nd),G5.2,nd⟩
   ·simp only[min_eq_right hle,max_eq_left hle]
    have xu: |f y-f x| =f x-f y:=by
     rw[Su]
     exact QC (sub_nonneg.mpr (hf hle))
    have C6: |y-x| =x-y:=by
     rw[Su]
     exact QC (sub_nonneg.mpr hle)
    rw[xu,C6] at nd
    exact ⟨G5.1,QV (fun heq↦by
     have:x=y:=SC heq hle
     subst y
     norm_num at nd),G6.2,nd⟩
  obtain ⟨b,MD,l0⟩:=HC p Lh
  have Oo:x∈Metric.closedBall (center p) (radius p):=by
   rw[T8]
   dsimp[center,radius,p]
   constructor<;>rcases le_total x y with hle | hle <;>
    simp[hle]<;>linarith
  have Ek:x∈Metric.closedBall (center b) (5*radius b):=l0 Oo
  rw[Metric.mem_closedBall] at Ek
  rw[Set.mem_iUnion]
  refine ⟨⟨b,MD⟩, ?_⟩
  rw[Metric.mem_ball]
  have PW:0<radius b:=tu (x9 MD)
  linarith
 obtain ⟨v,Ch⟩:=isCompact_Icc.elim_finite_subcover
  (fun b:↥u↦Metric.ball (center b.1) (6*radius b.1))
  (fun _↦Metric.isOpen_ball) zO
 have BH:v.Nonempty:=by
  by_contra hv
  rw[Finset.not_nonempty_iff_eq_empty] at hv
  simpa[hv] using Ch (show(1/2:ℝ)∈Set.Icc (1/2) 1 by norm_num)
 have NN:(1/2:ℝ)≤6* ∑ b∈v,(b.1.2-b.1.1):=by
  have hm:MeasureTheory.volume (Set.Icc (1/2:ℝ) 1) ≤
    MeasureTheory.volume (⋃ b∈v,
     Metric.ball (center b.1) (6*radius b.1)) :=
   MeasureTheory.measure_mono Ch
  have oL:0≤6* ∑ b∈v,(b.1.2-b.1.1):=by
   apply Qn (by norm_num)
   apply UZ
   intro b hb
   have:=tu (x9 b.2)
   dsimp[radius] at this
   linarith
  rw[←ENNReal.ofReal_le_ofReal_iff oL]
  have iB:ENNReal.ofReal (1/2:ℝ) =
    MeasureTheory.volume (Set.Icc (1/2:ℝ) 1):=by
   rw[Real.volume_Icc]
   norm_num
  rw[iB]
  calc
   MeasureTheory.volume (Set.Icc (1/2:ℝ) 1) ≤
     MeasureTheory.volume (⋃ b∈v,
      Metric.ball (center b.1) (6*radius b.1)):=hm
   _≤ ∑ b∈v,MeasureTheory.volume
     (Metric.ball (center b.1) (6*radius b.1)) :=
    MeasureTheory.measure_biUnion_finset_le v _
   _=ENNReal.ofReal (6* ∑ b∈v,(b.1.2-b.1.1)):=by
    simp only[Real.volume_ball]
    rw[←ENNReal.ofReal_sum_of_nonneg]
    ·congr 1
     simp only[radius]
     calc
      ∑ b∈v,2*(6*((b.1.2-b.1.1)/2)) =
        ∑ b∈v,6*(b.1.2-b.1.1):=by
       apply Io rfl
       intro b hb
       ring
      _=6* ∑ b∈v,(b.1.2-b.1.1):=by
       rw[Qj]
    ·intro b hb
     have:=tu (x9 b.2)
     dsimp[radius] at this
     positivity
   _=ENNReal.ofReal (6* ∑ b∈v,(b.1.2-b.1.1)):=rfl
 let e:↥u ↪ (ℝ × ℝ):=⟨Subtype.val,Subtype.val_injective⟩
 let F:Finset (ℝ × ℝ):=v.map e
 have G7 (p:ℝ × ℝ) :
   Metric.closedBall (center p) (radius p)=Set.Icc p.1 p.2:=by
  rw[T8]
  dsimp[center,radius]
  congr<;>ring
 have Et: ∀ ⦃z⦄,z∈F →
   (1/4:ℝ)≤z.1∧z.1≤z.2∧z.2≤5/4:=by
  intro z hz
  obtain ⟨b,hb,rfl⟩:=Finset.mem_map.mp hz
  have ow:=x9 b.2
  dsimp[zj] at ow
  exact ⟨ow.1,ow.2.1.le,ow.2.2.1⟩
 have BI:(SetLike.coe F).PairwiseDisjoint
   (fun z↦Set.Icc z.1 z.2):=by
  intro z hz w hw Oq
  obtain ⟨bz,PX,rfl⟩:=Finset.mem_map.mp hz
  obtain ⟨bw,PY,rfl⟩:=Finset.mem_map.mp hw
  have vE:(bz:ℝ × ℝ)≠bw:=by
   simpa[e] using Oq
  have hd:=C5 bz.2 bw.2 vE
  change Disjoint (Metric.closedBall (center bz) (radius bz))
   (Metric.closedBall (center bw) (radius bw)) at hd
  rw[G7,G7] at hd
  simpa[e] using hd
 have NO: ∑ z∈F,(f z.2-f z.1)≤f (5/4)-f (1/4):=by
  have M6:=F.sum_intervalGapsWithin_add_sum_eq_sub rfl
   (a:=(1/4:ℝ)) (b:=(5/4:ℝ)) f
  calc
   ∑ z∈F,(f z.2-f z.1)≤_:=by
    rw[le_add_iff_nonneg_left]
    apply UZ
    intro i hi
    apply sub_nonneg.mpr
    apply hf
    exact F.intervalGapsWithin_fst_le_snd rfl _ (by norm_num)
     Et BI
   _=f (5/4)-f (1/4):=M6
 have M7:60* ∑ b∈v,(b.1.2-b.1.1) <
   ∑ z∈F,(f z.2-f z.1):=by
  rw[Finset.sum_map]
  simp only[e,Function.Embedding.coeFn_mk]
  rw[Qj]
  exact Tt BH
   (fun b hb↦(x9 b.2).2.2.2)
 linarith
omit [DecidableEq G] in
private lemma nN (B:aj G) :
  Real.log ((B.ai (5/4)).Zc.card:ℝ) -
    Real.log ((B.ai (1/4)).Zc.card:ℝ) <
   5*(max B.rank 1:ℕ):=by
 classical
 let d:ℕ:=max B.rank 1
 have ch:(B.ai (5/4)).Zc.card ≤
   4^(3*B.rank)*(B.ai (1/4)).Zc.card:=by
  calc
   (B.ai (5/4)).Zc.card≤(B.ai 2).Zc.card :=
    Qu (b5
     (show(5/4:NNReal)≤2 by
      rw[QF (by norm_num:(0:NNReal)<4)]
      norm_num))
   _≤4^(3*B.rank)*(B.ai (1/4)).Zc.card :=
    iW B
 have C7:(0:ℝ)<(B.ai (1/4)).Zc.card:=by
  exact_mod_cast(B.ai (1/4)).aE.card_pos
 have C8:(0:ℝ)<(B.ai (5/4)).Zc.card:=by
  exact_mod_cast(B.ai (5/4)).aE.card_pos
 have eu:=QG C8 (show
   ((B.ai (5/4)).Zc.card:ℝ) ≤
    ((4^(3*B.rank)*(B.ai (1/4)).Zc.card:ℕ):ℝ) by
   exact_mod_cast ch)
 rw[Rm,Rv,Ql (by positivity) C7.ne',
  QB] at eu
 have z1:(0:ℝ)<d:=by
  exact_mod_cast(show 0<d by simp[d])
 have M8:(B.rank:ℝ)≤d:=by
  exact_mod_cast(Tu B.rank 1)
 have Pu:Real.log (4:ℝ)<5/3:=by
  rw[Real.log_four_eq]
  linarith[Real.log_two_lt_d9]
 have fF:(3*B.rank:ℕ)*Real.log (4:ℝ)<5*d:=by
  push_cast
  calc
   3*(B.rank:ℝ)*Real.log 4≤3*d*Real.log 4:=by
    gcongr
   _<3*d*(5/3):=by gcongr
   _=5*d:=by ring
 dsimp[d] at fF ⊢
 linarith
private noncomputable def fi (B:aj G) (s:ℝ):ℝ :=
 Real.log ((B.ai s.toNNReal).Zc.card:ℝ) /
  (max B.rank 1:ℕ)
omit [DecidableEq G] in
private lemma q1 (B:aj G) :
  Monotone B.fi:=by
 intro s t pA
 dsimp[fi]
 apply Qz _ (by positivity)
 apply QG
 ·exact_mod_cast(B.ai s.toNNReal).aE.card_pos
 ·exact_mod_cast Qu
   (b5 (B:=B) (Real.toNNReal_mono pA))
omit [DecidableEq G] in
private lemma n9 (B:aj G) :
  B.fi (5/4)-B.fi (1/4)<5:=by
 classical
 have h:=nN B
 have hd:(0:ℝ)<(max B.rank 1:ℕ):=by positivity
 have Os:Real.toNNReal (5/4:ℝ)=(5/4:NNReal):=by
  apply NNReal.eq
  rw[Tg _ (by norm_num)]
  norm_num
 have Ot:Real.toNNReal (1/4:ℝ)=(1/4:NNReal):=by
  apply NNReal.eq
  rw[Tg _ (by norm_num)]
  norm_num
 dsimp[fi]
 rw[Os,Ot]
 rw[div_sub_div_same]
 exact(Tv hd).2 (by simpa[Qx] using h)
omit [DecidableEq G] in
lemma eP (B:aj G) :
  ∃ a8:NNReal,1/2≤a8∧a8≤1 ∧
   (B.ai a8).a1:=by
 classical
 let d:ℕ:=max B.rank 1
 obtain ⟨r,hr,Jt⟩:=nM
  B.fi (q1 B)
   (n9 B)
 let a8:NNReal:=r.toNNReal
 have jL:(a8:ℝ)=r:=Tg r (by linarith[hr.1])
 have zk:(1/2:NNReal)≤a8:=by
  rw[←U0,jL]
  norm_num
  exact hr.1
 have AG:a8≤1:=by
  rw[←U0,jL]
  norm_num
  exact hr.2
 refine ⟨a8,zk,AG, ?_⟩
 rw[si]
 dsimp only[f6]
 intro aF dy
 have Ju:0<d:=by simp[d]
 have z1:(0:ℝ)<d:=by exact_mod_cast Ju
 have oH:aF≤1:=by
  apply dy.trans
  rw[Q9]
  ·exact_mod_cast(show 1≤100*d by omega)
  ·positivity
 have BJ:(aF:ℝ)≤1/(100*(d:ℝ)):=by
  exact_mod_cast dy
 let j3:NNReal:=(1-aF)*a8
 let mv:NNReal:=(1+aF)*a8
 have Ou:(aF:ℝ)≤1/100:=by
  calc
   (aF:ℝ)≤1/(100*(d:ℝ)):=BJ
   _≤1/100:=by
    apply Rb (by norm_num) (by norm_num)
    have D8:(1:ℝ)≤d:=by
     exact_mod_cast(show 1≤d by simp[d])
    nlinarith
 have s7:(1/2:ℝ)≤a8∧(a8:ℝ)≤1:=by
  exact ⟨by exact_mod_cast zk,by exact_mod_cast AG⟩
 have BK:(j3:ℝ)∈Set.Icc (1/4:ℝ) (5/4):=by
  dsimp[j3]
  rw[NNReal.coe_sub oH]
  simp only[TN]
  have F3:(99/100:ℝ)≤1-(aF:ℝ):=by
   nlinarith
  constructor
  ·calc
    (1/4:ℝ)≤(99/100)*(1/2):=by norm_num
    _≤(1-(aF:ℝ))*(a8:ℝ):=by
     exact QW F3 s7.1 (by norm_num)
      (sub_nonneg.mpr (by exact_mod_cast oH))
  ·calc
    (1-(aF:ℝ))*(a8:ℝ)≤1*a8 :=
     Qi (sub_le_self 1 (by positivity)) (by positivity)
    _≤1*1:=iO s7.2 (by norm_num)
    _≤5/4:=by norm_num
 have C9:(mv:ℝ)∈Set.Icc (1/4:ℝ) (5/4):=by
  dsimp[mv]
  constructor<;>nlinarith
 have Li: |(j3:ℝ)-r| ≤(aF:ℝ):=by
  rw[←jL]
  dsimp[j3]
  rw[NNReal.coe_sub oH]
  simp only[TN]
  have xv:(0:ℝ)≤a8:=by positivity
  rw[show(1-(aF:ℝ))*(a8:ℝ)-a8= -(aF*a8) by ring,
   abs_neg,QC (Qn (by positivity) xv)]
  nlinarith[s7.2]
 have ME: |(mv:ℝ)-r| ≤(aF:ℝ):=by
  rw[←jL]
  dsimp[mv]
  have xv:(0:ℝ)≤a8:=by positivity
  rw[show(1+(aF:ℝ))*(a8:ℝ)-a8=aF*a8 by ring,
   QC (Qn (by positivity) xv)]
  nlinarith[s7.2]
 have s8:=Jt (j3:ℝ) BK
 have uS:=Jt (mv:ℝ) C9
 simp only[fi,Real.toNNReal_coe,
  show r.toNNReal=a8 by rfl] at s8 uS
 change
  |Real.log ((B.ai j3).Zc.card:ℝ)/d -
   Real.log ((B.ai a8).Zc.card:ℝ)/d| ≤
    60* |(j3:ℝ)-r| at s8
 change
  |Real.log ((B.ai mv).Zc.card:ℝ)/d -
   Real.log ((B.ai a8).Zc.card:ℝ)/d| ≤
    60* |(mv:ℝ)-r| at uS
 rw[div_sub_div_same,TE,RT z1] at s8 uS
 have Eu :
   Real.log ((B.ai a8).Zc.card:ℝ) -
     Real.log ((B.ai j3).Zc.card:ℝ) ≤
    60*d*(aF:ℝ):=by
  have xu:=(QF z1).mp s8
  calc
   _≤ |Real.log ((B.ai j3).Zc.card:ℝ) -
     Real.log ((B.ai a8).Zc.card:ℝ)| :=by
    rw[Su]
    exact SG _
   _≤60* |(j3:ℝ)-r| *d:=xu
   _≤60*(aF:ℝ)*d:=by gcongr
   _=60*d*(aF:ℝ):=by ring
 have F4 :
   Real.log ((B.ai mv).Zc.card:ℝ) -
     Real.log ((B.ai a8).Zc.card:ℝ) ≤
    60*d*(aF:ℝ):=by
  have xu:=(QF z1).mp uS
  calc
   _≤ |Real.log ((B.ai mv).Zc.card:ℝ) -
     Real.log ((B.ai a8).Zc.card:ℝ)| :=SG _
   _≤60* |(mv:ℝ)-r| *d:=xu
   _≤60*(aF:ℝ)*d:=by gcongr
   _=60*d*(aF:ℝ):=by ring
 let u:ℝ:=100*d*(aF:ℝ)
 have Jv:0≤u:=by dsimp[u]; positivity
 have Ov:u≤1:=by
  dsimp[u]
  calc
   100*(d:ℝ)*(aF:ℝ) ≤
     100*d*(1/(100*d)):=by gcongr
   _=1:=by field_simp
 have Ev:60*d*(aF:ℝ)=(3/5:ℝ)*u:=by
  dsimp[u]
  ring
 constructor
 ·change(1-u)*((B.ai a8).Zc.card:ℝ) ≤
   ((B.ai j3).Zc.card:ℝ)
  by_cases hu:u=1
  ·rw[hu]
   norm_num
  ·have Lj:u<1:=SM Ov hu
   have G8:0<1-u:=sub_pos.mpr Lj
   have t4:(0:ℝ)<(B.ai a8).Zc.card:=by
    exact_mod_cast(B.ai a8).aE.card_pos
   have oG:(0:ℝ)<(B.ai j3).Zc.card:=by
    exact_mod_cast(B.ai j3).aE.card_pos
   rw[←SW (QM G8 t4) oG]
   rw[Ql (sub_ne_zero.mpr (Ne.symm hu)) t4.ne']
   have HG:=QX G8
   rw[Ev] at Eu
   nlinarith
 ·change((B.ai mv).Zc.card:ℝ) ≤
   (1+u)*((B.ai a8).Zc.card:ℝ)
  have t4:(0:ℝ)<(B.ai a8).Zc.card:=by
   exact_mod_cast(B.ai a8).aE.card_pos
  have ju:(0:ℝ)<(B.ai mv).Zc.card:=by
   exact_mod_cast(B.ai mv).aE.card_pos
  rw[←SW ju (QM (by linarith) t4)]
  rw[Ql (by linarith) t4.ne']
  have HG:=Real.le_log_one_add_of_nonneg Jv
  have Pv:(3/5:ℝ)*u≤2*u/(u+2):=by
   rw[Qs (by linarith)]
   nlinarith
  rw[Ev] at F4
  linarith
end aj
end
end ay
end
section
namespace ay
open Finset
open scoped BigOperators Pointwise translate ENNReal NNReal
noncomputable def cQ (q:ℕ) (ε:ℝ):ℕ :=
 ⌈(64:ℝ)*q/(ε/2)^2⌉₊
lemma vx
  {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  {A S:Finset G} (hA:A.Nonempty) (hS:S.Nonempty)
  (q:ℕ) (hq:1≤q) (ε:ℝ) (hε:0<ε) (f:G→ℂ) :
  let k:=cQ q ε
  ∃ T:Finset G,
   T⊆S ∧
   T.Nonempty ∧
   (((#A:ℝ)^k/2* #S)/(#(A+S):ℝ)^k≤ #T) ∧
   ∀ s∈T, ∀ t∈T,
    (aJ (2*q) (τ (t-s) ((aC (mu A) f))-(aC (mu A) f))) ≤
     ε*(aJ (2*q) f):=by
 classical
 let k:=cQ q ε
 let L:=gl.l k q (ε/2) f A
 have Ci:(64:ℝ)*q/(ε/2)^2≤k:=by
  change(64:ℝ)*q/(ε/2)^2 ≤
   (↑⌈(64:ℝ)*q/(ε/2)^2⌉₊:ℝ)
  exact Rr _
 have Lk:0<k:=by
  rw[← @Nat.cast_pos ℝ]
  exact Ci.trans_lt'
   (Rn (QM (by norm_num) (by positivity)) (RF (half_pos hε) 2))
 have Jw:(#A:ℝ)^k/2≤ #L :=
  gl.Hp (half_pos hε) hq Ci
 have M9:L.Nonempty:=by
  rw[←card_pos, ← @Nat.cast_pos ℝ]
  exact Jw.trans_lt' (by positivity)
 let P:Finset ((Fin k→G) × G):=L ×ˢ S
 let X:Finset (Fin k→G):=(Fintype.piFinset fun _:Fin k↦((A+S)))
 let φ:((Fin k→G) × G)→(Fin k→G):=fun z↦z.1+fun _↦z.2
 have pP:X.Nonempty:=(hA.add hS).piFinset_const
 have AH: ∀ z∈P,φ z∈X:=by
  rintro ⟨l,s⟩ Jx
  simp only[P,mem_product] at Jx
  simp only[X,RX,φ,RM]
  have AI:l∈L:=Jx.1
  change l∈gl.l k q (ε/2) f A at AI
  rw[gl.l,mem_filter] at AI
  have hl:l∈(Fintype.piFinset fun _:Fin k↦A):=AI.1
  intro i
  exact Finset.add_mem_add (Fintype.mem_piFinset.1 hl i) Jx.2
 have Ew: #X= #(A+S)^k:=by simp[X]
 have HI:(#X:ℝ)=(#(A+S):ℝ)^k:=by
  rw[Ew]
  norm_cast
 have F5:(#X:ℝ)≠0:=by exact_mod_cast pP.card_ne_zero
 have HJ :
   ∃ x∈X,((#L:ℝ)* #S)/ #X ≤
    ∑ z∈P with φ z=x,(1:ℝ):=by
  refine Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum AH pP ?_
  simp only[QS,sum_const,P,card_product,Rm]
  rw[Qx (#X:ℝ),Tz _ F5,Q3]
 obtain ⟨x,G9,hx⟩:=HJ
 let Q:Finset ((Fin k→G) × G):={z∈P | φ z=x}
 let T:Finset G:=Q.image Prod.snd
 have Ex:(#Q:ℝ)= ∑ z∈P with φ z=x,(1:ℝ):=by simp[Q]
 have HK:Set.InjOn Prod.snd (Q:Set ((Fin k→G) × G)):=by
  rintro ⟨Jy,s₁⟩ Ll ⟨Jz,s₂⟩ Lm hs
  have JA:(Jy,s₁)∈Q:=Ll
  have JC:(Jz,s₂)∈Q:=Lm
  have Ow:Jy+(fun _↦s₁)=Jz+fun _↦s₂ :=
   (mem_filter.1 JA).2.trans (mem_filter.1 JC).2.symm
  cases hs
  apply Prod.ext
  ·funext i
   exact add_right_cancel (SR Ow i)
  ·rfl
 have nf: #T= #Q:=card_image_iff.mpr HK
 have Ln:(0:ℝ)< #Q:=by
  have Ey:0<((#L:ℝ)* #S)/ #X :=
   Rn (QM (by exact_mod_cast M9.card_pos) (by exact_mod_cast hS.card_pos))
    (by exact_mod_cast pP.card_pos)
  exact Ey.trans_le (by simpa[Ex] using hx)
 have uT:T.Nonempty:=by
  rw[←card_pos, ← @Nat.cast_pos ℝ,nf]
  exact Ln
 refine ⟨T, ?_,uT, ?_, ?_⟩
 ·intro s JE
  obtain ⟨z,Ox,rfl⟩:=mem_image.1 JE
  exact(mem_product.1 (mem_filter.1 Ox).1).2
 ·calc
   (((#A:ℝ)^k/2* #S)/(#(A+S):ℝ)^k)
     = (((#A:ℝ)^k/2* #S)/ #X):=by rw[HI]
   _≤((#L:ℝ)* #S)/ #X:=by gcongr
   _≤ #Q:=by simpa[Ex] using hx
   _= #T:=by exact_mod_cast nf.symm
 ·intro s JE t Oy
  obtain ⟨⟨a,s'⟩,JF,Oz⟩:=mem_image.1 JE
  obtain ⟨⟨b,t'⟩,JG,OA⟩:=mem_image.1 Oy
  simp only at Oz OA
  subst s'
  subst t'
  have OB:a∈L:=(mem_product.1 (mem_filter.1 JF).1).1
  have OC:b∈L:=(mem_product.1 (mem_filter.1 JG).1).1
  have OD:a+(fun _↦s)=x:=(mem_filter.1 JF).2
  have OE:b+(fun _↦t)=x:=(mem_filter.1 JG).2
  have hab:a+(fun _↦s-t)=b:=by
   funext i
   have ha:=SR OD i
   have hb:=SR OE i
   simp only[RM] at ha hb ⊢
   calc
    a i+(s-t)=(a i+s)-t:=by abel
    _=x i-t:=by rw[ha]
    _=b i:=by rw[←hb]; abel
  have HL:a+(fun _↦s-t)∈L:=by rw[hab]; exact OC
  have JH:=gl.pK
   (A:=A) (f:=f) (m:=q) (k:=k) (t:=s-t) OB HL Lk hq
  simpa[neg_sub,mul_div_cancel₀ _ (two_ne_zero' ℝ)] using JH
private lemma t5
  {G:Type*} (B C:Finset G) (hB:B.Nonempty) (hC:C.Nonempty)
  (q:ℕ) (hq:q=⌈1+Real.log (min 1 ((#C:ℝ)/ #B))⁻¹⌉₊) :
  ((#C:ℝ)/ #B)^(-((2*q:ℕ):ℝ)⁻¹)≤Real.exp 1:=by
 let r:ℝ:=min 1 ((#C:ℝ)/ #B)
 have s9:0<r:=by
  dsimp[r]
  exact lt_min U1 (Rn (by exact_mod_cast hC.card_pos) (by exact_mod_cast hB.card_pos))
 have xw:r≤1:=Uv _ _
 have sh:0<1+Real.log r⁻¹ :=by
  have Cj:0≤Real.log r⁻¹ :=
   Qv ((Uw s9).2 xw)
  linarith
 have ya:1≤q:=by
  rw[hq,Nat.one_le_ceil_iff]
  have Cj:0≤Real.log r⁻¹ :=
   Qv ((Uw s9).2 xw)
  dsimp[r] at Cj ⊢
  linarith
 calc
  ((#C:ℝ)/ #B)^(-((2*q:ℕ):ℝ)⁻¹)
    ≤ r^(-((2*q:ℕ):ℝ)⁻¹) :=
   Real.rpow_le_rpow_of_nonpos (by positivity) inf_le_right<| neg_nonpos.2<| by positivity
  _≤r^(-(1+Real.log r⁻¹)⁻¹) :=
   Th (by positivity) xw<| TO<| inv_anti₀
    sh<| (Rr _).trans<| by
     rw[←hq]
     exact_mod_cast T9 q (by norm_num:0<2)
  _≤r^(-(0+Real.log r⁻¹)⁻¹):=by
   obtain hr | hr:r=1∨r<1:=xw.eq_or_lt
   ·simp[hr]
   have:0<Real.log r⁻¹ :=Sv<| (one_lt_inv₀ s9).2 hr
   exact Th (by positivity) xw
    (by gcongr; exact Us)
  _=r^(Real.log r)⁻¹ :=by simp[inv_neg]
  _≤Real.exp 1:=Real.rpow_inv_log_le_exp_one
private lemma sW
  {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  {A:Finset G} (B C:Finset G) (u x:G) (q:ℕ) (ya:1≤q) :
  ‖(τ u ((aC (((aC (mu A) (((Set.indicator B fun _↦(1:_)):G→ℂ))))) (mu C))) -
   (aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C)):G→ℂ) x‖ ≤
    (aJ (2*q) (τ u ((aC (mu A) (((Set.indicator B fun _↦(1:_)):G→ℂ))))-(aC (mu A) ((Set.indicator B fun _↦(1:_)))))) *
     (aJ (NNReal.conjExponent (2*q)) ((@mu (ℂ) _ _) (x+ᵥ -C))):=by
 let M:ℕ:=2*q
 have z0:1<(M:ℝ≥0):=by
  norm_cast
  dsimp[M]
  omega
 have hM:(M:ℝ≥0).HolderConjugate _:=S2 z0
 have PZ:(M:ℝ≥0∞).HolderConjugate _:=hM.coe_ennreal
 set F:G→ℂ:=τ u ((aC (mu A) ((Set.indicator B fun _↦(1:_)))))-(aC (mu A) ((Set.indicator B fun _↦(1:_))))
 have x8 :
   (τ u ((aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C)))-(aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C)):G→ℂ) x =
    ((aC F (mu C))) x:=by simp[CJ,F]
 have hsum:((aC F (mu C))) x= ∑ y,F y*mu (x+ᵥ -C) y:=by
  rw[cR]
  congr with y
  simp[neg_add_eq_sub]
 calc
  ‖(τ u ((aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C))) -
    (aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C)):G→ℂ) x‖
    = ‖∑ y,F y*mu (x+ᵥ -C) y‖ :=by rw[x8,hsum]
  _≤ ∑ y, ‖F y*mu (x+ᵥ -C) y‖ :=Rq _ _
  _=(aJ 1 (F*mu (x+ᵥ -C))):=by
   rw[ej]
   rfl
  _≤(aJ M F)*(aJ (NNReal.conjExponent M) ((@mu (ℂ) _ _) (x+ᵥ -C))) :=
   yP _ _
  _=_:=by simp[F,M]
private lemma vy
  {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  {A:Finset G} {ε:ℝ} (B C:Finset G)
  (hC:C.Nonempty) (u x:G) (q:ℕ) (ya:1≤q)
  (Da :
   (aJ (2*q) (τ u ((aC (mu A) (((Set.indicator B fun _↦(1:_)):G→ℂ))))-(aC (mu A) ((Set.indicator B fun _↦(1:_)))))) ≤
    ε/Real.exp 1*(aJ (2*q) (((Set.indicator B fun _↦(1:_)):G→ℂ)))) :
  ‖(τ u ((aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C))) -
   (aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C)):G→ℂ) x‖ ≤
    ε*(((#C:ℝ)/ #B)^(-((2*q:ℕ):ℝ)⁻¹)/Real.exp 1):=by
 let M:ℕ:=2*q
 have Lo:(M:ℝ≥0)≠0:=by positivity
 have z0:1<(M:ℝ≥0):=by
  norm_cast
  dsimp[M]
  omega
 have hM:(M:ℝ≥0).HolderConjugate _:=S2 z0
 calc
  ‖(τ u ((aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C))) -
    (aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C)):G→ℂ) x‖
    ≤ (aJ M (τ u ((aC (mu A) (((Set.indicator B fun _↦(1:_)):G→ℂ))))-(aC (mu A) ((Set.indicator B fun _↦(1:_)))))) *
      (aJ (NNReal.conjExponent M) ((@mu (ℂ) _ _) (x+ᵥ -C))):=by
     simpa[M] using sW B C u x q ya
  _≤ε/Real.exp 1* #B^(M:ℝ)⁻¹ *
     (aJ (NNReal.conjExponent M) ((@mu (ℂ) _ _) (x+ᵥ -C))):=by
   gcongr
   ·exact d8
   have Lq :
     (aJ M (τ u ((aC (mu A) (((Set.indicator B fun _↦(1:_)):G→ℂ))))-(aC (mu A) ((Set.indicator B fun _↦(1:_)))))) ≤
      ε/Real.exp 1*(aJ M (((Set.indicator B fun _↦(1:_)):G→ℂ))):=by
    simpa only[M,Rm,Nat.cast_ofNat] using Da
   have F6:(aJ M (((Set.indicator B fun _↦(1:_)):G→ℂ)))=(#B:ℝ)^(M:ℝ)⁻¹ :=by
    rw[show(M:ℝ≥0∞)=((M:ℝ≥0):ℝ≥0∞) by norm_num,
     n2 Lo]
    norm_num
   rw[←F6]
   exact Lq
  _=ε*(((#C:ℝ)/ #B)^(-(M:ℝ)⁻¹)/Real.exp 1):=by
   rw[←mul_comm_div,rx hM.symm.lt.le hC.neg.vadd_finset,
    card_vadd_finset,card_neg,hM.symm.coe.inv_sub_one,Real.div_rpow,Qo]
   any_goals positivity
   push_cast
   rw[TS,TS, ←Qw,inv_div_inv]
   all_goals positivity
  _=ε*(((#C:ℝ)/ #B)^(-((2*q:ℕ):ℝ)⁻¹)/Real.exp 1):=by
   simp[M]
private lemma sn
  {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  {A:Finset G} {ε:ℝ} (hε:0<ε) (B C:Finset G)
  (hC:C.Nonempty) (u:G) (q:ℕ) (ya:1≤q)
  (eO:((#C:ℝ)/ #B)^(-((2*q:ℕ):ℝ)⁻¹)≤Real.exp 1)
  (Da :
   (aJ (2*q) (τ u ((aC (mu A) (((Set.indicator B fun _↦(1:_)):G→ℂ))))-(aC (mu A) ((Set.indicator B fun _↦(1:_)))))) ≤
    ε/Real.exp 1*(aJ (2*q) (((Set.indicator B fun _↦(1:_)):G→ℂ)))) :
  (aJ (∞) ((τ u ((aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C))) -
   (aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C)):G→ℂ)))≤ε:=by
 rw[dw]
 refine ciSup_le fun x↦(vy B C hC u x q ya Da).trans ?_
 refine Sq hε.le ((Q9 (by positivity)).2 ?_)
 exact eO
lemma q2
  {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  {A S:Finset G} (hA:A.Nonempty) (hS:S.Nonempty)
  (ε:ℝ) (hε:0<ε) (B C:Finset G) (hB:B.Nonempty) (hC:C.Nonempty) :
  let q:=⌈1+Real.log (min 1 ((#C:ℝ)/ #B))⁻¹⌉₊
  let k:=cQ q (ε/Real.exp 1)
  ∃ T:Finset G,
   T⊆S∧T.Nonempty ∧
   (((#A:ℝ)^k/2* #S)/(#(A+S):ℝ)^k≤ #T) ∧
   ∀ s∈T, ∀ t∈T,
    (aJ (∞) ((τ (t-s) ((aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C))) -
     (aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C)):G→ℂ)))≤ε:=by
 let r:ℝ:=min 1 ((#C:ℝ)/ #B)
 let m:ℝ:=1+Real.log r⁻¹
 have s9:0<r:=by
  dsimp[r]
  exact lt_min U1 (Rn (by exact_mod_cast hC.card_pos) (by exact_mod_cast hB.card_pos))
 have xw:r≤1:=Uv _ _
 have Pw:0< m:=by
  have:0≤Real.log r⁻¹ :=Qv ((Uw s9).2 xw)
  positivity
 have Ha:1≤⌈m⌉₊:=Nat.one_le_iff_ne_zero.2 (by positivity)
 obtain ⟨T,Ez,uT,ch,hT⟩ :=
  vx hA hS ⌈m⌉₊ Ha (ε/Real.exp 1) (by positivity)
   ((Set.indicator B fun _↦(1:_)):G→ℂ)
 refine ⟨T,Ez,uT, ?_, ?_⟩
 ·simpa[r,m] using ch
 ·intro s hs t ht
  apply sn hε B C hC (t-s) ⌈m⌉₊ Ha
   (t5 B C hB hC ⌈m⌉₊ (by simp[r,m]))
  simpa[r,m] using hT s hs t ht
lemma mT
  {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  {A S:Finset G} (hA:A.Nonempty) (hS:S.Nonempty)
  (ε:ℝ) (hε:0<ε) (m:ℕ) (hm:m≠0)
  (B C:Finset G) (hB:B.Nonempty) (hC:C.Nonempty) :
  let q:=⌈1+Real.log (min 1 ((#C:ℝ)/ #B))⁻¹⌉₊
  let k:=cQ q ((ε/m)/Real.exp 1)
  ∃ (T:Finset G) (z:G),
   T⊆S∧z∈T ∧
   (-z+ᵥ T).Nonempty∧(-z+ᵥ T)⊆S-S ∧
   (((#A:ℝ)^k/2* #S)/(#(A+S):ℝ)^k≤ #T) ∧
   (aJ (∞) (((aC ((eo (mu (-z+ᵥ T)) m)) (((aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C))))) -
    (aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C)):G→ℂ)))≤ε:=by
 have G4:(0:ℝ)< m:=by exact_mod_cast(Nat.pos_iff_ne_zero.2 hm)
 have Ca:0<ε/(m:ℝ):=Rn hε G4
 obtain ⟨T,Ez,uT,ch,jl⟩ :=
  q2 hA hS (ε/(m:ℝ)) Ca B C hB hC
 obtain ⟨z,hz⟩:=uT
 let X:Finset G:=-z+ᵥ T
 have pP:X.Nonempty:=by
  refine ⟨0, ?_⟩
  change 0∈ -z+ᵥ T
  rw[mem_vadd_finset]
  exact ⟨z,hz,by simp⟩
 have F7: ∀ x∈X,
   (aJ (∞) ((τ x ((aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C))) -
    (aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C)):G→ℂ)))≤ε/(m:ℝ):=by
  intro x hx
  change x∈ -z+ᵥ T at hx
  rw[mem_vadd_finset] at hx
  obtain ⟨t,ht,rfl⟩:=hx
  have hp:=jl z hz t ht
  simpa[Qy,RV] using hp
 have Lr: -z+ᵥ T⊆S-S:=by
  intro x hx
  rw[mem_vadd_finset] at hx
  obtain ⟨t,ht,rfl⟩:=hx
  simpa[Qy,RV] using sub_mem_sub (Ez ht) (Ez hz)
 set F:G→ℂ:=(aC (((aC (mu A) ((Set.indicator B fun _↦(1:_)))))) (mu C))
 refine ⟨T,z,Ez,hz, ?_,Lr, ?_, ?_⟩
 ·simpa[X] using pP
 ·simpa using ch
 ·change(aJ (∞) ((aC ((eo (mu X) m)) F)-F))≤ε
  calc
   ((aJ (∞) ((aC ((eo (mu X) m)) F)-F)):ℝ)
     = (aJ (∞) (𝔼 a∈(Fintype.piFinset fun _:Fin m↦X),(τ (∑ i,a i) F-F))):=by
      rw[vI,expect_sub_distrib,expect_const pP.piFinset_const]
   _≤𝔼 a∈(Fintype.piFinset fun _:Fin m↦X),(aJ (∞) (τ (∑ i,a i) F-F)) :=
    wS le_top
   _≤𝔼 _a∈(Fintype.piFinset fun _:Fin m↦X),ε:=by
    refine expect_le_expect fun a ha↦ ?_
    calc
     ((aJ (∞) (τ (∑ i,a i) F-F)):ℝ)
       ≤ ∑ i,(aJ (∞) (τ (a i) F-F)) :=
        pJ le_top _ _ _
     _≤ ∑ _i,ε/(m:ℝ):=by
      gcongr
      simpa[F] using F7 (a _) (Fintype.mem_piFinset.1 ha _)
     _=ε:=by
      simp only[sum_const,card_fin,QS]
      rw[mul_div_cancel₀]
      exact_mod_cast hm
   _=ε:=by rw[expect_const pP.piFinset_const]
end ay
end
section
noncomputable section
open AddChar Finset Fintype Function RCLike
open scoped BigOperators ComplexConjugate
namespace ay.dT
variable {G:Type*} [AddCommGroup G] [Fintype G]
def coeff (f:G→ℂ) (χ:AddChar G ℂ):ℂ:=⟪(χ:G→ℂ),f⟫ₙ_[ℂ]
lemma Zi (f:G→ℂ) (a:G) :
  ∑ χ:AddChar G ℂ,coeff f χ*χ a=f a:=by
 classical
 simp_rw[coeff,wInner_cWeight_eq_expect,inner_apply',expect_mul,
  ←expect_sum_comm,QN _ (f _), ←sum_mul,
  ←Rz,TK, ←map_sub_eq_div,
  AddChar.sum_apply_eq_ite,sub_eq_zero,ite_mul,zero_mul,Fintype.expect_ite_eq]
 simp[NNRat.smul_def (K:=ℂ),SN]
def convolution (f g:G→ℂ) (x:G):ℂ :=
 𝔼 y:G,f y*g (x-y)
def a2 (f g:G→ℂ) (x:G):ℂ :=
 𝔼 y:G,f (x+y)*conj (g y)
lemma mU (f g:G→ℂ) (χ:AddChar G ℂ) :
  coeff (convolution f g) χ=coeff f χ*coeff g χ:=by
 classical
 simp_rw[coeff,wInner_cWeight_eq_expect,inner_apply,convolution,
  mul_expect,expect_mul, ←expect_product',univ_product_univ]
 refine RW ((Equiv.prodComm _ _).trans<|
  ((Equiv.refl _).prodShear Equiv.subRight).trans<| Equiv.prodComm _ _) _ _ fun (a,b)↦ ?_
 simp[Q7, ←RU, ←map_add_eq_mul]
lemma zP (f:G→ℂ) (χ:AddChar G ℂ) :
  coeff (fun x↦conj (f (-x))) χ=conj (coeff f χ):=by
 classical
 simp only[coeff,wInner_cWeight_eq_expect,inner_apply,map_expect,RU,
  Tl]
 refine RW (Equiv.neg _) _ _ fun i↦ ?_
 simp only[Equiv.neg_apply, ←inv_apply_eq_conj, ←inv_apply',inv_apply]
lemma l2 (f g:G→ℂ) :
  a2 f g=convolution f (fun x↦conj (g (-x))):=by
 funext x
 simp only[a2,convolution]
 refine RW (Equiv.addLeft x) _ _ fun y↦ ?_
 simp
lemma kr (f g:G→ℂ) (χ:AddChar G ℂ) :
  coeff (a2 f g) χ=coeff f χ*conj (coeff g χ):=by
 rw[l2,mU,zP]
lemma t6 (f:G→ℂ) (χ:AddChar G ℂ) :
  coeff (a2 f f) χ=(Complex.normSq (coeff f χ):ℂ):=by
 rw[kr]
 exact Complex.mul_conj _
end ay.dT
end
end
section
open AddChar Finset
open scoped BigOperators NNReal
namespace ay
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
private lemma t7 (A:Finset G) (psi:AddChar G ℂ) :
  (∑ x:G,(af A x:ℂ)*psi x) =
   ((A.card:ℂ)⁻¹)*c5.c6 A psi:=by
 classical
 rw[c5.c6,Qj]
 calc
  (∑ x:G,(af A x:ℂ)*psi x) =
    ∑ x:G,if x∈A then ((A.card:ℂ)⁻¹)*psi x else 0:=by
   apply Io rfl
   intro x _
   by_cases hx:x∈A<;>simp[af,hx]
  _= ∑ x∈A,((A.card:ℂ)⁻¹)*psi x:=by
   rw[←QE]
   have eI :
     (Finset.univ.filter fun x:G↦x∈A)=A:=by
    ext x
    simp
   rw[eI]
private lemma pQ (A:Finset G)
  (psi:AddChar G ℂ) (t:G) :
  (1-psi t)*(∑ x:G,(af A x:ℂ)*psi x) =
   ∑ x:G,
    ((af A x-af A (x-t):ℝ):ℂ) *
     psi x:=by
 classical
 have kC :
   (∑ x:G,(af A (x-t):ℂ)*psi x) =
    psi t* ∑ x:G,(af A x:ℂ)*psi x:=by
  rw[←(Equiv.addRight t).sum_comp]
  ·change
    (∑ x:G,(af A ((x+t)-t):ℂ)*psi (x+t)) =
     psi t* ∑ x:G,(af A x:ℂ)*psi x
   simp_rw[add_sub_cancel_right,map_add_eq_mul]
   rw[Qj]
   apply Io rfl
   intro x _
   ring
  ·simp
 push_cast
 simp_rw[sub_mul]
 rw[QJ,kC]
 ring
omit [DecidableEq G] in
lemma l3
  {C:aj G} (dF:C.a1) {eta:ℝ} (fC:0<eta)
  {sigma:ℝ≥0}
  (iX:sigma≤1/(100*(max C.rank 1:ℕ):ℝ≥0))
  {psi:AddChar G ℂ} (cT:psi∈c5.cj C.Zc eta)
  {t:G} (ht:t∈(C.ai sigma).Zc) :
  ‖1-psi t‖ ≤
   200*((max C.rank 1:ℕ):ℝ)*(sigma:ℝ)/eta:=by
 classical
 let F:ℂ:= ∑ x:G,(af C.Zc x:ℂ)*psi x
 have ch:(0:ℝ)<C.Zc.card:=by
  exact_mod_cast C.aE.card_pos
 have JI: ‖F‖ = ‖c5.c6 C.Zc psi‖ /C.Zc.card:=by
  dsimp[F]
  rw[t7,QO]
  simp[Ri]
 have iV:eta≤ ‖F‖ :=by
  rw[JI,Qs ch]
  exact c5.gm.mp cT
 have l4 :
   ‖1-psi t‖ * ‖F‖ ≤
    ∑ x:G,
     |af C.Zc (x-t) -
      af C.Zc x| :=by
  rw[←QO,pQ C.Zc psi t]
  calc
   ‖∑ x:G,
     ((af C.Zc x -
       af C.Zc (x-t):ℝ):ℂ)*psi x‖ ≤
     ∑ x:G,
      ‖((af C.Zc x -
        af C.Zc (x-t):ℝ):ℂ)*psi x‖ :=
    Rq _ _
   _= ∑ x:G,
     |af C.Zc (x-t) -
      af C.Zc x| :=by
    apply Io rfl
    intro x _
    rw[QO]
    rw[Rf,QK,Su]
    simp
 have AJ :=
  aj.cN
   dF iX ht
 have hmul :
   ‖1-psi t‖ *eta ≤
    200*((max C.rank 1:ℕ):ℝ)*(sigma:ℝ):=by
  calc
   ‖1-psi t‖ *eta≤ ‖1-psi t‖ * ‖F‖ :=
    iO iV (Re _)
   _≤ ∑ x:G,
     |af C.Zc (x-t) -
      af C.Zc x| :=l4
   _≤200*((max C.rank 1:ℕ):ℝ)*(sigma:ℝ):=AJ
 exact(Qs fC).2 hmul
omit [DecidableEq G] in
lemma kj
  {C:aj G} (dF:C.a1) {sigma:ℝ≥0}
  (iX:sigma≤1/(100*(max C.rank 1:ℕ):ℝ≥0))
  {psi:AddChar G ℂ} (cT:psi∈c5.cj C.Zc (1/2))
  {t:G} (ht:t∈(C.ai sigma).Zc) :
  ‖1-psi t‖ ≤400*((max C.rank 1:ℕ):ℝ)*(sigma:ℝ):=by
 classical
 have h:=l3 dF (eta:=(1/2:ℝ))
  (by norm_num) iX cT ht
 convert h using 1
 ring
end
end ay
end
section
noncomputable section
open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal
namespace ay.aI
variable {G:Type*} [Fintype G] [AddCommGroup G]
def eV (mu:G→ℝ) (K:ℝ)
  (Delta:Finset (AddChar G ℂ)):Prop :=
 ∀ u:AddChar G ℂ→ℂ,
  (∀ psi∈Delta, ‖u psi‖ ≤1) →
   ∑ x:G,mu x *
    ∏ psi∈Delta,(1+(u psi*psi x).re)≤exp K
def fO (mu f:G→ℝ) (eta:ℝ) :
  Finset (AddChar G ℂ) :=
  Finset.univ.filter fun psi ↦
  eta*(∑ x:G,f x*mu x) ≤
   ‖∑ x:G,(f x*mu x:ℝ)*psi x‖
@[simp] lemma lN {mu f:G→ℝ} {eta:ℝ}
  {psi:AddChar G ℂ} :
  psi∈fO mu f eta ↔
   eta*(∑ x:G,f x*mu x) ≤
    ‖∑ x:G,(f x*mu x:ℝ)*psi x‖ :=by
 simp[fO]
end ay.aI
end
end
section
noncomputable section
open Finset Real
open scoped BigOperators ComplexConjugate
namespace ay.aI
variable {G:Type*} [Fintype G] [AddCommGroup G]
def cy (S Delta:Finset (AddChar G ℂ)):Prop :=
 ∀ t u:Finset (AddChar G ℂ),t⊆Delta→u⊆Delta →
  Disjoint t u→(t∪u).Nonempty →
   (∑ psi∈t,psi)- ∑ psi∈u,psi∉S
omit [Fintype G] in
lemma sX (S:Finset (AddChar G ℂ)) :
  cy S ∅:=by
 intro t u ht hu x5 vE
 simp only[Finset.subset_empty] at ht hu
 subst t
 subst u
 simp at vE
omit [Fintype G] in
lemma cy.mono {S:Finset (AddChar G ℂ)}
  {Delta Gamma:Finset (AddChar G ℂ)}
  (h:cy S Delta) (l0:Gamma⊆Delta) :
  cy S Gamma:=by
 intro t u ht hu
 exact h t u (ht.trans l0) (hu.trans l0)
omit [Fintype G] in
lemma nO [Finite G]
  (S T:Finset (AddChar G ℂ))
  (hzero:0∈S)
  (hS: ∀ s,s∈S→ -s∈S) :
  ∃ Delta:Finset (AddChar G ℂ),
   Delta⊆T∧cy S Delta ∧
    ∀ psi∈T, ∃ z∈Delta.addSpan, ∃ s∈S,psi=z+s:=by
 let:=Fintype.ofFinite G
 classical
 let candidates:=T.powerset.filter (cy S)
 have BL:candidates.Nonempty:=by
  refine ⟨∅, ?_⟩
  simp[candidates,sX]
 obtain ⟨Delta,Db,Dc⟩:=candidates.exists_maximal BL
 have dQ:=Finset.mem_filter.mp Db
 refine ⟨Delta,Finset.mem_powerset.mp dQ.1,dQ.2, ?_⟩
 intro psi Lu
 by_cases zl:psi∈Delta
 ·exact ⟨psi,Finset.subset_addSpan zl,0,hzero,by simp⟩
 ·have yZ:insert psi Delta⊆T :=
   Finset.insert_subset Lu (Finset.mem_powerset.mp dQ.1)
  have hnot: ¬ cy S (insert psi Delta):=by
   intro Na
   have BM:insert psi Delta∈candidates:=by
    simp[candidates,yZ,Na]
   have l0:=Dc BM (Finset.subset_insert psi Delta)
   exact zl (l0 (Finset.mem_insert_self psi Delta))
  rw[cy] at hnot
  push Not at hnot
  obtain ⟨t,u,ht,hu,x5,vE,Dd⟩:=hnot
  have Ck:psi∈t∪u:=by
   by_contra cT
   have rU:t⊆Delta:=by
    intro a ha
    have mM:=ht ha
    rw[Rp] at mM
    exact mM.resolve_left (fun h↦cT (h▸Um u ha))
   have y0:u⊆Delta:=by
    intro a ha
    have mM:=hu ha
    rw[Rp] at mM
    exact mM.resolve_left (fun h↦cT (h▸Ua t ha))
   exact dQ.2 t u rU y0 x5 vE Dd
  rw[Finset.mem_union] at Ck
  rcases Ck with EA | EB
  ·have De:psi∉u:=fun h↦Finset.disjoint_left.mp x5 EA h
   have HM:t.erase psi⊆Delta:=by
    intro a ha
    have mM:=ht (Sm ha)
    rw[Rp] at mM
    exact mM.resolve_left (Sw ha)
   have y0:u⊆Delta:=by
    intro a ha
    have mM:=hu ha
    rw[Rp] at mM
    exact mM.resolve_left (fun h↦De (h▸ha))
   let z:=(∑ a∈u,a)- ∑ a∈t.erase psi,a
   have hz:z∈Delta.addSpan:=by
    exact Tp y0 HM
   refine ⟨z,hz,(∑ a∈t,a)- ∑ a∈u,a,Dd, ?_⟩
   dsimp[z]
   rw[←SO _ _ EA]
   abel
  ·have Df:psi∉t:=fun h↦Finset.disjoint_left.mp x5 h EB
   have HN:u.erase psi⊆Delta:=by
    intro a ha
    have mM:=hu (Sm ha)
    rw[Rp] at mM
    exact mM.resolve_left (Sw ha)
   have rU:t⊆Delta:=by
    intro a ha
    have mM:=ht ha
    rw[Rp] at mM
    exact mM.resolve_left (fun h↦Df (h▸ha))
   let z:=(∑ a∈t,a)- ∑ a∈u.erase psi,a
   have hz:z∈Delta.addSpan:=by
    exact Tp rU HN
   let s:=-((∑ a∈t,a)- ∑ a∈u,a)
   have hs:s∈S:=hS _ Dd
   refine ⟨z,hz,s,hs, ?_⟩
   dsimp[z,s]
   rw[←SO _ _ EB]
   abel
private def fq (t u:Finset (AddChar G ℂ)):AddChar G ℂ :=
 (∑ psi∈u,psi)- ∑ psi∈t \ u,psi
private def ek (v:AddChar G ℂ→ℂ)
  (t u:Finset (AddChar G ℂ)):ℂ :=
 ((∏ psi∈u,v psi)* ∏ psi∈t \ u,conj (v psi)) /
  (2:ℂ)^t.card
omit [Fintype G] in
private lemma oa [Finite G]
  (Delta:Finset (AddChar G ℂ)) (v:AddChar G ℂ→ℂ) (x:G) :
  ∏ psi∈Delta,((1+(v psi*psi x).re:ℝ):ℂ) =
   ∑ t∈Delta.powerset, ∑ u∈t.powerset,
    ek v t u*fq t u x:=by
 let:=Fintype.ofFinite G
 calc
  ∏ psi∈Delta,((1+(v psi*psi x).re:ℝ):ℂ) =
    ∏ psi∈Delta,
     (((v psi*psi x)+conj (v psi*psi x))/2+1):=by
   apply Finset.prod_congr rfl
   intro psi cT
   rw[RV, ←Complex.re_eq_add_conj]
   push_cast
   rfl
  _= ∑ t∈Delta.powerset,
    ∏ psi∈t,((v psi*psi x)+conj (v psi*psi x))/2:=by
   rw[Finset.prod_add]
   simp
  _= ∑ t∈Delta.powerset, ∑ u∈t.powerset,
    ek v t u*fq t u x:=by
   apply Io rfl
   intro t ht
   rw[Finset.prod_div_distrib]
   rw[Finset.prod_add]
   rw[TP]
   apply Io rfl
   intro u hu
   rw[ek,fq]
   simp only[AddChar.sum_apply,RO,
    TV]
   simp only[Finset.prod_const]
   simp_rw[RU,TW]
   rw[map_prod]
   ring
private lemma nP
  (w:G→ℝ) (Delta:Finset (AddChar G ℂ))
  (v:AddChar G ℂ→ℂ) :
  ((∑ x:G,w x *
    ∏ psi∈Delta,(1+(v psi*psi x).re)):ℂ) =
   ∑ t∈Delta.powerset, ∑ u∈t.powerset,
    ek v t u *
     ay.cG w (fq t u):=by
 simp_rw[Complex.ofReal_prod]
 simp_rw[oa]
 simp_rw[Qj]
 rw[QD]
 apply Io rfl
 intro t ht
 rw[QD]
 apply Io rfl
 intro u hu
 rw[ay.cG,Qj]
 apply Io rfl
 intro x hx
 ring
omit [Fintype G] in
private lemma sY
  {S Delta t u:Finset (AddChar G ℂ)}
  (dQ:cy S Delta)
  (ht:t⊆Delta) (JJ:t.Nonempty) (hu:u⊆t) :
  fq t u∉S:=by
 apply dQ u (t \ u)
 ·exact hu.trans ht
 ·exact Finset.sdiff_subset.trans ht
 ·rw[Finset.disjoint_left]
  intro psi Lv JK
  exact(Finset.mem_sdiff.mp JK).2 Lv
 ·simpa[Finset.union_sdiff_of_subset hu] using JJ
omit [Fintype G] in
private lemma rC
  {v:AddChar G ℂ→ℂ} {t u:Finset (AddChar G ℂ)}
  (hu:u⊆t) (hv: ∀ psi∈t, ‖v psi‖ ≤1) :
  ‖ek v t u‖ ≤((2:ℝ)^t.card)⁻¹ :=by
 have OF: ‖∏ psi∈u,v psi‖ ≤1:=by
  rw[norm_prod]
  exact UO (fun psi cT↦Re _)
   (fun psi cT↦hv psi (hu cT))
 have Nb: ‖∏ psi∈t \ u,conj (v psi)‖ ≤1:=by
  rw[norm_prod]
  exact UO (fun psi cT↦Re _)
   (fun psi cT↦by
    rw[RCLike.norm_conj]
    exact hv psi (Finset.sdiff_subset cT))
 have kD :
   ‖(∏ psi∈u,v psi)* ∏ psi∈t \ u,conj (v psi)‖ ≤1:=by
  rw[QO]
  calc
   _≤1*1:=QW OF Nb (Re _) (by norm_num)
   _=1:=by norm_num
 rw[ek,norm_div]
 calc
  _≤1/ ‖(2:ℂ)^t.card‖ :=
   Qz kD (Re _)
  _=((2:ℝ)^t.card)⁻¹ :=by
   rw[norm_pow]
   norm_num
lemma cy.ob
  {S Delta:Finset (AddChar G ℂ)} {w:G→ℝ} {q:ℝ}
  (dQ:cy S Delta)
  (_hw0: ∀ x,0≤w x) (AK: ∑ x:G,w x=1)
  (x1:0≤q)
  (hq: ∀ psi,psi∉S→ ‖ay.cG w psi‖ ≤q)
  (v:AddChar G ℂ→ℂ) (hv: ∀ psi∈Delta, ‖v psi‖ ≤1) :
  ∑ x:G,w x* ∏ psi∈Delta,(1+(v psi*psi x).re) ≤
   1+q*(2:ℝ)^Delta.card:=by
 classical
 let F:Finset (AddChar G ℂ)→ℂ:=fun t ↦
  ∑ u∈t.powerset,ek v t u *
   ay.cG w (fq t u)
 let E:ℂ:= ∑ t∈Delta.powerset.erase ∅,F t
 have ss:(∅:Finset (AddChar G ℂ))∈Delta.powerset:=by simp
 have Nc: ∑ x:G,(w x:ℂ)=1:=by exact_mod_cast AK
 have HO:F ∅=1:=by
  simp[F,ek,fq,ay.cG,Nc]
 have l5 :
   ((∑ x:G,w x *
     ∏ psi∈Delta,(1+(v psi*psi x).re)):ℂ)=1+E:=by
  rw[nP]
  rw[←SO _ _ ss]
  simp only[HO,E,F]
  ring
 have oG (t:Finset (AddChar G ℂ))
   (ht:t∈Delta.powerset.erase ∅): ‖F t‖ ≤q:=by
  have rU:t⊆Delta:=Finset.mem_powerset.mp (Sm ht)
  have JJ:t.Nonempty:=Finset.nonempty_iff_ne_empty.mpr (Sw ht)
  calc
   ‖F t‖ ≤ ∑ u∈t.powerset,
     ‖ek v t u *
      ay.cG w (fq t u)‖ :=by
    exact Rq _ _
   _≤ ∑ _u∈t.powerset,((2:ℝ)^t.card)⁻¹ *q:=by
    apply QI
    intro u hu
    rw[QO]
    apply QW
    ·exact rC (Finset.mem_powerset.mp hu)
      (fun psi cT↦hv psi (rU cT))
    ·exact hq _ (sY dQ rU JJ
      (Finset.mem_powerset.mp hu))
    ·exact Re _
    ·exact inv_nonneg.mpr (QH (by norm_num) _)
   _=q:=by
    rw[Tq,Ux]
    simp[QS]
 have JL: ‖E‖ ≤q*(2:ℝ)^Delta.card:=by
  calc
   ‖E‖ ≤ ∑ t∈Delta.powerset.erase ∅, ‖F t‖ :=Rq _ _
   _≤ ∑ _t∈Delta.powerset.erase ∅,q:=by
    exact QI fun t ht↦oG t ht
   _≤ ∑ _t∈Delta.powerset,q:=by
    exact Ry (Finset.erase_subset _ _)
     (fun _ _ _↦x1)
   _=q*(2:ℝ)^Delta.card:=by
    simp[Ux]
    ring
 let R:ℝ :=
  ∑ x:G,w x* ∏ psi∈Delta,(1+(v psi*psi x).re)
 have Lw:(R:ℂ)=1+E:=by
  calc
   (R:ℂ)= ∑ x:G,(w x:ℂ) *
     (↑(∏ psi∈Delta,(1+(v psi*psi x).re)):ℂ):=by
    dsimp[R]
    push_cast
    rfl
   _=1+E:=l5
 have JM:R=1+E.re:=by
  have:=QA Complex.re Lw
  simpa using this
 change R≤1+q*(2:ℝ)^Delta.card
 calc
  R=1+E.re:=JM
  _≤1+ ‖E‖ :=Sr (le_refl 1) (Complex.re_le_norm E)
  _≤1+q*(2:ℝ)^Delta.card:=Sr (le_refl 1) JL
lemma cy.t8
  {S Delta:Finset (AddChar G ℂ)} {w:G→ℝ} {q:ℝ} {k:ℕ}
  (dQ:cy S Delta)
  (vm: ∀ x,0≤w x) (AK: ∑ x:G,w x=1)
  (x1:0≤q)
  (hq: ∀ psi,psi∉S→ ‖ay.cG w psi‖ ≤q)
  (ch:Delta.card≤k) (OG:q*(2:ℝ)^k≤1) :
  eV w 1 Delta:=by
 intro v hv
 have HP:2^Delta.card≤2^k :=
  QR (by norm_num) ch
 have hpow:(2:ℝ)^Delta.card≤(2:ℝ)^k:=by
  exact_mod_cast HP
 have uU:q*(2:ℝ)^Delta.card≤1 :=
  (iO hpow x1).trans OG
 calc
  ∑ x:G,w x* ∏ psi∈Delta,(1+(v psi*psi x).re) ≤
    1+q*(2:ℝ)^Delta.card :=
   dQ.ob vm AK x1 hq v hv
  _≤2:=by linarith
  _≤exp 1:=Real.exp_one_gt_two.le
lemma cy.k0
  {S Delta:Finset (AddChar G ℂ)} {w:G→ℝ} {q:ℝ} {k:ℕ}
  (dQ:cy S Delta)
  (vm: ∀ x,0≤w x) (AK: ∑ x:G,w x=1)
  (x1:0≤q)
  (hq: ∀ psi,psi∉S→ ‖ay.cG w psi‖ ≤q)
  (ch:Delta.card≤k) (Dg:q≤(1/4:ℝ)^k) :
  eV w 1 Delta:=by
 apply dQ.t8 vm AK x1 hq ch
 calc
  q*(2:ℝ)^k≤(1/4:ℝ)^k*(2:ℝ)^k :=
   Qi Dg (QH (by norm_num) _)
  _=(1/2:ℝ)^k:=by rw[←QL]; congr 1; norm_num
  _≤1:=Uy (by norm_num) (by norm_num)
lemma ng (A:Finset G) :
  (0:AddChar G ℂ)∈ay.c5.cj A (1/2:ℝ):=by
 rw[ay.c5.gm]
 simp[ay.c5.c6]
 have ch:(0:ℝ)≤A.card:=by exact_mod_cast Nat.zero_le A.card
 nlinarith
lemma ks {A:Finset G} {eta:ℝ}
  {psi:AddChar G ℂ}
  (cT:psi∈ay.c5.cj A eta) :
  -psi∈ay.c5.cj A eta:=by
 rw[ay.c5.gm] at cT ⊢
 have hsum:ay.c5.c6 A (-psi) =
   conj (ay.c5.c6 A psi):=by
  unfold ay.c5.c6
  rw[RK]
  apply Io rfl
  intro x hx
  rw[U2,TV]
 rw[hsum,RCLike.norm_conj]
 exact cT
end ay.aI
end
end
section
open Finset
open scoped BigOperators
namespace ay.jM
variable {G:Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
omit [AddCommGroup G] in
lemma f2
  {B X:Finset G} (t9:X⊆B) {w:G→ℝ} {c:ℝ}
  (hw: ∀ x∈B,w x=c) :
  ∑ x:G,bs X x*w x=c*X.card:=by
 classical
 calc
  ∑ x:G,bs X x*w x= ∑ x∈X,c:=by
   rw[←Ro (s₁:=X) (s₂:=Finset.univ)]
   ·apply Io rfl
    intro x hx
    simp[bs,hx,hw x (t9 hx)]
   ·simp
   ·intro x MC G9
    simp[bs,G9]
  _=c*X.card:=by simp[Qx]
lemma jg
  {B X:Finset G} (t9:X⊆B) {w:G→ℝ} {c:ℝ}
  (hw: ∀ x∈B,w x=c) (psi:AddChar G ℂ) :
  ∑ x:G,((bs X x*w x:ℝ):ℂ)*psi x =
   (c:ℂ)*c5.c6 X psi:=by
 classical
 calc
  ∑ x:G,((bs X x*w x:ℝ):ℂ)*psi x =
    ∑ x∈X,(c:ℂ)*psi x:=by
   rw[←Ro (s₁:=X) (s₂:=Finset.univ)]
   ·apply Io rfl
    intro x hx
    simp[bs,hx,hw x (t9 hx)]
   ·simp
   ·intro x MC G9
    simp[bs,G9]
  _=(c:ℂ)*c5.c6 X psi:=by
   rw[c5.c6,Qj]
lemma kk
  {B X:Finset G} (t9:X⊆B) {w:G→ℝ} {c:ℝ}
  (hw: ∀ x∈B,w x=c) (hc:0<c)
  (eta:ℝ) (psi:AddChar G ℂ) :
  psi∈aI.fO w (bs X) eta ↔
   psi∈c5.cj X eta:=by
 classical
 rw[aI.lN,c5.gm]
 rw[f2 t9 hw]
 rw[jg t9 hw]
 rw[QO,Rf,QK,RT hc]
 constructor
 ·intro h
  have hh:c*(eta*(X.card:ℝ)) ≤
    c* ‖c5.c6 X psi‖ :=by
   calc
    c*(eta*(X.card:ℝ))=eta*(c*(X.card:ℝ)):=by ring
    _≤c* ‖c5.c6 X psi‖ :=h
  nlinarith
 ·intro h
  calc
   eta*(c*(X.card:ℝ))=c*(eta*(X.card:ℝ)):=by ring
   _≤c* ‖c5.c6 X psi‖ :=
    iO h hc.le
end ay.jM
end
section
noncomputable section
open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal
namespace ay.aI
variable {G:Type*} [Fintype G] [AddCommGroup G]
omit [AddCommGroup G] in
lemma j4
  (w:G→ℝ) (hw: ∀ x,0≤w x) (AL: ∑ x:G,w x=1)
  (f:G→ℝ) :
  exp (∑ x:G,w x*f x)≤ ∑ x:G,w x*exp (f x):=by
 have h:=convexOn_exp.map_sum_le (t:=(Finset.univ:Finset G))
  (p:=f) (fun x _↦hw x) (by simpa using AL)
  (fun x _↦Set.mem_univ (f x))
 simpa using h
lemma sZ
  (mu:G→ℝ) (K:ℝ) (Delta:Finset (AddChar G ℂ))
  (AM: ∀ x,0≤ mu x)
  (dQ:eV mu K Delta)
  (c:AddChar G ℂ→ℂ) :
  ∑ x:G,mu x*exp ((∑ psi∈Delta,c psi*psi x).re) ≤
   exp (K+(∑ psi∈Delta, ‖c psi‖ ^2)/2):=by
 have l5 (z:ℂ) :
   exp z.re≤cosh ‖z‖ +(z/ ‖z‖).re*sinh ‖z‖ :=by
  calc
   _=exp ((z/ ‖z‖).re* ‖z‖):=by
    obtain rfl | hz:=Tf z 0<;>simp[*]
   _≤_:=exp_mul_le_cosh_add_mul_sinh
    (by simpa using z.abs_re_div_norm_le_one) _
 choose u hu OH using fun psi↦Complex.exists_norm_mul_eq_self (c psi)
 have Jv (psi:AddChar G ℂ):u psi≠0:=fun h↦by
  simpa[h] using hu psi
 have gX (x:G) :
   exp ((∑ psi∈Delta,c psi*psi x).re) ≤
    ∏ psi∈Delta,
     (cosh ‖c psi‖ +(u psi*sinh ‖c psi‖ *psi x).re):=by
  calc
   exp ((∑ psi∈Delta,c psi*psi x).re) =
     ∏ psi∈Delta,exp ((c psi*psi x).re):=by
      simp_rw[←exp_sum, ←Complex.re_sum]
   _≤ ∏ psi∈Delta,
     (cosh ‖c psi*psi x‖ +
      ((c psi*psi x)/ ‖c psi*psi x‖).re *
       sinh ‖c psi*psi x‖):=by
    gcongr with psi cT
    exact l5 _
   _= ∏ psi∈Delta,
     (cosh ‖c psi‖ +
      (u psi*(c psi*psi x)/(u psi* ↑‖c psi‖)).re *
       sinh ‖c psi‖):=by
    apply prod_congr rfl
    intro psi cT
    rw[QO,Q0,Q3,
     mul_div_mul_left _ _ (Jv psi)]
   _= ∏ psi∈Delta,
     (cosh ‖c psi‖ +(u psi*sinh ‖c psi‖ *psi x).re):=by
    apply prod_congr rfl
    intro psi cT
    obtain hc | hc:=Tf (c psi) 0
    ·simp[hc]
    simp only[OH,Q6 (u psi),SH _ hc,
     ←Complex.re_mul_ofReal,QN]
 let q:AddChar G ℂ→ℝ:=fun psi↦sinh ‖c psi‖ /cosh ‖c psi‖
 let v:AddChar G ℂ→ℂ:=fun psi↦(q psi:ℂ)*u psi
 have n6 (x:G) :
   (∏ psi∈Delta,
     (cosh ‖c psi‖ +(u psi*sinh ‖c psi‖ *psi x).re)) =
    (∏ psi∈Delta,cosh ‖c psi‖) *
     (∏ psi∈Delta,
      (1+(v psi*psi x).re)):=by
  rw[←TW]
  apply prod_congr rfl
  intro psi cT
  have Px:cosh ‖c psi‖ ≠0:=Uq (cosh_pos _)
  have F8 :
    (u psi*(sinh ‖c psi‖ :ℂ)*psi x).re =
     sinh ‖c psi‖ *(u psi*psi x).re:=by
   rw[show u psi*(sinh ‖c psi‖ :ℂ)*psi x =
     (sinh ‖c psi‖ :ℂ)*(u psi*psi x) by ring]
   exact Un _ _
  have Lx:(v psi*psi x).re=q psi*(u psi*psi x).re:=by
   rw[show v psi*psi x=(q psi:ℂ)*(u psi*psi x) by
    simp[v]; ring]
   exact Un _ _
  rw[F8,Lx]
  dsimp[q]
  field_simp
 calc
  ∑ x:G,mu x*exp ((∑ psi∈Delta,c psi*psi x).re) ≤
    ∑ x:G,mu x* ∏ psi∈Delta,
     (cosh ‖c psi‖ +(u psi*sinh ‖c psi‖ *psi x).re):=by
   apply sum_le_sum
   intro x hx
   exact iO (gX x) (AM x)
  _=(∏ psi∈Delta,cosh ‖c psi‖) *
    (∑ x:G,mu x *
     ∏ psi∈Delta,
      (1+(v psi*psi x).re)):=by
   rw[Qj]
   apply sum_congr rfl
   intro x hx
   rw[n6]
   ring
  _≤(∏ psi∈Delta,cosh ‖c psi‖)*exp K:=by
   gcongr
   apply dQ v
   intro psi cT
   have hq: |q psi| ≤1:=by
    simpa[q,Real.tanh_eq_sinh_div_cosh] using(Real.abs_tanh_lt_one ‖c psi‖).le
   simpa[v,QO,hu psi,Rf,QK] using hq
  _≤exp ((∑ psi∈Delta, ‖c psi‖ ^2)/2)*exp K:=by
   apply Qi _ (exp_pos _).le
   calc
    ∏ psi∈Delta,cosh ‖c psi‖ ≤
      ∏ psi∈Delta,exp (‖c psi‖ ^2/2):=by
     gcongr with psi cT
     exact cosh_le_exp_half_sq _
    _=exp ((∑ psi∈Delta, ‖c psi‖ ^2)/2):=by
     simp_rw[←exp_sum, ←sum_div]
  _=exp (K+(∑ psi∈Delta, ‖c psi‖ ^2)/2):=by
   rw[←exp_add]
   congr 1
   ring
lemma iQ
  (mu f:G→ℝ) (K eta:ℝ) (Delta:Finset (AddChar G ℂ))
  (AM: ∀ x,0≤ mu x) (OI: ∀ x,0≤f x)
  (Jd: ∀ x,f x≤1)
  (fC:0<eta)
  (dQ:eV mu K Delta)
  (l0:Delta⊆fO mu f eta)
  (ft:0< ∑ x:G,f x*mu x) :
  (Delta.card:ℝ) ≤
   2*(K+log ((∑ x:G,f x*mu x)⁻¹))/eta^2:=by
 let a:ℝ:= ∑ x:G,f x*mu x
 have ha:0<a:=by simpa[a] using ft
 let spec:AddChar G ℂ→ℂ:=fun psi ↦
  ∑ x:G,(f x*mu x:ℝ)*psi x
 choose u hu JN using fun psi:AddChar G ℂ ↦
  Complex.exists_norm_eq_mul_self (spec psi)
 let c:AddChar G ℂ→ℂ:=fun psi↦(eta:ℂ)*u psi
 let P:G→ℝ:=fun x↦(∑ psi∈Delta,c psi*psi x).re
 have HQ (psi:AddChar G ℂ): ‖c psi‖ ^2=eta^2:=by
  simp[c,hu,RT fC]
 have Ly: ∑ psi∈Delta, ‖c psi‖ ^2=eta^2*Delta.card:=by
  simp_rw[HQ]
  simp
  ring
 have F9 :
   ∑ x:G,((f x*mu x:ℝ):ℂ) *
     (∑ psi∈Delta,c psi*psi x) =
    (eta:ℂ)* ∑ psi∈Delta,(‖spec psi‖ :ℂ):=by
  calc
   ∑ x:G,((f x*mu x:ℝ):ℂ) *
     (∑ psi∈Delta,c psi*psi x) =
     ∑ psi∈Delta,
      c psi* ∑ x:G,((f x*mu x:ℝ):ℂ)*psi x:=by
    simp_rw[Qj]
    rw[QD]
    apply sum_congr rfl
    intro psi cT
    apply sum_congr rfl
    intro x hx
    ring
   _= ∑ psi∈Delta,(eta:ℂ)*(‖spec psi‖ :ℂ):=by
    apply sum_congr rfl
    intro psi cT
    dsimp[c,spec]
    rw[Qo, ←JN]
   _=(eta:ℂ)* ∑ psi∈Delta,(‖spec psi‖ :ℂ):=by
    rw[Qj]
 have JO :
   ∑ x:G,f x*mu x*P x =
    eta* ∑ psi∈Delta, ‖spec psi‖ :=by
  have JM:=QA Complex.re F9
  calc
   ∑ x:G,f x*mu x*P x =
     (∑ x:G,((f x*mu x:ℝ):ℂ) *
      (∑ psi∈Delta,c psi*psi x)).re:=by
    simp[P,Complex.re_sum,Complex.mul_re]
   _=((eta:ℂ) *
     ∑ psi∈Delta,(‖spec psi‖ :ℂ)).re:=JM
   _=eta* ∑ psi∈Delta, ‖spec psi‖ :=by simp
 have BN :
   eta^2*a*Delta.card≤ ∑ x:G,f x*mu x*P x:=by
  rw[JO]
  calc
   eta^2*a*(Delta.card:ℝ) =
     ∑ psi∈Delta,eta*(eta*a):=by
    simp
    ring
   _≤ ∑ psi∈Delta,eta* ‖spec psi‖ :=by
    gcongr with psi cT
    have hs:=lN.mp (l0 cT)
    simpa[a,spec] using hs
   _=eta* ∑ psi∈Delta, ‖spec psi‖ :=by
    rw[Qj]
 let w:G→ℝ:=fun x↦f x*mu x/a
 have vm: ∀ x,0≤w x:=by
  intro x
  exact RS (Qn (OI x) (AM x)) ha.le
 have AL: ∑ x:G,w x=1:=by
  dsimp[w]
  rw[←TP]
  dsimp[a]
  exact div_self ha.ne'
 have HR:eta^2*Delta.card≤ ∑ x:G,w x*P x:=by
  calc
   eta^2*(Delta.card:ℝ) ≤
     (∑ x:G,f x*mu x*P x)/a:=by
    rw[Qs ha]
    calc
     eta^2*(Delta.card:ℝ)*a =
       eta^2*a*(Delta.card:ℝ):=by ring
     _≤_:=BN
   _= ∑ x:G,w x*P x:=by
    dsimp[w]
    rw[TP]
    apply sum_congr rfl
    intro x hx
    ring
 have HS :
   exp (eta^2*Delta.card) ≤
    ∑ x:G,w x*exp (P x):=by
  calc
   exp (eta^2*Delta.card)≤exp (∑ x:G,w x*P x):=by
    exact Real.exp_le_exp.mpr HR
   _≤_:=j4 w vm AL P
 have AN :
   ∑ x:G,w x*exp (P x) ≤
    a⁻¹ * ∑ x:G,mu x*exp (P x):=by
  dsimp[w]
  rw[Qj]
  apply sum_le_sum
  intro x hx
  rw[Ri]
  calc
   a⁻¹ *(f x*mu x)*exp (P x) ≤
     a⁻¹ *(1*mu x)*exp (P x):=by
    apply Qi _ (exp_pos _).le
    apply iO _ (inv_nonneg.mpr ha.le)
    exact Qi (Jd x) (AM x)
   _=a⁻¹ *(mu x*exp (P x)):=by ring
 have JP :
   ∑ x:G,mu x*exp (P x) ≤
    exp (K+eta^2*Delta.card/2):=by
  have hr:=sZ mu K Delta AM dQ c
  simpa[P,Ly] using hr
 have ua :
   exp (eta^2*Delta.card) ≤
    a⁻¹ *exp (K+eta^2*Delta.card/2) :=
  HS.trans (AN.trans
   (iO JP (inv_nonneg.mpr ha.le)))
 have hmul :
   a*exp (eta^2*Delta.card) ≤
    exp (K+eta^2*Delta.card/2):=by
  calc
   a*exp (eta^2*Delta.card) ≤
     a*(a⁻¹ *exp (K+eta^2*Delta.card/2)):=by
    gcongr
   _=exp (K+eta^2*Delta.card/2):=by
    field_simp
 have Cc :
   log a+eta^2*Delta.card ≤
    K+eta^2*Delta.card/2:=by
  rw[←exp_log ha, ←exp_add] at hmul
  exact Real.exp_le_exp.mp hmul
 have HT:0<eta^2:=SY fC
 rw[Qs HT]
 rw[log_inv]
 nlinarith
lemma jV
  (B X:Finset G) (t9:X⊆B) (hX:X.Nonempty)
  (w:G→ℝ) (c R eta:ℝ)
  (vm: ∀ x,0≤w x) (hw: ∀ x∈B,w x=c)
  (hc:0<c) (hR:(c*X.card)⁻¹ ≤R)
  (fC:0<eta) (Delta:Finset (AddChar G ℂ))
  (dQ:eV w 1 Delta)
  (l0:Delta⊆c5.cj X eta) :
  (Delta.card:ℝ)≤2*(1+log R)/eta^2:=by
 classical
 have AO :
   ∑ x:G,bs X x*w x=c*X.card :=
  jM.f2 t9 hw
 have ft:0< ∑ x:G,bs X x*w x:=by
  rw[AO]
  have Ew:(0:ℝ)<X.card:=by exact_mod_cast hX.card_pos
  positivity
 have Lz:Delta ⊆
   fO w (bs X) eta:=by
  intro psi cT
  exact(jM.kk
   t9 hw hc eta psi).2 (l0 cT)
 have oM:=iQ
  w (bs X) 1 eta Delta vm
  (by intro x; unfold bs; split<;>norm_num)
  (by intro x; unfold bs; split<;>norm_num)
  fC dQ Lz ft
 have Ga :
   ((∑ x:G,bs X x*w x)⁻¹)≤R:=by
  simpa[AO] using hR
 have eu :
   log ((∑ x:G,bs X x*w x)⁻¹)≤log R :=
  QG (inv_pos.mpr ft) Ga
 calc
  (Delta.card:ℝ) ≤
    2*(1+log ((∑ x:G,bs X x*w x)⁻¹)) /
     eta^2:=by simpa using oM
  _≤2*(1+log R)/eta^2:=by
   gcongr
omit [Fintype G] in
lemma oc [Finite G]
  (S T:Finset (AddChar G ℂ)) (hzero:0∈S)
  (eY: ∀ s∈S, -s∈S) (D:ℝ) (k:ℕ)
  (JQ:D<k)
  (oM: ∀ Gamma,Gamma⊆T→cy S Gamma →
   Gamma.card≤k→(Gamma.card:ℝ)≤D) :
  ∃ Delta:Finset (AddChar G ℂ),
   Delta⊆T∧(Delta.card:ℝ)≤D ∧
    ∀ psi∈T, ∃ z∈Delta.addSpan, ∃ s∈S,psi=z+s:=by
 let:=Fintype.ofFinite G
 classical
 obtain ⟨Delta,ub,zm,j5⟩ :=
  nO S T hzero eY
 have fH:Delta.card≤k:=by
  by_contra hnot
  have HU:k≤Delta.card:=Nat.le_of_not_ge hnot
  obtain ⟨Gamma,w5,rD⟩ :=
   Finset.exists_subset_card_eq HU
  have zn:= oM Gamma (w5.trans ub)
   (zm.mono w5) (by simp[rD])
  rw[rD] at zn
  exact(not_le_of_gt JQ) zn
 exact ⟨Delta,ub,oM Delta ub zm fH,j5⟩
def bf (B:aj G) (X:Finset G) (eta:ℝ):ℝ :=
 2*(1+log (2*(B.Zc.card:ℝ)/X.card))/eta^2
def dg (B:aj G) (X:Finset G) (eta:ℝ):ℕ :=
 ⌈bf B X eta⌉₊+1
def cJ (B:aj G) (X:Finset G)
  (eta:ℝ):NNReal :=
 (100*((max B.rank 1:ℕ):NNReal) *
  (((2*dg B X eta+1:ℕ):NNReal)))⁻¹
lemma mV
  (B:aj G) (rE:B.a1)
  (X:Finset G) (hX:X.Nonempty) (t9:X⊆B.Zc)
  (eta:ℝ) (fC:0<eta) :
  ∃ a8:NNReal, ∃ C:aj G,
   ∃ Delta:Finset (AddChar G ℂ),
    1/2≤a8∧a8≤1 ∧
    C=B.ai (a8*cJ B X eta) ∧
    C.a1 ∧
    (Delta.card:ℝ)≤bf B X eta ∧
    Delta⊆c5.cj X eta ∧
    ∀ psi∈c5.cj X eta,
     ∃ z∈Delta.addSpan,
      ∃ s∈c5.cj C.Zc (1/2),psi=z+s:=by
 classical
 let D:ℝ:=bf B X eta
 let k:ℕ:=dg B X eta
 let d:ℕ:=max B.rank 1
 let a:NNReal:=cJ B X eta
 obtain ⟨a8,gI,lf,xt⟩ :=
  (B.ai a).eP
 let tau:NNReal:=a8*a
 let C:aj G:=B.ai tau
 have ta:C.a1:=by
  simpa[C,tau] using xt
 have hd:0<d:=by simp[d]
 have hk:0<k:=by simp[k,dg]
 have ha:a =
   (100*(d:NNReal)*(((2*k+1:ℕ):NNReal)))⁻¹ :=by
  simp[a,cJ,d,k]
 have dV:(((2*k:ℕ):NNReal)*tau) ≤
   1/(100*(d:NNReal)):=by
  have LA:(0:NNReal)<(((2*k+1:ℕ):NNReal)):=by positivity
  have N0:(0:NNReal)<100*(d:NNReal):=by positivity
  calc
   (((2*k:ℕ):NNReal)*tau) =
     ((2*k:ℕ):NNReal)*(a8*a):=rfl
   _≤((2*k:ℕ):NNReal)*(1*a):=by gcongr
   _=(((2*k:ℕ):NNReal) /
     (((2*k+1:ℕ):NNReal))) /
      (100*(d:NNReal)):=by rw[ha]; field_simp
   _≤1/(100*(d:NNReal)):=by
    gcongr
    exact(Q9 LA).2 (by
     exact_mod_cast Nat.le_add_right (2*k) 1)
 let T:Finset (AddChar G ℂ):=c5.cj X eta
 let S:Finset (AddChar G ℂ) :=
  c5.cj C.Zc (1/2)
 let w:G→ℝ:=ay.ed B tau (2*k)
 let outer:Finset G :=
  (B.ai (1+(((2*k:ℕ):NNReal)*tau))).Zc
 let c:ℝ:=(outer.card:ℝ)⁻¹
 let R:ℝ:=2*(B.Zc.card:ℝ)/X.card
 have vm: ∀ x,0≤w x:=by
  intro x
  exact ay.qw B tau (2*k) x
 have AK: ∑ x:G,w x=1:=by
  exact ay.sm B tau (2*k)
 have HV: ∀ x∈B.Zc,w x=c:=by
  intro x hx
  simpa[w,c,outer] using
   (ay.nc B tau (2*k) hx)
 have Dh:outer.card≤2*B.Zc.card:=by
  simpa[outer,d] using
   (ay.oJ rE (2*k) dV)
 have EC:0<outer.card:=by
  exact outer.card_pos.mpr (by
   simpa[outer] using
    (B.ai (1+(((2*k:ℕ):NNReal)*tau))).aE)
 have hc:0<c:=by
  dsimp[c]
  positivity
 have hR:(c*X.card)⁻¹ ≤R:=by
  have hOr:(0:ℝ)<outer.card:=by exact_mod_cast EC
  have OJ:(0:ℝ)<X.card:=by exact_mod_cast hX.card_pos
  have Nd:(outer.card:ℝ)≤2*B.Zc.card:=by
   exact_mod_cast Dh
  calc
   (c*(X.card:ℝ))⁻¹ =(outer.card:ℝ)/X.card:=by
    dsimp[c]
    field_simp
   _≤(2*B.Zc.card:ℝ)/X.card :=
    (R9 OJ).2 Nd
   _=R:=by simp[R]
 have hzero:(0:AddChar G ℂ)∈S:=by
  exact ng C.Zc
 have eY: ∀ s∈S, -s∈S:=by
  intro s hs
  exact ks hs
 have JQ:D<(k:ℝ):=by
  calc
   D≤(⌈D⌉₊:ℝ):=Rr D
   _<((⌈D⌉₊+1:ℕ):ℝ):=by
    exact_mod_cast Tr ⌈D⌉₊
   _=(k:ℝ):=by simp[k,dg,D]
 have oM: ∀ Gamma,Gamma⊆T→cy S Gamma →
   Gamma.card≤k→(Gamma.card:ℝ)≤D:=by
  intro Gamma HW ED rD
  have hq: ∀ psi,psi∉S →
    ‖ay.cG w psi‖ ≤(1/2:ℝ)^(2*k):=by
   intro psi cT
   calc
    ‖ay.cG w psi‖ ≤
      ‖ay.cG
       (af (B.ai tau).Zc) psi‖ ^(2*k):=by
     exact ay.lu
      B tau (2*k) psi
    _≤(1/2:ℝ)^(2*k):=by
     gcongr
     exact(ay.fy
      (B.ai tau) psi (by simpa[S,C] using cT)).le
  have qv:eV w 1 Gamma:=by
   apply ED.k0
    vm AK (by positivity) hq rD
   rw[QU]
   norm_num
  have ch:=jV
   B.Zc X t9 hX w c R eta vm HV hc hR fC Gamma
    qv (by simpa[T] using HW)
  simpa[D,bf,R] using ch
 obtain ⟨Delta,ub,fH,j5⟩ :=
  oc S T hzero eY D k JQ oM
 refine ⟨a8,C,Delta,gI,lf, ?_,ta, ?_, ?_, ?_⟩
 ·simp[C,tau,a]
 ·simpa[D] using fH
 ·simpa[T] using ub
 ·simpa[T,S] using j5
end ay.aI
end
end
section
open Finset Function Real
open scoped BigOperators NNReal
namespace ay.jm
variable {G:Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
noncomputable def aP (psi:AddChar G ℂ):Zg G:=by
  let e:=AddCircle.homeomorphCircle (by norm_num:(1:ℝ)≠0)
  exact
    { toFun:=fun x↦e.symm ((AddChar.circleEquivComplex.symm psi) x)
      map_zero':=by
        apply e.injective
        simp[e,QY]
      map_add':=by
        intro x y
        apply e.injective
        rw[e.apply_symm_apply]
        rw[show e (e.symm ((AddChar.circleEquivComplex.symm psi) x) +
              e.symm ((AddChar.circleEquivComplex.symm psi) y)) =
            AddCircle.toCircle (e.symm ((AddChar.circleEquivComplex.symm psi) x) +
              e.symm ((AddChar.circleEquivComplex.symm psi) y)) by
              exact QY _ _]
        rw[Ub]
        rw[←QY (by norm_num:(1:ℝ)≠0),
          e.apply_symm_apply]
        rw[←QY (by norm_num:(1:ℝ)≠0),
          e.apply_symm_apply]
        exact St _ _ _ }
omit [DecidableEq G] in
lemma qy (psi:AddChar G ℂ) (x:G) :
  AddCircle.toCircle (aP psi x) =
   (AddChar.circleEquivComplex.symm psi) x:=by
 rw[←QY (by norm_num:(1:ℝ)≠0)]
 simp[aP]
omit [DecidableEq G] in
lemma eE (psi:AddChar G ℂ) (x:G) :
  (AddCircle.toCircle (aP psi x):ℂ)=psi x:=by
 classical
 rw[qy]
 exact S6 (AddChar.circleEquivComplex.apply_symm_apply psi) x
omit [DecidableEq G] in
lemma pR :
  Function.Injective (aP (G:=G)):=by
 intro psi fJ h
 ext x
 have hx:=S6 h x
 have hh:=QA (fun z:AddCircle (1:ℝ)↦(AddCircle.toCircle z:ℂ)) hx
 simpa only[eE] using hh
noncomputable def ga :
  AddChar G ℂ→+ Zg G where
 toFun:=aP
 map_zero':=by
  ext x
  apply TD (by norm_num:(1:ℝ)≠0)
  apply RI
  simp[eE]
 map_add' psi fJ:=by
  ext x
  apply TD (by norm_num:(1:ℝ)≠0)
  apply RI
  simp[eE,Ub,
   U3]
noncomputable def nG (Delta:Finset (AddChar G ℂ)) (r:ℝ≥0) :
  aj G where
 eX:=Delta.image aP
 width:=fun _↦r
omit [DecidableEq G] in
@[simp] lemma pD (Delta:Finset (AddChar G ℂ)) (r:ℝ≥0)
  (gamma:Zg G) :
  (nG Delta r).width gamma=r:=rfl
omit [DecidableEq G] in
lemma iC
  {Delta:Finset (AddChar G ℂ)} {r:ℝ≥0} {psi:AddChar G ℂ} {x:G}
  (hx:x∈(nG Delta r).Zc)
  (cT:psi∈Delta.addSpan) :
  ‖aP psi x‖ ≤(Delta.card:ℝ)*(r:ℝ):=by
 classical
 rw[Finset.mem_addSpan] at cT
 obtain ⟨epsilon,eM,hsum⟩:=cT
 have HX :
   ∑ gamma∈Delta,epsilon gamma•aP gamma =
    aP psi:=by
  change ∑ gamma∈Delta,epsilon gamma•ga gamma=ga psi
  calc
   ∑ gamma∈Delta,epsilon gamma•ga gamma =
     ∑ gamma∈Delta,ga (epsilon gamma•gamma):=by
      apply sum_congr rfl
      intro gamma k1
      exact(map_zsmul ga (epsilon gamma) gamma).symm
   _=ga (∑ gamma∈Delta,epsilon gamma•gamma):=by
    exact(RK ga (fun gamma↦epsilon gamma•gamma) Delta).symm
   _=ga psi:=QA ga hsum
 have EE :
   (∑ gamma∈Delta,epsilon gamma•aP gamma) x =
    ∑ gamma∈Delta,(epsilon gamma•aP gamma) x:=by
  induction Delta using Finset.induction_on with
  | empty=>simp
  | @insert gamma Delta k1 ih=>simp[k1]
 rw[←HX,EE]
 calc
  ‖∑ gamma∈Delta,(epsilon gamma•aP gamma) x‖ ≤
    ∑ gamma∈Delta, ‖(epsilon gamma•aP gamma) x‖ :=
   Rq _ _
  _≤ ∑ _gamma∈Delta,(r:ℝ):=by
   apply sum_le_sum
   intro gamma k1
   have CQ:aP gamma∈(nG Delta r).eX:=by
    exact Finset.mem_image.mpr ⟨gamma,k1,rfl⟩
   have d5:=(aj.Zm _ _).mp hx
    (aP gamma) CQ
   have hw: ‖aP gamma x‖ ≤(r:ℝ):=by
    simpa only[pD] using d5
   rcases eM gamma with eY | hzero | JR
   ·simpa[eY] using hw
   ·simp[hzero]
   ·simpa[JR] using hw
  _=(Delta.card:ℝ)*(r:ℝ):=by simp
noncomputable def cD (B:aj G)
    (Delta:Finset (AddChar G ℂ)) (aF r:ℝ≥0):aj G:=by
  classical
  let Cl:=Delta.image aP
  exact
    { eX:=B.eX∪Cl
      width:=fun gamma ↦
        if gamma∈B.eX then
          if gamma∈Cl then min (aF*B.width gamma) r
          else aF*B.width gamma
        else r }
omit [DecidableEq G] in
lemma vz (B:aj G)
  (Delta:Finset (AddChar G ℂ)) (aF r:ℝ≥0) :
  (cD B Delta aF r).rank≤B.rank+Delta.card:=by
 classical
 rw[aj.rank,aj.rank,cD]
 exact(Finset.card_union_le _ _).trans_eq (by
  rw[Finset.card_image_iff.mpr pR.injOn])
omit [DecidableEq G] in
lemma fD (B:aj G)
    (Delta:Finset (AddChar G ℂ)) (aF r:ℝ≥0) :
    (cD B Delta aF r).Zc⊆(B.ai aF).Zc:=by
  classical
  intro x hx
  rw[aj.Zm] at hx ⊢
  intro gamma k1
  have y1:gamma∈B.eX:=by simpa using k1
  have AQ:gamma∈B.eX∪Delta.image aP :=
    Um _ y1
  have hbound:=hx gamma (by simpa[cD] using AQ)
  by_cases AR:gamma∈Delta.image aP
  · change ‖gamma x‖ ≤
      (((if gamma∈B.eX then
          if gamma∈Delta.image aP then
            min (aF*B.width gamma) r else aF*B.width gamma
        else r):ℝ≥0):ℝ) at hbound
    rw[RP y1,RP AR] at hbound
    simpa only[aj.oC,SK] using
      hbound.trans (by exact_mod_cast(Uv (aF*B.width gamma) r))
  · change ‖gamma x‖ ≤
      (((if gamma∈B.eX then
          if gamma∈Delta.image aP then
            min (aF*B.width gamma) r else aF*B.width gamma
        else r):ℝ≥0):ℝ) at hbound
    rw[RP y1,if_neg AR] at hbound
    simpa only[aj.oC,SK] using hbound
omit [DecidableEq G] in
lemma gb (B:aj G)
  (Delta:Finset (AddChar G ℂ)) (aF r:ℝ≥0) :
  (cD B Delta aF r).Zc⊆(nG Delta r).Zc:=by
 classical
 intro x hx
 rw[aj.Zm] at hx ⊢
 intro gamma k1
 rw[pD]
 obtain ⟨psi,cT,rfl⟩:=Finset.mem_image.mp k1
 have AR:aP psi∈Delta.image aP :=
  Finset.mem_image.mpr ⟨psi,cT,rfl⟩
 have AQ:aP psi∈B.eX∪Delta.image aP :=
  Ua _ AR
 have hbound:=hx (aP psi) (by simpa[cD] using AQ)
 by_cases hold:aP psi∈B.eX
 ·change ‖aP psi x‖ ≤
   (((if aP psi∈B.eX then
     if aP psi∈Delta.image aP then
      min (aF*B.width (aP psi)) r
     else aF*B.width (aP psi)
    else r):ℝ≥0):ℝ) at hbound
  rw[RP hold,RP AR] at hbound
  exact hbound.trans (by
   exact_mod_cast(min_le_right (aF*B.width (aP psi)) r))
 ·change ‖aP psi x‖ ≤
   (((if aP psi∈B.eX then
     if aP psi∈Delta.image aP then
      min (aF*B.width (aP psi)) r
     else aF*B.width (aP psi)
    else r):ℝ≥0):ℝ) at hbound
  rw[if_neg hold] at hbound
  exact hbound
omit [DecidableEq G] in
lemma gZ
  (B:aj G) {Delta:Finset (AddChar G ℂ)} {aF r:ℝ≥0}
  {psi:AddChar G ℂ} {x:G}
  (hx:x∈(cD B Delta aF r).Zc)
  (cT:psi∈Delta.addSpan) :
  ‖aP psi x‖ ≤(Delta.card:ℝ)*(r:ℝ) :=
 iC
  (gb B Delta aF r hx) cT
omit [DecidableEq G] in
lemma lR
  (psi:AddChar G ℂ) (x:G)
  (JS: ‖aP psi x‖ ≤(2*Real.pi)⁻¹) :
  ‖1-psi x‖ ≤4*Real.pi* ‖aP psi x‖ :=by
 classical
 let a:ℝ:=AddCircle.equivIoc (1:ℝ) (-1/2) (aP psi x)
 have EG:a∈Set.Ioc (-1/2) (-1/2+1) :=
  (AddCircle.equivIoc (1:ℝ) (-1/2) (aP psi x)).property
 have JT: |a| ≤1/2:=by
  rw[abs_le]
  constructor<;>linarith[EG.1,EG.2]
 have ts:(a:AddCircle (1:ℝ))=aP psi x:=by
  exact AddCircle.coe_equivIoc
 have Cm: ‖aP psi x‖ = |a| :=by
  rw[←ts]
  exact(Ts (1:ℝ) (by norm_num)).2 (by simpa using JT)
 have vT: ‖(2*Real.pi*a:ℂ)‖ =2*Real.pi* |a| :=by
  simp[QK,QC Real.pi_nonneg]
 have uV: ‖(2*Real.pi*a:ℂ)*Complex.I‖ ≤1:=by
  rw[QO,Complex.norm_I,Q3,vT, ←Cm]
  have Ai:0<2*Real.pi:=by positivity
  calc
   2*Real.pi* ‖aP psi x‖ ≤
     2*Real.pi*(2*Real.pi)⁻¹ :=
    iO JS Ai.le
   _=1:=by field_simp
 have l5:=Complex.norm_exp_sub_one_le uV
 have heval:psi x=Complex.exp ((2*Real.pi*a:ℂ)*Complex.I):=by
  rw[←eE psi x, ←ts]
  simp only[AddCircle.toCircle_apply_mk,Circle.coe_exp]
  congr 1
  push_cast
  field_simp
 rw[heval,norm_sub_rev]
 calc
  ‖Complex.exp ((2*Real.pi*a:ℂ)*Complex.I)-1‖
    ≤ 2* ‖(2*Real.pi*a:ℂ)*Complex.I‖ :=l5
  _=4*Real.pi* ‖aP psi x‖ :=by
   rw[QO,Complex.norm_I,Q3,vT,Cm]
   ring
omit [DecidableEq G] in
lemma jN
  (B:aj G) {Delta:Finset (AddChar G ℂ)} {aF r:ℝ≥0}
  {psi:AddChar G ℂ} {x:G}
  (dV:(Delta.card:ℝ)*(r:ℝ)≤(2*Real.pi)⁻¹)
  (hx:x∈(cD B Delta aF r).Zc)
  (cT:psi∈Delta.addSpan) :
  ‖1-psi x‖ ≤4*Real.pi*((Delta.card:ℝ)*(r:ℝ)):=by
 classical
 have JU:=gZ
  B hx cT
 calc
  ‖1-psi x‖ ≤4*Real.pi* ‖aP psi x‖ :=
   lR psi x (JU.trans dV)
  _≤4*Real.pi*((Delta.card:ℝ)*(r:ℝ)) :=
   iO JU (by positivity)
omit [DecidableEq G] in
lemma jh
  (B:aj G) {Delta Q S:Finset (AddChar G ℂ)} {aF r:ℝ≥0}
  {beta:ℝ} {x:G}
  (dV:(Delta.card:ℝ)*(r:ℝ)≤(2*Real.pi)⁻¹)
  (hx:x∈(cD B Delta aF r).Zc)
  (j5: ∀ psi∈Q, ∃ z∈Delta.addSpan, ∃ s∈S,psi=z+s)
  (EH: ∀ s∈S, ‖1-s x‖ ≤beta) :
  ∀ psi∈Q,
   ‖1-psi x‖ ≤4*Real.pi*((Delta.card:ℝ)*(r:ℝ))+beta:=by
 classical
 intro psi cT
 obtain ⟨z,hz,s,hs,rfl⟩:=j5 psi cT
 have HY :
   ‖1-z x‖ ≤4*Real.pi*((Delta.card:ℝ)*(r:ℝ)) :=
  jN B dV hx hz
 calc
  ‖1-(z+s) x‖ = ‖(1-z x)+z x*(1-s x)‖ :=by
   rw[U3]
   congr 1
   ring
  _≤ ‖1-z x‖ + ‖z x*(1-s x)‖ :=norm_add_le _ _
  _= ‖1-z x‖ + ‖1-s x‖ :=by
   rw[QO,Q0,QT]
  _≤4*Real.pi*((Delta.card:ℝ)*(r:ℝ))+beta :=
   Sr HY (EH s hs)
omit [DecidableEq G] in
lemma iY
  (C:aj G) (dF:C.a1)
  {Delta Q:Finset (AddChar G ℂ)} {sigma r:ℝ≥0}
  (iX:sigma ≤
   1/(100*(max C.rank 1:ℕ):ℝ≥0))
  (dV:(Delta.card:ℝ)*(r:ℝ)≤(2*Real.pi)⁻¹)
  (j5: ∀ psi∈Q, ∃ z∈Delta.addSpan,
   ∃ s∈c5.cj C.Zc (1/2),psi=z+s) :
  ∀ x∈(cD C Delta sigma r).Zc, ∀ psi∈Q,
   ‖1-psi x‖ ≤
    4*Real.pi*((Delta.card:ℝ)*(r:ℝ)) +
     400*((max C.rank 1:ℕ):ℝ)*(sigma:ℝ):=by
 classical
 intro x hx
 apply jh
  C dV hx j5
 intro s hs
 exact ay.kj
  dF iX hs (fD C Delta sigma r hx)
end ay.jm
end
section
open Finset
open scoped BigOperators NNReal
namespace ay.qz
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
open aj jm
def rF (m:Nat) (hm:0< m) (z:AddCircle (1:Real)):Fin m:=by
 have uc:0≤(cx z+1/2)*(m:Real):=by
  have hz:=(kZ z).1
  have qA:(0:Real)≤ m:=by positivity
  exact Qn (by linarith) qA
 refine ⟨⌊(cx z+1/2)*m⌋₊,(Uc uc).2 ?_⟩
 have hz:cx z+1/2<1:=by
  linarith[(kZ z).2]
 have qA:(0:Real)< m:=by exact_mod_cast hm
 exact(Sk hz qA).trans_eq (QT (m:Real))
lemma nQ
  {m:Nat} (hm:0< m) {z w:AddCircle (1:Real)}
  (lM:rF m hm z=rF m hm w) :
  ‖z-w‖ ≤1/(m:Real):=by
 let rz:=cx z
 let rw:=cx w
 let uz:=(rz+1/2)*(m:Real)
 let uw:=(rw+1/2)*(m:Real)
 have P1:0≤rz+1/2:=by
  dsimp[rz]
  linarith[(kZ z).1]
 have P2:0≤rw+1/2:=by
  dsimp[rw]
  linarith[(kZ w).1]
 have qA:(0:Real)< m:=by exact_mod_cast hm
 have OK:0≤uz:=by dsimp[uz]; positivity
 have OL:0≤uw:=by dsimp[uw]; positivity
 have vU:⌊uz⌋₊=⌊uw⌋₊:=by
  have q0:=QA Fin.val lM
  simpa only[rF,uz,uw,rz,rw] using q0
 have uW:((⌊uz⌋₊:Nat):Real)≤uz:=Ti OK
 have uX:uz<((⌊uz⌋₊:Nat):Real)+1:=RY uz
 have AS:((⌊uw⌋₊:Nat):Real)≤uw:=Ti OL
 have AT:uw<((⌊uw⌋₊:Nat):Real)+1:=RY uw
 have Di:(rz-rw)*(m:Real)<1:=by
  dsimp[uz,uw] at uW uX AS AT
  rw[vU] at uW uX
  nlinarith
 have Dj: -(1/(m:Real))<rz-rw:=by
  have hmul:(-1:Real)<(rz-rw)*(m:Real):=by
   dsimp[uz,uw] at uW uX AS AT
   rw[vU] at uW uX
   nlinarith
  have hdiv:(-1:Real)/(m:Real)<rz-rw :=
   (Tv qA).2 hmul
  simpa only[neg_div,R6] using hdiv
 have BO:rz-rw<1/(m:Real) :=
  (SP qA).2 Di
 calc
  ‖z-w‖ ≤ |rz-rw| :=gu z w
  _≤1/(m:Real):=(abs_lt.2 ⟨Dj,BO⟩).le
def Zs (Delta:Finset (AddChar G Complex))
  (m:Nat) (hm:0< m) (x:G):Delta→Fin m :=
 fun psi↦rF m hm (aP psi.1 x)
omit [DecidableEq G] in
lemma qB
    (B:aj G) (Delta:Finset (AddChar G Complex))
    (aF r:NNReal) (x:G) :
    x∈(cD B Delta aF r).Zc ↔
      x∈(B.ai aF).Zc ∧
        ∀ psi∈Delta, ‖aP psi x‖ ≤(r:Real):=by
  classical
  constructor
  · intro hx
    refine ⟨fD B Delta aF r hx, ?_⟩
    intro psi cT
    have JV:=gb B Delta aF r hx
    exact(aj.Zm _ _).mp JV (aP psi)
      (Finset.mem_image.mpr ⟨psi,cT,rfl⟩)
  · rintro ⟨hB,dQ⟩
    rw[aj.Zm] at hB ⊢
    intro gamma k1
    change gamma∈B.eX∪Delta.image aP at k1
    rw[Finset.mem_union] at k1
    change ‖gamma x‖ ≤
      (((if gamma∈B.eX then
          if gamma∈Delta.image aP then
            min (aF*B.width gamma) r
          else aF*B.width gamma
        else r):NNReal):Real)
    rcases k1 with vV | JW
    · by_cases Dk:gamma∈Delta.image aP
      · obtain ⟨psi,cT,EI⟩:=Finset.mem_image.mp Dk
        subst gamma
        rw[RP vV,RP Dk]
        exact le_min (hB _ vV) (dQ psi cT)
      · rw[RP vV,if_neg Dk]
        exact hB gamma vV
    · obtain ⟨psi,cT,EI⟩:=Finset.mem_image.mp JW
      subst gamma
      by_cases vV:aP psi∈B.eX
      · rw[RP vV,RP JW]
        exact le_min (hB _ vV) (dQ psi cT)
      · rw[if_neg vV]
        exact dQ psi cT
omit [DecidableEq G] in
private lemma mw
  (B:aj G) (Delta:Finset (AddChar G Complex))
  (aF:NNReal) {m:Nat} (hm:0< m)
  (S:Finset G) (hS:S⊆(B.ai aF).Zc)
  {x y:↥S} (nd:Zs Delta m hm x.1=Zs Delta m hm y.1) :
  x.1-y.1 ∈
   (cD B Delta (aF+aF) (m:NNReal)⁻¹).Zc:=by
 classical
 rw[qB]
 constructor
 ·exact aj.j0 (hS x.2) (hS y.2)
 ·intro psi cT
  rw[map_sub]
  have vS:=Uu nd ⟨psi,cT⟩
  have hbound:=nQ hm vS
  simpa only[SE,S9,R6] using hbound
omit [DecidableEq G] in
private lemma s0
  (B:aj G) (Delta:Finset (AddChar G Complex))
  (aF:NNReal) {m:Nat} (hm:0< m)
  (S:Finset G) (hS:S⊆(B.ai aF).Zc)
  (a:Delta→Fin m) :
  Fintype.card {x:↥S// Zs Delta m hm x.1=a} ≤
   (cD B Delta (aF+aF) (m:NNReal)⁻¹).Zc.card:=by
 classical
 by_cases jv:Nonempty {x:↥S// Zs Delta m hm x.1=a}
 ·let x₀:{x:↥S// Zs Delta m hm x.1=a}:=Classical.choice jv
  let f:{x:↥S// Zs Delta m hm x.1=a} →
    ↥(cD B Delta (aF+aF) (m:NNReal)⁻¹).Zc :=
   fun x↦⟨x.1.1-x₀.1.1,mw
    B Delta aF hm S hS (x.2.trans x₀.2.symm)⟩
  have hf:Function.Injective f:=by
   intro x y nd
   apply RI
   apply RI
   have q0:=QA Subtype.val nd
   dsimp[f] at q0
   exact S8 q0
  calc
   Fintype.card {x:↥S// Zs Delta m hm x.1=a} ≤
     Fintype.card ↥(cD B Delta (aF+aF)
      (m:NNReal)⁻¹).Zc:=R1 f hf
   _=(cD B Delta (aF+aF)
      (m:NNReal)⁻¹).Zc.card:=Rx _
 ·simp only[To] at jv
  simp
omit [DecidableEq G] in
lemma nR
  (B:aj G) (Delta:Finset (AddChar G Complex))
  (aF:NNReal) {m:Nat} (hm:0< m)
  (S:Finset G) (hS:S⊆(B.ai aF).Zc) :
  S.card≤ m^Delta.card *
   (cD B Delta (aF+aF) (m:NNReal)⁻¹).Zc.card:=by
 classical
 let Sigma:=Delta→Fin m
 let q:↥S→ Sigma:=fun x↦Zs Delta m hm x.1
 have jv: ∀ a:Sigma,
   Fintype.card {x:↥S// q x=a} ≤
    (cD B Delta (aF+aF) (m:NNReal)⁻¹).Zc.card:=by
  intro a
  exact s0 B Delta aF hm S hS a
 have Dl:Fintype.card Sigma=m^Delta.card:=by
  dsimp[Sigma]
  rw[TC]
  simp
 rw[←Rx S, ←Dl]
 by_contra h
 have xP:Fintype.card Sigma *
   (cD B Delta (aF+aF) (m:NNReal)⁻¹).Zc.card <
    Fintype.card ↥S:=by omega
 obtain ⟨a,ha⟩:=Rk (f:=q) xP
 have Es: #{x | q x=a} ≤
   (cD B Delta (aF+aF) (m:NNReal)⁻¹).Zc.card:=by
  rw[←SL]
  exact jv a
 exact(Rd Es) ha
omit [DecidableEq G] in
lemma tv
  (B:aj G) (Delta:Finset (AddChar G Complex))
  (aF:NNReal) {m:Nat} (hm:0< m)
  (S:Finset G) (hS:S⊆(B.ai aF).Zc) :
  (cD B Delta (aF+aF) (m:NNReal)⁻¹).rank ≤
    B.rank+Delta.card ∧
   (cD B Delta (aF+aF) (m:NNReal)⁻¹).Zc ⊆
    (B.ai (aF+aF)).Zc ∧
   S.card≤ m^Delta.card *
    (cD B Delta (aF+aF)
     (m:NNReal)⁻¹).Zc.card:=by
 classical
 exact ⟨vz B Delta _ _,
  fD B Delta _ _,
  nR B Delta aF hm S hS⟩
end
end ay.qz
end
section
open scoped BigOperators ENNReal NNReal Pointwise translate
open Finset Function MeasureTheory RCLike
namespace ay.ag
variable {G:Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
omit [DecidableEq G] [Fintype G] in
lemma q3 [Finite G] (psi:AddChar G ℂ) (t:G) :
  ‖psi (-t)-1‖ = ‖1-psi t‖ :=by
 rw[psi.map_neg_eq_inv]
 have vE:psi t≠0:=by
  intro h
  have:=Q0 psi t
  simp[h] at this
 calc
  ‖(psi t)⁻¹ -1‖ = ‖(psi t)⁻¹ *(1-psi t)‖ :=by
   congr 1
   field_simp
  _= ‖1-psi t‖ :=by
   rw[QO,Up,Q0,inv_one,QT]
lemma oN
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  (X:Finset G) (hX:X.Nonempty) (m:ℕ) (F:G→ℂ)
  (eta theta:ℝ) (fC:0≤eta) (OM:0≤theta)
  (t:G)
  (l4: ∀ psi:AddChar G ℂ,
   eta≤ ‖dft ((@mu (ℂ) _ _) X) psi‖ → ‖1-psi t‖ ≤theta) :
  (aJ (∞) (τ t ((aC ((eo (mu X) m)) F))-((aC ((eo (mu X) m)) F)))) ≤
   (theta+2*eta^m)*(c2 1 (dft F)):=by
 rw[dw]
 refine ciSup_le fun x↦ ?_
 let P:G→ℂ:=(aC ((eo (mu X) m)) F)
 have gX :
   (τ t P-P) x =
    𝔼 psi:AddChar G ℂ,
     dft P psi*(psi (x-t)-psi x):=by
  simp only[Rw,QZ]
  rw[←vk P (x-t), ←vk P x,
   ←Finset.expect_sub_distrib]
  apply Finset.expect_congr rfl
  intro psi _
  ring
 rw[gX]
 calc
  ‖𝔼 psi:AddChar G ℂ,
    dft P psi*(psi (x-t)-psi x)‖
    ≤ 𝔼 psi:AddChar G ℂ,
      ‖dft P psi*(psi (x-t)-psi x)‖ :=
     RCLike.norm_expect_le (K:=ℝ)
  _≤𝔼 psi:AddChar G ℂ,
     (theta+2*eta^m)* ‖dft F psi‖ :=by
   refine expect_le_expect fun psi _↦ ?_
   rw[QO]
   have n6 :
     ‖psi (x-t)-psi x‖ = ‖1-psi t‖ :=by
    have AH:psi (x-t)=psi x*psi (-t):=by
     rw[Qy,psi.map_add_eq_mul]
    rw[AH]
    calc
     ‖psi x*psi (-t)-psi x‖ = ‖psi x*(psi (-t)-1)‖ :=by ring_nf
     _= ‖psi (-t)-1‖ :=by rw[QO,Q0,QT]
     _= ‖1-psi t‖ :=q3 psi t
   rw[n6]
   simp only[P,sa,vO,QO,norm_pow]
   have AM: ‖dft ((@mu (ℂ) _ _) X) psi‖ ≤1:=by
    calc
     ‖dft ((@mu (ℂ) _ _) X) psi‖ ≤(aJ 1 (((@mu (ℂ) _ _) X))):=pz _ _
     _=1:=uN hX
   by_cases iV:eta≤ ‖dft ((@mu (ℂ) _ _) X) psi‖
   ·have hpow: ‖dft ((@mu (ℂ) _ _) X) psi‖ ^m≤1 :=
     Uy (Re _) AM
    have hp:=l4 psi iV
    calc
     ‖dft ((@mu (ℂ) _ _) X) psi‖ ^m* ‖dft F psi‖ * ‖1-psi t‖ ≤
       1* ‖dft F psi‖ *theta:=by gcongr
     _≤(theta+2*eta^m)* ‖dft F psi‖ :=by
      have LB:0≤eta^m:=QH fC m
      have hF:0≤ ‖dft F psi‖ :=Re _
      nlinarith
   ·have uU: ‖dft ((@mu (ℂ) _ _) X) psi‖ ^m≤eta^m:=by
     exact Qp (Re _) (le_of_not_ge iV) m
    have ON: ‖1-psi t‖ ≤2:=by
     calc
      ‖1-psi t‖ ≤ ‖(1:ℂ)‖ + ‖psi t‖ :=norm_sub_le _ _
      _=2:=by norm_num
    calc
     ‖dft ((@mu (ℂ) _ _) X) psi‖ ^m* ‖dft F psi‖ * ‖1-psi t‖ ≤
       eta^m* ‖dft F psi‖ *2:=by gcongr
     _≤(theta+2*eta^m)* ‖dft F psi‖ :=by
      have LB:0≤eta^m:=QH fC m
      have hF:0≤ ‖dft F psi‖ :=Re _
      nlinarith
  _=(theta+2*eta^m)*(c2 1 (dft F)):=by
   rw[tl,Finset.mul_expect]
lemma su
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  (A B C:Finset G) (hA:A.Nonempty) (hC:C.Nonempty) :
  (c2 1 (dft ((aC (((aC ((@mu (ℂ) _ _) A) (((Set.indicator B fun _↦(1:_)):G→ℂ))))) (mu C))))) ≤
   Real.sqrt ((B.card:ℝ)/C.card):=by
 calc
  (c2 1 (dft ((aC (((aC ((@mu (ℂ) _ _) A) (((Set.indicator B fun _↦(1:_)):G→ℂ))))) (mu C)))))
    = (c2 1 (dft ((@mu (ℂ) _ _) A) *
      (dft ((Set.indicator B fun _↦(1:_)):G→ℂ)*dft ((@mu (ℂ) _ _) C)))):=by
     rw[x4,x4]
     congr 1
     funext psi
     ring_nf
  _≤(c2 1 (dft ((Set.indicator B fun _↦(1:_)):G→ℂ)*dft ((@mu (ℂ) _ _) C))):=by
   calc
    _≤(c2 1 (dft ((Set.indicator B fun _↦(1:_)):G→ℂ)*dft ((@mu (ℂ) _ _) C))) *
       (c2 (∞) (dft ((@mu (ℂ) _ _) A))):=by
      simpa[Qx] using
       (tV (f:=dft ((Set.indicator B fun _↦(1:_)):G→ℂ)*dft ((@mu (ℂ) _ _) C))
        (g:=dft ((@mu (ℂ) _ _) A)) 1 ∞)
    _≤(c2 1 (dft ((Set.indicator B fun _↦(1:_)):G→ℂ)*dft ((@mu (ℂ) _ _) C)))*1:=by
      gcongr
      ·exact yK
      exact(qV _).trans_eq (uN hA)
    _=_:=Q3 _
  _≤(c2 2 (dft ((Set.indicator B fun _↦(1:_)):G→ℂ)))*(c2 2 (dft ((@mu (ℂ) _ _) C))) :=
   tV 2 2
  _=Real.sqrt (B.card:ℝ)*(C.card:ℝ)^(-2⁻¹ :ℝ):=by
   rw[w4,tR,w4,CL hC]
  _=Real.sqrt ((B.card:ℝ)/C.card):=by
   rw[Real.sqrt_div (by positivity),U4,
    U4,Qw]
   congr 1
   rw[←TS (by positivity)]
   congr 1
   norm_num
lemma s3 (X:Finset G) (psi:AddChar G ℂ) :
  dft ((@mu (ℂ) _ _) X) psi =
   ay.cG (ay.af X) (-psi):=by
 classical
 rw[dft_apply,wInner_one_eq_sum]
 simp only[inner_apply',ay.cG,
  U2]
 apply Io rfl
 intro x _
 unfold mu ay.af
 by_cases hx:x∈X
 ·simp[hx,Q2, ←Rz,
   ←Ud,Qx]
 ·simp[hx,Q2]
omit [DecidableEq G] in
lemma vW (f:G→ℂ) (a:G) (psi:AddChar G ℂ) :
  ‖dft (τ a f) psi‖ = ‖dft f psi‖ :=by
 rw[dft_apply,dft_apply,wInner_one_eq_sum,wInner_one_eq_sum]
 simp only[inner_apply',QZ]
 have hsum :
   (∑ x:G,starRingEnd ℂ (psi x)*f (x-a)) =
    starRingEnd ℂ (psi a)* ∑ x:G,starRingEnd ℂ (psi x)*f x:=by
  rw[Qj]
  refine Qk (Equiv.addRight (-a)) _ _ (fun x↦ ?_)
  simp only[Equiv.coe_addRight,Qy,St,
   Ud,RU,map_inv₀]
  have vE:starRingEnd ℂ (psi a)≠0:=by
   have cT:psi a≠0:=by
    intro h
    have oO:=Q0 psi a
    rw[h,norm_zero] at oO
    norm_num at oO
   simpa using cT
  field_simp
 rw[hsum,QO]
 simp
lemma tw (T:Finset G) (a:G) (psi:AddChar G ℂ) :
  ‖dft ((@mu (ℂ) _ _) (a+ᵥ T)) psi‖ = ‖dft ((@mu (ℂ) _ _) T) psi‖ :=by
 rw[←vH (K:=ℂ)]
 exact vW ((@mu (ℂ) _ _) T) a psi
omit [DecidableEq G] in
lemma kE
  (X:Finset G) (hX:X.Nonempty) (psi:AddChar G ℂ)
  (cT:(1/2:ℝ)≤ ‖dft ((@mu (ℂ) _ _) X) psi‖) :
  psi∈ay.c5.cj X (1/2):=by
 classical
 by_contra hnot
 have eY: -psi∉ay.c5.cj X (1/2):=by
  intro hn
  have:=ay.aI.ks hn
  exact hnot (by simpa only[neg_neg] using this)
 have NQ :
   ‖ay.c5.c6 X (-psi)‖ <(1/2:ℝ)*X.card:=by
  exact QV fun h↦eY (ay.c5.gm.mpr h)
 have ch:(0:ℝ)<X.card:=by exact_mod_cast hX.card_pos
 have xP :
   ‖ay.cG (ay.af X) (-psi)‖ <1/2:=by
  rw[ay.jT,QO,Up,
   Rf,QK,RT ch]
  calc
   (X.card:ℝ)⁻¹ * ‖ay.c5.c6 X (-psi)‖ <
     (X.card:ℝ)⁻¹ *((1/2:ℝ)*X.card):=by gcongr
   _=1/2:=by field_simp
 rw[s3] at cT
 linarith
lemma ib
  (T:Finset G) (hT:T.Nonempty) (a:G) (psi:AddChar G ℂ)
  (cT:(1/2:ℝ)≤ ‖dft ((@mu (ℂ) _ _) (a+ᵥ T)) psi‖) :
  psi∈ay.c5.cj T (1/2):=by
 apply kE T hT psi
 rw[←tw T a psi]
 exact cT
noncomputable def a6 (D:ℝ):ℕ :=
 ⌈2*Real.pi*max D 0⌉₊+1
lemma gd (D:ℝ):0<a6 D:=by
 simp[a6]
lemma jc (D:ℝ) :
  D*((((a6 D:ℕ):ℝ≥0)⁻¹ :ℝ)) ≤
   (2*Real.pi)⁻¹ :=by
 let n:=a6 D
 have LD:0<n:=gd D
 have hn:(0:ℝ)<n:=by exact_mod_cast LD
 have Ai:(0:ℝ)<2*Real.pi:=by positivity
 have rG:2*Real.pi*max D 0 ≤
   (Nat.ceil (2*Real.pi*max D 0):ℝ):=Rr _
 have fF:2*Real.pi*D≤(n:ℝ):=by
  calc
   2*Real.pi*D≤2*Real.pi*max D 0:=by
    gcongr
    exact Tu _ _
   _≤(Nat.ceil (2*Real.pi*max D 0):ℝ):=rG
   _≤(n:ℝ):=by
    dsimp[n,a6]
    exact_mod_cast Nat.le_succ _
 have ts:((((n:ℕ):ℝ≥0)⁻¹ :ℝ))=(n:ℝ)⁻¹ :=by
  norm_cast
 rw[ts]
 rw[←Qw,QF hn]
 calc
  D≤(n:ℝ)/(2*Real.pi) :=
   (Qs Ai).2 (by nlinarith[fF])
  _=(2*Real.pi)⁻¹ *(n:ℝ):=by
   field_simp
lemma sv (D:ℝ) (d q:ℕ)
  (hd:(d:ℝ)≤D) (hq:0<q) :
  4*Real.pi*(d:ℝ) *
    (((((q*a6 D:ℕ):ℝ≥0)⁻¹ :ℝ))) ≤
   2/(q:ℝ):=by
 have hs:0<a6 D:=gd D
 have P3:(0:ℝ)<a6 D:=by exact_mod_cast hs
 have Je:(0:ℝ)<q:=by exact_mod_cast hq
 have dc:D*((a6 D:ℝ)⁻¹) ≤
   (2*Real.pi)⁻¹ :=by
  have h:=jc D
  have ts:((((a6 D:ℕ):ℝ≥0)⁻¹ :ℝ)) =
    (a6 D:ℝ)⁻¹ :=by norm_cast
  simpa[ts] using h
 have NR:(d:ℝ)*((a6 D:ℝ)⁻¹) ≤
   (2*Real.pi)⁻¹ :=by
  calc
   (d:ℝ)*((a6 D:ℝ)⁻¹) ≤
     D*((a6 D:ℝ)⁻¹):=by gcongr
   _≤_:=dc
 have ts:(((((q*a6 D:ℕ):ℝ≥0)⁻¹ :ℝ))) =
   ((q:ℝ)*(a6 D:ℝ))⁻¹ :=by
  norm_cast
 rw[ts,mul_inv]
 calc
  4*Real.pi*(d:ℝ) *
    ((q:ℝ)⁻¹ *(a6 D:ℝ)⁻¹) =
    (q:ℝ)⁻¹ *
     (4*Real.pi*((d:ℝ)*(a6 D:ℝ)⁻¹)):=by ring
  _≤(q:ℝ)⁻¹ *(4*Real.pi*(2*Real.pi)⁻¹):=by gcongr
  _=2/(q:ℝ):=by
   field_simp
   ring
omit [DecidableEq G] [Fintype G] in
lemma pS [Finite G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  (F P:G→ℂ) (t:G) {delta E:ℝ}
  (cu:(aJ (∞) (P-F))≤delta)
  (jl:(aJ (∞) (τ t P-P))≤E) :
  (aJ (∞) (τ t F-F))≤2*delta+E:=by
 have jw :
   (aJ (∞) (τ t F-F))≤(aJ (∞) (τ t F-τ t P))+(aJ (∞) (τ t P-F)) :=
  ep le_top
 have ud :
   (aJ (∞) (τ t P-F))≤(aJ (∞) (τ t P-P))+(aJ (∞) (P-F)) :=
  ep le_top
 calc
  (aJ (∞) (τ t F-F))≤(aJ (∞) (τ t F-τ t P))+(aJ (∞) (τ t P-F)):=jw
  _≤(aJ (∞) (τ t F-τ t P)) +
     ((aJ (∞) (τ t P-P))+(aJ (∞) (P-F))):=by gcongr
  _=(aJ (∞) (F-P))+((aJ (∞) (τ t P-P))+(aJ (∞) (P-F))):=by
   have JX:τ t F-τ t P=τ t (F-P):=by rfl
   rw[JX,jX]
  _≤delta+(E+delta):=by
   gcongr
   simpa[r5] using cu
  _=2*delta+E:=by ring
omit [DecidableEq G] in
lemma kl
  (C:ay.aj G) (ta:C.a1)
  (Q Delta:Finset (AddChar G ℂ)) (aF:ℝ≥0)
  (m:ℕ) (hm:0< m) (X:Finset G)
  (hX:X⊆(C.ai aF).Zc)
  (iX:aF+aF ≤
   1/(100*(max C.rank 1:ℕ):ℝ≥0))
  (dV:(Delta.card:ℝ)*((m:ℝ≥0)⁻¹ :ℝ) ≤
   (2*Real.pi)⁻¹)
  (j5: ∀ psi∈Q, ∃ z∈Delta.addSpan,
   ∃ s∈ay.c5.cj C.Zc (1/2),psi=z+s) :
  let D:=ay.jm.cD C Delta
   (aF+aF) (m:ℝ≥0)⁻¹
  D.rank≤C.rank+Delta.card ∧
   D.Zc⊆(C.ai (aF+aF)).Zc ∧
   X.card≤ m^Delta.card*D.Zc.card ∧
   ∀ t∈D.Zc, ∀ psi∈Q,
    ‖1-psi t‖ ≤
     4*Real.pi*((Delta.card:ℝ)*((m:ℝ≥0)⁻¹ :ℝ)) +
      400*((max C.rank 1:ℕ):ℝ)*(aF+aF:ℝ≥0):=by
 classical
 let D:=ay.jm.cD C Delta
  (aF+aF) (m:ℝ≥0)⁻¹
 have tx:=ay.qz.tv
  C Delta aF hm X hX
 refine ⟨tx.1,tx.2.1,tx.2.2, ?_⟩
 intro t ht psi cT
 simpa only[D,SE,S9] using
  (ay.jm.iY
   C ta iX dV j5 t ht psi cT)
omit [DecidableEq G] in
lemma kt (D:ay.aj G) :
  ∃ R:ay.aj G,
   R.a1∧R.rank=D.rank∧R.Zc⊆D.Zc ∧
    D.Zc.card≤4^D.rank*R.Zc.card:=by
 classical
 obtain ⟨a8,gI,lf,dF⟩:=D.eP
 refine ⟨D.ai a8,dF,by simp, ?_, ?_⟩
 ·simpa only[ay.aj.oD] using
   (ay.aj.b5 (B:=D) lf)
 ·have dc:=ay.aj.de D
  have iB:(D.ai (1/2)).Zc.card ≤
    (D.ai a8).Zc.card :=
   Qu (ay.aj.b5 gI)
  calc
   D.Zc.card=(D.ai 1).Zc.card:=by simp
   _≤4^D.rank*(D.ai (1/2)).Zc.card:=dc
   _≤4^D.rank*(D.ai a8).Zc.card :=
    Qr _ iB
omit [DecidableEq G] in
lemma gJ
  (C:ay.aj G) (ta:C.a1)
  (Q Delta:Finset (AddChar G ℂ)) (aF:ℝ≥0)
  (m:ℕ) (hm:0< m) (X:Finset G)
  (hX:X⊆(C.ai aF).Zc)
  (iX:aF+aF ≤
   1/(100*(max C.rank 1:ℕ):ℝ≥0))
  (dV:(Delta.card:ℝ)*((m:ℝ≥0)⁻¹ :ℝ) ≤
   (2*Real.pi)⁻¹)
  (j5: ∀ psi∈Q, ∃ z∈Delta.addSpan,
   ∃ s∈ay.c5.cj C.Zc (1/2),psi=z+s) :
  ∃ R:ay.aj G,
   R.a1∧R.rank≤C.rank+Delta.card ∧
   R.Zc⊆(C.ai (aF+aF)).Zc ∧
   X.card≤ m^Delta.card*(4^(C.rank+Delta.card)*R.Zc.card) ∧
   ∀ t∈R.Zc, ∀ psi∈Q,
    ‖1-psi t‖ ≤
     4*Real.pi*((Delta.card:ℝ)*((m:ℝ≥0)⁻¹ :ℝ)) +
      400*((max C.rank 1:ℕ):ℝ)*(aF+aF:ℝ≥0):=by
 classical
 let D:=ay.jm.cD C Delta
  (aF+aF) (m:ℝ≥0)⁻¹
 have hD:=kl
  C ta Q Delta aF m hm X hX iX dV j5
 obtain ⟨R,qi,oP,Hb,yb⟩:=kt D
 refine ⟨R,qi,oP.le.trans hD.1,Hb.trans hD.2.1, ?_, ?_⟩
 ·calc
   X.card≤ m^Delta.card*D.Zc.card:=hD.2.2.1
   _≤ m^Delta.card*(4^D.rank*R.Zc.card) :=
    Qr _ yb
   _≤ m^Delta.card*(4^(C.rank+Delta.card)*R.Zc.card):=by
    have hpow:4^D.rank≤4^(C.rank+Delta.card) :=
     QR (by omega) hD.1
    exact Qr _ (QQ _ hpow)
 ·intro t ht psi cT
  exact hD.2.2.2 t (Hb ht) psi cT
omit [DecidableEq G] in
lemma iD
  (B:ay.aj G) (rE:B.a1)
  (X:Finset G) (hX:X.Nonempty) (t9:X⊆B.Zc)
  (eta:ℝ) (fC:0<eta) (aF:ℝ≥0) (m:ℕ) (hm:0< m)
  (iX:aF+aF ≤
   1/(100*(max B.rank 1:ℕ):ℝ≥0))
  (dV :
   ay.aI.bf B X eta *
     (((m:ℝ≥0)⁻¹ :ℝ))≤(2*Real.pi)⁻¹) :
  ∃ a8:ℝ≥0, ∃ C:ay.aj G,
   ∃ Delta:Finset (AddChar G ℂ), ∃ R:ay.aj G,
    1/2≤a8∧a8≤1 ∧
    C=B.ai (a8 *
     ay.aI.cJ B X eta) ∧
    C.a1 ∧
    (Delta.card:ℝ) ≤
     ay.aI.bf B X eta ∧
    Delta⊆ay.c5.cj X eta ∧
    R.a1∧R.rank≤B.rank+Delta.card ∧
    R.Zc⊆(C.ai (aF+aF)).Zc ∧
    (C.ai aF).Zc.card ≤
     m^Delta.card*(4^(B.rank+Delta.card)*R.Zc.card) ∧
    ∀ t∈R.Zc,
     ∀ psi∈ay.c5.cj X eta,
      ‖1-psi t‖ ≤
       4*Real.pi *
         (Delta.card:ℝ)*(((m:ℝ≥0)⁻¹ :ℝ)) +
        400*((max B.rank 1:ℕ):ℝ) *
         (aF+aF:ℝ≥0):=by
 classical
 obtain ⟨a8,C,Delta,gI,lf,hC,ta,
   fH,uY,j5⟩ :=
  ay.aI.mV
   B rE X hX t9 eta fC
 have yc:C.rank=B.rank:=by simp[hC]
 have HZ:aF+aF ≤
   1/(100*(max C.rank 1:ℕ):ℝ≥0):=by
  simpa[yc] using iX
 have hinv:0≤(((m:ℝ≥0)⁻¹ :ℝ)):=by positivity
 have BP :
   (Delta.card:ℝ)*(((m:ℝ≥0)⁻¹ :ℝ)) ≤
    (2*Real.pi)⁻¹ :=
  (Qi fH hinv).trans dV
 obtain ⟨R,qi,oP,yd,vX,l4⟩ :=
  gJ
   C ta (ay.c5.cj X eta) Delta aF m hm
    (C.ai aF).Zc (fun _ hx↦hx) HZ BP j5
 refine ⟨a8,C,Delta,R,gI,lf,hC,ta,
  fH,uY,qi, ?_,yd, ?_, ?_⟩
 ·simpa[yc] using oP
 ·simpa[yc] using vX
 ·intro t ht psi cT
  simpa only[yc,Qo] using l4 t ht psi cT
lemma fj
  [MeasurableSpace G] [DiscreteMeasurableSpace G]
  {A:Finset G} (hA:A.Nonempty)
  (delta:ℝ) (cu:0<delta) (m:ℕ) (hm:m≠0)
  (M L:Finset G) (hM:M.Nonempty) (hL:L.Nonempty)
  (bl:ay.aj G) (sw:bl.a1)
  (aF:ℝ≥0)
  (dy:aF+aF ≤
   1/(100*(max bl.rank 1:ℕ):ℝ≥0))
  (dh:ℕ) (pT:0<dh) :
  let q:=⌈1+Real.log (min 1 ((L.card:ℝ)/M.card))⁻¹⌉₊
  let wI:=ay.cQ q
   ((delta/m)/Real.exp 1)
  ∃ (T X:Finset G) (z:G) (a8:ℝ≥0),
   ∃ (fk:ay.aj G)
    (Delta:Finset (AddChar G ℂ)) (R:ay.aj G),
   T⊆bl.Zc∧z∈T∧X= -z+ᵥ T∧X.Nonempty ∧
   (((A.card:ℝ)^wI/2*bl.Zc.card) /
     ((A+bl.Zc).card:ℝ)^wI≤T.card) ∧
   1/2≤a8∧a8≤1 ∧
   fk=bl.ai (a8 *
    ay.aI.cJ bl T (1/2)) ∧
   fk.a1 ∧
   (Delta.card:ℝ) ≤
    ay.aI.bf bl T (1/2) ∧
   Delta⊆ay.c5.cj T (1/2) ∧
   R.a1∧R.rank≤bl.rank+Delta.card ∧
   R.Zc⊆(fk.ai (aF+aF)).Zc ∧
   (fk.ai aF).Zc.card ≤
    (dh*a6
       (ay.aI.bf bl T (1/2))) ^
      Delta.card *
     (4^(bl.rank+Delta.card)*R.Zc.card) ∧
   ∀ t∈R.Zc,
    (aJ (∞) (τ t ((aC (((aC ((@mu (ℂ) _ _) A) (((Set.indicator M fun _↦(1:_)):G→ℂ))))) (mu L))) -
      ((aC (((aC ((@mu (ℂ) _ _) A) (((Set.indicator M fun _↦(1:_)):G→ℂ))))) (mu L))))) ≤
     2*delta +
      (4*Real.pi *
         (Delta.card:ℝ) *
          ((((dh*a6
           (ay.aI.bf
            bl T (1/2)):ℕ):ℝ≥0)⁻¹ :ℝ)) +
        400*((max bl.rank 1:ℕ):ℝ) *
         (aF+aF:ℝ≥0) +
        2*(1/2:ℝ)^m) *
       Real.sqrt ((M.card:ℝ)/L.card):=by
 classical
 let q:=⌈1+Real.log (min 1 ((L.card:ℝ)/M.card))⁻¹⌉₊
 let wI:=ay.cQ q
  ((delta/m)/Real.exp 1)
 obtain ⟨T,z,ue,MF,pP,_hXdiff,nf,j6⟩ :=
  ay.mT
   hA bl.aE delta cu m hm M L hM hL
 let X:Finset G:=-z+ᵥ T
 have uT:T.Nonempty:=⟨z,MF⟩
 let dim:=ay.aI.bf bl T (1/2)
 let n:=dh*a6 dim
 have hn:0<n:=QP pT (gd dim)
 have dV:dim*(((n:ℝ≥0)⁻¹ :ℝ))≤(2*Real.pi)⁻¹ :=by
  have oM:0≤dim:=by
   have nf:(0:ℝ)<T.card:=by exact_mod_cast uT.card_pos
   have ch:(T.card:ℝ)≤bl.Zc.card:=by
    exact_mod_cast Qu ue
   have eO:(1:ℝ)≤2*(bl.Zc.card:ℝ)/T.card:=by
    rw[Qs nf]
    nlinarith
   have eu:0≤Real.log (2*(bl.Zc.card:ℝ)/T.card) :=
    Qv eO
   dsimp[dim,ay.aI.bf]
   positivity
  have dc:dim *
    ((((a6 dim:ℕ):ℝ≥0)⁻¹ :ℝ)) ≤
     (2*Real.pi)⁻¹ :=
   jc dim
  have Dm:a6 dim≤n:=by
   dsimp[n]
   exact T9 _ pT
  have hinv:(((n:ℝ≥0)⁻¹ :ℝ)) ≤
    ((((a6 dim:ℕ):ℝ≥0)⁻¹ :ℝ)):=by
   have EJ:(0:ℝ≥0) <
     (a6 dim:ℕ):=by
    exact_mod_cast gd dim
   have JY:(0:ℝ≥0)<n:=by exact_mod_cast hn
   have BQ:(a6 dim:ℝ≥0)≤n:=by
    exact_mod_cast Dm
   exact_mod_cast(RJ JY EJ).2 BQ
  exact(iO hinv oM).trans dc
 obtain ⟨a8,fk,Delta,R,gI,lf,oQ,AU,
   fH,uY,qi,oP,yd,vX,l4⟩ :=
  iD
   bl sw T uT ue (1/2) (by norm_num)
    aF n hn dy (by simpa[dim] using dV)
 let F:G→ℂ:=(aC (((aC (mu A) ((Set.indicator M fun _↦(1:_)))))) (mu L))
 let P:G→ℂ:=(aC ((eo (mu X) m)) F)
 let phase:ℝ :=
  4*Real.pi*(Delta.card:ℝ)*(((n:ℝ≥0)⁻¹ :ℝ)) +
   400*((max bl.rank 1:ℕ):ℝ)*(aF+aF:ℝ≥0)
 have H3:0≤phase:=by
  dsimp[phase]
  positivity
 have MG:(c2 1 (dft F))≤Real.sqrt ((M.card:ℝ)/L.card):=by
  simpa[F] using su A M L hA hL
 have Gb:(aJ (∞) (P-F))≤delta:=by
  simpa[P,F,X] using j6
 have jl: ∀ t∈R.Zc,
   (aJ (∞) (τ t F-F)) ≤
    2*delta+(phase+2*(1/2:ℝ)^m) *
     Real.sqrt ((M.card:ℝ)/L.card):=by
  intro t ht
  have hP:= oN X (by simpa[X] using pP) m F
   (1/2) phase (by norm_num) H3 t (fun psi cT ↦
    l4 t ht psi
     (ib
      T uT (-z) psi (by simpa[X] using cT)))
  have OO:(aJ (∞) (τ t P-P)) ≤
    (phase+2*(1/2:ℝ)^m) *
     Real.sqrt ((M.card:ℝ)/L.card):=by
   calc
    (aJ (∞) (τ t P-P)) ≤
      (phase+2*(1/2:ℝ)^m)*(c2 1 (dft F)):=by
       simpa[P] using hP
    _≤(phase+2*(1/2:ℝ)^m) *
      Real.sqrt ((M.card:ℝ)/L.card):=by
       gcongr
  exact pS F P t Gb OO
 refine ⟨T,X,z,a8,fk,Delta,R,ue,MF,rfl,
  by simpa[X] using pP, ?_,gI,lf, ?_,AU,
  ?_,uY,qi,oP,yd, ?_, ?_⟩
 ·simpa[q,wI] using nf
 ·simpa using oQ
 ·simpa[dim] using fH
 ·simpa[n,dim] using vX
 ·intro t ht
  simpa[F,phase,n,dim,Qo] using jl t ht
noncomputable def aS (A:Finset G) (x:G):ℝ :=
 if x∈A then (A.card:ℝ)⁻¹ else 0
noncomputable def d9 (f g:G→ℝ) (x:G):ℝ :=
 ∑ y:G,f y*g (x-y)
noncomputable def a2 (f g:G→ℝ) (x:G):ℝ :=
 ∑ y:G,f y*g (y-x)
noncomputable def bC (f g:G→ℝ):ℝ :=
 ∑ x:G,f x*g x
noncomputable def bJ (A:Finset G) (x:G):ℝ :=
 if x∈A then 1 else 0
noncomputable def bW
  (aX a3 S:Finset G) (t:G):ℝ :=
 ∑ a₁:G, ∑ a₂:G,
  bJ aX a₁*bJ a3 a₂*bJ S (t+a₁-a₂)
lemma d7
  {aX a3:Finset G} (fY:aX.Nonempty) (ho:a3.Nonempty)
  (S:Finset G) (t:G) :
  bC
    (fun x↦a2 (aS aX)
     (aS a3) (x-t))
    (bJ S) =
   bW aX a3 S t/(aX.card*a3.card:ℝ):=by
 classical
 simp only[bC,a2,aS,
  bW]
 simp_rw[Qt]
 rw[sum_comm]
 calc
  ∑ y:G, ∑ x:G,
    ((if y∈aX then (#aX:ℝ)⁻¹ else 0) *
     (if y-(x-t)∈a3 then (#a3:ℝ)⁻¹ else 0))*bJ S x
    = ((#aX:ℝ)⁻¹ *(#a3:ℝ)⁻¹) *
      ∑ y:G, ∑ x:G,
       bJ aX y*bJ a3 (y-(x-t)) *
        bJ S x:=by
     rw[Qj]
     apply sum_congr rfl
     intro y _
     rw[Qj]
     apply sum_congr rfl
     intro x _
     simp only[bJ]
     split_ifs<;>ring
  _=((#aX:ℝ)⁻¹ *(#a3:ℝ)⁻¹) *
      ∑ a₁:G, ∑ a₂:G,
       bJ aX a₁*bJ a3 a₂ *
        bJ S (t+a₁-a₂):=by
     congr 1
     apply sum_congr rfl
     intro a₁ _
     refine(Qk (Equiv.subLeft (t+a₁)) _ _ fun a₂↦ ?_).symm
     simp only[SX]
     congr 2; abel_nf
  _=(∑ a₁:G, ∑ a₂:G,
      bJ aX a₁*bJ a3 a₂ *
       bJ S (t+a₁-a₂)) /
     (aX.card*a3.card:ℝ):=by
     rw[Ri]
     field_simp[fY.card_ne_zero,ho.card_ne_zero]
lemma ja
  {D:Finset G} (_hD:D.Nonempty) (f:G→ℝ) (x:G) :
  d9 (aS D) f x =
   (∑ t∈D,f (x-t))/D.card:=by
 classical
 simp only[d9,aS]
 rw[←sum_subset (s₁:=D) (s₂:=univ)]
 ·rw[Ri,Qj]
  apply sum_congr rfl
  intro t ht
  rw[RP ht]
 ·simp
 ·intro t _ ht
  simp[ht]
lemma mW
  {D:Finset G} (hD:D.Nonempty)
  (f h:G→ℝ) {eps:ℝ}
  (jl: ∀ t∈D,
   |bC (fun x↦f (x-t)) h-bC f h| ≤eps) :
  |bC (d9 (aS D) f) h -
    bC f h| ≤eps:=by
 classical
 have ch:(0:ℝ)<D.card:=by exact_mod_cast hD.card_pos
 have j6 :
   bC (d9 (aS D) f) h =
    (∑ t∈D,bC (fun x↦f (x-t)) h)/D.card:=by
  simp only[bC]
  simp_rw[ja hD]
  simp_rw[div_mul_eq_mul_div,sum_div,Qt]
  rw[sum_comm]
  simp_rw[←sum_div]
 rw[j6]
 have sx :
   (∑ t∈D,bC (fun x↦f (x-t)) h)/D.card-bC f h =
    (∑ t∈D,
     (bC (fun x↦f (x-t)) h-bC f h))/D.card:=by
  rw[QJ,Tq,QS]
  field_simp[ch.ne']
 rw[sx,TE,RT ch]
 apply(QF ch).2
 calc
  |∑ t∈D,(bC (fun x↦f (x-t)) h-bC f h)|
    ≤ ∑ t∈D,
      |bC (fun x↦f (x-t)) h-bC f h| :=
     abs_sum_le_sum_abs (fun t ↦
      bC (fun x↦f (x-t)) h-bC f h) D
  _≤ ∑ _t∈D,eps:=sum_le_sum fun t ht↦jl t ht
  _=eps*D.card:=by simp[Qx]
lemma ji
  {D:aj G} {aX a3 S:Finset G} {eps:ℝ}
  (fY:aX.Nonempty) (ho:a3.Nonempty)
  (uf: ∀ t∈D.Zc,
   |bW aX a3 S t-bW aX a3 S 0| ≤
    eps*(aX.card:ℝ)*a3.card) :
  |bC
     (d9 (aS D.Zc)
      (a2
       (aS aX) (aS a3)))
     (bJ S) -
    bC
     (a2
      (aS aX) (aS a3))
     (bJ S)| ≤eps:=by
 classical
 apply mW D.aE
 intro t ht
 have hzero:=d7 fY ho S (0:G)
 simp only[sub_zero] at hzero
 rw[d7 fY ho,hzero]
 rw[←UT,TE]
 have ch:(0:ℝ)<(aX.card:ℝ)*a3.card :=
  QM (by exact_mod_cast fY.card_pos) (by exact_mod_cast ho.card_pos)
 rw[RT ch]
 apply(QF ch).2
 simpa[Qo] using uf t ht
end ay.ag
end
section
open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal Pointwise
namespace ay
namespace aN
noncomputable section
variable {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
 [MeasurableSpace G] [DiscreteMeasurableSpace G]
def dU (D E:Finset G):G→ℝ≥0 :=
 (aC ((@mu (ℝ≥0) _ _) D) (mu E))
def bh (D E:Finset G):G→ℝ≥0 :=
 (al (dU D E) (dU D E))
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma wW {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty) :
  ∑ x:G,dU D E x=1:=by
 simp[dU,uM,hD,hE]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma i7 {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty) :
  ∑ x:G,bh D E x=1:=by
 simp[bh,jI,wW hD hE]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma gS (D E:Finset G) :
  0≤bh D E:=by
 simp[bh]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma od (D E:Finset G) :
  (al (((↑) ∘ dU D E:G→ℂ)) (((↑) ∘ dU D E))) =
   (↑) ∘ bh D E:=by
 let b:=dU D E
 calc
  (al (((↑) ∘ b:G→ℂ)) (((↑) ∘ b))) =
    (↑) ∘ ((al (((↑) ∘ b:G→ℝ)) (((↑) ∘ b)))):=by
     exact(Complex.px ((↑) ∘ b) ((↑) ∘ b)).symm
  _=(↑) ∘ ((al b b)):=by
   rw[←NNReal.gF]
   rfl
  _=(↑) ∘ bh D E:=by
   funext x
   rfl
omit [AddCommGroup G] [DecidableEq G] in
lemma dN (w:G→ℝ≥0) (f:G→ℝ)
  {p:ℕ} (hp:0<p) :
  an.aM ((↑) ∘ w) f p=(b0 p w f):=by
 rw[an.dG _ _ hp]
 rw[ln (by exact_mod_cast hp.ne') (by simp)]
 congr 1
 ·apply Io rfl
  intro x _
  simp only[RG,Q2,norm_eq_abs,
   Rh,Ue]
  rw[RN]
 ·simp[R6]
omit [AddCommGroup G] [DecidableEq G] in
lemma gv
  (w:G→ℝ≥0) (f:G→ℝ) (c:ℝ) (hc:0≤c)
  {p:ℕ} (hp:0<p) :
  an.aM ((↑) ∘ w) (c•f) p =
   c*an.aM ((↑) ∘ w) f p:=by
 classical
 rw[dN w _ hp,dN w _ hp,
  Ak]
 simp[QK,QC hc]
omit [AddCommGroup G] [DecidableEq G] in
lemma pU
  (w:G→ℝ≥0) (f g:G→ℝ) {p:ℕ} (hp:1≤p) :
  an.aM ((↑) ∘ w) f p ≤
   an.aM ((↑) ∘ w) (f+g) p +
    an.aM ((↑) ∘ w) g p:=by
 classical
 simp_rw[dN w _ (U5 hp)]
 exact qU (by exact_mod_cast hp) w f g
omit [AddCommGroup G] [DecidableEq G] in
lemma qC
  {w:G→ℝ≥0} (hw: ∑ x:G,w x=1)
  {f:G→ℝ} {C:ℝ} (hC:0≤C) {p:ℕ} (hp:0<p)
  (hf: ∀ x, |f x| ≤C) :
  an.aM ((↑) ∘ w) f p≤C:=by
 classical
 rw[dN w f hp]
 calc
  (b0 p w f)≤(b0 p w ((fun _:G↦C))):=by
   apply lpNorm_mono_real .of_discrete
   simpa[QC hC] using hf
  _=C:=by
   rw[ln (by exact_mod_cast hp.ne') (by simp)]
   simp only[Ue]
   have hsum: ∑ x:G,(w x:ℝ)=1:=by exact_mod_cast hw
   have heq: ∑ x:G,(w x:ℝ)* ‖C‖ ^(p:ℝ)=C^p:=by
    rw[norm_eq_abs,QC hC,RN, ←Qt,
     hsum,QT]
   rw[show(∑ x:G,w x• ‖C‖ ^(p:ℝ))=C^p by
    simpa[RG] using heq]
   exact Sc hC hp.ne'
omit [AddCommGroup G] [DecidableEq G] in
lemma lv
  {w:G→ℝ≥0} (hw: ∑ x:G,w x=1)
  {f:G→ℝ} {C:ℝ} (hC:0≤C) {p:ℕ} (hp:0<p)
  (hf: ∀ x,w x≠0→ |f x| ≤C) :
  an.aM ((↑) ∘ w) f p≤C:=by
 classical
 let g:G→ℝ:=fun x↦if w x=0 then 0 else f x
 have oO:an.aM ((↑) ∘ w) f p =
   an.aM ((↑) ∘ w) g p:=by
  rw[an.dG _ _ hp,
   an.dG _ _ hp]
  apply QA (fun z:ℝ↦z^(1/(p:ℝ)))
  unfold aK
  apply Io rfl
  intro x _
  by_cases hx:w x=0<;>simp[g,hx]
 rw[oO]
 apply qC hw hC hp
 intro x
 by_cases hx:w x=0
 ·simp[g,hx,hC]
 ·simpa[g,hx] using hf x hx
omit [AddCommGroup G] [DiscreteMeasurableSpace G] [Fintype G] [MeasurableSpace G] in
lemma eQ (S:Finset G) :
  (@mu (ℝ) _ _) S=af S:=by
 funext x
 by_cases hx:x∈S<;>simp[mu_apply,af,hx]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma eZ
  {B:aj G} (dF:B.a1)
  {A:Finset G} (hA:A.Nonempty) (zo:A⊆B.Zc)
  {aF:ℝ≥0}
  (dy:aF≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  {t:G} (ht:t∈(B.ai aF).Zc) :
  |((al ((@mu (ℝ) _ _) A) (mu B.Zc))) t-(B.Zc.card:ℝ)⁻¹| ≤
   (A.card:ℝ)⁻¹ *
    (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ)):=by
 have hB:B.Zc.Nonempty:=B.aE
 have dc :
   ∑ x:G,(@mu (ℝ) _ _) A x*mu B.Zc x =
    (B.Zc.card:ℝ)⁻¹ :=by
  calc
   ∑ x:G,(@mu (ℝ) _ _) A x*mu B.Zc x =
     ∑ x:G,(@mu (ℝ) _ _) A x*(B.Zc.card:ℝ)⁻¹ :=by
    apply Io rfl
    intro x _
    by_cases hx:x∈A
    ·rw[mu_apply,mu_apply]
     simp[hx,zo hx]
    ·simp[mu_apply,hx]
   _=(B.Zc.card:ℝ)⁻¹ :=by
    rw[←Qt,kU ℝ hA,QT]
 have kC :
   ∑ x:G, |(@mu (ℝ) _ _) B.Zc (x-t)-mu B.Zc x| ≤
    200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ):=by
  simpa only[eQ] using
   B.cN dF dy ht
 rw[eL]
 simp only[Rc,star_trivial]
 rw[←dc]
 rw[←QJ]
 have Dn :
   (∑ x:G,((@mu (ℝ) _ _) A x*mu B.Zc (x-t) -
    mu A x*mu B.Zc x)) =
   ∑ x:G,(@mu (ℝ) _ _) A x *
    (mu B.Zc (x-t)-mu B.Zc x):=by
  apply Io rfl
  intro x _
  ring
 rw[Dn]
 calc
  |∑ x:G,(@mu (ℝ) _ _) A x *
    (mu B.Zc (x-t)-mu B.Zc x)| ≤
    ∑ x:G, |(@mu (ℝ) _ _) A x *
     (mu B.Zc (x-t)-mu B.Zc x)| :=
   TQ _ _
  _= ∑ x:G,(@mu (ℝ) _ _) A x *
     |mu B.Zc (x-t)-mu B.Zc x| :=by
   apply Io rfl
   intro x _
   have LF:0≤(@mu (ℝ) _ _) A x:=by
    rw[mu_apply]
    positivity
   rw[SU,QC LF]
  _≤ ∑ x:G,(A.card:ℝ)⁻¹ *
     |(@mu (ℝ) _ _) B.Zc (x-t)-mu B.Zc x| :=by
   apply QI
   intro x _
   apply Qi _ (Q8 _)
   rw[mu_apply]
   split_ifs<;>simp
  _=(A.card:ℝ)⁻¹ *
     ∑ x:G, |(@mu (ℝ) _ _) B.Zc (x-t)-mu B.Zc x| :=by
   rw[Qj]
  _≤(A.card:ℝ)⁻¹ *
     (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ)) :=
   iO kC (by positivity)
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma km
  {B:aj G} (dF:B.a1)
  {A:Finset G} (hA:A.Nonempty) (zo:A⊆B.Zc)
  {aF:ℝ≥0}
  (dy:aF≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  {t:G} (ht:t∈(B.ai aF).Zc) :
  |((al ((@mu (ℝ) _ _) A) (mu A))) t -
    ((B.Zc.card:ℝ)⁻¹ +
     ((al (((@mu (ℝ) _ _) A-mu B.Zc)) ((mu A-mu B.Zc)))) t)| ≤
   2*((A.card:ℝ)⁻¹ *
     (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ))) +
    (B.Zc.card:ℝ)⁻¹ *
     (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ)):=by
 let m:ℝ:=(B.Zc.card:ℝ)⁻¹
 let eA:ℝ:=(A.card:ℝ)⁻¹ *
  (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ))
 let eB:ℝ:=(B.Zc.card:ℝ)⁻¹ *
  (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ))
 have PM:=eZ dF hA zo dy ht
 have H4:=eZ dF hA zo dy
  (aj.ec.mpr ht)
 have Nf :
   |((al ((@mu (ℝ) _ _) B.Zc) (mu A))) t-m| ≤eA:=by
  have Ng:((al ((@mu (ℝ) _ _) B.Zc) (mu A))) t =
    ((al (mu A) (mu B.Zc))) (-t):=by
   have h:=wR ((@mu (ℝ) _ _) A) ((@mu (ℝ) _ _) B.Zc) t
   simpa using h.symm
  simpa[m,eA,Ng] using H4
 have Py:=eZ dF
  B.aE (fun _ h↦h) dy ht
 have hsum :
   |(((al ((@mu (ℝ) _ _) A) (mu B.Zc))) t-m) +
    (((al (mu B.Zc) (mu A))) t-m) -
    (((al (mu B.Zc) (mu B.Zc))) t-m)| ≤
     2*eA+eB:=by
  calc
   |(((al ((@mu (ℝ) _ _) A) (mu B.Zc))) t-m) +
     (((al (mu B.Zc) (mu A))) t-m) -
     (((al (mu B.Zc) (mu B.Zc))) t-m)| ≤
     |((al ((@mu (ℝ) _ _) A) (mu B.Zc))) t-m| +
     |((al (mu B.Zc) (mu A))) t-m| +
     |((al (mu B.Zc) (mu B.Zc))) t-m| :=by
      have l0:=abs_sub
       ((((al ((@mu (ℝ) _ _) A) (mu B.Zc))) t-m) +
        (((al (mu B.Zc) (mu A))) t-m))
       (((al (mu B.Zc) (mu B.Zc))) t-m)
      have xq:=UP
       (((al ((@mu (ℝ) _ _) A) (mu B.Zc))) t-m)
       (((al (mu B.Zc) (mu A))) t-m)
      linarith
   _≤eA+eA+eB:=by gcongr
   _=2*eA+eB:=by ring
 have H5 :
   ((al ((@mu (ℝ) _ _) A) (mu A))) t -
     (m+((al ((mu A-mu B.Zc)) ((mu A-mu B.Zc)))) t) =
    (((al (mu A) (mu B.Zc))) t-m) +
    (((al (mu B.Zc) (mu A))) t-m) -
    (((al (mu B.Zc) (mu B.Zc))) t-m):=by
  simp only[BC,BB,Rw]
  ring
 simpa[m,eA,eB,H5] using hsum
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma oe
  (A K:Finset G) :
  (al (((Real.sqrt (K.card:ℝ):ℂ) •
     ((↑) ∘ ((@mu (ℝ) _ _) A-mu K):G→ℂ))) (((Real.sqrt (K.card:ℝ):ℂ) •
     ((↑) ∘ ((@mu (ℝ) _ _) A-mu K):G→ℂ)))) =
   (↑) ∘ ((K.card:ℝ) •
    ((al (((@mu (ℝ) _ _) A-mu K)) ((mu A-mu K))))):=by
 rw[oy,oz]
 rw[←Complex.px]
 funext x
 simp only[RD,Rh,Q2]
 rw[show star (↑(Real.sqrt (K.card:ℝ)):ℂ) =
   ↑(Real.sqrt (K.card:ℝ)) by simp]
 rw[←Qo]
 norm_cast
 rw[←TI,Uf (by positivity:(0:ℝ)≤K.card)]
lemma ug
  {B:aj G} (dF:B.a1)
  {A:Finset G} (hA:A.Nonempty) (zo:A⊆B.Zc)
  {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty)
  {aF:ℝ≥0}
  (dy:aF≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  (kF: ∀ t,bh D E t≠0 →
   t∈(B.ai aF).Zc)
  {epsilon:ℝ} (eM:0<epsilon) (oR:epsilon≤1)
  (d5 :
   2*((A.card:ℝ)⁻¹ *
     (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ))) +
    (B.Zc.card:ℝ)⁻¹ *
     (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ)) ≤
    epsilon/8*(B.Zc.card:ℝ)⁻¹)
  {p:ℕ} (hp:0<p)
  (iV :
   epsilon*(B.Zc.card:ℝ)⁻¹ /2 <
    an.aM
     ((↑) ∘ bh D E)
     ((al (((@mu (ℝ) _ _) A-mu B.Zc)) ((mu A-mu B.Zc))))
     (an.bS p)) :
  ∃ r:ℕ,0<r∧Even r ∧
   r≤an.cz epsilon p ∧
   (1+epsilon/8)*(B.Zc.card:ℝ)⁻¹ ≤
    an.aM
     ((↑) ∘ bh D E) ((al ((@mu (ℝ) _ _) A) (mu A))) r:=by
 let K:=B.Zc
 let nu:=bh D E
 let balanced:G→ℝ:=(@mu (ℝ) _ _) A-mu K
 let gH:G→ℝ:=(al balanced balanced)
 let positive:G→ℝ:=(al ((@mu (ℝ) _ _) A) (mu A))
 let main:ℝ:=(K.card:ℝ)⁻¹
 let f:G→ℝ:=(K.card:ℝ)•gH
 let g0:G→ℝ:=main•(f+1)
 have hK:K.Nonempty:=B.aE
 have ye:(0:ℝ)<K.card:=by exact_mod_cast hK.card_pos
 have fF:0< main:=by simp[main,ye]
 have ft: ∑ x:G,nu x=1:=i7 hD hE
 have wJ:an.cw ((↑) ∘ nu) :=
  ⟨fun x↦by exact_mod_cast(show 0≤nu x by exact gS D E x),
   by simpa using QA (fun z:ℝ≥0↦(z:ℝ)) ft⟩
 have LG :
   (al (((Real.sqrt (K.card:ℝ):ℂ)•((↑) ∘ balanced:G→ℂ))) (((Real.sqrt (K.card:ℝ):ℂ)•((↑) ∘ balanced:G→ℂ)))) =
    (↑) ∘ f:=by
  simpa[K,balanced,gH,f] using oe A K
 have JZ :
   (al (((↑) ∘ dU D E:G→ℂ)) (((↑) ∘ dU D E)))=(↑) ∘ nu:=by
  simpa[nu] using od D E
 have Ar: ∀ k:ℕ,0≤ iP ((↑) ∘ nu) f k:=by
  intro k
  have h:=ry LG JZ k
  simpa[iP,wInner_one_eq_sum,Sb,Qx] using h
 have MH:(K.card:ℝ)*main=1:=by
  simp[main,Uq ye]
 have H6:epsilon/2 <
   an.aM ((↑) ∘ nu) f
    (an.bS p):=by
  rw[show f=(K.card:ℝ)•gH by rfl,
   gv nu gH (K.card:ℝ) (by positivity)
    (by simp[an.bS,hp])]
  have NS:epsilon*main/2 <
    an.aM ((↑) ∘ nu) gH
     (an.bS p):=by
   simpa[K,nu,balanced,gH,main] using iV
  nlinarith
 let sy:=an.cF p
 have LH:0<sy:=by
  have:=an.fK hp
  omega
 have Gc:=an.js
  wJ hp (f:=f)
 have EK:epsilon/2 <
   an.aM ((↑) ∘ nu) f sy:=by
  exact H6.trans_le (by simpa[sy] using Gc)
 have AV:(epsilon/2)^sy ≤
   aK ((↑) ∘ nu) f sy:=by
  calc
   (epsilon/2)^sy ≤
     an.aM ((↑) ∘ nu) f sy^sy :=
    Qp (by positivity) EK.le sy
   _=aK ((↑) ∘ nu) f sy :=
    an.jr wJ LH
 have c3: ∀ x,g0 x=main*(1+f x):=by
  intro x
  simp[g0,Q2,RV]
  ring
 obtain ⟨r,hr,Aw,yV,Dp⟩ :=
  an.pM wJ
   (f:=f) (fB:=g0) (η:=epsilon/2)
   (bo:=main) (by positivity) (by linarith) fF
   (an.fK hp)
   (an.pL p) Ar AV c3
 have J0:r≤an.cz epsilon p:=by
  simpa[an.cz,sy] using yV
 have BR: ∀ x,nu x≠0→ |positive x-g0 x| ≤epsilon/8*main:=by
  intro x hx
  have hb:=km dF hA zo dy
   (kF x hx)
  have yf:g0 x=main+gH x:=by
   simp only[smul_add,RM,RD,Q2,Rt,
    Q3,g0,f]
   rw[←Qo,show main*(K.card:ℝ)=1 by nlinarith,QT]
   ring
  simpa[K,balanced,gH,positive,main,yf] using hb.trans d5
 have EL :
   an.aM ((↑) ∘ nu) (positive-g0) r ≤
    epsilon/8*main:=by
  apply lv ft
   (Qn (by positivity) fF.le) hr
  intro x hx
  simpa[Rw] using BR x hx
 have zq:=pU nu g0 (positive-g0)
  (Nat.succ_le_iff.mpr hr)
 have xq:g0+(positive-g0)=positive:=by ext x; simp
 rw[xq] at zq
 refine ⟨r,hr,Aw,J0, ?_⟩
 simpa[K,nu,positive,main] using(by nlinarith[Dp,zq,EL])
end
end aN
end ay
end
section
open scoped BigOperators
open Finset
namespace ay
namespace cA
variable {G:Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
noncomputable section
def cS (A B:Finset G) {p:ℕ} (s:Fin p→G):Finset G :=
 B.filter fun b↦ ∀ i,b-s i∈A
omit [Fintype G] in
lemma kG (A B:Finset G) {p:ℕ} (s:Fin p→G) :
  cS A B s⊆B:=by
 intro b hb
 exact(mem_filter.mp hb).1
omit [Fintype G] in
@[simp] lemma jn {A B:Finset G} {p:ℕ} {s:Fin p→G} {b:G} :
  b∈cS A B s↔b∈B∧ ∀ i,b-s i∈A:=by
 simp[cS]
def wK (aX a3:Finset G) (F:G→ℝ):ℝ :=
 ∑ a₁∈aX, ∑ a₂∈a3,F (a₁-a₂)
def ef (A:Finset G) (x:G):ℕ :=
 #(Finset.univ.filter fun t:G↦x-t∈A∧ -t∈A)
private lemma sA (A:Finset G) (ey b₂:G) :
  (∑ s:G,if ey-s∈A∧b₂-s∈A then (1:ℝ) else 0) =
   ef A (ey-b₂):=by
 rw[ef]
 let e:G ≃ G:=Equiv.subRight b₂
 rw[show((#(Finset.univ.filter fun t:G↦ey-b₂-t∈A∧ -t∈A):ℕ):ℝ) =
   ∑ t:G,if ey-b₂-t∈A∧ -t∈A then (1:ℝ) else 0 by
  simp]
 refine Qk e
  (fun s:G↦if ey-s∈A∧b₂-s∈A then (1:ℝ) else 0)
  (fun t:G↦if ey-b₂-t∈A∧ -t∈A then (1:ℝ) else 0)
  (fun t↦ ?_)
 change(if ey-t∈A∧b₂-t∈A then (1:ℝ) else 0) =
  if ey-b₂-(t-b₂)∈A∧ -(t-b₂)∈A then 1 else 0
 have h₁:ey-b₂-(t-b₂)=ey-t:=by abel
 have h₂: -(t-b₂)=b₂-t:=by abel
 rw[h₁,h₂]
private lemma pk (A:Finset G) (ey b₂:G) (p:ℕ) :
  (∑ s:Fin p→G,
    if ∀ i,ey-s i∈A∧b₂-s i∈A then (1:ℝ) else 0) =
   (ef A (ey-b₂):ℝ)^p:=by
 let D:Finset G:=Finset.univ.filter fun t:G↦ey-t∈A∧b₂-t∈A
 have LI :
   Finset.univ.filter
     (fun s:Fin p→G↦ ∀ i,ey-s i∈A∧b₂-s i∈A) =
    Fintype.piFinset (fun _:Fin p↦D):=by
  ext s
  simp[D,RX]
 calc
  (∑ s:Fin p→G,
    if ∀ i,ey-s i∈A∧b₂-s i∈A then (1:ℝ) else 0) =
    ((Finset.univ.filter
     (fun s:Fin p→G↦ ∀ i,ey-s i∈A∧b₂-s i∈A)).card:ℝ):=by
   simp
  _=((Fintype.piFinset fun _:Fin p↦D).card:ℝ):=by rw[LI]
  _=(D.card:ℝ)^p:=by simp[Fintype.card_piFinset]
  _=(ef A (ey-b₂):ℝ)^p:=by
   congr 1
   have hsum:=sA A ey b₂
   simpa[D] using hsum
lemma vY (A aL a0:Finset G) (p:ℕ) (F:G→ℝ) :
  (∑ s:Fin p→G,wK (cS A aL s) (cS A a0 s) F) =
   ∑ ey∈aL, ∑ b₂∈a0,
    (ef A (ey-b₂):ℝ)^p*F (ey-b₂):=by
 classical
 simp only[wK,cS,sum_filter]
 rw[QD]
 apply sum_congr rfl
 intro ey Pz
 have LJ: ∀ s:Fin p→G,
   (if ∀ i,ey-s i∈A then
     ∑ a∈a0,if ∀ i,a-s i∈A then F (ey-a) else 0
    else 0) =
    ∑ a∈a0,if ∀ i,ey-s i∈A then
     if ∀ i,a-s i∈A then F (ey-a) else 0 else 0:=by
  intro s
  by_cases h: ∀ i,ey-s i∈A<;>simp[h]
 simp_rw[LJ]
 rw[QD]
 apply sum_congr rfl
 intro b₂ PA
 calc
  (∑ s:Fin p→G,
   if ∀ i,ey-s i∈A then
    if ∀ i,b₂-s i∈A then F (ey-b₂) else 0
   else 0) =
    (∑ s:Fin p→G,
     (if ∀ i,ey-s i∈A∧b₂-s i∈A then (1:ℝ) else 0)) *
      F (ey-b₂):=by
       rw[Qt]
       apply sum_congr rfl
       intro s hs
       split_ifs<;>simp_all
  _=(ef A (ey-b₂):ℝ)^p*F (ey-b₂):=by
   rw[pk]
section vZ
open Function MeasureTheory Real
open scoped ENNReal NNReal Pointwise
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
lemma v3 {A:Finset G} {p:ℕ} {ε δ:ℝ}
  (aL a0:Finset G) (hε:0<ε) (An:ε≤1) (Ca:0<δ)
  (hp:Even p) (hp₂:2≤p) (FW:ε⁻¹ *Real.log (2/δ)≤p)
  (hB:(aL∩a0).Nonempty) (hA:A.Nonempty)
  (hf: ∃ x,x∈aL-a0∧x∈A-A∧x∉s p ε aL a0 A) :
  ∃ aX,aX⊆aL∧ ∃ a3,a3⊆a0 ∧
   1-δ≤ ∑ x∈s p ε aL a0 A,((al (mu aX) (mu a3))) x ∧
   (4:ℝ)⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p) ≤
    #aX/ #aL ∧
   (4:ℝ)⁻¹ *(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))^(2*p)/ #A^(2*p) ≤
    #a3/ #a0:=by
 exact Hr aL a0 hε An Ca hp hp₂ FW hB hA hf
end vZ
end
end cA
end ay
end
section
open Finset
open scoped BigOperators NNReal translate
namespace ay.ah
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
namespace Dq
end Dq
open br
structure aA (original:Finset G) where
 restriction:aY G
 shift:G
 eR :
  ∀ x∈restriction.set,x-shift∈original
namespace aA
def e8 {original:Finset G} (s:aA original):Finset G :=
 s.restriction.e8
def Zd {original:Finset G} (s:aA original):Real :=
 s.restriction.Zd
def rank {original:Finset G} (s:aA original):Nat :=
 s.restriction.rank
def card {original:Finset G} (s:aA original):Nat :=
 s.restriction.card
lemma dI {original:Finset G} (s:aA original) :
  0<s.Zd:=s.restriction.dI
lemma Zn {original:Finset G} (s:aA original) :
  s.Zd≤1:=s.restriction.Zn
end aA
inductive cU {original:Finset G}
  (q:Real) (aq:Nat) (aU:Real) :
  Nat→aA original→aA original→Prop
 | nil (s:aA original) :
   cU q aq aU 0 s s
 | cons {n:Nat} {s t u:aA original}
   (pA:dk q aq aU
    s.restriction t.restriction)
   (x5:cU q aq aU n t u) :
   cU q aq aU (n+1) s u
namespace cU
lemma Zf {original:Finset G} {q:Real} {aq:Nat}
  {aU:Real} {n:Nat} {s t:aA original}
  (h:cU q aq aU n s t) :
  et q aq aU n s.restriction t.restriction:=by
 induction h with
 | nil s=>exact et.nil s.restriction
 | cons pA _ ih=>exact et.cons pA ih
lemma qW {original:Finset G} {q:Real} {aq:Nat}
  {aU:Real} (hq:0≤q) {n:Nat}
  {s t:aA original}
  (h:cU q aq aU n s t) :
  q^n*s.Zd≤t.Zd :=
 h.Zf.qW hq
lemma Zb {original:Finset G} {q:Real} {aq:Nat}
  {aU:Real} {n:Nat} {s t:aA original}
  (h:cU q aq aU n s t) :
  Real.exp (-(n:Real)*aU)*(s.card:Real)≤(t.card:Real) :=
 h.Zf.Zb
end cU
def dn (A C:Finset G) (x:G):Finset G :=
 (C.filter fun c=>x-c∈A).image fun c=>-c
omit [Fintype G] in
@[simp] lemma e3 {A C:Finset G} {x z:G} :
  z∈dn A C x↔ -z∈C∧x+z∈A:=by
 classical
 simp only[dn,mem_image,mem_filter]
 constructor
 ·rintro ⟨c,⟨hc,OP⟩,rfl⟩
  exact ⟨by simpa,by simpa[Qy] using OP⟩
 ·rintro ⟨OQ,Nh⟩
  refine ⟨-z, ?_,by simp⟩
  exact ⟨OQ,by simpa[Qy] using Nh⟩
omit [Fintype G] in
lemma wX (A C:Finset G) (x:G) :
  (dn A C x).card=(C.filter fun c=>x-c∈A).card:=by
 classical
 unfold dn
 rw[Finset.card_image_of_injective]
 intro a b h
 exact neg_injective h
lemma dz
  {B:aj G} {a8:NNReal} {A C:Finset G} {x:G}
  (hC:C⊆(B.ai a8).Zc) :
  dn A C x⊆(B.ai a8).Zc:=by
 intro z hz
 have OR:=(e3.mp hz).1
 exact aj.ec.mp (hC OR)
lemma bk
  {A C:Finset G} (_hC:C.Nonempty) (x:G) :
  a9 A C x=(dn A C x).card/(C.card:Real):=by
 classical
 rw[a9,ao]
 let e:G ≃ G:=Equiv.subLeft x
 rw[Qk e
  (fun y:G=>bs A y*af C (x-y))
  (fun c:G=>bs A (x-c)*af C c)
  (fun c=>by simp[e])]
 rw[wX]
 simp only[bs,af,Qw]
 have gX (c:G) :
   (if x-c∈A then (1:Real) else 0) *
     (if c∈C then (C.card:Real)⁻¹ else 0) =
    if c∈C∧x-c∈A then (C.card:Real)⁻¹ else 0:=by
  by_cases hc:c∈C<;>by_cases ha:x-c∈A<;>simp[hc,ha]
 simp_rw[gX]
 rw[←QE]
 have eI :
   (Finset.univ.filter fun c:G=>c∈C∧x-c∈A) =
    C.filter fun c=>x-c∈A:=by
  ext c
  simp
 rw[eI]
 simp
open Function MeasureTheory
open scoped ENNReal Pointwise
omit [AddCommGroup G] [Fintype G] in
lemma hZ (A:Finset G) :
  ag.aS A=(@mu Real _ _) A:=by
 funext x
 simp[ag.aS,mu_apply]
lemma eg (aX a3:Finset G) :
  ag.a2
    (ag.aS aX)
    (ag.aS a3) =
   (al ((@mu Real _ _) aX) (mu a3)):=by
 funext x
 rw[hZ,hZ,
  ag.a2,eL]
 simp
lemma og
  (aX a3 S:Finset G) (t:G) :
  ((aC (((aC ((@mu (ℂ) _ _) (-aX)) (((Set.indicator S fun _↦(1:_)):G→ℂ))))) (mu a3))) t =
   Complex.ofReal
    (ag.bC
     (fun x↦ag.a2
      (ag.aS aX)
      (ag.aS a3) (x-t))
     (ag.bJ S)):=by
 classical
 let a:G→Real:=(@mu Real _ _) aX
 let b:G→Real:=(@mu Real _ _) a3
 let kH:G→Real:=(Set.indicator S fun _↦(1:_))
 have ox :
   ag.bC
     (fun x↦ag.a2
      (ag.aS aX)
      (ag.aS a3) (x-t))
     (ag.bJ S) =
    ⟪τ t ((al a b)),kH⟫_[Real]:=by
  rw[eg]
  unfold ag.bC
   ag.bJ
  simp only[Sg,SV,
   R3,QZ,a,b,kH,Qm,
   mem_coe]
 have uO :
   ((aC (((aC ((@mu Real _ _) (-aX)) kH))) b)) t =
    ag.bC
     (fun x↦ag.a2
      (ag.aS aX)
      (ag.aS a3) (x-t))
     (ag.bJ S):=by
  calc
   ((aC (((aC ((@mu Real _ _) (-aX)) kH))) b)) t =
     ((aC (((aC kH b))) ((@mu Real _ _) (-aX)))) t:=by
      apply Uu
      calc
       (aC (((aC ((@mu Real _ _) (-aX)) kH))) b) =
         (aC kH (((aC ((@mu Real _ _) (-aX)) b)))):=by
          rw[fA ((@mu Real _ _) (-aX)) kH,
           iT]
       _=(aC kH (((aC b ((@mu Real _ _) (-aX)))))):=by
          rw[fA ((@mu Real _ _) (-aX)) b]
       _=(aC (((aC kH b))) ((@mu Real _ _) (-aX))):=by
          rw[iT]
   _=((al (((aC kH b))) a)) t:=by
    rw[←CK (K:=Real) aX,iM]
   _=⟪τ t a,(aC kH b)⟫_[Real]:=by
    rw[tS]
    exact RCLike.conj_wInner_symm (𝕜:=Real)
     (1:G→Real) ((aC kH b)) (τ t a)
   _=⟪(al (τ t a) b),kH⟫_[Real]:=by
    exact(kW
     (τ t a) b kH).symm
   _=⟪τ t ((al a b)),kH⟫_[Real]:=by rw[rh]
   _=_:= ox.symm
 have LK:((↑) ∘ kH:G→ Complex)=((Set.indicator S fun _↦(1:_)):G→ Complex):=by
  ext x
  by_cases hx:x∈S<;>simp[kH,hx]
 rw[←uO]
 change((aC (((aC ((@mu Complex _ _) (-aX)) (((Set.indicator S fun _↦(1:_)):G→ Complex))))) (mu a3))) t =
  (Complex.ofReal ∘ ((aC (((aC ((@mu Real _ _) (-aX)) kH))) b))) t
 rw[Complex.ql,Complex.ql]
 simp only[Complex.yJ,b]
 rw[LK]
lemma ca
  (aX a3 S:Finset G) :
  ag.bC
    (ag.a2
     (ag.aS aX)
     (ag.aS a3))
    (ag.bJ S) =
   ∑ x∈S,((al ((@mu Real _ _) aX) (mu a3))) x:=by
 classical
 rw[eg]
 unfold ag.bC
  ag.bJ
 simp only[Td,Q3,mul_zero]
 rw[←QE]
 have eI:Finset.univ.filter (fun x:G=>x∈S)=S:=by ext; simp
 rw[eI]
lemma nh
  {D:aj G} {aX a3 S:Finset G} {epsilon delta:Real}
  (fY:aX.Nonempty) (ho:a3.Nonempty)
  (ft:1-delta≤ ∑ x∈S,((al ((@mu Real _ _) aX) (mu a3))) x)
  (uf: ∀ t∈D.Zc,
   |ag.bW aX a3 S t -
     ag.bW aX a3 S 0| ≤
    epsilon*(aX.card:Real)*a3.card) :
  1-delta-epsilon ≤
   ag.bC
    (ag.d9
     (ag.aS D.Zc)
     (ag.a2
      (ag.aS aX)
      (ag.aS a3)))
    (ag.bJ S):=by
 have Ni :=
  ag.ji
   fY ho uf
 have dc :
   1-delta ≤
    ag.bC
     (ag.a2
      (ag.aS aX)
      (ag.aS a3))
     (ag.bJ S):=by
  rwa[ca]
 have ic:=(abs_le.mp Ni).1
 linarith
section zQ
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
def bj (A aL a0:Finset G) (p:Nat):Real :=
 (4:Real)⁻¹ *
   (b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))^(2*p) /
  (A.card:Real)^(2*p)
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma kI
  (A:Finset G) (x:G) :
  (cA.ef A x:Real) =
   ((al ((Set.indicator A fun _↦(1:Real))) ((Set.indicator A fun _↦(1:_))))) x:=by
 classical
 rw[cA.ef,eL]
 have ox :
   ((#(Finset.univ.filter fun t:G↦x-t∈A∧ -t∈A):Nat):Real) =
    ∑ t:G,if x-t∈A∧ -t∈A then (1:Real) else 0:=by
  simp
 rw[ox]
 refine Qk (Equiv.subLeft x) _ _ (fun y↦ ?_)
 simp only[SX,Qm]
 have eY:x-y-x= -y:=by abel
 rw[eY]
 split_ifs<;>simp_all
lemma gQ
  (A aL a0:Finset G) (p:Nat) (hp:p≠0)
  (rH:aL.Nonempty) (uZ:a0.Nonempty) :
  (∑ u:Fin p→G,
    ((cA.cS A aL u).card:Real) *
     (cA.cS A a0 u).card) =
   (aL.card:Real)*a0.card *
    (b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:Real))) ((Set.indicator A fun _↦(1:_))))))^p:=by
 classical
 let gH:G→Real:=(al ((Set.indicator A fun _↦(1:Real))) ((Set.indicator A fun _↦(1:_))))
 have rI: ∀ x,0≤gH x:=fun x ↦
  dM Set.cZ Set.cZ x
 have pV:=cA.vY A aL a0 p (fun _↦(1:Real))
 have kz :
   (∑ u:Fin p→G,
     cA.wK (cA.cS A aL u)
      (cA.cS A a0 u) (fun _↦(1:Real))) =
    ∑ u:Fin p→G,
     ((cA.cS A aL u).card:Real) *
      (cA.cS A a0 u).card:=by
  apply Io rfl
  intro u _
  simp[cA.wK]
 have oL :
   (∑ ey∈aL, ∑ b₂∈a0,
     (cA.ef A (ey-b₂):Real)^p) =
    ∑ x:G,((al ((Set.indicator aL fun _↦(1:Real))) ((Set.indicator a0 fun _↦(1:_))))) x*gH x^p:=by
  rw[lJ]
  simp[Qm,gH,kI]
 have uh :
   ((al ((Set.indicator aL fun _↦(1:Real))) ((Set.indicator a0 fun _↦(1:_))))) =
    fun x↦(aL.card:Real)*a0.card *
     ((al ((@mu Real _ _) aL) (mu a0))) x:=by
  ext x
  simp only[eL,Qm,mu_apply]
  rw[Qj]
  apply Io rfl
  intro y _
  by_cases hy:y∈aL<;>by_cases EM:y-x∈a0
  ·simp only[mem_coe,RP hy,RP EM,Rc,
    star_trivial,Q3]
   have yg:(aL.card:Real)≠0:=by
    exact_mod_cast rH.card_ne_zero
   have yh:(a0.card:Real)≠0:=by
    exact_mod_cast uZ.card_ne_zero
   field_simp
  ·simp[hy,EM]
  ·simp[hy]
  ·simp[hy]
 have oO:=jd hp
  ((al ((@mu NNReal _ _) aL) (mu a0))) gH
 rw[kz] at pV
 simp only[Q3] at pV
 calc
  (∑ u:Fin p→G,
    ((cA.cS A aL u).card:Real) *
     (cA.cS A a0 u).card) =
    ∑ ey∈aL, ∑ b₂∈a0,
     (cA.ef A (ey-b₂):Real)^p:=by
   simpa using pV
  _ =
    ∑ x:G,((al ((Set.indicator aL fun _↦(1:Real))) ((Set.indicator a0 fun _↦(1:_))))) x*gH x^p:=by
   exact oL
  _=(aL.card:Real)*a0.card *
     ∑ x:G,((al ((@mu Real _ _) aL) (mu a0))) x*gH x^p:=by
   rw[uh]
   rw[Qj]
   apply Io rfl
   intro x _
   ring
  _=(aL.card:Real)*a0.card *
    (b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:Real))) ((Set.indicator A fun _↦(1:_))))))^p:=by
   congr 1
   rw[oO]
   apply Io rfl
   intro x _
   simp only[RG,Q2,QK,
    QC (rI x),NNReal.lb,
    NNReal.iF,gH]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
theorem qD (A B : Finset G) (p : Nat) :
    (∑ u : Fin p → G, ((cA.cS A B u).card : Real)) =
      (A.card : Real) ^ p * B.card := by
  classical
  have sB :
      ∑ u : Fin p → G, (cA.cS A B u).card =
        A.card ^ p * B.card := by
    simp only [lK, cA.cS,
      Set.indicator_apply, mem_coe, mem_filter,
      mul_sum, sum_mul, @sum_comm G, Fintype.piFinset_univ,
      sum_pow']
    congr with b
    refine Fintype.sum_equiv (Equiv.subLeft fun _ : Fin p ↦ b) _ _ (fun u ↦ ?_)
    simp only [Equiv.subLeft_apply]
    by_cases hb : b ∈ B
    · simp only [hb, true_and, if_pos, mul_one]
      rw [Fintype.prod_boole]
      simp only [Pi.sub_apply]
      by_cases h : ∀ i : Fin p, b - u i ∈ A <;> simp [h]
    · simp [hb]
  exact_mod_cast sB
lemma pW
  (A aL a0:Finset G) (p:Nat) (u0:2≤p)
  (hB:(aL∩a0).Nonempty) (hA:A.Nonempty) :
  ∃ u:Fin p→G,
   (cA.cS A aL u).Nonempty ∧
   (cA.cS A a0 u).Nonempty ∧
   bj A aL a0 p ≤
    ((cA.cS A aL u).card:Real)/aL.card ∧
   bj A aL a0 p ≤
    ((cA.cS A a0 u).card:Real)/a0.card:=by
 classical
 have hp:p≠0:=by omega
 have rH:aL.Nonempty:=hB.mono inter_subset_left
 have uZ:a0.Nonempty:=hB.mono inter_subset_right
 have uJ:A.Nonempty:=hA
 let aX:(Fin p→G)→Finset G:=fun u↦cA.cS A aL u
 let a3:(Fin p→G)→Finset G:=fun u↦cA.cS A a0 u
 let N:Real:=(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:Real))) ((Set.indicator A fun _↦(1:_))))))
 let g:(Fin p→G)→Real:=fun u↦(aX u).card*(a3 u).card
 have hg: ∀ u,0≤g u:=fun u↦by dsimp[g]; positivity
 have Am: ∑ u,g u=(aL.card:Real)*a0.card*N^p:=by
  simpa[g,aX,a3,N] using
   gQ A aL a0 p hp rH uZ
 obtain ⟨b,hb⟩:=hB
 obtain ⟨a,ha⟩:=hA
 let sC:Fin p→G:=fun _↦b-a
 have v5:b∈aX sC:=by
  simp only[aX,cA.jn,sC]
  refine ⟨(inter_subset_left hb), ?_⟩
  intro i
  have:b-(b-a)=a:=by abel
  rwa[this]
 have v7:b∈a3 sC:=by
  simp only[a3,cA.jn,sC]
  refine ⟨(inter_subset_right hb), ?_⟩
  intro i
  have:b-(b-a)=a:=by abel
  rwa[this]
 have rV:0< ∑ u,g u:=by
  exact Finset.sum_pos' (fun u _↦hg u) ⟨sC,Sz _,by
   dsimp only[g]
   exact QM (by exact_mod_cast(Finset.card_pos.mpr ⟨b,v5⟩))
    (by exact_mod_cast(Finset.card_pos.mpr ⟨b,v7⟩))⟩
 have Hc:0<N^p:=by
  have jt:0<(aL.card:Real)*a0.card:=by positivity
  rw[Am] at rV
  rcases mul_pos_iff.mp rV with gw | eY
  ·exact gw.2
  ·exact(Rd jt.le eY.1).elim
 let M:Real :=
  2⁻¹ *N^p*(Real.sqrt aL.card*Real.sqrt a0.card) /
   (A.card:Real)^p
 have hM:0<M:=by
  dsimp[M]
  have J1:(0:Real)<A.card:=by exact_mod_cast uJ.card_pos
  have yg:(0:Real)<aL.card:=by exact_mod_cast rH.card_pos
  have yh:(0:Real)<a0.card:=by exact_mod_cast uZ.card_pos
  exact Rn (QM (QM (by norm_num) Hc)
   (QM (Real.sqrt_pos.2 yg) (Real.sqrt_pos.2 yh)))
   (RF J1 p)
 have H7: ∑ u,((aX u).card:Real)=(A.card:Real)^p*aL.card:=by
  simpa[aX] using qD A aL p
 have H8: ∑ u,((a3 u).card:Real)=(A.card:Real)^p*a0.card:=by
  simpa[a3] using qD A a0 p
 have mx: ∃ u,M^2≤g u:=by
  by_cases h: ∀ u,g u≠0→M^2≤g u
  ·have vE: ∃ u,g u≠0:=by
    by_contra hn
    push Not at hn
    have: ∑ u,g u=0:=by simp[hn]
    linarith
   obtain ⟨u,hu⟩:=vE
   exact ⟨u,h u hu⟩
  ·push Not at h
   obtain ⟨u₁,H9,Gd⟩:=h
   have As:(2:Real)* ∑ u with g u<M^2,g u< ∑ u,g u:=by
    rw[←lt_div_iff₀' (by norm_num:(0:Real)<2),Ri]
    calc
     ∑ u with g u<M^2,g u =
       ∑ u with g u<M^2∧g u≠0,
        Real.sqrt (g u)*Real.sqrt (g u):=by
      simp_rw[Ta (hg _), ←Finset.filter_filter,
       Finset.sum_filter_ne_zero]
     _< ∑ u with g u<M^2∧g u≠0,
        M*Real.sqrt (g u):=by
      apply Tt
      ·exact ⟨u₁,Finset.mem_filter.mpr ⟨Sz _,Gd,H9⟩⟩
      ·intro u hu
       have OS:=(Finset.mem_filter.mp hu).2.1
       have Nj:=(Finset.mem_filter.mp hu).2.2
       exact Sk ((Real.sqrt_lt' hM).2 OS)
        (Real.sqrt_pos.2 ((hg u).lt_of_ne' Nj))
     _≤ ∑ u,M*Real.sqrt (g u) :=
      Tj fun u↦by positivity
     _=M*(∑ u,Real.sqrt ((aX u).card) *
        Real.sqrt ((a3 u).card)):=by
      rw[Qj]
      apply Io rfl
      intro u _
      dsimp only[g]
      rw[Real.sqrt_mul (by positivity:(0:Real)≤(aX u).card)]
     _≤M*(Real.sqrt (∑ u,((aX u).card:Real)) *
        Real.sqrt (∑ u,((a3 u).card:Real))):=by
      gcongr
      exact Real.sum_sqrt_mul_sqrt_le _ (fun _↦by positivity)
       (fun _↦by positivity)
     _=(2:Real)⁻¹ * ∑ u,g u:=by
      dsimp only[M]
      rw[H7,H8,Real.sqrt_mul' _ (by positivity),
       Real.sqrt_mul' _ (by positivity),
       Q7 (Real.sqrt _),Ta,
       ←Qo,Tz, ←Real.sqrt_mul,
       Qo,Ta,Am,QN,Qo]
      all_goals positivity
   by_contra z2
   push Not at z2
   have Dr: ∑ u,g u= ∑ u with g u<M^2,g u:=by
    congr 1
    symm
    exact Finset.filter_eq_self.mpr (fun u _↦z2 u)
   rw[Dr] at As
   linarith
 obtain ⟨u,hu⟩:=mx
 have tb:bj A aL a0 p ≤
   (((aX u).card:Real)/aL.card) *
    (((a3 u).card:Real)/a0.card):=by
  dsimp[bj,M,N,g] at hu ⊢
  have J1:(A.card:Real)≠0:=by exact_mod_cast uJ.card_ne_zero
  have yg:(aL.card:Real)≠0:=by exact_mod_cast rH.card_ne_zero
  have yh:(a0.card:Real)≠0:=by exact_mod_cast uZ.card_ne_zero
  rw[div_mul_div_comm,Qs (by positivity)]
  simpa[QL,TY,pow_mul',show(2:Real)^2=4 by norm_num,
   Uf (show 0≤(aL.card:Real) by positivity),
   Uf (show 0≤(a0.card:Real) by positivity),
   J1,yg,yh,S5] using hu
 have J2:0<g u:=(SY hM).trans_le hu
 have EN:0<((aX u).card:Real)*(a3 u).card:=by
  simpa only[g] using J2
 have EO:0<((aX u).card:Real)∧0<((a3 u).card:Real):=by
  rcases mul_pos_iff.mp EN with gw | eY
  ·exact gw
  ·exact(Rd (Q5 _) eY.1).elim
 have xx:0<((aX u).card:Real):=EO.1
 have Ge:0<((a3 u).card:Real):=EO.2
 refine ⟨u,Finset.card_pos.mp (by exact_mod_cast xx),
  Finset.card_pos.mp (by exact_mod_cast Ge), ?_, ?_⟩
 ·have r9:((a3 u).card:Real)≤a0.card:=by
   exact_mod_cast Qu (cA.kG A a0 u)
  exact tb.trans (Sq (by positivity)
   ((Q9 (by positivity:(0:Real)<a0.card)).2 r9))
 ·have r8:((aX u).card:Real)≤aL.card:=by
   exact_mod_cast Qu (cA.kG A aL u)
  exact tb.trans (RQ (by positivity)
   ((Q9 (by positivity:(0:Real)<aL.card)).2 r8))
structure aW (A aL a0:Finset G)
  (p:Nat) (epsilon delta:Real) where
 aX:Finset G
 a3:Finset G
 u1:aX⊆aL
 rJ:a3⊆a0
 oS:1-delta ≤
  ag.bC
   (ag.a2
    (ag.aS aX)
    (ag.aS a3))
   (ag.bJ (s p epsilon aL a0 A))
 tz:bj A aL a0 p ≤
  (aX.card:Real)/aL.card
 tA:bj A aL a0 p ≤
  (a3.card:Real)/a0.card
namespace aW
def bg
  (A aL a0:Finset G) (p:Nat) (epsilon:Real):Finset G :=
 s p epsilon aL a0 A∩(aL-a0)
omit [DiscreteMeasurableSpace G] in
lemma oT
  (A aL a0:Finset G) (p:Nat) (epsilon:Real) :
  bg A aL a0 p epsilon⊆aL-a0 :=
 Sd
omit [DiscreteMeasurableSpace G] in
lemma lO
  {A aL a0:Finset G} {p:Nat} {epsilon delta:Real}
  (data:aW A aL a0 p epsilon delta)
  (cu:delta<1):data.aX.Nonempty∧data.a3.Nonempty:=by
 have ft:1-delta ≤
   ∑ x∈s p epsilon aL a0 A,((al ((@mu Real _ _) data.aX) (mu data.a3))) x:=by
  simpa only[ca] using
   data.oS
 constructor
 ·by_contra v8
  have ss:data.aX=∅:=not_nonempty_iff_eq_empty.mp v8
  rw[ss] at ft
  simp at ft
  linarith
 ·by_contra v8
  have ss:data.a3=∅:=not_nonempty_iff_eq_empty.mp v8
  rw[ss] at ft
  simp at ft
  linarith
omit [DiscreteMeasurableSpace G] in
lemma ni
  {A aL a0:Finset G} {p:Nat} {epsilon delta:Real}
  (data:aW A aL a0 p epsilon delta) :
  1-delta ≤
   ag.bC
    (ag.a2
     (ag.aS data.aX)
     (ag.aS data.a3))
    (ag.bJ
     (bg A aL a0 p epsilon)):=by
 have Ia:1-delta ≤
   ∑ x∈s p epsilon aL a0 A,
    ((al ((@mu Real _ _) data.aX) (mu data.a3))) x:=by
  simpa only[ca] using
   data.oS
 have hsum :
   ∑ x∈bg A aL a0 p epsilon,
     ((al ((@mu Real _ _) data.aX) (mu data.a3))) x =
    ∑ x∈s p epsilon aL a0 A,
     ((al ((@mu Real _ _) data.aX) (mu data.a3))) x:=by
  apply Ro Sh
  intro x xA LL
  rw[←UQ]
  intro Nk
  apply LL
  have EP :
    x∈Function.support ((al ((@mu Real _ _) data.aX) (mu data.a3))):=Nk
  have J3:x∈data.aX-data.a3:=by
   simpa only[f8 cC cC,jo,
    ←coe_sub,mem_coe] using EP
  obtain ⟨a₁,z3,a₂,z4,Hd⟩:=Finset.mem_sub.mp J3
  exact Finset.mem_inter.mpr ⟨xA,
   Finset.mem_sub.mpr ⟨a₁,data.u1 z3,a₂,
    data.rJ z4,Hd⟩⟩
 rw[ca,hsum]
 exact Ia
omit [DiscreteMeasurableSpace G] in
lemma gK
  {A aL a0:Finset G} {p:Nat} {epsilon delta:Real}
  (data:aW A aL a0 p epsilon delta)
  (cu:delta<1) :
  (bg A aL a0 p epsilon).Nonempty:=by
 by_contra z2
 have ss:bg A aL a0 p epsilon=∅ :=
  not_nonempty_iff_eq_empty.mp z2
 have ft:=data.ni
 rw[ss] at ft
 simp[ag.bC,
  ag.bJ] at ft
 linarith
end aW
lemma q4
  {A:Finset G} {p:Nat} {epsilon delta:Real}
  (aL a0:Finset G) (eM:0<epsilon) (tB:epsilon≤1)
  (cu:0<delta) (hp:Even p) (u0:2≤p)
  (v9:epsilon⁻¹ *Real.log (2/delta)≤p)
  (hB:(aL∩a0).Nonempty) (hA:A.Nonempty)
  (ow: ∃ x,x∈aL-a0∧x∈A-A ∧
   x∉s p epsilon aL a0 A) :
  Nonempty (aW A aL a0 p epsilon delta):=by
 obtain ⟨aX,fY,a3,ho,ft,y2,y3⟩ :=
  cA.v3 aL a0 eM tB cu hp u0
   v9 hB hA ow
 refine ⟨{
  aX:=aX
  a3:=a3
  u1:=fY
  rJ:=ho
  oS:= ?_
  tz:= ?_
  tA:= ?_ }⟩
 ·rwa[ca]
 ·simpa only[bj] using y2
 ·simpa only[bj] using y3
lemma l6
  {A:Finset G} {p:Nat} {epsilon delta:Real}
  (aL a0:Finset G) (cu:0<delta) (u0:2≤p)
  (hB:(aL∩a0).Nonempty) (hA:A.Nonempty)
  (kF: ∀ x,x∈aL-a0→x∈A-A →
   x∈s p epsilon aL a0 A) :
  Nonempty (aW A aL a0 p epsilon delta):=by
 classical
 obtain ⟨u,fY,ho,y2,y3⟩ :=
  pW A aL a0 p u0 hB hA
 let aX:=cA.cS A aL u
 let a3:=cA.cS A a0 u
 have Cn:aX⊆aL:=cA.kG A aL u
 have Co:a3⊆a0:=cA.kG A a0 u
 have hp:0<p:=by omega
 let i:Fin p:=⟨0,hp⟩
 have LN:aX-a3⊆s p epsilon aL a0 A:=by
  intro x hx
  obtain ⟨a₁,z3,a₂,z4,Hd⟩:=Finset.mem_sub.mp hx
  apply kF x
  ·exact Finset.mem_sub.mpr ⟨a₁,Cn z3,a₂,Co z4,Hd⟩
  ·have J4:=(cA.jn.mp z3).2 i
   have J5:=(cA.jn.mp z4).2 i
   refine Finset.mem_sub.mpr ⟨a₁-u i,J4,a₂-u i,J5, ?_⟩
   rw[←Hd]
   abel
 have hsum :
   ∑ x∈s p epsilon aL a0 A,((al ((@mu Real _ _) aX) (mu a3))) x=1:=by
  calc
   ∑ x∈s p epsilon aL a0 A,((al ((@mu Real _ _) aX) (mu a3))) x =
     ∑ x:G,((al ((@mu Real _ _) aX) (mu a3))) x:=by
    apply Ro (S7 _)
    intro x _ LO
    rw[←UQ]
    intro Nl
    apply LO
    apply LN
    have LP:x∈Function.support ((al ((@mu Real _ _) aX) (mu a3))):=Nl
    simpa only[f8 cC cC,jo,
     ←coe_sub,mem_coe] using LP
   _=1:=by
    rw[jI]
    simp only[Rc,star_trivial]
    rw[kU _ (by simpa[aX] using fY),
     kU _ (by simpa[a3] using ho),QT]
 refine ⟨{
  aX:=aX
  a3:=a3
  u1:=Cn
  rJ:=Co
  oS:= ?_
  tz:=by simpa[aX] using y2
  tA:=by simpa[a3] using y3 }⟩
 rw[ca,hsum]
 linarith
lemma kJ
  {A:Finset G} {p:Nat} {epsilon delta:Real}
  (aL a0:Finset G) (eM:0<epsilon) (tB:epsilon≤1)
  (cu:0<delta) (hp:Even p) (u0:2≤p)
  (v9:epsilon⁻¹ *Real.log (2/delta)≤p)
  (hB:(aL∩a0).Nonempty) (hA:A.Nonempty) :
  Nonempty (aW A aL a0 p epsilon delta):=by
 classical
 by_cases ow: ∃ x,x∈aL-a0∧x∈A-A ∧
   x∉s p epsilon aL a0 A
 ·exact q4 aL a0 eM tB
   cu hp u0 v9 hB hA ow
 ·apply l6 aL a0 cu u0 hB hA
  intro x OT Ep
  by_contra OU
  exact ow ⟨x,OT,Ep,OU⟩
structure cb
  {A aL a0:Finset G} {p:Nat} {epsilon delta:Real}
  (data:aW A aL a0 p epsilon delta)
  (parent:aj G) (dR:NNReal)
  (source:Finset G) (aq bq:Nat)
  (bm:Real) where
 child:aj G
 k2:child.a1
 rK:child.rank≤parent.rank+aq
 tC:child.Zc⊆(parent.ai dR).Zc
 nH:source.card≤bq*child.Zc.card
 oU: ∀ t∈child.Zc,
  |ag.bW
    data.aX data.a3
     (aW.bg A aL a0 p epsilon) t -
   ag.bW
    data.aX data.a3
     (aW.bg A aL a0 p epsilon) 0| ≤
   bm*(data.aX.card:Real)*data.a3.card
def cb.mono
  {A aL a0:Finset G} {p:Nat} {epsilon delta:Real}
  {data:aW A aL a0 p epsilon delta}
  {parent:aj G} {dR:NNReal} {source:Finset G}
  {aq bq zr tc:Nat}
  {bm lx:Real}
  (P:cb data parent dR source
   aq bq bm)
  (cK:aq≤zr)
  (ch:bq≤tc)
  (EL:bm≤lx) :
  cb data parent dR source
   zr tc lx where
 child:=P.child
 k2:=P.k2
 rK:=P.rK.trans (Nat.add_le_add_left cK _)
 tC:=P.tC
 nH:=P.nH.trans
  (QQ P.child.Zc.card ch)
 oU:=by
  intro t ht
  calc
   |ag.bW
     data.aX data.a3
      (aW.bg A aL a0 p epsilon) t -
    ag.bW
     data.aX data.a3
      (aW.bg A aL a0 p epsilon) 0|
     ≤ bm*(data.aX.card:Real)*data.a3.card :=
    P.oU t ht
   _≤lx*(data.aX.card:Real)*data.a3.card:=by
    gcongr
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma kK
  (D aX a3:Finset G) :
  ag.d9
    (ag.aS D)
    (ag.a2
     (ag.aS aX)
     (ag.aS a3)) =
   (aC ((@mu Real _ _) D) (((al (mu aX) (mu a3))))):=by
 funext x
 rw[hZ,
  eg,
  ag.d9,cR]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma j7
  (D aX a3 S:Finset G) :
  ag.bC
    (ag.d9
     (ag.aS D)
     (ag.a2
      (ag.aS aX)
      (ag.aS a3)))
    (ag.bJ S) =
   ∑ x∈S,((aC ((@mu Real _ _) D) (((al (mu aX) (mu a3)))))) x:=by
 classical
 rw[kK]
 unfold ag.bC
  ag.bJ
 simp only[Td,Q3,mul_zero]
 rw[←QE]
 have eI:Finset.univ.filter (fun x:G↦x∈S)=S:=by ext; simp
 rw[eI]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma lS
  {D aX a3 S:Finset G} {gH:G→Real}
  {mass threshold:Real}
  (oV:0≤threshold)
  (rI: ∀ x,0≤gH x)
  (sD: ∀ x∈S,threshold≤gH x)
  (ft:mass ≤
   ag.bC
    (ag.d9
     (ag.aS D)
     (ag.a2
      (ag.aS aX)
      (ag.aS a3)))
    (ag.bJ S)) :
  threshold*mass ≤
   ∑ x:G,((aC ((@mu Real _ _) D) (((al (mu aX) (mu a3)))))) x*gH x:=by
 classical
 rw[j7] at ft
 have zs: ∀ x:G,
   0≤((aC ((@mu Real _ _) D) (((al (mu aX) (mu a3)))))) x:=by
  intro x
  exact py cC
   (fun y↦dM cC cC y) x
 calc
  threshold*mass ≤
    threshold* ∑ x∈S,
     ((aC ((@mu Real _ _) D) (((al (mu aX) (mu a3)))))) x :=
   iO ft oV
  _= ∑ x∈S,
    threshold*((aC ((@mu Real _ _) D) (((al (mu aX) (mu a3)))))) x:=by
   rw[Qj]
  _≤ ∑ x∈S,
    ((aC ((@mu Real _ _) D) (((al (mu aX) (mu a3)))))) x*gH x:=by
   apply QI
   intro x hx
   rw[Qx threshold]
   exact iO (sD x hx) (zs x)
  _≤ ∑ x:G,
    ((aC ((@mu Real _ _) D) (((al (mu aX) (mu a3)))))) x*gH x:=by
   exact Tj fun x ↦
    Qn (zs x) (rI x)
omit [DecidableEq G] [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma my
  {w f:G→Real} (hw: ∀ x,0≤w x)
  (u2: ∑ x:G,w x=1) {lower:Real}
  (ic:lower≤ ∑ x:G,w x*f x) :
  ∃ x:G,lower≤f x:=by
 classical
 obtain ⟨x,_hx,Ds⟩ :=
  TX Finset.univ f (Finset.univ_nonempty :
   (Finset.univ:Finset G).Nonempty)
 refine ⟨x,ic.trans ?_⟩
 calc
  ∑ y:G,w y*f y≤ ∑ y:G,w y*f x:=by
   apply QI
   intro y _
   exact iO (Ds y (by simp)) (hw y)
  _=f x:=by rw[←Qt,u2,QT]
omit [AddCommGroup G] [DecidableEq G] [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma ly
  {w f:G→Real} {T:Finset G} (hT:T.Nonempty)
  (hw: ∀ x,0≤w x) (wa: ∀ x,x∉T→w x=0)
  (u2: ∑ x:G,w x=1) {lower:Real}
  (ic:lower≤ ∑ x:G,w x*f x) :
  ∃ x∈T,lower≤f x:=by
 classical
 obtain ⟨x,OV,Ds⟩:=TX T f hT
 refine ⟨x,OV,ic.trans ?_⟩
 calc
  ∑ y:G,w y*f y≤ ∑ y:G,w y*f x:=by
   apply QI
   intro y _
   by_cases hy:y∈T
   ·exact iO (Ds y hy) (hw y)
   ·rw[wa y hy,zero_mul,zero_mul]
  _=f x:=by rw[←Qt,u2,QT]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma lz
  (D E:Finset G) :
  ((↑) ∘ aN.bh D E:G→Real) =
   (aC (((al ((@mu Real _ _) D) (mu E)))) (((al (mu E) (mu D))))):=by
 unfold aN.bh
  aN.dU
 simp only[NNReal.gF,NNReal.oA,
  NNReal.iF]
 symm
 rw[kp,fA ((@mu Real _ _) E) (mu D)]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma kn
  (D E:Finset G) (f:G→Real) (p:Nat) :
  aK
    ((↑) ∘ aN.bh D E) f p =
   ∑ z:G,((al ((@mu Real _ _) D) (mu E))) z *
    aK
     (fun x↦((al ((@mu Real _ _) E) (mu D))) (x-z)) f p:=by
 rw[lz]
 unfold aK
 simp_rw[cR,Qt]
 rw[QD]
 apply Io rfl
 intro z _
 rw[Qj]
 apply Io rfl
 intro x _
 ring
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma lA
  {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty)
  (f:G→Real) (p:Nat) {lower:Real}
  (ic:lower≤aK
   ((↑) ∘ aN.bh D E) f p) :
  ∃ z∈D-E,
   ((z+ᵥ E)∩D).Nonempty ∧
   lower≤aK ((al ((@mu Real _ _) (z+ᵥ E)) (mu D))) f p:=by
 let w:G→Real:=(al ((@mu Real _ _) D) (mu E))
 let F:G→Real:=fun z ↦
  aK (fun x↦((al ((@mu Real _ _) E) (mu D))) (x-z)) f p
 have OW:(D-E).Nonempty:=by
  obtain ⟨d,hd⟩:=hD
  obtain ⟨e,he⟩:=hE
  refine ⟨d-e, ?_⟩
  exact Finset.mem_sub.mpr ⟨d,hd,e,he,rfl⟩
 have hw: ∀ z,0≤w z:=by
  intro z
  exact dM cC cC z
 have wa: ∀ z,z∉D-E→w z=0:=by
  intro z hz
  rw[←UQ]
  intro OX
  apply hz
  have ER:z∈Function.support w:= OX
  simpa only[w,f8 cC cC,
   jo, ←coe_sub,mem_coe] using ER
 have u2: ∑ z:G,w z=1:=by
  dsimp only[w]
  rw[jI]
  simp only[Rc,star_trivial]
  rw[kU _ hD,kU _ hE,QT]
 have Gf:lower≤ ∑ z:G,w z*F z:=by
  rw[←kn]
  exact ic
 obtain ⟨z,hz,y4⟩ :=
  ly OW hw wa u2 Gf
 obtain ⟨d,hd,e,he,OY⟩:=Finset.mem_sub.mp hz
 refine ⟨z,hz, ?_, ?_⟩
 ·refine ⟨d,Finset.mem_inter.mpr ⟨?_,hd⟩⟩
  rw[Ug]
  refine ⟨e,he, ?_⟩
  rw[←OY]
  simp only[Uz]
  exact Rs d e
 ·dsimp only[F] at y4
  have uh :
    (fun x↦((al ((@mu Real _ _) E) (mu D))) (x-z)) =
     (al ((@mu Real _ _) (z+ᵥ E)) (mu D)):=by
   rw[←vH,rh]
   rfl
  rw[uh] at y4
  exact y4
lemma lB
  {D E A:Finset G} (hD:D.Nonempty) (hE:E.Nonempty)
  (_hA:A.Nonempty) {p:Nat} (hp:0<p) {lower:Real}
  (AW:0≤lower)
  (ic:lower ≤
   an.aM
    ((↑) ∘ aN.bh D E)
    ((al ((@mu Real _ _) A) (mu A))) p) :
  ∃ z∈D-E,
   ((z+ᵥ E)∩D).Nonempty ∧
   lower≤(b0 p ((al (mu (z+ᵥ E)) (mu D))) ((al ((@mu Real _ _) A) (mu A)))):=by
 let nu:=aN.bh D E
 have rm:an.cw
   ((↑) ∘ nu:G→Real):=by
  refine ⟨?_, ?_⟩
  ·intro x
   exact_mod_cast(aN.gS D E x)
  ·simpa using QA (fun r:NNReal↦(r:Real))
    (aN.i7 hD hE)
 have yU:lower^p ≤
   aK ((↑) ∘ nu:G→Real)
    ((al ((@mu Real _ _) A) (mu A))) p:=by
  calc
   lower^p ≤
     an.aM
       ((↑) ∘ nu:G→Real) ((al ((@mu Real _ _) A) (mu A))) p^p :=
    Qp AW ic p
   _=aK ((↑) ∘ nu:G→Real)
     ((al ((@mu Real _ _) A) (mu A))) p :=
    an.jr rm hp
 obtain ⟨z,hz,ui,ES⟩ :=
  lA hD hE
   ((al ((@mu Real _ _) A) (mu A))) p (by simpa[nu] using yU)
 let u3:G→NNReal:=(al ((@mu NNReal _ _) (z+ᵥ E)) (mu D))
 have rH:(z+ᵥ E).Nonempty:=by
  obtain ⟨e,he⟩:=hE
  refine ⟨z+e, ?_⟩
  rw[Ug]
  exact ⟨e,he,rfl⟩
 have He:an.cw
   ((↑) ∘ u3:G→Real):=by
  refine ⟨?_, ?_⟩
  ·intro x
   exact_mod_cast(dM cC cC x:0≤u3 x)
  ·dsimp only[u3]
   simp only[NNReal.gF,NNReal.iF]
   rw[jI]
   simp only[Rc,star_trivial]
   rw[kU _ rH,kU _ hD,QT]
 have Dt:lower^p ≤
   aK ((↑) ∘ u3:G→Real)
    ((al ((@mu Real _ _) A) (mu A))) p:=by
  simpa only[u3,NNReal.gF,NNReal.iF] using ES
 have ET:lower^p ≤
   an.aM
     ((↑) ∘ u3:G→Real) ((al ((@mu Real _ _) A) (mu A))) p^p:=by
  rw[an.jr He hp]
  exact Dt
 have AX:0 ≤
   an.aM
    ((↑) ∘ u3:G→Real) ((al ((@mu Real _ _) A) (mu A))) p :=
  an.j1 He _ _
 have yi:lower ≤
   an.aM
    ((↑) ∘ u3:G→Real) ((al ((@mu Real _ _) A) (mu A))) p:=by
  by_contra hnot
  have xP:=QV hnot
  have LQ:=pow_lt_pow_left₀ xP AX hp.ne'
  exact(Rd ET) LQ
 refine ⟨z,hz,ui, ?_⟩
 rw[aN.dN u3
  ((al ((@mu Real _ _) A) (mu A))) hp] at yi
 exact yi
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma mX
  {A D:Finset G} (hA:A.Nonempty) (x:G) :
  (A.card:Real)*((aC ((@mu Real _ _) D) (mu A))) x=a9 A D x:=by
 classical
 rw[cR,a9,ao,Qj]
 let e:G ≃ G:=Equiv.subLeft x
 rw[Qk e
  (fun z:G↦(A.card:Real)*((@mu Real _ _) D z*mu A (x-z)))
  (fun y:G↦(A.card:Real)*((@mu Real _ _) D (x-y)*mu A y))]
 ·apply Io rfl
  intro y _
  simp only[mu_apply,bs,af]
  have r0:(A.card:Real)≠0:=by exact_mod_cast hA.card_ne_zero
  by_cases J6:y∈A
  ·by_cases J7:x-y∈D
   ·simp only[RP J6,RP J7,Q3]
    calc
     (A.card:Real)*((D.card:Real)⁻¹ *(A.card:Real)⁻¹) =
       (D.card:Real)⁻¹ *((A.card:Real)*(A.card:Real)⁻¹):=by ring
     _=(D.card:Real)⁻¹ :=by rw[Tw r0,Q3]
     _=1*(D.card:Real)⁻¹ :=by rw[QT]
   ·simp[J6,J7]
  ·simp[J6]
 ·intro y
  simp[e]
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma pX
  (d a₁ a₂ a:G→Real) :
  ⟪(aC d (((al a₁ a₂)))),(al a a)⟫_[Real] =
   ⟪(aC d a),(aC (((al a₂ a₁))) a)⟫_[Real]:=by
 rw[rk,rk]
 congr 1
 change(al (((al a a))) (((al a₁ a₂))))=(al (((aC (((al a₂ a₁))) a))) a)
 simp_rw[←iM,pI,conjneg_conjneg]
 calc
  (aC (((aC a (conjneg a)))) (((aC (conjneg a₁) a₂)))) =
    (aC (((aC a (conjneg a₁)))) (((aC (conjneg a) a₂)))) :=
   ir _ _ _ _
  _=(aC (((aC (conjneg a₁) a))) (((aC a₂ (conjneg a))))):=by
   rw[fA a,fA (conjneg a) a₂]
  _=(aC (((aC (conjneg a₁) a₂))) (((aC a (conjneg a))))) :=
   ir _ _ _ _
  _=(aC (((aC (((aC a₂ (conjneg a₁)))) a))) (conjneg a)):=by
   rw[fA (conjneg a₁) a₂]
   exact(iT _ _ _).symm
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma jx
  {D aX a3 A S:Finset G}
  (_hD:D.Nonempty) (fY:aX.Nonempty)
  (ho:a3.Nonempty) (hA:A.Nonempty)
  {threshold mass lower:Real} (oV:0≤threshold)
  (rI: ∀ x,0≤((al ((@mu Real _ _) A) (mu A))) x)
  (sD: ∀ x∈S,threshold≤((al ((@mu Real _ _) A) (mu A))) x)
  (ft:mass ≤
   ag.bC
    (ag.d9
     (ag.aS D)
     (ag.a2
      (ag.aS aX)
      (ag.aS a3)))
    (ag.bJ S))
  (ic:lower≤threshold*mass) :
  ∃ x:G,(A.card:Real)*lower≤a9 A D x:=by
 have EU:=lS oV rI
  sD ft
 have xB:=pX
  ((@mu Real _ _) D) (mu aX) (mu a3) (mu A)
 rw[Sg,Sg] at xB
 simp only[SV,R3] at xB
 let w:G→Real:=(aC (((al ((@mu Real _ _) a3) (mu aX)))) (mu A))
 let f:G→Real:=(aC ((@mu Real _ _) D) (mu A))
 have hw: ∀ x,0≤w x:=by
  intro x
  exact py
   (fun y↦dM cC cC y) cC x
 have u2: ∑ x:G,w x=1:=by
  dsimp only[w]
  rw[uM,jI]
  simp only[Rc,star_trivial]
  rw[kU _ ho,kU _ fY,QT,
   kU _ hA,Q3]
 have AA:lower≤ ∑ x:G,w x*f x:=by
  calc
   lower≤threshold*mass:=ic
   _≤ ∑ x:G,
     ((aC ((@mu Real _ _) D) (((al (mu aX) (mu a3)))))) x*((al (mu A) (mu A))) x :=
    EU
   _= ∑ x:G,w x*f x:=by
    rw[xB]
    apply Io rfl
    intro x _
    rw[Qx]
 obtain ⟨x,hx⟩:=my hw u2 AA
 refine ⟨x, ?_⟩
 rw[←mX hA]
 exact iO hx (Q5 _)
end zQ
lemma bK
  {A C:Finset G} (hC:C.Nonempty) {x:G}
  (hx:0<a9 A C x) :
  (dn A C x).Nonempty:=by
 by_contra h
 have Gg: ¬ 0<(dn A C x).card:=by
  intro ch
  exact h (Finset.card_pos.mp ch)
 have ch:(dn A C x).card=0:=Nat.eq_zero_of_not_pos Gg
 rw[bk hC,ch] at hx
 norm_num at hx
structure bt where
 ba:aj G
 outer:NNReal
 inner:NNReal
 regular:0< inner∧inner≤outer ∧
  (ba.ai (outer+inner)).Zc.card ≤
   2*(ba.ai (outer-inner)).Zc.card
namespace bt
def Zc (c:bt (G:=G)):Finset G :=
 (c.ba.ai c.outer).Zc
omit [DecidableEq G] in
lemma aE (c:bt (G:=G)):c.Zc.Nonempty :=
 (c.ba.ai c.outer).aE
def en (c:bt (G:=G))
  (A:Finset G) (hA:A.Nonempty) (EV:A⊆c.Zc) :
  aY G where
 ba:=c.ba
 outer:=c.outer
 inner:=c.inner
 regular:=c.regular
 set:=A
 nonempty:=hA
 mo:=EV
omit [DecidableEq G] in
lemma n7 (B:aj G) (dF:B.a1) :
    ∃ c:bt (G:=G),
      c.ba=B∧c.outer=1∧c.Zc=B.Zc:=by
  let d:Nat:=max B.rank 1
  let aF:NNReal:=1/(400*(d:NNReal))
  have hd:0<d:=by simp[d]
  have EW:0<aF:=by
    dsimp[aF]
    positivity
  have zt:aF≤1/(100*(d:NNReal)):=by
    dsimp[aF]
    apply Rb (by positivity) (by positivity)
    exact Qi (by norm_num:(100:NNReal)≤400)
      (by positivity)
  have EX:aF≤1:=by
    apply zt.trans
    rw[Q9]
    · exact_mod_cast(show 1≤100*d by omega)
    · positivity
  have jt:=dF aF (by simpa[d] using zt)
  have Az:(100:Real)*d*(aF:Real)≤1/4:=by
    have LS:(aF:Real)≤1/(400*(d:Real)):=by
      exact_mod_cast(show aF≤1/(400*(d:NNReal)) by rfl)
    have OZ:(0:Real)<d:=by exact_mod_cast hd
    calc
      (100:Real)*d*(aF:Real) ≤
          100*d*(1/(400*(d:Real))):=by gcongr
      _=1/4:=by field_simp; ring
  have EY :
      ((B.ai (1+aF)).Zc.card:Real) ≤
        2*((B.ai (1-aF)).Zc.card:Real):=by
    nlinarith[jt.1,jt.2,Az,
      show(0:Real)<B.Zc.card by
        exact_mod_cast B.aE.card_pos]
  have ch :
      (B.ai (1+aF)).Zc.card ≤
        2*(B.ai (1-aF)).Zc.card:=by
    exact_mod_cast EY
  let c:bt (G:=G) :=
    { ba:=B
      outer:=1
      inner:=aF
      regular:=⟨EW,EX,ch⟩ }
  refine ⟨c,rfl,rfl, ?_⟩
  simp only[Zc,c,aj.oD]
end bt
def di {original:Finset G} (s:aA original)
  (child:bt (G:=G)) (x:G)
  (gw:0<a9 s.restriction.set child.Zc x) :
  aA original where
 restriction:=child.en
  (dn s.restriction.set child.Zc x)
  (bK child.aE gw)
  (dz (B:=child.ba) (a8:=child.outer)
   (A:=s.restriction.set) (C:=child.Zc) (x:=x) fun _ h=>h)
 shift:=s.shift-x
 eR:=by
  intro z hz
  have O0:=(e3.mp hz).2
  have gL:=s.eR (x+z) O0
  have heq:z-(s.shift-x)=(x+z)-s.shift:=by abel
  rwa[heq]
@[simp] lemma hO {original:Finset G}
  (s:aA original) (child:bt (G:=G)) (x:G)
  (gw:0<a9 s.restriction.set child.Zc x) :
  (di s child x gw).Zd =
   a9 s.restriction.set child.Zc x:=by
 change((dn s.restriction.set child.Zc x).card:Real) /
   child.Zc.card=a9 s.restriction.set child.Zc x
 exact(bk child.aE x).symm
lemma fa
  {original:Finset G} (s:aA original)
  (child:bt (G:=G)) (x:G)
  {q aU:Real} {aq:Nat}
  (gw:0<a9 s.restriction.set child.Zc x)
  (c8:q*s.Zd ≤
   a9 s.restriction.set child.Zc x)
  (cK:child.ba.rank≤ s.rank+aq)
  (ch:Real.exp (-aU)*(s.card:Real)≤child.Zc.card) :
  dk q aq aU s.restriction
   (di s child x gw).restriction:=by
 refine ⟨?_,cK, ?_⟩
 ·change q*s.Zd ≤
   ((dn s.restriction.set child.Zc x).card:Real) /
    child.Zc.card
  rw[←bk child.aE]
  exact c8
 ·change Real.exp (-aU)*(s.restriction.card:Real) ≤
   child.Zc.card
  exact ch
section sE
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
lemma nj
  {D:aj G} {aX a3 S:Finset G} {error:Real}
  (fY:aX.Nonempty) (ho:a3.Nonempty)
  (jl: ∀ t∈D.Zc,
   (aJ (∞) (τ t ((aC (((aC ((@mu Complex _ _) (-aX)) (((Set.indicator S fun _↦(1:_)):G→ Complex))))) (mu a3))) -
     ((aC (((aC ((@mu Complex _ _) (-aX)) (((Set.indicator S fun _↦(1:_)):G→ Complex))))) (mu a3))))) ≤
    error) :
  ∀ t∈D.Zc,
   |ag.bW aX a3 S t -
     ag.bW aX a3 S 0| ≤
    error*(aX.card:Real)*a3.card:=by
 classical
 let F:G→ Complex :=
  (aC (((aC ((@mu Complex _ _) (-aX)) (((Set.indicator S fun _↦(1:_)):G→ Complex))))) (mu a3))
 have hF (u:G) :
   F u=Complex.ofReal
    (ag.bW aX a3 S u /
     (aX.card*a3.card:Real)):=by
  dsimp only[F]
  rw[og]
  congr 1
  exact ag.d7
   fY ho S u
 intro t ht
 have eY: -t∈D.Zc:=aj.ec.mpr ht
 have gX :
   ‖(τ (-t) F-F) 0‖ ≤error:=by
  calc
   ‖(τ (-t) F-F) 0‖ ≤(aJ (∞) (τ (-t) F-F)) :=
    vu
   _≤error:=by simpa only[F] using jl (-t) eY
 have Hf :
   |(ag.bW aX a3 S t -
     ag.bW aX a3 S 0) /
     (aX.card*a3.card:Real)| ≤error:=by
  rw[Rw,QZ,sub_neg_eq_add,zero_add,
   hF t,hF 0, ←Complex.ofReal_sub,Rf,QK,
   ←UT] at gX
  exact gX
 have ch:(0:Real)<(aX.card:Real)*a3.card :=
  QM (by exact_mod_cast fY.card_pos) (by exact_mod_cast ho.card_pos)
 rw[TE,RT ch] at Hf
 have pH:=(QF ch).mp Hf
 nlinarith
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma hQ
  (aX a3 S:Finset G) (t:G) :
  ag.bW a3 aX (-S) t =
   ag.bW aX a3 S (-t):=by
 classical
 unfold ag.bW
 rw[QD]
 apply Io rfl
 intro a₁ _
 apply Io rfl
 intro a₂ _
 have F6 (u:G) :
   ag.bJ (-S) u =
    ag.bJ S (-u):=by
  by_cases hu:u∈ -S
  ·have eY: -u∈S:=by simpa using hu
   simp[ag.bJ,hu,eY]
  ·have eY: -u∉S:=by
    intro h
    apply hu
    simpa using h
   simp[ag.bJ,hu,eY]
 rw[F6]
 have uV: -(t+a₂-a₁)= -t+a₁-a₂:=by abel
 rw[uV]
 ring
lemma h4
  {D:aj G} {aX a3 S:Finset G} {error:Real}
  (fY:aX.Nonempty) (ho:a3.Nonempty)
  (jl: ∀ t∈D.Zc,
   (aJ (∞) (τ t ((aC (((aC ((@mu Complex _ _) (-a3)) (((Set.indicator ((-S:Finset G)) fun _↦(1:_)):G→ Complex))))) (mu aX))) -
     ((aC (((aC ((@mu Complex _ _) (-a3)) (((Set.indicator ((-S:Finset G)) fun _↦(1:_)):G→ Complex))))) (mu aX))))) ≤
    error) :
  ∀ t∈D.Zc,
   |ag.bW aX a3 S t -
     ag.bW aX a3 S 0| ≤
    error*(aX.card:Real)*a3.card:=by
 classical
 have dc:=nj
  (D:=D) (aX:=a3) (a3:=aX) (S:=-S) (error:=error)
  ho fY jl
 intro t ht
 have eY: -t∈D.Zc:=aj.ec.mpr ht
 have h:=dc (-t) eY
 rw[hQ aX a3 S (-t),
  hQ aX a3 S 0] at h
 simpa[Qx,Q6,Qo] using h
noncomputable def l7 (M L:Finset G):Nat :=
 ⌈1+Real.log (min 1 ((L.card:Real)/M.card))⁻¹⌉₊
noncomputable def cm
  (M L:Finset G) (dv:Real) (m:Nat):Nat :=
 cQ (l7 M L)
  ((dv/m)/Real.exp 1)
lemma ei
    {A aL a0:Finset G} {p:Nat} {sigma delta:Real}
    (data:aW A aL a0 p sigma delta)
    (cu:delta<1)
    (dv:Real) (sF:0<dv)
    (m:Nat) (hm:m≠0)
    (bl:aj G) (sw:bl.a1)
    (aF:NNReal)
    (dy:aF+aF ≤
      1/(100*(max bl.rank 1:Nat):NNReal))
    (dh:Nat) (pT:0<dh)
    (bm:Real)
    (dV: ∀ (T:Finset G) (Delta:Finset (AddChar G Complex)),
      (Delta.card:Real) ≤
        aI.bf bl T (1/2) →
      2*dv +
          (2/(dh:Real) +
            400*((max bl.rank 1:Nat):Real) *
              (aF+aF:NNReal) +
            2*(1/2:Real)^m) *
          Real.sqrt
            (((aW.bg A aL a0 p sigma).card:Real) /
              data.aX.card)≤bm) :
    ∃ (T X:Finset G) (a8:NNReal) (fk:aj G)
      (Delta:Finset (AddChar G Complex)),
      ((((-data.a3).card:Real) ^
            cm
              (-(aW.bg A aL a0 p sigma))
              data.aX dv m/2*bl.Zc.card) /
          ((-data.a3+bl.Zc).card:Real) ^
            cm
              (-(aW.bg A aL a0 p sigma))
              data.aX dv m≤T.card) ∧
      T⊆bl.Zc∧X.Nonempty ∧
      (Delta.card:Real) ≤
        aI.bf bl T (1/2) ∧
      1/2≤a8∧a8≤1 ∧
      fk=bl.ai (a8 *
        aI.cJ bl T (1/2)) ∧
      Nonempty
        (cb data fk (aF+aF)
          (fk.ai aF).Zc Delta.card
          ((dh*ag.a6
              (aI.bf bl T (1/2))) ^
              Delta.card *
            4^(bl.rank+Delta.card))
          bm):=by
  classical
  let S:Finset G :=
    aW.bg A aL a0 p sigma
  have gM:=data.lO cu
  have Gh:(-data.a3).Nonempty:=by
    obtain ⟨a,ha⟩:=gM.2
    exact ⟨-a,by simpa using ha⟩
  have hS:S.Nonempty:=by
    simpa[S] using data.gK cu
  have LU:(-S).Nonempty:=by
    obtain ⟨s,hs⟩:=hS
    exact ⟨-s,by simpa using hs⟩
  obtain ⟨T,X,z,a8,fk,Delta,R,ue,_hzT,_hX,
      pP,nf,gI,lf,oQ,AU,
      fH,_hDeltaSpec,qi,oP,yd,vX,
      jl⟩ :=
    ag.fj
      (A:=-data.a3) Gh dv sF m hm
      (-S) data.aX LU gM.1 bl sw aF dy
      dh pT
  let n:Nat :=
    dh*ag.a6
      (aI.bf bl T (1/2))
  let pY:Real :=
    2*dv +
      (4*Real.pi*(Delta.card:Real) *
          ((((n:Nat):NNReal)⁻¹ :Real)) +
        400*((max bl.rank 1:Nat):Real) *
          (aF+aF:NNReal) +
        2*(1/2:Real)^m) *
      Real.sqrt ((S.card:Real)/data.aX.card)
  have l4 :
      4*Real.pi*(Delta.card:Real) *
          ((((n:Nat):NNReal)⁻¹ :Real))≤2/(dh:Real):=by
    simpa[n] using
      (ag.sv
        (aI.bf bl T (1/2))
        Delta.card dh fH pT)
  have pV:pY≤bm:=by
    calc
      pY ≤
          2*dv +
            (2/(dh:Real) +
              400*((max bl.rank 1:Nat):Real) *
                (aF+aF:NNReal) +
              2*(1/2:Real)^m) *
            Real.sqrt ((S.card:Real)/data.aX.card):=by
        dsimp only[pY]
        gcongr
      _≤bm:=by simpa[S] using dV T Delta fH
  refine ⟨T,X,a8,fk,Delta, ?_,ue,pP,fH,
    gI,lf,oQ,⟨?_⟩⟩
  · simpa[S,cm,l7] using nf
  refine
    { child:=R
      k2:=qi
      rK:= ?_
      tC:=yd
      nH:= ?_
      oU:= ?_ }
  · simpa[oQ] using oP
  · simpa[n,SZ] using vX
  · have uf:=h4
      gM.1 gM.2 (D:=R) (error:=pY) (by
        intro t ht
        simpa[S,n,pY,Qo] using jl t ht)
    intro t ht
    calc
      |ag.bW
          data.aX data.a3
            (aW.bg A aL a0 p sigma) t -
        ag.bW
          data.aX data.a3
            (aW.bg A aL a0 p sigma) 0|
          ≤ pY*(data.aX.card:Real)*data.a3.card:=by
            simpa[S] using uf t ht
      _≤bm*(data.aX.card:Real)*data.a3.card:=by
        gcongr
end sE
def bV {original:Finset G} (s:aA original)
  (ak aB:bt (G:=G)) (epsilon:Real):Prop :=
 ∃ x∈s.e8,
  (1-epsilon)*s.Zd ≤
   a9 s.restriction.set ak.Zc x ∧
  (1-epsilon)*s.Zd ≤
   a9 s.restriction.set aB.Zc x
structure kL {original:Finset G}
  (s:aA original) (epsilon aU:Real)
  (aq:Nat) where
 eta:NNReal
 NU:s.restriction.ba.vR s.restriction.outer eta
 ak:bt (G:=G)
 aB:bt (G:=G)
 nS:ak.Zc ⊆
  (s.restriction.ba.ai eta).Zc
 pZ:aB.Zc ⊆
  (s.restriction.ba.ai eta).Zc
 rankOne:ak.ba.rank≤ s.rank+aq
 p0:aB.ba.rank≤ s.rank+aq
 mz:Real.exp (-aU)*(s.card:Real)≤ak.Zc.card
 mA:Real.exp (-aU)*(s.card:Real)≤aB.Zc.card
end
end ay.ah
end
section
open scoped BigOperators
open Finset
namespace ay
namespace aw
variable {G:Type*} [Fintype G] [AddCommGroup G]
noncomputable def uj (f:G→ℝ):ℝ :=
 (∑ x,f x)/Fintype.card G
noncomputable def indicator (C:Finset G) (x:G):ℝ :=
 open scoped Classical in
 if x∈C then 1 else 0
noncomputable def af (C:Finset G) (x:G):ℝ :=
 (Fintype.card G:ℝ)/C.card*indicator C x
noncomputable def aT (B:Finset G) (f:G→ℝ):ℝ :=
 (∑ x∈B,f x)/B.card
noncomputable def bL (C B:Finset G):ℝ :=
 C.card/B.card
noncomputable def cO (B:Finset G) (p:ℕ) (f:G→ℝ):ℝ :=
 aT B fun x↦ |f x| ^p
noncomputable def Zp (f:G→ℝ) (C:Finset G):ℝ :=
 uj fun x↦f x*af C x
lemma mP {C:Finset G} (hC:C.Nonempty) (f:G→ℝ) :
  Zp f C=aT C f:=by
 classical
 unfold Zp aT uj af indicator
 rw[show(∑ x:G,f x *
   ((Fintype.card G:ℝ)/(C.card:ℝ)*if x∈C then 1 else 0)) =
   (Fintype.card G:ℝ)/(C.card:ℝ)* ∑ x∈C,f x by
  simp_rw[Td,Q3,mul_zero]
  simp only[←QE]
  simp only[subset_univ,filter_mem_eq_of_subset]
  rw[←Qt]
  exact Qx _ _]
 have O1:(C.card:ℝ)≠0:=by exact_mod_cast hC.card_ne_zero
 have yj:(Fintype.card G:ℝ)≠0:=by
  exact_mod_cast(SN:Fintype.card G≠0)
 field_simp
omit [AddCommGroup G] [Fintype G] in
lemma g1 {C:Finset G} (f:G→ℝ) :
  |aT C f| ≤aT C fun x↦ |f x| :=by
 unfold aT
 calc
  |(∑ x∈C,f x)/(C.card:ℝ)| =
    |(∑ x∈C,f x)| /(C.card:ℝ):=by
   rw[TE]
   congr 1
   exact QC (Q5 C.card)
  _≤(∑ x∈C, |f x|)/(C.card:ℝ) :=
   Qz (TQ f C) (by positivity)
omit [AddCommGroup G] [Fintype G] in
lemma mB {C:Finset G} (hC:C.Nonempty)
  (p:ℕ) (f:G→ℝ) :
  (aT C fun x↦ |f x|)^p≤cO C p f:=by
 let w:G→ℝ:=fun _↦(C.card:ℝ)⁻¹
 have hw: ∀ x∈C,0≤w x:=by
  intro x hx
  exact inv_nonneg.mpr (by positivity)
 have O2: ∑ x∈C,w x=1:=by
  simp[w,hC.card_ne_zero]
 have hz: ∀ x∈C,0≤ |f x| :=by
  intro x hx
  positivity
 have h:=Real.pow_arith_mean_le_arith_mean_pow C w (fun x↦ |f x|)
  hw O2 hz p
 simpa[aT,cO,w,Ri,Qj] using h
lemma s4 {B C:Finset G} (hC:C.Nonempty)
  (w6:C⊆B) (p:ℕ) (f:G→ℝ) :
  bL C B* |Zp f C| ^p≤cO B p f:=by
 have hB:B.Nonempty:=hC.mono w6
 have nI: |Zp f C| ^p≤cO C p f:=by
  rw[mP hC]
  calc
   |aT C f| ^p
     ≤ (aT C fun x↦ |f x|)^p :=
      Qp (Q8 _) (g1 f) p
   _≤cO C p f:=mB hC p f
 have uI:0≤bL C B:=by
  unfold bL
  positivity
 calc
  bL C B* |Zp f C| ^p
    ≤ bL C B*cO C p f:=iO nI uI
  _=(∑ x∈C, |f x| ^p)/B.card:=by
   unfold bL cO aT
   field_simp[hC.card_ne_zero,hB.card_ne_zero]
  _≤(∑ x∈B, |f x| ^p)/B.card:=by
   apply Qz _ (by positivity)
   exact Ry w6 fun _ _ _↦by positivity
  _=cO B p f:=rfl
lemma q5 {B C:Finset G} (hC:C.Nonempty)
  (w6:C⊆B) (p:ℕ) (_hp:0<p) (f:G→ℝ)
  (dK bo ε:ℝ) (fF:0≤bo) (hε:0≤ε)
  (c8:(2/3:ℝ)^p≤bL C B)
  (ew: |(dK-bo)-Zp f C| ≤ε*bo/4) :
  |dK-bo| ≤ε*bo ∨
   (ε*bo/2)^p≤cO B p f:=by
 by_cases rB: |dK-bo| ≤ε*bo
 ·exact Or.inl rB
 right
 have JH: |dK-bo| ≤
   |(dK-bo)-Zp f C| + |Zp f C| :=by
  calc
   |dK-bo| =
     |((dK-bo)-Zp f C)+Zp f C| :=by ring_nf
   _≤ |(dK-bo)-Zp f C| + |Zp f C| :=UP _ _
 have nI:3*(ε*bo)/4< |Zp f C| :=by
  have iV:ε*bo< |dK-bo| :=QV rB
  nlinarith
 have uI:0≤bL C B:=by
  unfold bL
  positivity
 have Gi:(3*(ε*bo)/4)^p≤ |Zp f C| ^p :=
  Qp (by positivity) nI.le p
 have AY :
   (2/3:ℝ)^p*(3*(ε*bo)/4)^p ≤
    bL C B* |Zp f C| ^p:=by
  exact QW c8 Gi (by positivity) uI
 calc
  (ε*bo/2)^p =
    (2/3:ℝ)^p*(3*(ε*bo)/4)^p:=by
   rw[←QL]
   congr 1
   ring
  _≤bL C B* |Zp f C| ^p:=AY
  _≤cO B p f:=s4 hC w6 p f
lemma nT {B C:Finset G} (hC:C.Nonempty)
  (w6:C⊆B) (p:ℕ) (hp:0<p) (f:G→ℝ)
  (dK bo:ℝ) (fF:0<bo)
  (c8:(2/3:ℝ)^p≤bL C B)
  (ew: |(dK-bo)-Zp f C| ≤bo/8) :
  bo/2≤dK ∨
   (bo/4)^p≤cO B p f:=by
 have Aq: |(dK-bo)-Zp f C| ≤
   (1/2:ℝ)*bo/4:=by
  convert ew using 1; ring
 have LV:=q5 hC w6 p hp f dK bo
  (1/2:ℝ) fF.le (by norm_num) c8 Aq
 rcases LV with rB | ow
 ·left
  have ic:=(abs_le.mp rB).1
  linarith
 ·right
  convert ow using 1; ring
lemma nk {B C:Finset G} (hC:C.Nonempty)
  (w6:C⊆B) (p:ℕ) (hp:0<p) (f:G→ℝ)
  (dK bo:ℝ) (fF:0<bo)
  (c8:(2/3:ℝ)^p≤bL C B)
  (ew: |(dK-bo)-Zp f C| ≤bo/8)
  (ee:cO B p f≤(bo/8)^p) :
  bo/2≤dK:=by
 rcases nT hC w6 p hp f dK bo fF
  c8 ew with rB | ow
 ·exact rB
 ·have Nm:p≠0:=Nat.ne_of_gt hp
  have Ib:(bo/8)^p<(bo/4)^p:=by
   apply pow_lt_pow_left₀
   ·nlinarith
   ·positivity
   ·exact Nm
  have:(bo/4)^p≤(bo/8)^p:= ow.trans ee
  exact(Rd this Ib).elim
end aw
end ay
end
section
open Finset
namespace ay
namespace aO
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def a4 (S:Finset G):Finset G :=
 S.image fun x↦x+x
omit [Fintype G] in
@[simp] lemma mY {S:Finset G} {x:G} :
  x∈a4 S↔ ∃ y∈S,y+y=x:=by
 simp[a4]
omit [Fintype G] in
lemma eJ {S:Finset G} (hS:S.Nonempty) :
  (a4 S).Nonempty:=by
 exact hS.image _
omit [Fintype G] in
lemma qE {S T:Finset G} (O3:S⊆T) :
  a4 S⊆a4 T:=by
 intro x hx
 obtain ⟨y,hy,rfl⟩:=mY.mp hx
 exact mY.mpr ⟨y,O3 hy,rfl⟩
omit [Fintype G] in
lemma qF (S:Finset G)
  (eU:Function.Injective (fun x:G↦x+x)) :
  #(a4 S)= #S:=by
 exact card_image_of_injective _ eU
omit [Fintype G] in
lemma pl (S T:Finset G)
  (eU:Function.Injective (fun x:G↦x+x)) :
  aw.bL (a4 S) (a4 T) =
   aw.bL S T:=by
 simp only[aw.bL,qF S eU,
  qF T eU]
omit [DecidableEq G] in
lemma sG
  {H:Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
  (B:aj G) (e:G ≃+ H) :
  B.Zc.image e=(B.map e).Zc:=by
 ext x
 constructor
 ·intro hx
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
  exact(aj.oE B e y).2 hy
 ·intro hx
  refine Finset.mem_image.mpr ⟨e.symm x, ?_,by simp⟩
  have AH:=(aj.oE B e (e.symm x)).1
  exact AH (by simpa using hx)
def hU (M:ℕ) (hM:Odd M) (B:aj (ZMod M)) :
  aj (ZMod M) :=
 B.map (aj.eK M hM)
lemma jO
    {M:ℕ} [NeZero M] (hM:Odd M) (B:aj (ZMod M)) :
    a4 B.Zc=(hU M hM B).Zc:=by
  rw[a4,hU, ←sG]
  apply Finset.image_congr
  intro x _
  exact aj.sS M hM x
@[simp] lemma u4
  (M:ℕ) (hM:Odd M) (B:aj (ZMod M)) :
  (hU M hM B).rank=B.rank:=by
 exact aj.Ap B (aj.eK M hM)
@[simp] lemma p3
  (M:ℕ) [NeZero M] (hM:Odd M) (B:aj (ZMod M)) :
  (hU M hM B).Zc.card=B.Zc.card:=by
 exact aj.tW M hM B
def bb (A' b4:Finset G):ℝ :=
 (Fintype.card G:ℝ) *
  qh
   (ao (af A') (af A'))
   (af (a4 b4))
lemma pn
  (eU:Function.Injective (fun x:G↦x+x))
  (A' b4:Finset G) :
  bb A' b4 =
   (Fintype.card G:ℝ)*(df A' b4:ℝ) *
    (#A':ℝ)⁻¹ ^2*(#b4:ℝ)⁻¹ :=by
 rw[bb,
  a4,
  jJ eU]
 ring
lemma nm
  (eU:Function.Injective (fun x:G↦x+x))
  {A' b4:Finset G} (qG:A'.Nonempty) (gN:b4.Nonempty) :
  bb A' b4 =
   (Fintype.card G:ℝ)*(df A' b4:ℝ) /
    ((#A':ℝ)^2*(#b4:ℝ)):=by
 rw[pn eU]
 have NV:(#A':ℝ)≠0:=by exact_mod_cast qG.card_ne_zero
 have Nn:(#b4:ℝ)≠0:=by exact_mod_cast gN.card_ne_zero
 field_simp
lemma j8
  {A' b4:Finset G} (gN:b4.Nonempty) :
  bb A' b4 =
   aw.aT (a4 b4) (fun x ↦
    (Fintype.card G:ℝ) *
     ao (af A') (af A') x):=by
 let D:=a4 b4
 let F:=ao (af A') (af A')
 have hD:D.Nonempty:=eJ gN
 have yb:(#D:ℝ)≠0:=by exact_mod_cast hD.card_ne_zero
 unfold bb aw.aT qh
 change(Fintype.card G:ℝ) *
   ∑ x:G,F x*af D x =
  (∑ x∈D,(Fintype.card G:ℝ)*F x)/(#D:ℝ)
 have vQ :
   (∑ x:G,F x*af D x) =
    (∑ x∈D,F x)*(#D:ℝ)⁻¹ :=by
  change(∑ x:G,F x*(if x∈D then (#D:ℝ)⁻¹ else 0))=_
  simp only[Td,mul_zero]
  rw[←QE]
  have eI:univ.filter (fun x:G↦x∈D)=D:=by ext; simp
  rw[eI,Qt]
 rw[vQ]
 rw[show(∑ x∈D,(Fintype.card G:ℝ)*F x) =
   (Fintype.card G:ℝ)* ∑ x∈D,F x by
  rw[Qj]]
 field_simp
omit [AddCommGroup G] in
lemma k3 {S:Finset G} (hS:S.Nonempty) :
  an.cw (af S):=by
 refine ⟨bO S, ?_⟩
 exact cf hS
omit [AddCommGroup G] in
lemma h5
  {S:Finset G} (hS:S.Nonempty) (p:ℕ) (f:G→ℝ) :
  aK (af S) f p =
   aw.cO S p f:=by
 have EZ:(#S:ℝ)≠0:=by exact_mod_cast hS.card_ne_zero
 unfold aK aw.cO aw.aT
  af
 change(∑ x:G,(if x∈S then (#S:ℝ)⁻¹ else 0)* |f x| ^p) =
  (∑ x∈S, |f x| ^p)/(#S:ℝ)
 simp only[ite_mul,zero_mul]
 rw[←QE]
 have eI:univ.filter (fun x:G↦x∈S)=S:=by ext; simp
 rw[eI]
 rw[←Qj,Qw]
 ring
omit [AddCommGroup G] in
lemma fb
  {S:Finset G} (hS:S.Nonempty) {p:ℕ} (hp:0<p)
  (f:G→ℝ) {C:ℝ} (_hC:0≤C)
  (ee :
   an.aM (af S) f p≤C) :
  aw.cO S p f≤C^p:=by
 have wJ:=k3 hS
 rw[←h5 hS p f,
  ←an.jr wJ hp]
 exact Qp
  (an.j1 wJ f p) ee p
structure eh (original:Finset G) where
 A':Finset G
 b4:Finset G
 B:Finset G
 B':Finset G
 translate:G
 alpha:ℝ
 p:ℕ
 f:G→ℝ
 jP:A'.Nonempty
 iZ:b4.Nonempty
 kM:B.Nonempty
 h6:b4⊆B'
 fL: ∀ x∈A',x-translate∈original
 fl: ∀ x∈b4,x-translate∈original
 i0:0≤alpha
 kN:alpha*(#B:ℝ)≤(#A':ℝ)
 jQ:alpha*(#B':ℝ)≤(#b4:ℝ)
 p_pos:0<p
 gf :
  (2/3:ℝ)^p≤aw.bL b4 B'
 e6 :
  |(bb A' b4 -
    (Fintype.card G:ℝ)/(#B:ℝ)) -
    aw.Zp f (a4 b4)| ≤
   ((Fintype.card G:ℝ)/(#B:ℝ))/8
 gg :
  aw.cO (a4 B') p f ≤
   (((Fintype.card G:ℝ)/(#B:ℝ))/8)^p
noncomputable def cr {original:Finset G}
  {s:ah.aA original}
  {ak aB:ah.bt (G:=G)} {epsilon:ℝ}
  (h:ah.bV s ak aB epsilon):G :=
 Classical.choose h
lemma c0 {original:Finset G}
  {s:ah.aA original}
  {ak aB:ah.bt (G:=G)} {epsilon:ℝ}
  (h:ah.bV s ak aB epsilon) :
  (1-epsilon)*s.Zd ≤
   a9 s.restriction.set ak.Zc (cr h) :=
 (Uo h).2.1
lemma ea {original:Finset G}
  {s:ah.aA original}
  {ak aB:ah.bt (G:=G)} {epsilon:ℝ}
  (h:ah.bV s ak aB epsilon) :
  (1-epsilon)*s.Zd ≤
   a9 s.restriction.set aB.Zc (cr h) :=
 (Uo h).2.2
def kO {original:Finset G}
  {s:ah.aA original}
  {epsilon aU:ℝ} {aq:ℕ}
  (P:ah.kL s epsilon aU aq)
  (h:ah.bV s P.ak P.aB epsilon):Finset G :=
 ah.dn s.restriction.set P.ak.Zc (cr h)
def g2 {original:Finset G}
  {s:ah.aA original}
  {epsilon aU:ℝ} {aq:ℕ}
  (P:ah.kL s epsilon aU aq)
  (h:ah.bV s P.ak P.aB epsilon):Finset G :=
 ah.dn s.restriction.set P.aB.Zc (cr h)
def a5 {original:Finset G}
  (s:ah.aA original) (epsilon:ℝ):ℝ :=
 (1-epsilon)*s.Zd
noncomputable def iG
    {original:Finset G} (s:ah.aA original)
    {epsilon aU:ℝ} {aq:ℕ}
    (P:ah.kL s epsilon aU aq)
    (aQ:ah.bV s P.ak P.aB epsilon)
    (_hepsilon_nonneg:0≤epsilon) (b2:epsilon<1)
    {p:ℕ} (hp:0<p) (f:G→ℝ)
    (jy:(2/3:ℝ)^p≤a5 s epsilon)
    (ew :
      |(bb
            (kO P aQ) (g2 P aQ) -
          (Fintype.card G:ℝ)/(#P.ak.Zc:ℝ)) -
          aw.Zp f (a4 (g2 P aQ))| ≤
        ((Fintype.card G:ℝ)/(#P.ak.Zc:ℝ))/8)
    (ee :
      an.aM
          (af (a4 P.aB.Zc)) f p ≤
        ((Fintype.card G:ℝ)/(#P.ak.Zc:ℝ))/8) :
    eh original:=by
  let x:G:=cr aQ
  let A':Finset G:=kO P aQ
  let b4:Finset G:=g2 P aQ
  let B:Finset G:=P.ak.Zc
  let B':Finset G:=P.aB.Zc
  let alpha:ℝ:=a5 s epsilon
  have lC:alpha≤a9 s.restriction.set B x:=by
    simpa[alpha,x,B,a5] using c0 aQ
  have oW:alpha≤a9 s.restriction.set B' x:=by
    simpa[alpha,x,B',a5] using ea aQ
  have b8:0<alpha:=by
    exact QM (sub_pos.mpr b2) s.dI
  have qG:A'.Nonempty:=by
    apply ah.bK P.ak.aE
    exact b8.trans_le lC
  have gN:b4.Nonempty:=by
    apply ah.bK P.aB.aE
    exact b8.trans_le oW
  have j9:b4⊆B':=by
    exact ah.dz
      (B:=P.aB.ba) (a8:=P.aB.outer)
      (A:=s.restriction.set) (C:=P.aB.Zc)
      (x:=x) (fun _ hz↦hz)
  have gO: ∀ z∈A',z-(s.shift-x)∈original:=by
    intro z hz
    have i1:x+z∈s.restriction.set :=
      (ah.e3.mp hz).2
    have hs:=s.eR (x+z) i1
    have heq:z-(s.shift-x)=(x+z)-s.shift:=by abel
    rwa[heq]
  have fP: ∀ z∈b4,z-(s.shift-x)∈original:=by
    intro z hz
    have i1:x+z∈s.restriction.set :=
      (ah.e3.mp hz).2
    have hs:=s.eR (x+z) i1
    have heq:z-(s.shift-x)=(x+z)-s.shift:=by abel
    rwa[heq]
  have nn:alpha*(#B:ℝ)≤(#A':ℝ):=by
    have wL:(0:ℝ)< #B:=by exact_mod_cast P.ak.aE.card_pos
    rw[ah.bk
      P.ak.aE x] at lC
    exact(Qs wL).mp lC
  have np:alpha*(#B':ℝ)≤(#b4:ℝ):=by
    have wb:(0:ℝ)< #B':=by exact_mod_cast P.aB.aE.card_pos
    rw[ah.bk
      P.aB.aE x] at oW
    exact(Qs wb).mp oW
  have qH :
      (2/3:ℝ)^p≤aw.bL b4 B':=by
    calc
      (2/3:ℝ)^p≤alpha:=jy
      _≤a9 s.restriction.set B' x:=by
        simpa[alpha,x,B',a5] using
          ea aQ
      _=aw.bL b4 B':=by
        rw[ah.bk
          P.aB.aE x]
        rfl
  have oX:(a4 B').Nonempty :=
    eJ P.aB.aE
  have uk :
      aw.cO (a4 B') p f ≤
        (((Fintype.card G:ℝ)/(#B:ℝ))/8)^p:=by
    apply fb oX hp f (by positivity)
    simpa[B,B'] using ee
  exact
    { A':=A'
      b4:=b4
      B:=B
      B':=B'
      translate:=s.shift-x
      alpha:=alpha
      p:=p
      f:=f
      jP:=qG
      iZ:=gN
      kM:=P.ak.aE
      h6:=j9
      fL:=gO
      fl:=fP
      i0:=b8.le
      kN:=nn
      jQ:=np
      p_pos:=hp
      gf:=qH
      e6:=by simpa[A',b4,B] using ew
      gg:=uk }
lemma lT
  (eU:Function.Injective (fun x:G↦x+x))
  {A' b4:Finset G} (qG:A'.Nonempty) (gN:b4.Nonempty)
  {bo:ℝ}
  (iB:bo/2≤bb A' b4) :
  bo*(#A':ℝ)^2*(#b4:ℝ) /
    (2*(Fintype.card G:ℝ)) ≤
   (df A' b4:ℝ):=by
 have hG:(0:ℝ)<Fintype.card G:=by
  exact_mod_cast(Fintype.card_pos:0<Fintype.card G)
 have J8:(0:ℝ)<(#A':ℝ)^2*(#b4:ℝ):=by
  positivity
 rw[nm eU qG gN] at iB
 have hmul :
   bo/2*((#A':ℝ)^2*(#b4:ℝ)) ≤
    (Fintype.card G:ℝ)*(df A' b4:ℝ) :=
  (Qs J8).mp iB
 rw[QF (QM (by norm_num) hG)]
 nlinarith
lemma mZ
  (eU:Function.Injective (fun x:G↦x+x))
  {A A' b4 B':Finset G} (qG:A'.Nonempty) (gN:b4.Nonempty)
  (j9:b4⊆B') (t:G)
  (gO: ∀ x∈A',x-t∈A)
  (fP: ∀ x∈b4,x-t∈A)
  {p:ℕ} (hp:0<p) (f:G→ℝ) {bo:ℝ}
  (fF:0<bo)
  (c8:(2/3:ℝ)^p≤aw.bL b4 B')
  (ew :
   |(bb A' b4-bo) -
     aw.Zp f (a4 b4)| ≤bo/8)
  (ee :
   aw.cO (a4 B') p f≤(bo/8)^p) :
  bo*(#A':ℝ)^2*(#b4:ℝ) /
    (2*(Fintype.card G:ℝ))≤(dL A:ℝ):=by
 have hC:(a4 b4).Nonempty:=eJ gN
 have w6:a4 b4⊆a4 B':=qE j9
 have E0 :
   (2/3:ℝ)^p ≤
    aw.bL (a4 b4) (a4 B'):=by
  rwa[pl b4 B' eU]
 have iB :
   bo/2≤bb A' b4 :=
  aw.nk hC w6 p hp f
   (bb A' b4) bo fF E0 ew ee
 have J9 :=
  lT eU qG gN iB
 have E1:df A' b4≤dL A :=
  iA t gO fP
 have Du :
   (df A' b4:ℝ)≤(dL A:ℝ):=by
  exact_mod_cast E1
 exact J9.trans Du
lemma ka
  (eU:Function.Injective (fun x:G↦x+x))
  {A A' b4 B B':Finset G}
  (qG:A'.Nonempty) (gN:b4.Nonempty) (hB:B.Nonempty)
  (j9:b4⊆B') (t:G)
  (gO: ∀ x∈A',x-t∈A)
  (fP: ∀ x∈b4,x-t∈A)
  {alpha:ℝ} (b8:0≤alpha)
  (oY:alpha*(#B:ℝ)≤(#A':ℝ))
  (nq:alpha*(#B':ℝ)≤(#b4:ℝ))
  {p:ℕ} (hp:0<p) (f:G→ℝ)
  (c8:(2/3:ℝ)^p≤aw.bL b4 B')
  (ew :
   |(bb A' b4 -
     (Fintype.card G:ℝ)/(#B:ℝ)) -
     aw.Zp f (a4 b4)| ≤
    ((Fintype.card G:ℝ)/(#B:ℝ))/8)
  (ee :
   aw.cO (a4 B') p f ≤
    (((Fintype.card G:ℝ)/(#B:ℝ))/8)^p) :
  alpha^3*(#B:ℝ)*(#B':ℝ)/2 ≤
   (dL A:ℝ):=by
 have hG:(0:ℝ)<Fintype.card G:=by
  exact_mod_cast(Fintype.card_pos:0<Fintype.card G)
 have yk:(0:ℝ)< #B:=by exact_mod_cast hB.card_pos
 have fF:(0:ℝ)<(Fintype.card G:ℝ)/(#B:ℝ) :=
  Rn hG yk
 have ic:=mZ eU qG gN j9 t
  gO fP hp f fF c8 ew ee
 have Ic :
   (alpha*(#B:ℝ))^2≤(#A':ℝ)^2 :=
  Qp (Qn b8 yk.le) oY 2
 have Ka :
   alpha^3*(#B:ℝ)^2*(#B':ℝ) ≤
    (#A':ℝ)^2*(#b4:ℝ):=by
  have hmul:=QW Ic nq
   (Qn b8 (Q5 _)) (sq_nonneg (#A':ℝ))
  nlinarith only[hmul]
 have kz :
   alpha^3*(#B:ℝ)*(#B':ℝ)/2 =
    (alpha^3*(#B:ℝ)^2*(#B':ℝ)) /
     (2*(#B:ℝ)):=by
  field_simp
 have oL :
   ((Fintype.card G:ℝ)/(#B:ℝ))*(#A':ℝ)^2 *
     (#b4:ℝ)/(2*(Fintype.card G:ℝ)) =
    ((#A':ℝ)^2*(#b4:ℝ))/(2*(#B:ℝ)):=by
  field_simp
 rw[oL] at ic
 rw[kz]
 exact(Qz Ka (by positivity)).trans ic
namespace eh
end eh
lemma l8
  (eU:Function.Injective (fun x:G↦x+x))
  {A A' b4 B B':Finset G}
  (qG:A'.Nonempty) (gN:b4.Nonempty) (hB:B.Nonempty)
  (j9:b4⊆B') (t:G)
  (gO: ∀ x∈A',x-t∈A)
  (fP: ∀ x∈b4,x-t∈A)
  {alpha K:ℝ} {d p:ℕ} (b8:0≤alpha)
  (oY:alpha*(#B:ℝ)≤(#A':ℝ))
  (nq:alpha*(#B':ℝ)≤(#b4:ℝ))
  (hp:0<p) (f:G→ℝ)
  (c8:(2/3:ℝ)^p≤aw.bL b4 B')
  (ew :
   |(bb A' b4 -
     (Fintype.card G:ℝ)/(#B:ℝ)) -
     aw.Zp f (a4 b4)| ≤
    ((Fintype.card G:ℝ)/(#B:ℝ))/8)
  (ee :
   aw.cO (a4 B') p f ≤
    (((Fintype.card G:ℝ)/(#B:ℝ))/8)^p)
  (AZ:Real.exp (-K*(d:ℝ)^12)*(Fintype.card G:ℝ)^2 ≤
   alpha^3*(#B:ℝ)*(#B':ℝ)/2) :
  Real.exp (-K*(d:ℝ)^12)*(Fintype.card G:ℝ)^2 ≤
   (dL A:ℝ):=by
 exact AZ.trans<|
  ka eU qG gN hB j9 t
   gO fP b8 oY nq hp f c8 ew ee
lemma ko
    {M:ℕ} [NeZero M] (hM:Odd M)
    {A A' b4 B B':Finset (ZMod M)}
    (qG:A'.Nonempty) (gN:b4.Nonempty) (hB:B.Nonempty)
    (j9:b4⊆B') (t:ZMod M)
    (gO: ∀ x∈A',x-t∈A)
    (fP: ∀ x∈b4,x-t∈A)
    {alpha K:ℝ} {d p:ℕ} (b8:0≤alpha)
    (oY:alpha*(#B:ℝ)≤(#A':ℝ))
    (nq:alpha*(#B':ℝ)≤(#b4:ℝ))
    (hp:0<p) (f:ZMod M→ℝ)
    (c8:(2/3:ℝ)^p≤aw.bL b4 B')
    (ew :
      |(bb A' b4 -
          (Fintype.card (ZMod M):ℝ)/(#B:ℝ)) -
          aw.Zp f (a4 b4)| ≤
        ((Fintype.card (ZMod M):ℝ)/(#B:ℝ))/8)
    (ee :
      aw.cO (a4 B') p f ≤
        (((Fintype.card (ZMod M):ℝ)/(#B:ℝ))/8)^p)
    (AZ:Real.exp (-K*(d:ℝ)^12) *
        (Fintype.card (ZMod M):ℝ)^2 ≤
      alpha^3*(#B:ℝ)*(#B':ℝ)/2) :
    Real.exp (-K*(d:ℝ)^12) *
        (Fintype.card (ZMod M):ℝ)^2≤(dL A:ℝ):=by
  apply l8
    (aj.eK M hM).injective qG gN hB j9 t
    gO fP b8 oY nq hp f c8 ew ee
    AZ
end
end aO
end ay
end
section
open Finset
open scoped NNReal
namespace ay
def f1 (K:ℝ):Prop :=
 0<K ∧
  ∀ (N:ℕ),1≤N →
   ∀ (A:Finset (ZMod (aD N))),A.Nonempty →
    ∀ d:ℕ,1≤d →
     Real.log (((aD N:ℕ):ℝ)/(#A:ℝ)) ≤
       (d:ℝ)*Real.log 2 →
      Real.exp (-K*(d:ℝ)^12) *
        ((aD N:ℕ):ℝ)^2 ≤
       (dL A:ℝ)
noncomputable def gn (G:Type*) [AddCommGroup G]:aj G where
 eX:=∅
 width:=fun _↦0
@[simp] lemma tD (G:Type*) [AddCommGroup G] :
  aj.rank (gn G)=0:=by
 change(∅:Finset (Zg G)).card=0
 simp
@[simp] lemma fZ (G:Type*) [AddCommGroup G] [Fintype G]
  (a8:ℝ≥0) :
  ((gn G).ai a8).Zc=(Finset.univ:Finset G):=by
 classical
 ext x
 simp[aj.Zm,gn]
@[simp] lemma oZ
  (G:Type*) [AddCommGroup G] [Fintype G] :
  (gn G).Zc=(Finset.univ:Finset G):=by
 simpa using fZ G 1
noncomputable def dA (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  br.aY (ZMod (aD N)) where
 ba:=gn (ZMod (aD N))
 outer:=1
 inner:=1
 regular:=by
  refine ⟨by norm_num,by norm_num, ?_⟩
  simp only[fZ]
  omega
 set:=A
 nonempty:=hA
 mo:=by
  intro x hx
  rw[fZ]
  simp
@[simp] lemma nU (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (dA N A hA).Zd =
   (#A:ℝ)/(aD N:ℕ):=by
 simp[br.aY.Zd,
  br.aY.e8,dA]
@[simp] lemma po (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (dA N A hA).rank=0:=by
 simp[br.aY.rank,dA]
@[simp] lemma pq (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (dA N A hA).card=aD N:=by
 simp[br.aY.card,
  br.aY.e8,dA]
noncomputable def bQ (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  ah.aA A where
 restriction:=dA N A hA
 shift:=0
 eR:=by
  intro x hx
  simpa[dA] using hx
@[simp] lemma p4 (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (bQ N A hA).Zd =
   (#A:ℝ)/(aD N:ℕ):=by
 exact nU N A hA
@[simp] lemma rL (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (bQ N A hA).rank=0:=by
 exact po N A hA
@[simp] lemma rM (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (bQ N A hA).card=aD N:=by
 exact pq N A hA
lemma l9
  {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  {original:Finset G} {d:ℕ}
  (s:ah.aA original)
  (c3:br.nF d s.Zd) :
  1<(1025/1024:ℝ)^(1024*(d+1))*s.Zd:=by
 have dc:(2:ℝ)≤(1025/1024:ℝ)^1024:=by
  have h:=UM (a:=(1/1024:ℝ)) (by norm_num) 1024
  norm_num at h
  exact h
 have hpow:(2:ℝ)^(d+1) ≤
   (1025/1024:ℝ)^(1024*(d+1)):=by
  calc
   (2:ℝ)^(d+1)≤((1025/1024:ℝ)^1024)^(d+1) :=
    Qp (by positivity) dc (d+1)
   _=(1025/1024:ℝ)^(1024*(d+1)):=by rw[←QU]
 change 1/(2:ℝ)^d≤ s.Zd at c3
 have hmul:=QW hpow c3 (by positivity) (by positivity)
 have kz:(2:ℝ)^(d+1)*(1/(2:ℝ)^d)=2:=by
  rw[RB]
  field_simp
 rw[kz] at hmul
 exact SI (by norm_num:(1:ℝ)<2) hmul
structure dm (N:ℕ)
  (A:Finset (ZMod (aD N))) (K:ℝ) (d:ℕ) where
 A':Finset (ZMod (aD N))
 b4:Finset (ZMod (aD N))
 B:Finset (ZMod (aD N))
 B':Finset (ZMod (aD N))
 translate:ZMod (aD N)
 alpha:ℝ
 p:ℕ
 f:ZMod (aD N)→ℝ
 jP:A'.Nonempty
 iZ:b4.Nonempty
 kM:B.Nonempty
 h6:b4⊆B'
 fL: ∀ x∈A',x-translate∈A
 fl: ∀ x∈b4,x-translate∈A
 i0:0≤alpha
 kN:alpha*(#B:ℝ)≤(#A':ℝ)
 jQ:alpha*(#B':ℝ)≤(#b4:ℝ)
 p_pos:0<p
 gf :
  (2/3:ℝ)^p≤aw.bL b4 B'
 e6 :
  |(aO.bb A' b4 -
    (Fintype.card (ZMod (aD N)):ℝ)/(#B:ℝ)) -
    aw.Zp f (aO.a4 b4)| ≤
   ((Fintype.card (ZMod (aD N)):ℝ)/(#B:ℝ))/8
 gg :
  aw.cO (aO.a4 B') p f ≤
   (((Fintype.card (ZMod (aD N)):ℝ)/(#B:ℝ))/8)^p
 rn :
  Real.exp (-K*(d:ℝ)^12) *
    (Fintype.card (ZMod (aD N)):ℝ)^2 ≤
   alpha^3*(#B:ℝ)*(#B':ℝ)/2
structure dr
  {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  {original:Finset G} (t:ah.aA original)
  (K:ℝ) (d:ℕ) where
 lg:aO.eh original
 tE:(3/4:ℝ)*t.Zd≤lg.alpha
 A0:Real.exp (-(K*((d+1:ℕ):ℝ)^11)) *
   (t.card:ℝ)≤(#lg.B:ℝ)
 y5:Real.exp (-(K*((d+1:ℕ):ℝ)^11)) *
   (t.card:ℝ)≤(#lg.B':ℝ)
namespace dr
noncomputable def KS
    {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {original:Finset G} (t:ah.aA original)
    {K:ℝ} {d aq p:ℕ}
    (P:ah.kL t (1/8:ℝ)
      (K*((d+1:ℕ):ℝ)^11) aq)
    (aQ:ah.bV t P.ak P.aB (1/8:ℝ))
    (hp:0<p) (f:G→ℝ)
    (jy:(2/3:ℝ)^p ≤
      aO.a5 t (1/8:ℝ))
    (ew :
      |(aO.bb
            (aO.kO P aQ)
            (aO.g2 P aQ) -
          (Fintype.card G:ℝ)/(#P.ak.Zc:ℝ)) -
          aw.Zp f
            (aO.a4
              (aO.g2 P aQ))| ≤
        ((Fintype.card G:ℝ)/(#P.ak.Zc:ℝ))/8)
    (ee :
      an.aM
          (af
            (aO.a4 P.aB.Zc)) f p ≤
        ((Fintype.card G:ℝ)/(#P.ak.Zc:ℝ))/8) :
    dr t K d:=by
  let c:=aO.iG t P aQ
    (by norm_num) (by norm_num) hp f jy ew ee
  refine
    { lg:=c
      tE:= ?_
      A0:= ?_
      y5:= ?_ }
  · change(3/4:ℝ)*t.Zd ≤
      aO.a5 t (1/8:ℝ)
    simp only[aO.a5]
    nlinarith[t.dI.le]
  · change Real.exp (-(K*((d+1:ℕ):ℝ)^11)) *
        (t.card:ℝ)≤(#P.ak.Zc:ℝ)
    exact P.mz
  · change Real.exp (-(K*((d+1:ℕ):ℝ)^11)) *
        (t.card:ℝ)≤(#P.aB.Zc:ℝ)
    exact P.mA
end dr
namespace dm
private lemma vA:Real.exp (-1)≤(1/2:ℝ):=by
 have he:(2:ℝ)≤Real.exp 1:=Real.exp_one_gt_two.le
 have hm:=Qi he (Q1 (-1)).le
 have tb:Real.exp 1*Real.exp (-1)=1:=by
  rw[←R7]
  norm_num
 rw[tb] at hm
 exact(Qs (by norm_num:(0:ℝ)<2)).2
  (by simpa[Qx] using hm)
lemma p5
  {d:ℕ} (hd:1≤d) {alpha:ℝ}
  (b8:(3/4:ℝ)*(1/(2:ℝ)^d)≤alpha) :
  Real.exp (-(8:ℝ)*(d:ℝ)^12)≤alpha^3/2:=by
 let m:ℕ:=8*d^12
 have l5:Real.exp (-(8:ℝ)*(d:ℝ)^12) =
   Real.exp (-1)^m:=by
  rw[show-(8:ℝ)*(d:ℝ)^12=(m:ℝ)*(-1) by
   simp[m],Real.exp_nat_mul]
 have iB:Real.exp (-1)^m≤(1/2:ℝ)^m :=
  Qp (Q1 _).le vA m
 have PC:d≤d^12:=Nat.le_pow (by norm_num)
 have hm:3*d+3≤ m:=by
  dsimp[m]
  omega
 have vG:(1/2:ℝ)^m≤(1/2:ℝ)^(3*d+3) :=
  SJ (by norm_num) (by norm_num) hm
 have qI:(1/2:ℝ)^(3*d+3) ≤
   ((3/4:ℝ)*(1/(2:ℝ)^d))^3/2:=by
  rw[RL,QU]
  ring_nf
  rw[show(1/8:ℝ)=(1/2:ℝ)^3 by norm_num, ←QU]
  gcongr
  all_goals norm_num[R8]
 calc
  Real.exp (-(8:ℝ)*(d:ℝ)^12)=Real.exp (-1)^m:=l5
  _≤(1/2:ℝ)^m:=iB
  _≤(1/2:ℝ)^(3*d+3):=vG
  _≤((3/4:ℝ)*(1/(2:ℝ)^d))^3/2:=qI
  _≤alpha^3/2:=by gcongr
def sH {N:ℕ}
  {A:Finset (ZMod (aD N))} {K:ℝ} {d:ℕ}
  (c:aO.eh A)
  (Dv:Real.exp (-K*(d:ℝ)^12) *
    (Fintype.card (ZMod (aD N)):ℝ)^2 ≤
   c.alpha^3*(#c.B:ℝ)*(#c.B':ℝ)/2) :
  dm N A K d where
 A':=c.A'
 b4:=c.b4
 B:=c.B
 B':=c.B'
 translate:=c.translate
 alpha:=c.alpha
 p:=c.p
 f:=c.f
 jP:=c.jP
 iZ:=c.iZ
 kM:=c.kM
 h6:=c.h6
 fL:=c.fL
 fl:=c.fl
 i0:=c.i0
 kN:=c.kN
 jQ:=c.jQ
 p_pos:=c.p_pos
 gf:=c.gf
 e6:=c.e6
 gg:=c.gg
 rn:=Dv
lemma nr
  {G:Type*} [Fintype G] {y6 y7:ℝ} {d:ℕ} {B B':Finset G}
  (hB:Real.exp (-y6*(d:ℝ)^12)*(Fintype.card G:ℝ) ≤
   (#B:ℝ))
  (Kb:Real.exp (-y7*(d:ℝ)^12)*(Fintype.card G:ℝ) ≤
   (#B':ℝ)) :
  Real.exp (-(y6+y7)*(d:ℝ)^12) *
    (Fintype.card G:ℝ)^2≤(#B:ℝ)*(#B':ℝ):=by
 calc
  Real.exp (-(y6+y7)*(d:ℝ)^12) *
     (Fintype.card G:ℝ)^2 =
    (Real.exp (-y6*(d:ℝ)^12)*(Fintype.card G:ℝ)) *
     (Real.exp (-y7*(d:ℝ)^12)*(Fintype.card G:ℝ)):=by
   rw[show-(y6+y7)*(d:ℝ)^12 =
     -y6*(d:ℝ)^12+ -y7*(d:ℝ)^12 by ring,
    R7]
   ring
  _≤(#B:ℝ)*(#B':ℝ):=by
   exact QW hB Kb (by positivity) (by positivity)
lemma lU
  {G:Type*} [Fintype G] {alpha nV wM:ℝ} {d:ℕ}
  {B B':Finset G}
  (c8:Real.exp (-nV*(d:ℝ)^12)≤alpha^3/2)
  (Dw:Real.exp (-wM*(d:ℝ)^12) *
    (Fintype.card G:ℝ)^2≤(#B:ℝ)*(#B':ℝ)) :
  Real.exp (-(nV+wM)*(d:ℝ)^12) *
    (Fintype.card G:ℝ)^2 ≤
   alpha^3*(#B:ℝ)*(#B':ℝ)/2:=by
 have Gj:0≤(#B:ℝ)*(#B':ℝ):=by positivity
 calc
  Real.exp (-(nV+wM)*(d:ℝ)^12) *
     (Fintype.card G:ℝ)^2 =
    Real.exp (-nV*(d:ℝ)^12) *
     (Real.exp (-wM*(d:ℝ)^12) *
      (Fintype.card G:ℝ)^2):=by
   rw[show-(nV+wM)*(d:ℝ)^12 =
     -nV*(d:ℝ)^12+ -wM*(d:ℝ)^12 by ring,
    R7]
   ring
  _≤Real.exp (-nV*(d:ℝ)^12) *
     ((#B:ℝ)*(#B':ℝ)) :=
   iO Dw (Q1 _).le
  _≤(alpha^3/2)*((#B:ℝ)*(#B':ℝ)) :=
   Qi c8 Gj
  _=alpha^3*(#B:ℝ)*(#B':ℝ)/2:=by ring
lemma BS {N:ℕ} {A:Finset (ZMod (aD N))}
  {K:ℝ} {d:ℕ} (c:dm N A K d) :
  Real.exp (-K*(d:ℝ)^12) *
    ((aD N:ℕ):ℝ)^2≤(dL A:ℝ):=by
 let:NeZero (aD N):=⟨by simp[aD]⟩
 have A1:Odd (aD N):=by
  exact ⟨N,by simp[aD,R5]⟩
 simpa using aO.ko A1
  c.jP c.iZ c.kM c.h6 c.translate
  c.fL c.fl c.i0 c.kN
  c.jQ c.p_pos c.f c.gf c.e6
  c.gg c.rn
end dm
def eT (K:ℝ):Prop :=
 0<K ∧
  ∀ (N:ℕ),1≤N →
   ∀ (A:Finset (ZMod (aD N))),A.Nonempty →
    ∀ d:ℕ,1≤d →
     Real.log (((aD N:ℕ):ℝ)/(#A:ℝ)) ≤
       (d:ℝ)*Real.log 2 →
      Nonempty (dm N A K d)
def wN (K:ℝ):Prop :=
 0<K ∧
  ∀ (N:ℕ),1≤N →
   ∀ (A:Finset (ZMod (aD N))),A.Nonempty →
    ∀ d:ℕ,1≤d →
     Real.log (((aD N:ℕ):ℝ)/(#A:ℝ)) ≤
       (d:ℝ)*Real.log 2 →
      ∃ aq:ℕ,
       ∀ t:ah.aA A,
        (1/(2:ℝ)^d)≤t.Zd →
        t.rank≤1024*(d+1)*aq →
        (¬ ∃ u:ah.aA A,
         br.dk (1025/1024:ℝ) aq
          (K*((d+1:ℕ):ℝ)^11)
          t.restriction u.restriction) →
        Nonempty (dr t K d)
lemma nt
  {K:ℝ} (h:eT K) :
  f1 K:=by
 refine ⟨h.1, ?_⟩
 intro N hN A hA d hd eu
 exact(Classical.choice (h.2 N hN A hA d hd eu)).BS
private lemma um {d:ℕ} (hd:1≤d) :
  ((d+1:ℕ):ℝ)^12≤(2:ℝ)^12*(d:ℝ)^12:=by
 have O4:(1:ℝ)≤d:=by exact_mod_cast hd
 have dc:((d+1:ℕ):ℝ)≤2*(d:ℝ):=by
  push_cast
  linarith
 calc
  ((d+1:ℕ):ℝ)^12≤(2*(d:ℝ))^12 :=
   Qp (by positivity) dc 12
  _=(2:ℝ)^12*(d:ℝ)^12:=by rw[QL]
namespace dm
lemma iH
  {G:Type*} [Fintype G] {K:ℝ} (hK:0≤K)
  {d n ma:ℕ} (hd:1≤d) (hn:n≤1024*(d+1))
  {B:Finset G}
  (ua:Real.exp (-(n:ℝ) *
     (K*((d+1:ℕ):ℝ)^11))*(Fintype.card G:ℝ) ≤
    (ma:ℝ))
  (A2:Real.exp (-(K*((d+1:ℕ):ℝ)^11)) *
    (ma:ℝ)≤(#B:ℝ)) :
  Real.exp (-(1025*(2:ℝ)^12*K)*(d:ℝ)^12) *
    (Fintype.card G:ℝ)≤(#B:ℝ):=by
 let step:ℝ:=K*((d+1:ℕ):ℝ)^11
 have Kc:n+1≤1025*(d+1):=by omega
 have Kd:(n:ℝ)+1≤1025*((d+1:ℕ):ℝ):=by
  exact_mod_cast Kc
 have yl:0≤ step:=by
  dsimp[step]
  positivity
 have Gk:((n:ℝ)+1)*step ≤
   1025*K*((d+1:ℕ):ℝ)^12:=by
  calc
   ((n:ℝ)+1)*step ≤
     (1025*((d+1:ℕ):ℝ))*step :=
    Qi Kd yl
   _=1025*K*((d+1:ℕ):ℝ)^12:=by
    simp only[step]
    ring
 have hpow:=um hd
 have ym:((n:ℝ)+1)*step ≤
   (1025*(2:ℝ)^12*K)*(d:ℝ)^12:=by
  calc
   ((n:ℝ)+1)*step ≤
     1025*K*((d+1:ℕ):ℝ)^12:=Gk
   _≤1025*K*((2:ℝ)^12*(d:ℝ)^12) :=
    iO hpow (Qn (by norm_num) hK)
   _=(1025*(2:ℝ)^12*K)*(d:ℝ)^12:=by ring
 have E3:Real.exp (-((n:ℝ)+1)*step) *
   (Fintype.card G:ℝ)≤(#B:ℝ):=by
  calc
   Real.exp (-((n:ℝ)+1)*step)*(Fintype.card G:ℝ) =
     Real.exp (-step) *
      (Real.exp (-(n:ℝ)*step)*(Fintype.card G:ℝ)):=by
    rw[show-((n:ℝ)+1)*step =
      -step+(-(n:ℝ)*step) by ring,R7]
    ring
   _≤Real.exp (-step)*(ma:ℝ) :=
    iO (by simpa[step] using ua)
     (Q1 _).le
   _≤(#B:ℝ):=by simpa[step] using A2
 have l5:Real.exp (-(1025*(2:ℝ)^12*K)*(d:ℝ)^12) ≤
   Real.exp (-((n:ℝ)+1)*step):=by
  apply Real.exp_le_exp.mpr
  nlinarith
 exact(Qi l5 (by positivity)).trans E3
noncomputable def tF
  {N d n:ℕ} (hd:1≤d)
  {A:Finset (ZMod (aD N))} (hA:A.Nonempty)
  {K:ℝ} (hK:0≤K)
  {t:ah.aA A}
  (hn:n≤1024*(d+1))
  (uo:br.nF d
   (bQ N A hA).Zd)
  (c8:(1025/1024:ℝ)^n *
    (bQ N A hA).Zd≤t.Zd)
  (ch:Real.exp (-(n:ℝ) *
     (K*((d+1:ℕ):ℝ)^11)) *
    ((bQ N A hA).card:ℝ)≤(t.card:ℝ))
  (terminal:dr t K d) :
  dm N A
   (8+2050*(2:ℝ)^12*K) d:=by
 letI:NeZero (aD N):=⟨by simp[aD]⟩
 let c:=terminal.lg
 have BT:0≤(bQ N A hA).Zd :=
  (bQ N A hA).dI.le
 have uP:(1:ℝ)≤(1025/1024:ℝ)^n :=
  RH (by norm_num)
 have Gl:(bQ N A hA).Zd≤t.Zd:=by
  calc
   (bQ N A hA).Zd =
     1*(bQ N A hA).Zd:=by ring
   _≤(1025/1024:ℝ)^n*(bQ N A hA).Zd :=
    Qi uP BT
   _≤t.Zd:=c8
 have c3:(1/(2:ℝ)^d) ≤
   (bQ N A hA).Zd:=uo
 have b8:(3/4:ℝ)*(1/(2:ℝ)^d)≤c.alpha:=by
  calc
   (3/4:ℝ)*(1/(2:ℝ)^d) ≤
     (3/4:ℝ)*(bQ N A hA).Zd :=
    iO c3 (by norm_num)
   _≤(3/4:ℝ)*t.Zd :=
    iO Gl (by norm_num)
   _≤c.alpha:=terminal.tE
 have A3:Real.exp (-(8:ℝ)*(d:ℝ)^12) ≤
   c.alpha^3/2:=p5 hd b8
 have yo:Real.exp (-(n:ℝ) *
    (K*((d+1:ℕ):ℝ)^11)) *
   (Fintype.card (ZMod (aD N)):ℝ)≤(t.card:ℝ):=by
  simpa only[rM,ZMod.card] using ch
 have hB:Real.exp (-(1025*(2:ℝ)^12*K)*(d:ℝ)^12) *
   (Fintype.card (ZMod (aD N)):ℝ)≤(#c.B:ℝ):=by
  exact iH
   (G:=ZMod (aD N)) (K:=K) hK
   (d:=d) (n:=n) (ma:=t.card) hd hn yo terminal.A0
 have Kb:Real.exp (-(1025*(2:ℝ)^12*K)*(d:ℝ)^12) *
   (Fintype.card (ZMod (aD N)):ℝ)≤(#c.B':ℝ):=by
  exact iH
   (G:=ZMod (aD N)) (K:=K) hK
   (d:=d) (n:=n) (ma:=t.card) hd hn yo terminal.y5
 have Dw:=nr hB Kb
 have Dv:=lU A3 Dw
 exact sH c (by
  convert Dv using 1; ring_nf)
end dm
private lemma nW {N:ℕ} (hN:1≤N) :
  (((aD N:ℕ):ℝ))≤4*(N:ℝ):=by
 push_cast
 have P4:(1:ℝ)≤N:=by exact_mod_cast hN
 linarith
private lemma oh
  {N d:ℕ} {A:Finset ℕ} (hN:1≤N) (hA:A.Nonempty)
  (eu:Real.log ((N:ℝ)/(#A:ℝ))≤(d:ℝ)*Real.log 2) :
  Real.log (((aD N:ℕ):ℝ)/(#A:ℝ)) ≤
   ((d+2:ℕ):ℝ)*Real.log 2:=by
 have Ke:(0:ℝ)<N:=by exact_mod_cast hN
 have E4:(0:ℝ)< #A:=by exact_mod_cast hA.card_pos
 have Ie:(0:ℝ)<(N:ℝ)/(#A:ℝ):=Rn Ke E4
 have wc :
   (((aD N:ℕ):ℝ)/(#A:ℝ)) ≤
    4*((N:ℝ)/(#A:ℝ)):=by
  calc
   (((aD N:ℕ):ℝ)/(#A:ℝ)) ≤
     (4*(N:ℝ))/(#A:ℝ) :=
    Qz (nW hN) E4.le
   _=4*((N:ℝ)/(#A:ℝ)):=by ring
 calc
  Real.log (((aD N:ℕ):ℝ)/(#A:ℝ)) ≤
    Real.log (4*((N:ℝ)/(#A:ℝ))) :=
   QG (by positivity) wc
  _=2*Real.log 2+Real.log ((N:ℝ)/(#A:ℝ)):=by
   rw[Ql (by norm_num:(4:ℝ)≠0) Ie.ne',
    show(4:ℝ)=2*2 by norm_num,
    Ql (by norm_num:(2:ℝ)≠0) (by norm_num:(2:ℝ)≠0)]
   ring
  _≤2*Real.log 2+(d:ℝ)*Real.log 2:=by linarith
  _=((d+2:ℕ):ℝ)*Real.log 2:=by
   push_cast
   ring
private lemma uq {d:ℕ} (hd:1≤d) :
  ((d+2:ℕ):ℝ)^12≤(3:ℝ)^12*(d:ℝ)^12:=by
 have O4:(1:ℝ)≤d:=by exact_mod_cast hd
 have dc:((d+2:ℕ):ℝ)≤3*(d:ℝ):=by
  push_cast
  linarith
 calc
  ((d+2:ℕ):ℝ)^12≤(3*(d:ℝ))^12 :=
   Qp (by positivity) dc 12
  _=(3:ℝ)^12*(d:ℝ)^12:=by rw[QL]
lemma tG
  {K:ℝ} (y8:f1 K) :
  dX ((3:ℝ)^12*K) 1:=by
 refine ⟨QM (RF (by norm_num) _) y8.1, ?_⟩
 intro N hN A zZ hA d hd eu
 have Kf: ∀ a∈A,a≤N:=by
  intro a ha
  exact(Finset.mem_Icc.mp (zZ ha)).2
 have y9:(cY N A).Nonempty:=by
  obtain ⟨a,ha⟩:=hA
  exact ⟨cn N a,fh.mpr ⟨a,ha,rfl⟩⟩
 have Dx: #(cY N A)= #A:=vF Kf
 have E5 :
   Real.log (((aD N:ℕ):ℝ) /
     (#(cY N A):ℝ)) ≤
    ((d+2:ℕ):ℝ)*Real.log 2:=by
  rw[Dx]
  exact oh hN hA eu
 have Kg:=y8.2 N hN (cY N A) y9
  (d+2) (by omega) E5
 have hpow:=uq hd
 have l5 :
   Real.exp (-((3:ℝ)^12*K)*(d:ℝ)^12) ≤
    Real.exp (-K*((d+2:ℕ):ℝ)^12):=by
  apply Real.exp_le_exp.mpr
  have hK:=y8.1.le
  nlinarith[iO hpow hK]
 have Kh:(N:ℝ)^2≤(((aD N:ℕ):ℝ))^2:=by
  apply Qp (by positivity) _ 2
  push_cast
  have MI:(0:ℝ)≤N:=by positivity
  linarith
 calc
  Real.exp (-((3:ℝ)^12*K)*(d:ℝ)^12)*(N:ℝ)^2 ≤
    Real.exp (-K*((d+2:ℕ):ℝ)^12) *
     (((aD N:ℕ):ℝ))^2 :=
   QW l5 Kh (sq_nonneg _) (Q1 _).le
  _≤(dL (cY N A):ℝ):=Kg
  _=(dL A:ℝ):=by rw[qR Kf]
lemma mb
  (h: ∃ K:ℝ,f1 K) :
  ∃ K:ℝ, ∃ nJ:ℕ,dX K nJ:=by
 obtain ⟨K,hK⟩:=h
 exact ⟨(3:ℝ)^12*K,1,tG hK⟩
lemma i2
  (h: ∃ K:ℝ,eT K) :
  ∃ K:ℝ, ∃ nJ:ℕ,dX K nJ:=by
 obtain ⟨K,hK⟩:=h
 exact mb
  ⟨K,nt hK⟩
end ay
end
section
noncomputable section
open AddChar Finset Fintype Function RCLike
open scoped BigOperators ComplexConjugate
namespace ay.jz
open dT
variable {G:Type*} [AddCommGroup G] [Fintype G]
def MJ (f:G→ℂ) (p:ℕ):ℝ :=
 𝔼 x:G, ‖f x‖ ^p
def aK (nu:G→ℝ) (f:G→ℂ) (p:ℕ):ℝ :=
 𝔼 x:G,nu x* ‖f x‖ ^p
def ds (nu:G→ℝ) (fJ:AddChar G ℂ):ℂ :=
 𝔼 x:G,(nu x:ℂ)*fJ x
def fQ (nu:G→ℝ):Prop :=
 ∀ fJ:AddChar G ℂ,
  0≤(ds nu fJ).re∧(ds nu fJ).im=0
lemma k4 (a b:G→ℝ) (x:G) :
  (ay.ao a b x:ℂ) =
   (Fintype.card G:ℂ) *
    dT.convolution ((↑) ∘ a) ((↑) ∘ b) x:=by
 unfold ay.ao dT.convolution
 rw[Rj]
 push_cast
 field_simp
 simp[Rh]
lemma gh (a:G→ℝ) (x:G) :
  (ay.aZ a a x:ℂ) =
   (Fintype.card G:ℂ) *
    a2 ((↑) ∘ a) ((↑) ∘ a) x:=by
 unfold ay.aZ dT.a2
 rw[Rj]
 push_cast
 field_simp
 refine Qk (Equiv.subRight x) _ _ fun y↦ ?_
 simp
lemma k5 {nu:G→ℝ}
  (rm:fQ nu) (fJ:AddChar G ℂ) :
  ds nu fJ=((ds nu fJ).re:ℂ):=by
 apply Complex.ext
 ·simp
 ·simpa using(rm fJ).2
lemma q6 (nu:G→ℝ) (fJ:AddChar G ℂ) (t:G) :
  (𝔼 x:G,(nu (x-t):ℂ)*fJ x)=fJ t*ds nu fJ:=by
 unfold ds
 rw[mul_expect]
 refine RW (M:=ℂ) (Equiv.subRight t:G ≃ G) _ _ fun y↦ ?_
 simp only[Ut,Qy]
 have hc:fJ y=fJ t*fJ (y+ -t):=by
  rw[←map_add_eq_mul]
  congr 1
  abel
 rw[hc]
 ring
lemma oi {nu:G→ℝ}
  (rm:fQ nu) (fJ:AddChar G ℂ) (t:G) :
  ‖𝔼 x:G,(nu (x-t):ℂ)*fJ x‖ =(ds nu fJ).re:=by
 rw[q6,QO,Q0,
  QT,k5 rm]
 simp[QC (rm fJ).1]
lemma gx
  (a b:G→ℝ) :
  fQ
   (ay.ao
    (ay.aZ a a)
    (ay.aZ b b)):=by
 let ac:G→ℂ:=(↑) ∘ a
 let bc:G→ℂ:=(↑) ∘ b
 let da:G→ℂ:=a2 ac ac
 let db:G→ℂ:=a2 bc bc
 let h:G→ℂ:=dT.convolution da db
 have uh (x:G) :
   (ay.ao
     (ay.aZ a a)
     (ay.aZ b b) x:ℂ) =
    (Fintype.card G:ℂ)^3*h x:=by
  rw[k4]
  have O5:((↑) ∘ ay.aZ a a) =
    fun y↦(Fintype.card G:ℂ)*da y:=by
   funext y
   exact gh a y
  have O6:((↑) ∘ ay.aZ b b) =
    fun y↦(Fintype.card G:ℂ)*db y:=by
   funext y
   exact gh b y
  rw[O5,O6]
  simp only[h,da,db,dT.convolution,
   Rj]
  have ch:(Fintype.card G:ℂ)≠0:=by
   exact_mod_cast SN
  field_simp
  rw[Qj]
  apply Io rfl
  intro x hx
  ring
 intro fJ
 have AA :
   ds
     (ay.ao
      (ay.aZ a a)
      (ay.aZ b b)) fJ =
    (Fintype.card G:ℂ)^3*coeff h (-fJ):=by
  unfold ds
  simp_rw[uh]
  calc
   (𝔼 x:G,(Fintype.card G:ℂ)^3*h x*fJ x) =
     (Fintype.card G:ℂ)^3*(𝔼 x:G,h x*fJ x):=by
    calc
     _=𝔼 x:G,(Fintype.card G:ℂ)^3*(h x*fJ x):=by
      congr 1 with x
      ring
     _=_:=by rw[←mul_expect]
   _=_:=by
    congr 1
    simp[coeff,wInner_cWeight_eq_expect,inner_apply,map_neg_eq_conj]
 have uO :
   ds
     (ay.ao
      (ay.aZ a a)
      (ay.aZ b b)) fJ =
    (((Fintype.card G:ℝ)^3*Complex.normSq (coeff ac (-fJ)) *
     Complex.normSq (coeff bc (-fJ)):ℝ):ℂ):=by
  rw[AA]
  simp only[h,mU,da,db,t6]
  push_cast
  ring
 rw[uO]
 constructor
 ·simpa only[Complex.ofReal_re] using
   (Qn
   (Qn (by positivity) (Uk _))
   (Uk _))
 ·exact Complex.ofReal_im _
omit [AddCommGroup G] in
lemma iI {I:Type*} {k:ℕ} (_hk:k≠0)
  (nu:G→ℝ) (s:Finset I) (u:I→G→ℂ) :
  (aK nu (∑ i∈s,u i) (2*k):ℂ) =
   ∑ x∈(Fintype.piFinset fun _:Fin k↦s), ∑ y∈(Fintype.piFinset fun _:Fin k↦s),
    𝔼 a:G,(nu a:ℂ) *
     ((∏ i,conj (u (x i) a))* ∏ i,u (y i) a):=by
 rw[aK]
 push_cast
 simp_rw[Si]
 calc
  (𝔼 a:G,(nu a:ℂ)*(‖∑ i∈s,u i a‖ :ℂ)^(2*k)) =
    𝔼 a:G,(nu a:ℂ) *
     ((∑ i∈s,conj (u i a))^k*(∑ j∈s,u j a)^k):=by
   congr 1 with a
   simp_rw[QU, ←UX,QL,RK]
  _=_:=by
   simp_rw[sum_pow',Finset.sum_mul_sum,mul_sum,expect_sum_comm]
omit [AddCommGroup G] in
lemma dx {nu:G→ℝ} (rm: ∀ x,0≤nu x)
  (f:G→ℂ) (p:ℕ):0≤aK nu f p:=by
 exact expect_nonneg fun x _↦Qn (rm x) (QH (Re _) _)
lemma gy
  {p:ℕ} (hp:p≠0) (mq:Even p)
  (nu:G→ℝ) (rm: ∀ x,0≤nu x)
  (z5:fQ nu) (t:G) (f:G→ℂ) :
  aK (fun x↦nu (x-t)) (convolution f f) p ≤
   aK nu (a2 f f) p:=by
 obtain ⟨k,rfl⟩:=mq.two_dvd
 simp only[ne_eq,mul_eq_zero,OfNat.ofNat_ne_zero,false_or] at hp
 let term:(Fin k→ AddChar G ℂ) × (Fin k→ AddChar G ℂ)→ℂ :=
  fun psi ↦
   conj (∏ i,coeff f (psi.1 i)^2) *
    (∏ i,coeff f (psi.2 i)^2) *
     (𝔼 x:G,(nu (x-t):ℂ) *
      ((∑ i,psi.2 i- ∑ i,psi.1 i) x))
 refine Complex.le_of_eq_sum_of_eq_sum_norm term univ
  (dx (fun x↦rm (x-t)) _ _) ?_ ?_
 ·have hinv:convolution f f =
    ∑ fJ:AddChar G ℂ,fun x↦coeff (convolution f f) fJ*fJ x:=by
   funext x
   simpa only[Si] using(Zi (convolution f f) x).symm
  rw[hinv]
  have hm:=iI (G:=G) hp
   (fun x↦nu (x-t)) (univ:Finset (AddChar G ℂ))
   (fun fJ x↦coeff (convolution f f) fJ*fJ x)
  rw[hm]
  simp only[term]
  simp_rw[mU, ←sq,Ul,mul_expect,
   RO]
  simp[Q7,Qx,map_neg_eq_conj,prod_mul_distrib]
  ring_nf
 ·have hinv:a2 f f =
    ∑ fJ:AddChar G ℂ,
     fun x↦coeff (a2 f f) fJ*fJ x:=by
   funext x
   simpa only[Si] using
    (Zi (a2 f f) x).symm
  rw[hinv]
  have hm:=iI (G:=G) hp nu
   (univ:Finset (AddChar G ℂ))
   (fun fJ x↦coeff (a2 f f) fJ*fJ x)
  rw[hm]
  simp only[term]
  simp_rw[kr,Complex.mul_conj',
   Ul,mul_expect]
  congr 1 with psi
  congr 1 with phi
  simp only[RU,map_pow,prod_mul_distrib,Q7,
   map_prod,RO,AddChar.coe_sum,
   Finset.prod_apply,
   Complex.conj_ofReal]
  have Ki :
    (𝔼 x:G,(nu x:ℂ) *
      ((∏ i,conj (psi i x))* ∏ i,phi i x)) =
     ds nu (∑ i,phi i- ∑ i,psi i):=by
   simp[ds,map_neg_eq_conj,Qx,
    RO]
  let a:ℂ :=
   (∏ i,(‖coeff f (psi i)‖ ^2:ℂ)) *
    ∏ i,(‖coeff f (phi i)‖ ^2:ℂ)
  let c:ℂ :=
   conj (∏ i,coeff f (psi i)^2)* ∏ i,coeff f (phi i)^2
  let eta:AddChar G ℂ:= ∑ i,phi i- ∑ i,psi i
  have kz :
    (𝔼 x:G,(nu x:ℂ) *
      (a*((∏ i,conj (psi i x))* ∏ i,phi i x))) =
     a*ds nu eta:=by
   calc
    _=𝔼 x:G,a*((nu x:ℂ) *
       ((∏ i,conj (psi i x))* ∏ i,phi i x)):=by
      congr 1 with x
      ring
    _=a*(𝔼 x:G,(nu x:ℂ) *
       ((∏ i,conj (psi i x))* ∏ i,phi i x)):=by
      rw[←mul_expect]
    _=_:=by simpa only[eta] using QA (a*·) Ki
  have za :
    (𝔼 x:G,c*(nu (x-t):ℂ) *
      ((∏ i,phi i x)* ∏ i,psi i (-x))) =
     c*(𝔼 x:G,(nu (x-t):ℂ)*eta x):=by
   calc
    _=𝔼 x:G,c*((nu (x-t):ℂ)*eta x):=by
     congr 1 with x
     dsimp only[eta]
     simp[map_neg_eq_conj,RO,Qx,Q6]
     ring
    _=_:=by rw[←mul_expect]
  have LW :
    (𝔼 x:G,(nu x:ℂ) *
      (a*((∏ i,conj (psi i x))* ∏ i,phi i x))) =
     (‖𝔼 x:G,c*(nu (x-t):ℂ) *
      ((∏ i,phi i x)* ∏ i,psi i (-x))‖ :ℂ):=by
   rw[kz,za,QO,
    oi z5 eta t]
   rw[k5 z5]
   dsimp only[a,c]
   push_cast
   simp[norm_prod]
  simpa[a,c,TI,prod_mul_distrib,Qo,Qx,Q6] using LW
lemma jR
  {p:ℕ} (hp:p≠0) (mq:Even p)
  (nu:G→ℝ) (rm: ∀ x,0≤nu x)
  (z5:fQ nu) (t:G) (f:G→ℂ) :
  ∑ x:G,nu (x-t)* ‖convolution f f x‖ ^p ≤
   ∑ x:G,nu x* ‖a2 f f x‖ ^p:=by
 have h:=gy
  hp mq nu rm z5 t f
 simp only[aK,Rj] at h
 exact(R9
  (by positivity:(0:ℝ)<Fintype.card G)).mp h
end ay.jz
end
end
section
open Finset Fintype Function
open scoped BigOperators NNReal
namespace ay
namespace hV
noncomputable section
open dT
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def c4 (C D:Finset G):G→ℝ :=
 ao
  (aZ (af C) (af C))
  (aZ (af D) (af D))
lemma mQ (C D:Finset G) (x:G) :
  0≤c4 C D x:=by
 apply e9
 ·exact gB
   (bO C) (bO C)
 ·exact gB
   (bO D) (bO D)
lemma u5 {C D:Finset G}
  (hC:C.Nonempty) (hD:D.Nonempty) :
  ∑ x:G,c4 C D x=1:=by
 rw[c4,iz,
  hH,hH,
  cf hC,cf hD]
 norm_num
lemma hY
  {B:aj G} {eta:ℝ≥0} {C:Finset G}
  (hC:C.Nonempty) (fN:C⊆(B.ai eta).Zc)
  {x:G}
  (hx:aZ
   (af C) (af C) x≠0) :
  x∈(B.ai (2*eta)).Zc:=by
 by_contra Dy
 apply hx
 rw[aZ]
 apply UN
 intro y _
 by_cases hy:af C y=0
 ·simp[hy]
 have O7:y∈C:=(d6 hC y).mp hy
 by_cases EM:af C (y-x)=0
 ·simp[EM]
 have No:y-x∈C :=
  (d6 hC (y-x)).mp EM
 have A4:=aj.j0 (fN O7) (fN No)
 have heq:y-(y-x)=x:=by abel
 rw[heq] at A4
 exact(Dy (by simpa[R5] using A4)).elim
lemma nv
  {B:aj G} {eta:ℝ≥0} {C D:Finset G}
  (hC:C.Nonempty) (hD:D.Nonempty)
  (fN:C⊆(B.ai eta).Zc)
  (gp:D⊆(B.ai eta).Zc)
  {x:G} (hx:c4 C D x≠0) :
  x∈(B.ai (4*eta)).Zc:=by
 by_contra Dy
 apply hx
 rw[c4,ao]
 apply UN
 intro y _
 let Hg:=aZ
  (af C) (af C)
 let Hh:=aZ
  (af D) (af D)
 by_cases hy:Hg y=0
 ·exact mul_eq_zero.mpr (Or.inl (by simpa[Hg] using hy))
 by_cases nd:Hh (x-y)=0
 ·exact mul_eq_zero.mpr (Or.inr (by simpa[Hh] using nd))
 have Jp:y∈(B.ai (2*eta)).Zc :=
  hY hC fN hy
 have F2:x-y∈(B.ai (2*eta)).Zc :=
  hY hD gp nd
 have A4:=aj.e7 Jp F2
 have heq:y+(x-y)=x:=by abel
 rw[heq] at A4
 exact(Dy (by
  simpa[show(2:ℝ≥0)*eta+2*eta=4*eta by ring] using A4)).elim
omit [DecidableEq G] in
lemma lV
  (mu outer nu h:G→ℝ) (R:ℝ)
  (zR: ∀ x,0≤outer x)
  (BU: ∑ x:G,outer x=1)
  (hh: ∀ x,0≤h x)
  (Kj: ∀ x,mu x≤2*ao outer nu x)
  (kC: ∀ t:G, ∑ x:G,nu (x-t)*h x≤R) :
  ∑ x:G,mu x*h x≤2*R:=by
 calc
  ∑ x:G,mu x*h x ≤
    ∑ x:G,(2*ao outer nu x)*h x:=by
   apply QI
   intro x _
   exact Qi (Kj x) (hh x)
  _=2* ∑ x:G,ao outer nu x*h x:=by
   rw[Qj]
   apply Io rfl
   intro x _
   ring
  _=2* ∑ t:G,outer t* ∑ x:G,nu (x-t)*h x:=by
   apply QA (fun z:ℝ↦2*z)
   simp only[ao]
   calc
    ∑ x:G,(∑ y:G,outer y*nu (x-y))*h x =
      ∑ x:G, ∑ y:G,(outer y*nu (x-y))*h x:=by
     apply Io rfl
     intro x _
     rw[Qt]
    _= ∑ t:G, ∑ x:G,(outer t*nu (x-t))*h x :=
     QD
    _= ∑ t:G,outer t* ∑ x:G,nu (x-t)*h x:=by
     apply Io rfl
     intro t _
     rw[Qj]
     apply Io rfl
     intro x _
     ring
  _≤2* ∑ t:G,outer t*R:=by
   apply iO
   ·apply QI
    intro t _
    exact iO (kC t) (zR t)
   ·norm_num
  _=2*R:=by rw[←Qt,BU,QT]
lemma gP
  {B:aj G} {eta:ℝ≥0} {C D:Finset G}
  (dF:B.a1) (fC:0<eta)
  (mC:4*eta ≤
   1/(400*(max B.rank 1:ℕ):ℝ≥0))
  (hC:C.Nonempty) (hD:D.Nonempty)
  (fN:C⊆(B.ai eta).Zc)
  (gp:D⊆(B.ai eta).Zc)
  (p:ℕ) (f:G→ℂ)
  (l4: ∀ t:G,
   ∑ x:G,c4 C D (x-t)* ‖convolution f f x‖ ^p ≤
    ∑ x:G,c4 C D x* ‖a2 f f x‖ ^p) :
  ∑ x:G,af B.Zc x* ‖convolution f f x‖ ^p ≤
   2* ∑ x:G,c4 C D x *
    ‖a2 f f x‖ ^p:=by
 let nu:=c4 C D
 let outer:=af (B.ai (1+4*eta)).Zc
 apply lV
   (af B.Zc) outer nu
   (fun x↦ ‖convolution f f x‖ ^p)
   (∑ x:G,c4 C D x* ‖a2 f f x‖ ^p)
 ·exact bO _
 ·exact cf (B.ai (1+4*eta)).aE
 ·intro x
  positivity
 ·intro x
  exact gC
   dF (by positivity:0<(4:ℝ≥0)*eta) mC nu
   (mQ C D) (u5 hC hD)
   (fun t ht↦nv hC hD fN gp ht) x
 ·exact l4
lemma kP
  {B:aj G} {eta:ℝ≥0} {C D:Finset G}
  (dF:B.a1) (fC:0<eta)
  (mC:4*eta ≤
   1/(400*(max B.rank 1:ℕ):ℝ≥0))
  (hC:C.Nonempty) (hD:D.Nonempty)
  (fN:C⊆(B.ai eta).Zc)
  (gp:D⊆(B.ai eta).Zc)
  {p:ℕ} (hp:p≠0) (mq:Even p) (f:G→ℂ) :
  ∑ x:G,af B.Zc x* ‖convolution f f x‖ ^p ≤
   2* ∑ x:G,c4 C D x *
    ‖a2 f f x‖ ^p:=by
 apply gP
  dF fC mC hC hD fN gp p f
 intro t
 apply jz.jR hp mq
   (c4 C D) (mQ C D)
 ·simpa only[c4] using
   jz.gx
    (af C) (af D)
end
end hV
end ay
end
section
open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal Pointwise
namespace ay.fu
noncomputable section
variable {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
lemma oj (f g:G→ℝ) :
  ao f g=(aC f g):=by
 funext x
 rw[ao,cR]
lemma er (f g:G→ℝ) :
  aZ f g=(al f g):=by
 funext x
 rw[aZ,eL]
 simp
lemma k6 (D E:Finset G) :
  ((↑) ∘ aN.bh D E:G→ℝ) =
   hV.c4 D E:=by
 rw[hV.c4,
  oj,
  er,
  er]
 simp only[aN.bh,
  aN.dU,NNReal.gF,
  NNReal.oA,NNReal.iF,
  aN.eQ]
 exact(kp
  (af D) (af D)
  (af E) (af E)).symm
omit [DecidableEq G] in
private lemma pr
  (a:G→ℝ) (p:ℕ) (x:G) :
  |ao a a x| ^p =
   (Fintype.card G:ℝ)^p *
    ‖dT.convolution ((↑) ∘ a) ((↑) ∘ a) x‖ ^p:=by
 have h:=QA norm
  (jz.k4 a a x)
 simp only[Rf,QO,UA] at h
 have h': |ao a a x| =
   (Fintype.card G:ℝ) *
    ‖dT.convolution ((↑) ∘ a) ((↑) ∘ a) x‖ :=by
  simpa only[QK] using h
 rw[h',QL]
omit [DecidableEq G] in
private lemma k7
  (a:G→ℝ) (p:ℕ) (x:G) :
  |aZ a a x| ^p =
   (Fintype.card G:ℝ)^p *
    ‖dT.a2 ((↑) ∘ a) ((↑) ∘ a) x‖ ^p:=by
 have h:=QA norm
  (jz.gh a x)
 simp only[Rf,QO,UA] at h
 have h': |aZ a a x| =
   (Fintype.card G:ℝ) *
    ‖dT.a2 ((↑) ∘ a) ((↑) ∘ a) x‖ :=by
  simpa only[QK] using h
 rw[h',QL]
omit [DecidableEq G] in
private lemma kb
  (w a:G→ℝ) (p:ℕ) :
  aK w (ao a a) p =
   (Fintype.card G:ℝ)^p *
    ∑ x:G,w x *
     ‖dT.convolution ((↑) ∘ a) ((↑) ∘ a) x‖ ^p:=by
 classical
 unfold aK
 rw[Qj]
 apply Io rfl
 intro x _
 rw[pr]
 ring
omit [DecidableEq G] in
private lemma h7
  (w a:G→ℝ) (p:ℕ) :
  aK w (aZ a a) p =
   (Fintype.card G:ℝ)^p *
    ∑ x:G,w x *
     ‖dT.a2 ((↑) ∘ a) ((↑) ∘ a) x‖ ^p:=by
 classical
 unfold aK
 rw[Qj]
 apply Io rfl
 intro x _
 rw[k7]
 ring
lemma q7
  {B:aj G} {eta:ℝ≥0} {D E:Finset G}
  (dF:B.a1) (fC:0<eta)
  (mC:4*eta ≤
   1/(400*(max B.rank 1:ℕ):ℝ≥0))
  (hD:D.Nonempty) (hE:E.Nonempty)
  (gp:D⊆(B.ai eta).Zc)
  (lh:E⊆(B.ai eta).Zc)
  {p:ℕ} (hp:p≠0) (mq:Even p) (a:G→ℝ) :
  aK (af B.Zc)
    (ao a a) p ≤
   2*aK
    ((↑) ∘ aN.bh D E)
    (aZ a a) p:=by
 have h:=hV.kP
  dF fC mC hD hE gp lh hp mq ((↑) ∘ a)
 rw[←k6 D E] at h
 have c3:0≤(Fintype.card G:ℝ)^p:=by positivity
 have hmul:=iO h c3
 rw[kb,
  h7]
 nlinarith
lemma tH
  {B:aj G} {eta:ℝ≥0} {D E:Finset G}
  (dF:B.a1) (fC:0<eta)
  (mC:4*eta ≤
   1/(400*(max B.rank 1:ℕ):ℝ≥0))
  (hD:D.Nonempty) (hE:E.Nonempty)
  (gp:D⊆(B.ai eta).Zc)
  (lh:E⊆(B.ai eta).Zc)
  {p:ℕ} (hp:0<p) (mq:Even p) (a:G→ℝ) :
  an.aM (af B.Zc)
    (ao a a) p ≤
   2*an.aM
    ((↑) ∘ aN.bh D E)
    (aZ a a) p:=by
 have ju:an.cw
   (af B.Zc) :=
  ⟨bO B.Zc,
   cf B.aE⟩
 have rm:an.cw
   ((↑) ∘ aN.bh D E) :=
  ⟨fun x↦by
   exact_mod_cast(show 0≤aN.bh D E x by
    exact aN.gS D E x),
   by
    simpa using QA (fun z:ℝ≥0↦(z:ℝ))
     (aN.i7 hD hE)⟩
 apply an.lq
  ju rm hp
 exact q7 dF fC mC hD hE gp lh
  hp.ne' mq a
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
lemma nw
  {B:aj G} (dF:B.a1)
  {A:Finset G} (hA:A.Nonempty) (zo:A⊆B.Zc)
  {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty)
  {aF:ℝ≥0}
  (dy:aF≤1/(100*(max B.rank 1:ℕ):ℝ≥0))
  (kF: ∀ t,aN.bh D E t≠0 →
   t∈(B.ai aF).Zc)
  {epsilon:ℝ} (eM:0<epsilon) (oR:epsilon≤1)
  (d5 :
   2*((A.card:ℝ)⁻¹ *
     (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ))) +
    (B.Zc.card:ℝ)⁻¹ *
     (200*((max B.rank 1:ℕ):ℝ)*(aF:ℝ)) ≤
    epsilon/8*(B.Zc.card:ℝ)⁻¹)
  {p:ℕ} (hp:0<p)
  {tI pE:G→ℝ}
  (ju:an.cw tI)
  (ld :
   an.aM tI pE
     (an.bS p) ≤
    2*an.aM
     ((↑) ∘ aN.bh D E)
     ((al (((@mu (ℝ) _ _) A-mu B.Zc)) ((mu A-mu B.Zc))))
     (an.bS p))
  (qs :
   an.aM
     ((↑) ∘ aN.bh D E)
     ((al ((@mu (ℝ) _ _) A) (mu A))) (an.cz epsilon p) <
    (1+epsilon/8)*(B.Zc.card:ℝ)⁻¹) :
  an.aM tI pE p ≤
   epsilon*(B.Zc.card:ℝ)⁻¹ :=by
 let nu:=aN.bh D E
 have ft: ∑ x:G,nu x=1 :=
  aN.i7 hD hE
 have rm:an.cw ((↑) ∘ nu) :=
  ⟨fun x↦by
   exact_mod_cast(show 0≤nu x by
    exact aN.gS D E x),
   by simpa using QA (fun z:ℝ≥0↦(z:ℝ)) ft⟩
 have ch:(0:ℝ)<B.Zc.card:=by
  exact_mod_cast B.aE.card_pos
 have fF:0<(B.Zc.card:ℝ)⁻¹ :=inv_pos.mpr ch
 apply an.nK
   ju rm eM fF hp (by simpa[nu] using ld) _
   (by simpa[nu] using qs)
 intro iV
 obtain ⟨r,hr,_hreven,Ji,Ig⟩ :=
  aN.ug dF hA zo hD hE dy
   kF eM oR d5 hp (by simpa[nu] using iV)
 exact ⟨r,hr,Ji,by simpa[nu] using Ig⟩
end
end ay.fu
end
section
open Finset
open scoped NNReal Pointwise
namespace ay
noncomputable section
namespace aj
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
end aj
lemma lW
  {G:Type*} [AddCommGroup G] [Fintype G]
  (B:aj G) (X:Finset G) {beta eta:ℝ}
  (g8:0<beta) (fC:0<eta)
  (hX:X.Nonempty)
  (ch:beta*(B.Zc.card:ℝ)≤(X.card:ℝ)) :
  aI.bf B X eta ≤
   2*(1+Real.log (2/beta))/eta^2:=by
 have wL:(0:ℝ)<B.Zc.card:=by
  exact_mod_cast B.aE.card_pos
 have LX:(0:ℝ)<X.card:=by
  exact_mod_cast hX.card_pos
 have eO :
   2*(B.Zc.card:ℝ)/X.card≤2/beta:=by
  rw[Sy LX g8]
  nlinarith
 have Ih:0<2*(B.Zc.card:ℝ)/X.card:=by
  positivity
 have eu :
   Real.log (2*(B.Zc.card:ℝ)/X.card) ≤
    Real.log (2/beta) :=
  QG Ih eO
 have Kk:0<eta^2:=SY fC
 rw[aI.bf]
 apply(R9 Kk).2
 nlinarith
lemma fR
  {G:Type*} [AddCommGroup G] [Fintype G]
  (B:aj G) (X:Finset G) {beta:ℝ}
  (g8:0<beta) (hX:X.Nonempty)
  (ch:beta*(B.Zc.card:ℝ)≤(X.card:ℝ)) :
  aI.bf B X (1/2) ≤
   8*(1+Real.log (2/beta)):=by
 have h :=
  lW B X g8
   (by norm_num:(0:ℝ)<1/2) hX ch
 convert h using 1
 ring
lemma om
  {α:Type*} (S:Finset α) {D:ℝ}
  (ch:(S.card:ℝ)≤D) :
  S.card≤⌈D⌉₊:=by
 exact_mod_cast ch.trans (Rr D)
end
end ay
end
section
open Finset Fintype Function
open scoped BigOperators NNReal
namespace ay.bA
noncomputable section
variable {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
 [MeasurableSpace G] [DiscreteMeasurableSpace G]
def es (K:aj G) (A:Finset G):G→ℝ :=
 (Fintype.card G:ℝ) •
  ao ((@mu (ℝ) _ _) A-mu K.Zc) (mu A-mu K.Zc)
lemma lX
  {K W:aj G} (LY:K.a1)
  (u6:W.a1)
  {A:Finset G} (hA:A.Nonempty) (lL:A⊆K.Zc)
  {eta:ℝ≥0} (fC:0<eta)
  (mC:4*eta ≤
   1/(400*(max W.rank 1:ℕ):ℝ≥0))
  {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty)
  (gp:D⊆(W.ai eta).Zc)
  (lh:E⊆(W.ai eta).Zc)
  {aF:ℝ≥0}
  (dy:aF≤1/(100*(max K.rank 1:ℕ):ℝ≥0))
  (kF: ∀ t,aN.bh D E t≠0 →
   t∈(K.ai aF).Zc)
  {epsilon:ℝ} (eM:0<epsilon) (oR:epsilon≤1)
  (d5 :
   2*((A.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(aF:ℝ))) +
    (K.Zc.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(aF:ℝ)) ≤
    epsilon/8*(K.Zc.card:ℝ)⁻¹)
  {p:ℕ} (hp:0<p)
  (qs :
   an.aM
     ((↑) ∘ aN.bh D E)
     ((al ((@mu (ℝ) _ _) A) (mu A))) (an.cz epsilon p) <
    (1+epsilon/8)*(K.Zc.card:ℝ)⁻¹) :
  an.aM (af W.Zc)
    (ao
     ((@mu (ℝ) _ _) A-mu K.Zc) (mu A-mu K.Zc)) p ≤
   epsilon*(K.Zc.card:ℝ)⁻¹ :=by
 let a:G→ℝ:=(@mu (ℝ) _ _) A-mu K.Zc
 have hq:0<an.bS p :=
  QP (by norm_num) hp
 have ld :=
  fu.tH u6 fC mC
   hD hE gp lh hq
   (an.sU p) a
 rw[fu.er]
  at ld
 apply fu.nw
   LY hA lL hD hE dy kF eM oR d5 hp
   ⟨bO W.Zc,
    cf W.aE⟩
 ·simpa[a] using ld
 ·exact qs
structure aG (original:Finset G) where
 aV:ah.aA original
 fS:aV.restriction.outer=1
 iJ:aV.restriction.ba.a1
namespace aG
def Zd {original:Finset G} (s:aG original) :
  ℝ:=s.aV.Zd
def rank {original:Finset G} (s:aG original) :
  ℕ:=s.aV.rank
def card {original:Finset G} (s:aG original) :
  ℕ:=s.aV.card
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma dI {original:Finset G} (s:aG original) :
  0<s.Zd:=s.aV.dI
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma Zo {original:Finset G} (s:aG original) :
  0≤ s.Zd:=s.dI.le
end aG
structure dB
  {original:Finset G} (s:aG original)
  (epsilon aU:ℝ) (aq:ℕ) where
 aF:ℝ≥0
 w7 :
  aF ≤
   1/(100*(max s.aV.restriction.ba.rank 1:ℕ):ℝ≥0)
 ak:ah.bt (G:=G)
 aB:ah.bt (G:=G)
 fT:ak.outer=1
 g3:aB.outer=1
 ez:ak.ba.a1
 fc:aB.ba.a1
 nS:ak.Zc ⊆
  (s.aV.restriction.ba.ai aF).Zc
 pZ:aB.Zc ⊆
  (s.aV.restriction.ba.ai aF).Zc
 td :
  400*((max s.aV.restriction.ba.rank 1:ℕ):ℝ)*(aF:ℝ) ≤
   epsilon *
    cp s.aV.restriction.set
     s.aV.restriction.ba.Zc/4
 rankOne:ak.ba.rank≤ s.rank+aq
 p0:aB.ba.rank≤ s.rank+aq
 mz:Real.exp (-aU)*(s.card:ℝ)≤ak.Zc.card
 mA:Real.exp (-aU)*(s.card:ℝ)≤aB.Zc.card
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma m0
  {original:Finset G} (s:aG original)
  {epsilon aU:ℝ} {aq:ℕ}
  (eM:0<epsilon)
  (P:dB s epsilon aU aq) :
  ah.bV s.aV P.ak P.aB epsilon ∨
   ∃ t:aG original,
    br.dk (1+epsilon/2) aq aU
     s.aV.restriction t.aV.restriction:=by
 have hA:=s.aV.restriction.nonempty
 have lL :
   s.aV.restriction.set⊆s.aV.restriction.ba.Zc:=by
  simpa[br.aY.e8,s.fS] using
   s.aV.restriction.mo
 have o0 :
   cp s.aV.restriction.set
     s.aV.restriction.ba.Zc=s.aV.Zd:=by
  unfold ah.aA.Zd br.aY.Zd
   cp br.aY.e8
  simp[s.fS]
 rcases ki
   s.iJ P.w7 hA lL
   P.ak.aE P.aB.aE
   P.nS P.pZ eM P.td with
  aQ | Ii | Ij
 ·left
  rw[o0] at aQ
  simpa[ah.bV,ah.aA.e8,
   ah.aA.Zd,
   br.aY.Zd,
   br.aY.e8,s.fS] using aQ
 ·right
  obtain ⟨x,hx⟩:=Ii
  rw[o0] at hx
  have gw:0<a9 s.aV.restriction.set
    P.ak.Zc x:=by
   have hs:0<s.aV.Zd:=s.aV.dI
   have hq:0<(1+epsilon/2:ℝ):=by nlinarith
   exact(QM hq hs).trans_le (by simpa using hx)
  let u:=ah.di s.aV P.ak x gw
  refine ⟨{ aV:=u,fS:= ?_,iJ:= ?_ }, ?_⟩
  ·simpa[u,ah.di,ah.bt.en]
    using P.fT
  ·simpa[u,ah.di,ah.bt.en]
    using P.ez
  ·apply ah.fa
    s.aV P.ak x gw
   ·simpa[ah.aA.Zd,
     br.aY.Zd,
     br.aY.e8] using hx
   ·exact P.rankOne
   ·exact P.mz
 ·right
  obtain ⟨x,hx⟩:=Ij
  rw[o0] at hx
  have gw:0<a9 s.aV.restriction.set
    P.aB.Zc x:=by
   have hs:0<s.aV.Zd:=s.aV.dI
   have hq:0<(1+epsilon/2:ℝ):=by nlinarith
   exact(QM hq hs).trans_le (by simpa using hx)
  let u:=ah.di s.aV P.aB x gw
  refine ⟨{ aV:=u,fS:= ?_,iJ:= ?_ }, ?_⟩
  ·simpa[u,ah.di,ah.bt.en]
    using P.g3
  ·simpa[u,ah.di,ah.bt.en]
    using P.fc
  ·apply ah.fa
    s.aV P.aB x gw
   ·simpa[ah.aA.Zd,
     br.aY.Zd,
     br.aY.e8] using hx
   ·exact P.p0
   ·exact P.mA
def a7
  {original:Finset G} {s:ah.aA original}
  {ak aB:ah.bt (G:=G)} {epsilon:ℝ}
  (h:ah.bV s ak aB epsilon):Finset G :=
 ah.dn s.restriction.set ak.Zc
  (aO.cr h)
def d3
  {original:Finset G} {s:ah.aA original}
  {ak aB:ah.bt (G:=G)} {epsilon:ℝ}
  (h:ah.bV s ak aB epsilon):Finset G :=
 ah.dn s.restriction.set aB.Zc
  (aO.cr h)
noncomputable def mc
    {original:Finset G} (s:ah.aA original)
    {ak aB:ah.bt (G:=G)} {epsilon:ℝ}
    (aQ:ah.bV s ak aB epsilon)
    (_hepsilon_nonneg:0≤epsilon) (b2:epsilon<1)
    {p:ℕ} (hp:0<p) (f:G→ℝ)
    (jy:(2/3:ℝ)^p≤aO.a5 s epsilon)
    (ew :
      |(aO.bb
            (a7 aQ) (d3 aQ) -
          (Fintype.card G:ℝ)/(#ak.Zc:ℝ)) -
          aw.Zp f
            (aO.a4 (d3 aQ))| ≤
        ((Fintype.card G:ℝ)/(#ak.Zc:ℝ))/8)
    (ee :
      an.aM
          (af (aO.a4 aB.Zc)) f p ≤
        ((Fintype.card G:ℝ)/(#ak.Zc:ℝ))/8) :
    aO.eh original:=by
  let x:G:=aO.cr aQ
  let A':Finset G:=a7 aQ
  let b4:Finset G:=d3 aQ
  let B:Finset G:=ak.Zc
  let B':Finset G:=aB.Zc
  let alpha:ℝ:=aO.a5 s epsilon
  have lC:alpha≤a9 s.restriction.set B x:=by
    simpa[alpha,x,B,aO.a5] using
      aO.c0 aQ
  have oW:alpha≤a9 s.restriction.set B' x:=by
    simpa[alpha,x,B',aO.a5] using
      aO.ea aQ
  have b8:0<alpha :=
    QM (sub_pos.mpr b2) s.dI
  have qG:A'.Nonempty:=by
    apply ah.bK ak.aE
    exact b8.trans_le lC
  have gN:b4.Nonempty:=by
    apply ah.bK aB.aE
    exact b8.trans_le oW
  have j9:b4⊆B':=by
    exact ah.dz
      (B:=aB.ba) (a8:=aB.outer)
      (A:=s.restriction.set) (C:=aB.Zc)
      (x:=x) (fun _ hz↦hz)
  have gO: ∀ z∈A',z-(s.shift-x)∈original:=by
    intro z hz
    have i1:x+z∈s.restriction.set :=
      (ah.e3.mp hz).2
    have hs:=s.eR (x+z) i1
    have heq:z-(s.shift-x)=(x+z)-s.shift:=by abel
    rwa[heq]
  have fP: ∀ z∈b4,z-(s.shift-x)∈original:=by
    intro z hz
    have i1:x+z∈s.restriction.set :=
      (ah.e3.mp hz).2
    have hs:=s.eR (x+z) i1
    have heq:z-(s.shift-x)=(x+z)-s.shift:=by abel
    rwa[heq]
  have nn:alpha*(#B:ℝ)≤(#A':ℝ):=by
    have wL:(0:ℝ)< #B:=by exact_mod_cast ak.aE.card_pos
    rw[ah.bk
      ak.aE x] at lC
    exact(Qs wL).mp lC
  have np:alpha*(#B':ℝ)≤(#b4:ℝ):=by
    have wb:(0:ℝ)< #B':=by exact_mod_cast aB.aE.card_pos
    rw[ah.bk
      aB.aE x] at oW
    exact(Qs wb).mp oW
  have qH :
      (2/3:ℝ)^p≤aw.bL b4 B':=by
    calc
      (2/3:ℝ)^p≤alpha:=jy
      _≤a9 s.restriction.set B' x:= oW
      _=aw.bL b4 B':=by
        rw[ah.bk
          aB.aE x]
        rfl
  have oX:(aO.a4 B').Nonempty :=
    aO.eJ aB.aE
  have uk :
      aw.cO (aO.a4 B') p f ≤
        (((Fintype.card G:ℝ)/(#B:ℝ))/8)^p:=by
    apply aO.fb oX hp f (by positivity)
    simpa[B,B'] using ee
  exact
    { A':=A'
      b4:=b4
      B:=B
      B':=B'
      translate:=s.shift-x
      alpha:=alpha
      p:=p
      f:=f
      jP:=qG
      iZ:=gN
      kM:=ak.aE
      h6:=j9
      fL:=gO
      fl:=fP
      i0:=b8.le
      kN:=nn
      jQ:=np
      p_pos:=hp
      gf:=qH
      e6:=by simpa[A',b4,B] using ew
      gg:=uk }
structure eS
  {original:Finset G} (s:aG original)
  {epsilon aU:ℝ} {aq p:ℕ}
  (P:dB s epsilon aU aq)
  (aQ:ah.bV s.aV P.ak P.aB epsilon) where
 base:aj G
 weight:aj G
 wd:base.a1
 uu:weight.a1
 we:base.Zc=P.ak.Zc
 uv :
  weight.Zc=aO.a4 P.aB.Zc
 ro:(a7 aQ).Nonempty
 te:a7 aQ⊆base.Zc
 eta:ℝ≥0
 ux:0<eta
 mD:4*eta ≤
  1/(400*(max weight.rank 1:ℕ):ℝ≥0)
 D:Finset G
 E:Finset G
 yp:D.Nonempty
 yq:E.Nonempty
 rW:D⊆(weight.ai eta).Zc
 rX:E⊆(weight.ai eta).Zc
 aF:ℝ≥0
 yr:aF≤1/(100*(max base.rank 1:ℕ):ℝ≥0)
 rp :
  ∀ t,aN.bh D E t≠0 →
   t∈(base.ai aF).Zc
 uy :
  2*(((a7 aQ).card:ℝ)⁻¹ *
    (200*((max base.rank 1:ℕ):ℝ)*(aF:ℝ))) +
   (base.Zc.card:ℝ)⁻¹ *
    (200*((max base.rank 1:ℕ):ℝ)*(aF:ℝ)) ≤
   (1/8:ℝ)/8*(base.Zc.card:ℝ)⁻¹
 vn :
  (2/3:ℝ)^p≤aO.a5 s.aV epsilon
 e6 :
  |(aO.bb
     (a7 aQ) (d3 aQ) -
    (Fintype.card G:ℝ)/(#P.ak.Zc:ℝ)) -
    aw.Zp
     (es base (a7 aQ))
     (aO.a4 (d3 aQ))| ≤
   ((Fintype.card G:ℝ)/(#P.ak.Zc:ℝ))/8
 qJ :
  (1+(1/8:ℝ)/8)*(base.Zc.card:ℝ)⁻¹ ≤
    an.aM
     ((↑) ∘ aN.bh D E)
     ((al ((@mu (ℝ) _ _) (a7 aQ)) (mu (a7 aQ))))
     (an.cz (1/8:ℝ) p) →
   ∃ t:aG original,
    (257/256:ℝ) *
      aO.a5 s.aV epsilon≤t.Zd ∧
    t.rank≤ s.rank+aq ∧
    Real.exp (-aU)*(s.card:ℝ)≤(t.card:ℝ)
noncomputable def oo
    {original:Finset G} (s:aG original)
    {K:ℝ} {d aq p:ℕ}
    (P:dB s (1/512:ℝ)
      (K*((d+1:ℕ):ℝ)^11) aq)
    (aQ:ah.bV s.aV P.ak P.aB
      (1/512:ℝ))
    (hp:0<p)
    (Q:eS (p:=p) s P aQ)
    (pV :
      an.aM (af Q.weight.Zc)
          (ao
            ((@mu (ℝ) _ _) (a7 aQ)-mu Q.base.Zc)
            (mu (a7 aQ)-mu Q.base.Zc)) p ≤
        (1/8:ℝ)*(Q.base.Zc.card:ℝ)⁻¹) :
    dr s.aV K d:=by
  let c:=mc s.aV aQ
    (by norm_num) (by norm_num) hp
    (es Q.base (a7 aQ))
    Q.vn Q.e6 (by
      let w:G→ℝ≥0:=mu Q.weight.Zc
      have c3 :=
        aN.gv w
          (ao
            ((@mu (ℝ) _ _) (a7 aQ)-mu Q.base.Zc)
            (mu (a7 aQ)-mu Q.base.Zc))
          (Fintype.card G:ℝ) (by positivity) hp
      have uA :
          an.aM
              (af Q.weight.Zc)
              (es Q.base (a7 aQ)) p =
            (Fintype.card G:ℝ) *
              an.aM
                (af Q.weight.Zc)
                (ao
                  ((@mu (ℝ) _ _) (a7 aQ)-mu Q.base.Zc)
                  (mu (a7 aQ)-mu Q.base.Zc)) p:=by
        simpa only[w,NNReal.iF,
          aN.eQ,
          es] using c3
      have pH :
          an.aM
              (af Q.weight.Zc)
              (es Q.base (a7 aQ)) p ≤
            (Fintype.card G:ℝ) *
              ((1/8:ℝ)*(Q.base.Zc.card:ℝ)⁻¹):=by
        rw[uA]
        exact iO pV (by positivity)
      rw[Q.uv] at pH
      simpa[Q.we,Qw,Qo,Q6,
        Qx] using pH)
  refine
    { lg:=c
      tE:= ?_
      A0:= ?_
      y5:= ?_ }
  · change(3/4:ℝ)*s.aV.Zd ≤
      aO.a5 s.aV (1/512:ℝ)
    simp only[aO.a5]
    nlinarith[s.aV.dI.le]
  · change Real.exp (-(K*((d+1:ℕ):ℝ)^11)) *
        (s.card:ℝ)≤(#P.ak.Zc:ℝ)
    exact P.mz
  · change Real.exp (-(K*((d+1:ℕ):ℝ)^11)) *
        (s.card:ℝ)≤(#P.aB.Zc:ℝ)
    exact P.mA
lemma lY
  {original:Finset G} (s:aG original)
  {K:ℝ} {d aq p:ℕ}
  (P:dB s (1/512:ℝ)
   (K*((d+1:ℕ):ℝ)^11) aq)
  (hp:0<p)
  (md :
   ∀ aQ:ah.bV s.aV P.ak P.aB
     (1/512:ℝ),
    Nonempty (eS (p:=p) s P aQ)) :
  Nonempty (dr s.aV K d) ∨
   ∃ t:aG original,
    br.dk (1025/1024:ℝ) aq
     (K*((d+1:ℕ):ℝ)^11)
     s.aV.restriction t.aV.restriction:=by
 rcases m0 s
   (by norm_num:(0:ℝ)<1/512) P with nI | Dz
 ·obtain ⟨Q⟩:=md nI
  by_cases mx :
    (1+(1/8:ℝ)/8)*(Q.base.Zc.card:ℝ)⁻¹ ≤
     an.aM
      ((↑) ∘ aN.bh Q.D Q.E)
      ((al ((@mu (ℝ) _ _) (a7 nI)) (mu (a7 nI))))
      (an.cz (1/8:ℝ) p)
  ·right
   obtain ⟨u,c8,Kl,Km⟩:=Q.qJ mx
   refine ⟨u, ?_,Kl,Km⟩
   calc
    (1025/1024:ℝ)*s.aV.Zd ≤
      (257/256:ℝ) *
       aO.a5 s.aV (1/512:ℝ):=by
     simp only[aO.a5]
     nlinarith[s.aV.dI.le]
    _≤u.Zd:=c8
  ·left
   have LZ :
     an.aM
       ((↑) ∘ aN.bh Q.D Q.E)
       ((al ((@mu (ℝ) _ _) (a7 nI)) (mu (a7 nI))))
       (an.cz (1/8:ℝ) p) <
      (1+(1/8:ℝ)/8)*(Q.base.Zc.card:ℝ)⁻¹ :=
    QV mx
   have pV:=lX Q.wd
    Q.uu Q.ro Q.te Q.ux
    Q.mD Q.yp Q.yq Q.rW Q.rX
    Q.yr Q.rp (by norm_num) (by norm_num)
    Q.uy hp LZ
   exact ⟨oo s P nI hp Q pV⟩
 ·right
  obtain ⟨u,hu⟩:=Dz
  refine ⟨u, ?_⟩
  simpa only[show(1+(1/512:ℝ)/2) =
    (1025/1024:ℝ) by norm_num] using hu
inductive c1 {original:Finset G}
  (q:ℝ) (aq:ℕ) (aU:ℝ) :
  ℕ→aG original →
   aG original→Prop
 | nil (s:aG original) :
   c1 q aq aU 0 s s
 | cons {n:ℕ} {s t u:aG original}
   (pA:br.dk q aq aU
    s.aV.restriction t.aV.restriction)
   (x5:c1 q aq aU n t u) :
   c1 q aq aU (n+1) s u
namespace c1
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma Zf {original:Finset G} {q aU:ℝ} {aq n:ℕ}
  {s t:aG original}
  (h:c1 q aq aU n s t) :
  ah.cU q aq aU n s.aV t.aV:=by
 induction h with
 | nil s=>exact ah.cU.nil s.aV
 | cons pA _ ih=>exact ah.cU.cons pA ih
end c1
lemma ps
  (G:Type*) [AddCommGroup G] [Fintype G] :
  (gn G).a1:=by
 intro aF _hkappa
 simp only[tD,show max 0 1=1 by omega,
  Nat.cast_one]
 rw[oZ]
 simp only[fZ]
 have ch:(0:ℝ)≤Fintype.card G:=by positivity
 constructor<;>nlinarith[show(0:ℝ)≤aF by positivity]
noncomputable def eF (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  aG A where
 aV:=bQ N A hA
 fS:=rfl
 iJ:=ps (ZMod (aD N))
@[simp] lemma k8 (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (eF N A hA).Zd =
   (#A:ℝ)/(aD N:ℕ):=by
 exact p4 N A hA
@[simp] lemma wg (N:ℕ)
  (A:Finset (ZMod (aD N))) (hA:A.Nonempty) :
  (eF N A hA).rank=0:=by
 exact rL N A hA
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma jA
  {original:Finset G}
  {Terminal:aG original→Prop}
  {q lower aU:ℝ} {aq total used remaining:ℕ}
  (hq:1≤q)
  (n8:used+remaining≤total)
  (yl: ∀ n<total, ∀ s:aG original,
   lower≤ s.Zd →
   s.rank≤n*aq →
   Terminal s∨ ∃ t:aG original,
    br.dk q aq aU
     s.aV.restriction t.aV.restriction)
  (initial:aG original)
  (c3:lower≤ initial.Zd)
  (cK:initial.rank≤used*aq)
  (rT:1<q^remaining*initial.Zd) :
  ∃ n≤remaining, ∃ t:aG original,
   c1 q aq aU n initial t ∧
   Terminal t:=by
 induction remaining generalizing initial used with
 | zero =>
   have hs:=initial.aV.Zn
   simp only[pow_zero,QT] at rT
   exact(Rd hs rT).elim
 | succ remaining ih =>
   have L0:used<total:=by omega
   rcases yl used L0 initial c3 cK with wh | ⟨t,pA⟩
   ·exact ⟨0,by omega,initial,
     c1.nil initial,wh⟩
   ·have L3:initial.Zd≤t.Zd:=by
     calc
      initial.Zd=1*initial.Zd:=by ring
      _≤q*initial.Zd :=
       Qi hq initial.Zo
      _≤t.Zd:=pA.1
    have uA:lower≤t.Zd:=c3.trans L3
    have A5:t.rank≤(used+1)*aq:=by
     calc
      t.rank≤ initial.rank+aq:=pA.2.1
      _≤used*aq+aq :=
       RZ cK aq
      _=(used+1)*aq:=by
       rw[Nat.add_mul]
       simp
    have xC:used+1+remaining≤total:=by omega
    have uP:0≤q^remaining:=QH (zero_le_one.trans hq) _
    have Gm:1<q^remaining*t.Zd:=by
     calc
      1<q^(remaining+1)*initial.Zd:=by simpa using rT
      _=q^remaining*(q*initial.Zd):=by
       rw[RB]
       ring
      _≤q^remaining*t.Zd :=
       iO pA.1 uP
    obtain ⟨n,hn,u,ua,hu⟩ :=
     ih xC t uA A5 Gm
    exact ⟨n+1,by omega,u,
     c1.cons pA ua,hu⟩
lemma lD
  {N d:ℕ} (_hN:1≤N)
  {A:Finset (ZMod (aD N))} (hA:A.Nonempty)
  (eu:Real.log (((aD N:ℕ):ℝ)/(#A:ℝ)) ≤
   (d:ℝ)*Real.log 2) :
  br.nF d
   (eF N A hA).Zd:=by
 have Ik:0<aD N:=by simp[aD]
 have yE:(0:ℝ)<aD N:=by exact_mod_cast Ik
 have ch:(0:ℝ)< #A:=by exact_mod_cast hA.card_pos
 have eO:(0:ℝ) <
   ((aD N:ℕ):ℝ)/(#A:ℝ):=Rn yE ch
 have hpow:(0:ℝ)<(2:ℝ)^d:=RF (by norm_num) _
 have L4 :
   Real.log (((aD N:ℕ):ℝ)/(#A:ℝ)) ≤
    Real.log ((2:ℝ)^d):=by
  simpa[QB] using eu
 have wc :
   (((aD N:ℕ):ℝ)/(#A:ℝ))≤(2:ℝ)^d :=
  (SW eO hpow).mp L4
 have hmul:(((aD N:ℕ):ℝ)) ≤
   (2:ℝ)^d*(#A:ℝ):=(QF ch).mp wc
 rw[br.nF]
 simp only[k8]
 apply(Sy hpow yE).2
 simpa[Qx] using hmul
def rq (K:ℝ):Prop :=
 ∀ (N:ℕ),
  ∀ (A:Finset (ZMod (aD N))),A.Nonempty →
   ∀ d:ℕ,1≤d →
    ∃ aq p:ℕ,0<p ∧
     ∀ n<1024*(d+1),
      ∀ s:aG A,
       (1/(2:ℝ)^d)≤ s.Zd →
       s.rank≤n*aq →
       ∃ P:dB s (1/512:ℝ)
        (K*((d+1:ℕ):ℝ)^11) aq,
        ∀ aQ:ah.bV s.aV
          P.ak P.aB (1/512:ℝ),
         Nonempty (eS (p:=p) s P aQ)
lemma k9
  {K:ℝ} (hK:0<K) (Il:rq K) :
  eT
   (8+2050*(2:ℝ)^12*K):=by
 refine ⟨by positivity, ?_⟩
 intro N hN A hA d hd eu
 obtain ⟨aq,p,hp,yi⟩:=Il N A hA d hd
 let fuel:ℕ:=1024*(d+1)
 let initial:=eF N A hA
 let Terminal:aG A→Prop :=
  fun s=>Nonempty (dr s.aV K d)
 have yl: ∀ n<fuel, ∀ s:aG A,
   (1/(2:ℝ)^d)≤ s.Zd →
   s.rank≤n*aq →
   Terminal s∨ ∃ t:aG A,
    br.dk (1025/1024:ℝ) aq
     (K*((d+1:ℕ):ℝ)^11)
     s.aV.restriction t.aV.restriction:=by
  intro n hn s c3 cK
  obtain ⟨P,md⟩:=yi n (by simpa[fuel] using hn) s c3 cK
  exact lY s P hp md
 have uo:=lD hN hA eu
 have zS :
   (1/(2:ℝ)^d)≤ initial.Zd:=by
  change(1/(2:ℝ)^d)≤(bQ N A hA).Zd
  exact uo
 have rT :
   1<(1025/1024:ℝ)^fuel*initial.Zd:=by
  simpa[fuel,initial] using
   l9
    (bQ N A hA) uo
 obtain ⟨n,hn,t,ua,wh⟩ :=
  jA
   (Terminal:=Terminal) (q:=(1025/1024:ℝ))
   (lower:=1/(2:ℝ)^d)
   (aU:=K*((d+1:ℕ):ℝ)^11)
   (aq:=aq) (total:=fuel) (used:=0)
   (remaining:=fuel) (by norm_num) (by omega) yl initial
   zS (by simp[initial]) rT
 let data:=Classical.choice wh
 have Cp:=ua.Zf
 have zu :=
  Cp.qW (by norm_num)
 change(1025/1024:ℝ)^n *
   (bQ N A hA).Zd≤t.aV.Zd at zu
 have c8 :
   (1025/1024:ℝ)^n *
     (bQ N A hA).Zd≤t.aV.Zd:=by
  exact zu
 have E9:=Cp.Zb
 change Real.exp (-(n:ℝ)*(K*((d+1:ℕ):ℝ)^11)) *
   ((bQ N A hA).card:ℝ)≤t.aV.card at E9
 have ch :
   Real.exp (-(n:ℝ)*(K*((d+1:ℕ):ℝ)^11)) *
     ((bQ N A hA).card:ℝ)≤t.aV.card:=by
  exact E9
 exact ⟨dm.tF hd hA hK.le hn
  uo c8 ch data⟩
end
end ay.bA
end
section
open Finset
open scoped BigOperators NNReal
namespace ay
noncomputable section
namespace aj
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
def rN (m:ℕ) (w r:ℝ):Fin (2*m+1) :=
 ⟨min ⌊((r+w)*(m:ℝ))/w⌋₊ (2*m),
  Nat.lt_succ_iff.mpr (Nat.min_le_right _ _)⟩
lemma oq
  {m:ℕ} (hm:0< m) {w r s:ℝ}
  (hw:0≤w) (hr: |r| ≤w) (hs: |s| ≤w)
  (lM:rN m w r=rN m w s) :
  |r-s| ≤w/(m:ℝ):=by
 by_cases vm:w=0
 ·subst w
  have O8:r=0:=by
   apply abs_eq_zero.mp
   exact SC hr (Q8 r)
  have O9:s=0:=by
   apply abs_eq_zero.mp
   exact SC hs (Q8 s)
  simp[O8,O9]
 have z6:0<w:=SM hw (Ne.symm vm)
 have qA:(0:ℝ)< m:=by exact_mod_cast hm
 let ur:ℝ:=((r+w)*(m:ℝ))/w
 let us:ℝ:=((s+w)*(m:ℝ))/w
 have MK: -w≤r∧r≤w:=(abs_le.mp hr)
 have ML: -w≤ s∧s≤w:=(abs_le.mp hs)
 have Kn:0≤ur:=by
  dsimp[ur]
  exact RS (Qn (by linarith) qA.le) hw
 have Ko:0≤us:=by
  dsimp[us]
  exact RS (Qn (by linarith) qA.le) hw
 have Kp:ur≤(2*m:ℕ):=by
  dsimp[ur]
  apply(QF z6).2
  push_cast
  nlinarith
 have Kq:us≤(2*m:ℕ):=by
  dsimp[us]
  apply(QF z6).2
  push_cast
  nlinarith
 have KT:⌊ur⌋₊<2*m+1:=by
  apply(Uc Kn).2
  exact lt_of_le_of_lt Kp (by exact_mod_cast(Tr (2*m)))
 have KU:⌊us⌋₊<2*m+1:=by
  apply(Uc Ko).2
  exact lt_of_le_of_lt Kq (by exact_mod_cast(Tr (2*m)))
 have BV:⌊ur⌋₊≤2*m:=by omega
 have BW:⌊us⌋₊≤2*m:=by omega
 have vU:⌊ur⌋₊=⌊us⌋₊:=by
  have q0:=QA Fin.val lM
  simpa only[rN,ur,us,Nat.min_eq_left BV,
   Nat.min_eq_left BW] using q0
 have MM:((⌊ur⌋₊:ℕ):ℝ)≤ur:=Ti Kn
 have Fa:ur<((⌊ur⌋₊:ℕ):ℝ)+1:=RY ur
 have MN:((⌊us⌋₊:ℕ):ℝ)≤us:=Ti Ko
 have Fb:us<((⌊us⌋₊:ℕ):ℝ)+1:=RY us
 have IW:ur<us+1:=by
  calc
   ur<((⌊ur⌋₊:ℕ):ℝ)+1:=Fa
   _=((⌊us⌋₊:ℕ):ℝ)+1:=by rw[vU]
   _≤us+1:=by gcongr
 have IX:us<ur+1:=by
  calc
   us<((⌊us⌋₊:ℕ):ℝ)+1:=Fb
   _=((⌊ur⌋₊:ℕ):ℝ)+1:=by rw[←vU]
   _≤ur+1:=by gcongr
 have ys :
   ur-us=((r-s)*(m:ℝ))/w:=by
  dsimp[ur,us]
  field_simp
  ring
 have BX:((r-s)*(m:ℝ))/w<1:=by
  rw[←ys]
  linarith
 have BY:(-1:ℝ)<((r-s)*(m:ℝ))/w:=by
  rw[←ys]
  linarith
 have DA:(r-s)*(m:ℝ)<w:=by
  have h:=(Tv z6).mp BX
  simpa only[QT] using h
 have DB: -w<(r-s)*(m:ℝ):=by
  have h:=(SP z6).mp BY
  simpa only[neg_one_mul] using h
 have Kr:r-s<w/(m:ℝ) :=
  (SP qA).2 DA
 have ic: -(w/(m:ℝ))<r-s:=by
  have h:=(Tv qA).2 DB
  simpa only[neg_div] using h
 exact(abs_lt.2 ⟨ic,Kr⟩).le
def fv (B:aj G) (a8:NNReal) (m:ℕ)
  (x:↥(B.ai a8).Zc):B.eX→Fin (2*m+1) :=
 fun γ ↦
  rN m ((a8:ℝ)*(B.width γ.1:ℝ))
   (cx (γ.1 x.1))
omit [DecidableEq G] in
private lemma kQ
  (B:aj G) (a8:NNReal) {m:ℕ} (hm:0< m)
  {x y:↥(B.ai a8).Zc}
  (nd:B.fv a8 m x=B.fv a8 m y) :
  x.1-y.1∈(B.ai (a8/(m:NNReal))).Zc:=by
 rw[Zm]
 intro γ n4
 have hx:=(Zm (B.ai a8) x.1).mp x.2 γ n4
 have hy:=(Zm (B.ai a8) y.1).mp y.2 γ n4
 simp only[oC,SK] at hx hy ⊢
 rw[map_sub]
 have C2 :
   |cx (γ x.1)| ≤(a8:ℝ)*(B.width γ:ℝ):=by
  rwa[←hJ]
 have C3 :
   |cx (γ y.1)| ≤(a8:ℝ)*(B.width γ:ℝ):=by
  rwa[←hJ]
 have vS:=Uu nd ⟨γ,n4⟩
 have hdiv:= oq hm
  (Qn (by positivity) (by positivity)) C2 C3 vS
 calc
  ‖γ x.1-γ y.1‖ ≤
    |cx (γ x.1)-cx (γ y.1)| :=
   gu _ _
  _≤((a8:ℝ)*(B.width γ:ℝ))/(m:ℝ):=hdiv
  _=((a8/(m:NNReal):NNReal):ℝ) *
    (B.width γ:ℝ):=by
   push_cast
   field_simp
omit [DecidableEq G] in
private lemma pv
  (B:aj G) (a8:NNReal) {m:ℕ} (hm:0< m)
  (a:B.eX→Fin (2*m+1)) :
  Fintype.card
    {x:↥(B.ai a8).Zc// B.fv a8 m x=a} ≤
   (B.ai (a8/(m:NNReal))).Zc.card:=by
 classical
 by_cases jv:Nonempty
   {x:↥(B.ai a8).Zc// B.fv a8 m x=a}
 ·let x₀ :
    {x:↥(B.ai a8).Zc// B.fv a8 m x=a} :=
   Classical.choice jv
  let f :
    {x:↥(B.ai a8).Zc// B.fv a8 m x=a} →
     ↥(B.ai (a8/(m:NNReal))).Zc :=
   fun x ↦
    ⟨x.1.1-x₀.1.1,
     kQ B a8 hm
      (x.2.trans x₀.2.symm)⟩
  have hf:Function.Injective f:=by
   intro x y nd
   apply RI
   apply RI
   have q0:=QA Subtype.val nd
   dsimp[f] at q0
   exact S8 q0
  calc
   Fintype.card
     {x:↥(B.ai a8).Zc// B.fv a8 m x=a} ≤
     Fintype.card ↥(B.ai (a8/(m:NNReal))).Zc :=
    R1 f hf
   _=(B.ai (a8/(m:NNReal))).Zc.card :=
    Rx _
 ·simp only[To] at jv
  simp
omit [DecidableEq G] in
lemma h8
  (B:aj G) (a8:NNReal) {m:ℕ} (hm:0< m) :
  (B.ai a8).Zc.card ≤
   (2*m+1)^B.rank *
    (B.ai (a8/(m:NNReal))).Zc.card:=by
 classical
 let S:=B.eX→Fin (2*m+1)
 let q:↥(B.ai a8).Zc→ S:=B.fv a8 m
 have jv: ∀ a:S,
   Fintype.card {x:↥(B.ai a8).Zc// q x=a} ≤
    (B.ai (a8/(m:NNReal))).Zc.card:=by
  intro a
  exact pv B a8 hm a
 have AF:Fintype.card S=(2*m+1)^B.rank:=by
  dsimp[S,rank]
  rw[TC]
  simp
 rw[←Rx (B.ai a8).Zc, ←AF]
 by_contra h
 have xP :
   Fintype.card S*(B.ai (a8/(m:NNReal))).Zc.card <
    Fintype.card ↥(B.ai a8).Zc:=by omega
 obtain ⟨a,ha⟩ :=
  Rk (f:=q) xP
 have Es: #{x | q x=a} ≤
   (B.ai (a8/(m:NNReal))).Zc.card:=by
  rw[←SL]
  exact jv a
 exact(Rd Es) ha
omit [DecidableEq G] in
lemma cM
  (B:aj G) (a8:NNReal) {m:ℕ} (hm:0< m) :
  (B.ai a8).Zc.card ≤
   (3*m)^B.rank *
    (B.ai (a8/(m:NNReal))).Zc.card:=by
 classical
 calc
  (B.ai a8).Zc.card ≤
    (2*m+1)^B.rank *
     (B.ai (a8/(m:NNReal))).Zc.card :=
   h8 B a8 hm
  _≤(3*m)^B.rank *
     (B.ai (a8/(m:NNReal))).Zc.card:=by
   apply QQ
   apply R4
   omega
end aj
end
end ay
end
section
open Finset
open scoped NNReal
namespace ay.ar
noncomputable section
def ax (d aq:ℕ):ℕ :=
 1024*(d+1)*aq
def bn (d aq:ℕ):ℕ :=
 819200*ax d aq*2^d
def bd (d aq:ℕ):ℕ :=
 76800*ax d aq*2^(d+1)
lemma iK {d aq:ℕ} (cE:0<aq) :
  0<ax d aq:=by
 unfold ax
 positivity
lemma zb {d aq:ℕ} (cE:0<aq) :
  1≤ax d aq :=
 Nat.one_le_iff_ne_zero.mpr (iK cE).ne'
lemma i8 {d aq r:ℕ}
  (cE:0<aq)
  (cK:r≤ax d aq) :
  max r 1≤ax d aq:=by
 exact max_le cK (zb cE)
lemma me {d aq:ℕ} (cE:0<aq) :
  0<bn d aq:=by
 unfold bn
 exact QP
  (QP (by norm_num) (iK cE))
  (RF (by norm_num) _)
lemma mf {d aq:ℕ} (cE:0<aq) :
  0<bd d aq:=by
 unfold bd
 exact QP
  (QP (by norm_num) (iK cE))
  (RF (by norm_num) _)
lemma p6 {d aq r:ℕ}
  (cE:0<aq)
  (cK:r≤ax d aq) :
  100*max r 1≤bn d aq:=by
 have lE:=i8 cE cK
 unfold bn
 calc
  100*max r 1≤100*ax d aq :=
   Qr 100 lE
  _≤819200*ax d aq*2^d:=by
   have qI:100≤819200:=by omega
   calc
    100*ax d aq≤819200*ax d aq :=
     QQ _ qI
    _≤819200*ax d aq*2^d :=
     Q4 _ (RF (by norm_num) _)
lemma tJ {d aq r:ℕ}
  (cE:0<aq)
  (cK:r≤ax d aq) :
  ((bn d aq:NNReal)⁻¹) ≤
   1/(100*(max r 1:ℕ):NNReal):=by
 rw[R6]
 have kz:(0:NNReal)<bn d aq:=by
  exact_mod_cast me cE
 have oL:(0:NNReal)<100*(max r 1:ℕ):=by
  positivity
 apply(RJ kz oL).2
 exact_mod_cast p6 cE cK
lemma wj {d aq r:ℕ}
  (cE:0<aq)
  (cK:r≤ax d aq)
  {Zd:ℝ}
  (c8:1/(2:ℝ)^d≤Zd) :
  400*((max r 1:ℕ):ℝ) *
    ((((bn d aq:ℕ):NNReal)⁻¹ :NNReal):ℝ) ≤
   (1/512:ℝ)*Zd/4:=by
 change 400*((max r 1:ℕ):ℝ) *
   (bn d aq:ℝ)⁻¹ ≤(1/512:ℝ)*Zd/4
 have lE:=i8 cE cK
 have Fc :
   819200*max r 1*2^d≤bn d aq:=by
  unfold bn
  exact QQ (2^d)
   (Qr 819200 lE)
 have hbound :
   (819200:ℝ)*(max r 1:ℕ)*(2:ℝ)^d ≤
    (bn d aq:ℝ):=by
  exact_mod_cast Fc
 have Hi:(0:ℝ)<bn d aq:=by
  exact_mod_cast me cE
 have xD :
   (0:ℝ)<(819200:ℝ)*(max r 1:ℕ)*(2:ℝ)^d:=by
  positivity
 have hinv :
   (bn d aq:ℝ)⁻¹ ≤
    ((819200:ℝ)*(max r 1:ℕ)*(2:ℝ)^d)⁻¹ :=
  (RJ Hi xD).2 hbound
 calc
  400*((max r 1:ℕ):ℝ)*(bn d aq:ℝ)⁻¹ ≤
    400*((max r 1:ℕ):ℝ) *
     ((819200:ℝ)*(max r 1:ℕ)*(2:ℝ)^d)⁻¹ :=by
   gcongr
  _=(1/2048:ℝ)*(1/(2:ℝ)^d):=by
   have s9:(0:ℝ)<(max r 1:ℕ):=by positivity
   have Im:(0:ℝ)<(2:ℝ)^d:=by positivity
   field_simp
   ring
  _≤(1/2048:ℝ)*Zd:=by
   gcongr
  _=(1/512:ℝ)*Zd/4:=by ring
lemma nX {d aq r:ℕ}
  (cE:0<aq)
  (cK:r≤ax d aq) :
  200*max r 1≤bd d aq:=by
 have lE:=i8 cE cK
 unfold bd
 calc
  200*max r 1≤200*ax d aq :=
   Qr 200 lE
  _≤76800*ax d aq*2^(d+1):=by
   have qI:200≤76800:=by omega
   calc
    200*ax d aq≤76800*ax d aq :=
     QQ _ qI
    _≤76800*ax d aq*2^(d+1) :=
     Q4 _ (RF (by norm_num) _)
lemma q8 {d aq r:ℕ}
  (cE:0<aq)
  (cK:r≤ax d aq) :
  (bd d aq:NNReal)⁻¹ +(bd d aq:NNReal)⁻¹ ≤
   1/(100*(max r 1:ℕ):NNReal):=by
 have sh:=nX cE cK
 have kz:(0:NNReal)<bd d aq:=by
  exact_mod_cast mf cE
 have oL:(0:NNReal)<200*(max r 1:ℕ):=by
  positivity
 have hinv :
   (bd d aq:NNReal)⁻¹ ≤
    (200*(max r 1:ℕ):NNReal)⁻¹ :=by
  apply(RJ kz oL).2
  exact_mod_cast sh
 calc
  (bd d aq:NNReal)⁻¹ +(bd d aq:NNReal)⁻¹ ≤
    (200*(max r 1:ℕ):NNReal)⁻¹ +
     (200*(max r 1:ℕ):NNReal)⁻¹ :=
   Sr hinv hinv
  _=1/(100*(max r 1:ℕ):NNReal):=by
   have s9:(0:NNReal)<(max r 1:ℕ):=by positivity
   field_simp
   norm_num
end
end ay.ar
end
section
open Finset Fintype Function
open scoped BigOperators NNReal
namespace ay.pF
noncomputable section
variable {G:Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
private lemma q9 (K:aj G) (x:G) :
  af K.Zc (-x)=af K.Zc x:=by
 by_cases hx:x∈K.Zc
 ·have Ks: -x∈K.Zc:=aj.ec.mpr hx
  simp[dj hx,dj Ks]
 ·have Ks: -x∉K.Zc:=by
   intro h
   exact hx (aj.ec.mp h)
  simp[dO hx,
   dO Ks]
lemma ie
  {K:aj G} (dF:K.a1) {κ:ℝ≥0}
  (qu:κ≤1/(100*(max K.rank 1:ℕ):ℝ≥0))
  {A:Finset G} (hA:A.Nonempty) (lL:A⊆K.Zc)
  {t:G} (ht:t∈(K.ai κ).Zc) :
  |ao (af A)
    (af K.Zc) t-(K.Zc.card:ℝ)⁻¹| ≤
   (A.card:ℝ)⁻¹ *
    (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ)):=by
 let E:ℝ:=200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ)
 have r0:(A.card:ℝ)≠0:=by exact_mod_cast hA.card_ne_zero
 have L5: ∑ x:G,af A x=1 :=
  cf hA
 have dc :
   ∑ x:G,af A x*(K.Zc.card:ℝ)⁻¹ =
    (K.Zc.card:ℝ)⁻¹ :=by
  rw[←Qt,L5,QT]
 have Gn :
   ∑ x:G,
     |af K.Zc (t-x) -
      af K.Zc (-x)| ≤E:=by
  have eY: -t∈(K.ai κ).Zc :=
   aj.ec.mpr ht
  have kC :=
   aj.cN
    dF qu eY
  calc
   ∑ x:G,
     |af K.Zc (t-x) -
      af K.Zc (-x)| =
     ∑ x:G,
      |af K.Zc (x- -t) -
       af K.Zc x| :=by
    refine Qk (Equiv.neg G) _ _ ?_
    intro x
    simp only[Equiv.neg_apply]
    congr 2; abel_nf
   _≤E:=kC
 have qv :
   ∑ x:G,af A x *
     |af K.Zc (t-x) -
      af K.Zc (-x)| ≤
    (A.card:ℝ)⁻¹ *E:=by
  calc
   ∑ x:G,af A x *
     |af K.Zc (t-x) -
      af K.Zc (-x)| =
     (A.card:ℝ)⁻¹ * ∑ x∈A,
      |af K.Zc (t-x) -
       af K.Zc (-x)| :=by
    change(∑ x:G,(if x∈A then (A.card:ℝ)⁻¹ else 0) *
      |af K.Zc (t-x) -
       af K.Zc (-x)|)=_
    simp only[ite_mul,zero_mul]
    rw[←QE]
    have eI:(Finset.univ:Finset G).filter (fun x↦x∈A)=A:=by
     ext x
     simp
    rw[eI,Qj]
   _≤(A.card:ℝ)⁻¹ * ∑ x:G,
      |af K.Zc (t-x) -
       af K.Zc (-x)| :=by
    apply iO
    ·exact Ry (S7 A)
      (fun _ _ _↦Q8 _)
    ·positivity
   _≤(A.card:ℝ)⁻¹ *E :=
    iO Gn (by positivity)
 rw[ao, ←dc, ←QJ]
 simp_rw[←UY]
 calc
  |∑ x:G,af A x *
    (af K.Zc (t-x) -
     (K.Zc.card:ℝ)⁻¹)| =
    |∑ x:G,af A x *
     (af K.Zc (t-x) -
      af K.Zc (-x))| :=by
   apply QA abs
   apply Io rfl
   intro x _
   by_cases hx:x∈A
   ·rw[q9 K x,
     dj (lL hx)]
   ·simp[dO hx]
  _≤ ∑ x:G, |af A x *
     (af K.Zc (t-x) -
      af K.Zc (-x))| :=
   abs_sum_le_sum_abs _ _
  _= ∑ x:G,af A x *
     |af K.Zc (t-x) -
      af K.Zc (-x)| :=by
   apply Io rfl
   intro x _
   rw[SU,QC (bO A x)]
  _≤(A.card:ℝ)⁻¹ *E:=qv
omit [AddCommGroup G] [DecidableEq G] [Fintype G] in
private lemma tK
  {C:Finset G} (hC:C.Nonempty) (f:G→ℝ) (c:ℝ) :
  aw.aT C f-c =
   aw.aT C (fun x↦f x-c):=by
 unfold aw.aT
 rw[QJ]
 simp only[Tq,QS]
 have Pa:(C.card:ℝ)≠0:=by exact_mod_cast hC.card_ne_zero
 field_simp
omit [AddCommGroup G] [DecidableEq G] [Fintype G] in
private lemma wk
  {C:Finset G} (hC:C.Nonempty) (c:ℝ) :
  aw.aT C (fun _↦c)=c:=by
 unfold aw.aT
 simp[hC.card_ne_zero]
lemma dY
  {K:aj G} (dF:K.a1) {κ:ℝ≥0}
  (qu:κ≤1/(100*(max K.rank 1:ℕ):ℝ≥0))
  {A C:Finset G} (hA:A.Nonempty) (lL:A⊆K.Zc)
  (hC:C.Nonempty) (fN:C⊆(K.ai κ).Zc) :
  |aw.aT C
    (ao (af A)
     (af K.Zc))-(K.Zc.card:ℝ)⁻¹| ≤
   (A.card:ℝ)⁻¹ *
    (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ)):=by
 let M:ℝ:=(A.card:ℝ)⁻¹ *
  (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ))
 rw[tK hC]
 calc
  |aw.aT C (fun x ↦
    ao (af A)
     (af K.Zc) x-(K.Zc.card:ℝ)⁻¹)| ≤
   aw.aT C (fun x ↦
    |ao (af A)
     (af K.Zc) x-(K.Zc.card:ℝ)⁻¹|) :=
   aw.g1 _
  _≤aw.aT C (fun _↦M):=by
   unfold aw.aT
   apply Qz
   ·apply QI
    intro x hx
    exact ie
     dF qu hA lL (fN hx)
   ·positivity
  _=M:=wk hC M
omit [DecidableEq G] in
private lemma mE
  (a k:G→ℝ) (x:G) :
  ao (a-k) (a-k) x =
   ao a a x-ao a k x -
    ao k a x+ao k k x:=by
 unfold ao
 simp only[Rw,UY,sub_mul,QJ]
 ring
omit [AddCommGroup G] [DecidableEq G] [Fintype G] in
private lemma xE
  {C:Finset G} (f g:G→ℝ) :
  aw.aT C (fun x↦f x+g x) =
   aw.aT C f+aw.aT C g:=by
 unfold aw.aT
 rw[T7,add_div]
omit [AddCommGroup G] [DecidableEq G] [Fintype G] in
private lemma sI
  {C:Finset G} (f g:G→ℝ) :
  aw.aT C (fun x↦f x-g x) =
   aw.aT C f-aw.aT C g:=by
 unfold aw.aT
 rw[QJ,UT]
omit [AddCommGroup G] [DecidableEq G] [Fintype G] in
private lemma ku
  {C:Finset G} (c:ℝ) (f:G→ℝ) :
  aw.aT C (fun x↦c*f x) =
   c*aw.aT C f:=by
 unfold aw.aT
 rw[←Qj]
 ring
lemma gT
  {K:aj G} (dF:K.a1) {κ:ℝ≥0}
  (qu:κ≤1/(100*(max K.rank 1:ℕ):ℝ≥0))
  {A b4:Finset G} (hA:A.Nonempty) (lL:A⊆K.Zc)
  (gN:b4.Nonempty)
  (fN:aO.a4 b4⊆(K.ai κ).Zc)
  (d5 :
   2*((A.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ))) +
    (K.Zc.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ)) ≤
    ((K.Zc.card:ℝ)⁻¹)/8) :
  |(aO.bb A b4 -
    (Fintype.card G:ℝ)/(#K.Zc:ℝ)) -
    aw.Zp
     ((Fintype.card G:ℝ) •
      ao
       (af A-af K.Zc)
       (af A-af K.Zc))
     (aO.a4 b4)| ≤
   ((Fintype.card G:ℝ)/(#K.Zc:ℝ))/8:=by
 let C:=aO.a4 b4
 let yt:=ao (af A) (af A)
 let qK:=ao (af A) (af K.Zc)
 let rr:=ao (af K.Zc) (af A)
 let sJ:=ao (af K.Zc) (af K.Zc)
 let eC:ℝ:=(K.Zc.card:ℝ)⁻¹
 let E:ℝ:=200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ)
 have hC:C.Nonempty:=aO.eJ gN
 have Kt: |aw.aT C qK-eC| ≤
   (A.card:ℝ)⁻¹ *E:=by
  simpa[C,qK,eC,E] using
   dY
    dF qu hA lL hC fN
 have Pb: |aw.aT C rr-eC| ≤
   (A.card:ℝ)⁻¹ *E:=by
  rw[show rr=qK by
   dsimp[rr,qK]
   exact fG _ _]
  exact Kt
 have Pc: |aw.aT C sJ-eC| ≤eC*E:=by
  simpa[C,sJ,eC,E] using
   dY
    dF qu K.aE (Finset.Subset.rfl) hC fN
 have hsum :
   |(aw.aT C qK-eC) +
     (aw.aT C rr-eC) -
     (aw.aT C sJ-eC)| ≤
    2*((A.card:ℝ)⁻¹ *E)+eC*E:=by
  calc
   |(aw.aT C qK-eC) +
     (aw.aT C rr-eC) -
     (aw.aT C sJ-eC)| ≤
    |aw.aT C qK-eC| +
     |aw.aT C rr-eC| +
     |aw.aT C sJ-eC| :=by
    calc
     |_-_| ≤ |(aw.aT C qK-eC) +
       (aw.aT C rr-eC)| +
       |aw.aT C sJ-eC| :=by
      simpa[Su] using(abs_sub_le
       ((aw.aT C qK-eC) +
        (aw.aT C rr-eC))
       (0:ℝ) (aw.aT C sJ-eC))
     _≤(|aw.aT C qK-eC| +
       |aw.aT C rr-eC|) +
       |aw.aT C sJ-eC| :=by
      gcongr
      exact UP _ _
   _≤2*((A.card:ℝ)⁻¹ *E)+eC*E:=by
    nlinarith
 have fF:(Fintype.card G:ℝ)/(#K.Zc:ℝ) =
   (Fintype.card G:ℝ)*eC:=by
  simp[eC,Qw]
 have L6:aO.bb A b4 =
   (Fintype.card G:ℝ)*aw.aT C yt:=by
  rw[aO.j8 gN]
  change aw.aT C
    (fun x↦(Fintype.card G:ℝ)*yt x)=_
  rw[ku]
 have nI :
   aw.Zp
     ((Fintype.card G:ℝ) •
      ao
       (af A-af K.Zc)
       (af A-af K.Zc)) C =
    (Fintype.card G:ℝ) *
     (aw.aT C yt-aw.aT C qK -
      aw.aT C rr+aw.aT C sJ):=by
  rw[aw.mP hC]
  change aw.aT C (fun x↦(Fintype.card G:ℝ) *
   ao
    (af A-af K.Zc)
    (af A-af K.Zc) x)=_
  rw[ku]
  congr 1
  rw[show ao
    (af A-af K.Zc)
    (af A-af K.Zc) =
    (fun x↦yt x-qK x-rr x+sJ x) by
   funext x
   simpa[yt,qK,rr,sJ] using
    mE (af A)
     (af K.Zc) x]
  rw[xE,sI,sI]
 rw[L6,fF,nI]
 have yj:0≤(Fintype.card G:ℝ):=by positivity
 calc
  |((Fintype.card G:ℝ)*aw.aT C yt -
    (Fintype.card G:ℝ)*eC) -
    (Fintype.card G:ℝ) *
     (aw.aT C yt-aw.aT C qK -
      aw.aT C rr+aw.aT C sJ)| =
   (Fintype.card G:ℝ) *
    |(aw.aT C qK-eC) +
     (aw.aT C rr-eC) -
     (aw.aT C sJ-eC)| :=by
   have heq :
     (Fintype.card G:ℝ)*aw.aT C yt -
       (Fintype.card G:ℝ)*eC -
       (Fintype.card G:ℝ) *
        (aw.aT C yt-aw.aT C qK -
         aw.aT C rr+aw.aT C sJ) =
      (Fintype.card G:ℝ) *
       ((aw.aT C qK-eC) +
        (aw.aT C rr-eC) -
        (aw.aT C sJ-eC)):=by ring
   rw[heq,SU,QC yj]
  _≤(Fintype.card G:ℝ) *
    (2*((A.card:ℝ)⁻¹ *E)+eC*E) :=
   iO hsum yj
  _≤(Fintype.card G:ℝ)*(eC/8):=by
   apply iO
   ·simpa[E,eC] using d5
   ·exact yj
  _=((Fintype.card G:ℝ)/(#K.Zc:ℝ))/8:=by
   rw[fF]
   ring
lemma e4
  {K:aj G} (dF:K.a1) {κ:ℝ≥0}
  (qu:κ≤1/(100*(max K.rank 1:ℕ):ℝ≥0))
  {A b4:Finset G} (hA:A.Nonempty) (lL:A⊆K.Zc)
  (gN:b4.Nonempty)
  (fN:aO.a4 b4⊆(K.ai κ).Zc)
  (d5 :
   2*((A.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ))) +
    (K.Zc.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ)) ≤
    (1/8:ℝ)/8*(K.Zc.card:ℝ)⁻¹) :
  |(aO.bb A b4 -
    (Fintype.card G:ℝ)/(#K.Zc:ℝ)) -
    aw.Zp
     ((Fintype.card G:ℝ) •
      ao
       ((@mu (ℝ) _ _) A-mu K.Zc)
       (mu A-mu K.Zc))
     (aO.a4 b4)| ≤
   ((Fintype.card G:ℝ)/(#K.Zc:ℝ))/8:=by
 have L7:0≤(K.Zc.card:ℝ)⁻¹ :=by positivity
 have Cq :
   2*((A.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ))) +
    (K.Zc.card:ℝ)⁻¹ *
     (200*((max K.rank 1:ℕ):ℝ)*(κ:ℝ)) ≤
    ((K.Zc.card:ℝ)⁻¹)/8:=by
  apply d5.trans
  nlinarith
 have Np:(@mu (ℝ) _ _) A=af A :=
  aN.eQ A
 have Nq:(@mu (ℝ) _ _) K.Zc=af K.Zc :=
  aN.eQ K.Zc
 simpa only[Np,Nq] using
  gT dF qu hA lL
   gN fN Cq
end
end ay.pF
end
section
open Finset
open scoped NNReal
namespace ay.aa
noncomputable section
def cH:ℝ:=1/8192
def dh (alpha:ℝ):ℕ:=⌈8192/alpha⌉₊
def dq (alpha:ℝ):ℕ:=Nat.clog 2 (dh alpha)
def g4 (alpha:ℝ):ℕ :=
 ⌈1+Real.log (2/alpha)⌉₊
def fE (alpha:ℝ):ℕ :=
 ay.cQ (g4 alpha)
  ((cH/dq alpha)/Real.exp 1)
def gs (alpha:ℝ) (k:ℕ):ℝ :=
 (alpha/2)^k/2
def ra (alpha:ℝ) (k:ℕ):ℕ :=
 ⌈8*(1+Real.log (2/gs alpha k))⌉₊
def dt (d:ℕ):ℕ:=4*(d+1)
def bH (d:ℕ):ℕ :=
 an.cz (1/8:ℝ) (dt d)
def av (d:ℕ):ℕ :=
 2+2*d*bH d
def aR (d:ℕ):ℝ :=
 1/(2:ℝ)^av d
def au (d:ℕ):ℕ :=
 max 1 (ra (aR d)
  (fE (aR d)))
def bE (d:ℕ):ℕ:=dh (aR d)
def b1 (d:ℕ):ℕ :=
 dq (aR d)
def dC (d:ℕ):ℕ :=
 fE (aR d)
def nx (d:ℕ):ℕ :=
 2^38*(av d+13)^3
def o1 (d:ℕ):ℕ :=
 2^42*(av d+13)^4
def aH:ℕ :=
 2^42*1720335^4
lemma ny:0<cH:=by
 norm_num[cH]
lemma mg (d:ℕ):0<dt d:=by
 unfold dt
 positivity
lemma fU (d:ℕ):0<bH d:=by
 unfold bH
 exact an.uQ (by norm_num) (mg d)
lemma nA (d:ℕ):Even (bH d):=by
 unfold bH
 exact an.tY _ _
lemma u7 (d:ℕ) :
  bH d≤860160*(d+1):=by
 have h :=
  an.pj
   (ε:=(1/8:ℝ)) (p:=dt d) (mg d)
 norm_num[bH,dt,cP] at h ⊢
 omega
lemma gU (d:ℕ) :
  av d≤1720322*(d+1)^2:=by
 unfold av
 have h:=u7 d
 nlinarith[show d≤d+1 by omega]
lemma bP (d:ℕ):0<aR d:=by
 unfold aR
 positivity
lemma dZ (d:ℕ):aR d≤1:=by
 unfold aR
 have hpow:(1:ℝ)≤(2:ℝ)^av d:=by
  exact RH (by norm_num)
 exact(QF (by positivity)).2
  (by simpa only[av,QT] using hpow)
lemma i3 (d:ℕ):aR d≤2 :=
 (dZ d).trans (by norm_num)
lemma bX (d:ℕ):0<au d:=by
 unfold au
 exact SI (by norm_num) (Tu _ _)
lemma tf (d:ℕ) :
  bE d=8192*2^av d:=by
 unfold bE dh aR
 have hpow:(0:ℝ)<(2:ℝ)^av d:=by positivity
 rw[show(8192:ℝ)/(1/(2:ℝ)^av d) =
   ((8192*2^av d:ℕ):ℝ) by
    push_cast
    field_simp]
 exact Nat.ceil_natCast _
lemma uB (d:ℕ) :
  b1 d=13+av d:=by
 unfold b1 dq
 change Nat.clog 2 (bE d)=13+av d
 rw[tf]
 rw[show(8192:ℕ)=2^13 by norm_num, ←RL,
  Nat.clog_pow 2 (13+av d) (by norm_num)]
lemma tL (d:ℕ) :
  g4 (aR d)≤av d+2:=by
 unfold g4 aR
 apply Nat.ceil_le.mpr
 have hpow:(0:ℝ)<(2:ℝ)^av d:=by positivity
 have uV :
   2/(1/(2:ℝ)^av d) =
    (2:ℝ)^(av d+1):=by
  field_simp
  rw[RB]
  ring
 rw[uV,QB]
 have eu:Real.log (2:ℝ)≤1:=by
  convert QX (show(0:ℝ)<2 by norm_num) using 1
  norm_num
 push_cast
 nlinarith[iO eu
  (show(0:ℝ)≤av d+1 by positivity)]
lemma nY (d:ℕ) :
  dC d≤nx d:=by
 unfold dC fE nx
 unfold ay.cQ
 apply Nat.ceil_le.mpr
 have hq:=tL d
 have uU:=uB d
 have Je:(g4 (aR d):ℝ) ≤
   av d+2:=by exact_mod_cast hq
 have Ku:(dq (aR d):ℝ) =
   av d+13:=by
  change(b1 d:ℝ) =
   av d+13
  exact_mod_cast(by simpa[Nat.add_comm] using uU)
 have l5:Real.exp 1≤3:=Real.exp_one_lt_three.le
 have hE:(0:ℝ)≤av d:=by positivity
 rw[Ku]
 unfold cH
 have sh :
   (0:ℝ) <
    (((1/8192:ℝ)/(av d+13)) /
     Real.exp 1/2)^2:=by positivity
 apply(QF sh).2
 have Go:(0:ℝ)<av d+13:=by positivity
 have PE:(g4 (aR d):ℝ) ≤
   av d+13:=by linarith
 have PF:Real.exp 1^2≤(9:ℝ):=by
  nlinarith[Q1 (1:ℝ)]
 field_simp
 push_cast
 calc
  64*(g4 (aR d):ℝ)*8192^2 *
    (av d+13)^2*Real.exp 1^2*2^2 ≤
   64*(av d+13)*8192^2 *
    (av d+13)^2*9*2^2:=by
     gcongr
  _=(64*8192^2*9*2^2:ℝ) *
    (av d+13)^3:=by ring
  _≤(2^38:ℝ)*(av d+13)^3:=by
   gcongr
   norm_num
  _=(274877906944:ℝ) *
    (av d+13)^3:=by norm_num
lemma gV {alpha:ℝ} (b8:0<alpha) :
  0<dh alpha:=by
 unfold dh
 apply Nat.ceil_pos.2
 positivity
lemma m1 {alpha:ℝ} (_halpha:0<alpha) :
  8192/alpha≤(dh alpha:ℝ):=by
 exact Rr _
lemma s5 {alpha ratio:ℝ}
  (b8:0<alpha) (yu:alpha≤2)
  (eO:alpha/2≤ratio) :
  ⌈1+Real.log (min 1 ratio)⁻¹⌉₊≤g4 alpha:=by
 have yv:0<alpha/2:=by positivity
 have Gp:alpha/2≤(1:ℝ):=by linarith
 have Kv:alpha/2≤ min 1 ratio:=le_min Gp eO
 have In:0< min 1 ratio:=yv.trans_le Kv
 have hinv:(min 1 ratio)⁻¹ ≤(alpha/2)⁻¹ :=
  (RJ In yv).2 Kv
 have eu:Real.log (min 1 ratio)⁻¹ ≤Real.log (2/alpha):=by
  have sx:(alpha/2)⁻¹ =2/alpha:=by
   field_simp
  rw[←sx]
  exact QG (by positivity) hinv
 unfold g4
 apply S3
 linarith
lemma p7 {q Q:ℕ} {epsilon:ℝ}
  (hq:q≤Q) (eM:0<epsilon) :
  ay.cQ q epsilon ≤
   ay.cQ Q epsilon:=by
 unfold ay.cQ
 apply S3
 have sh:0<(epsilon/2)^2:=by positivity
 exact Qz
  (by exact_mod_cast Qr 64 hq) sh.le
lemma ig
  {G:Type*} [AddCommGroup G]
  (M L:Finset G) {alpha:ℝ}
  (b8:0<alpha) (yu:alpha≤2)
  (eO:alpha/2≤(L.card:ℝ)/M.card)
  (hm:0<dq alpha) :
  ah.cm M L cH
    (dq alpha)≤fE alpha:=by
 classical
 unfold ah.cm fE
 apply p7
 ·unfold ah.l7
  exact s5 b8 yu eO
 ·have uU:(0:ℝ)<dq alpha:=by exact_mod_cast hm
  exact Rn (Rn ny uU) (Q1 _)
lemma sK {alpha:ℝ} (b8:0<alpha)
  (o2:alpha≤1) :
  0<dq alpha:=by
 unfold dq
 have hq:1<dh alpha:=by
  have iV:(1:ℝ)<8192/alpha:=by
   have:alpha<8192:=by
    nlinarith
   exact(SP b8).2 (by nlinarith)
  have rG:8192/alpha≤(dh alpha:ℝ):=m1 b8
  exact_mod_cast iV.trans_le rG
 exact Nat.clog_pos (by norm_num) hq
lemma o3 {alpha:ℝ} (_halpha:0<alpha) :
  dh alpha≤2^dq alpha:=by
 unfold dq
 exact Nat.le_pow_clog (by norm_num) _
lemma qL {alpha:ℝ} (b8:0<alpha) :
  (1/2:ℝ)^dq alpha≤alpha/8192:=by
 have hq:(0:ℝ)<dh alpha:=by
  exact_mod_cast gV b8
 have hpow:(0:ℝ)<(2:ℝ)^dq alpha:=by positivity
 have uP:(dh alpha:ℝ)≤(2:ℝ)^dq alpha:=by
  exact_mod_cast o3 b8
 have rG:8192/alpha≤(dh alpha:ℝ) :=
  m1 b8
 calc
  (1/2:ℝ)^dq alpha =
    ((2:ℝ)^dq alpha)⁻¹ :=by
     rw[R6,Te]
  _≤(dh alpha:ℝ)⁻¹ :=
   (RJ hpow hq).2 uP
  _≤(8192/alpha)⁻¹ :=by
   have dc:(0:ℝ)<8192/alpha:=by positivity
   exact(RJ hq dc).2 rG
  _=alpha/8192:=by
   field_simp
lemma jj {alpha:ℝ}
  (b8:0<alpha) (o2:alpha≤1) :
  Real.sqrt (2/alpha)≤2/alpha:=by
 have JR:(1:ℝ)≤2/alpha:=by
  apply(Qs b8).2
  nlinarith
 have uc:0≤2/alpha:=by positivity
 rw[Real.sqrt_le_iff]
 constructor
 ·exact uc
 ·nlinarith
lemma qM
  {alpha:ℝ} (b8:0<alpha) (o2:alpha≤1) :
  (2/(dh alpha:ℝ))*Real.sqrt (2/alpha)≤1/2048:=by
 have hq:(0:ℝ)<dh alpha:=by
  exact_mod_cast gV b8
 have rG:=m1 b8
 have DC:=jj b8 o2
 calc
  (2/(dh alpha:ℝ))*Real.sqrt (2/alpha) ≤
    (2/(dh alpha:ℝ))*(2/alpha):=by
   gcongr
  _≤(2/(8192/alpha))*(2/alpha):=by
   have dc:(0:ℝ)<8192/alpha:=by positivity
   have hdiv:2/(dh alpha:ℝ)≤2/(8192/alpha):=by
    exact Rb (by norm_num) dc rG
   exact Qi hdiv (by positivity)
  _=1/2048:=by
   field_simp
   norm_num
lemma s6
  {alpha:ℝ} (b8:0<alpha) (o2:alpha≤1) :
  (2*(1/2:ℝ)^dq alpha) *
    Real.sqrt (2/alpha)≤1/2048:=by
 have uU:=qL b8
 have DC:=jj b8 o2
 calc
  (2*(1/2:ℝ)^dq alpha) *
    Real.sqrt (2/alpha) ≤
   (2*(alpha/8192))*(2/alpha):=by
    gcongr
  _=1/2048:=by
   field_simp
   norm_num
lemma zT {alpha:ℝ} {k:ℕ} (b8:0<alpha) :
  0<gs alpha k:=by
 unfold gs
 positivity
lemma sL
  {alpha:ℝ} {k:ℕ} (b8:0<alpha) :
  Real.log (2/gs alpha k) =
   Real.log 4+(k:ℝ)*Real.log (2/alpha):=by
 have iB:(0:ℝ)<alpha/2:=by positivity
 have uV :
   2/gs alpha k=4/(alpha/2)^k:=by
  unfold gs
  field_simp
  ring
 rw[uV,Ui (by norm_num) (Rg _ iB.ne'),
  QB,Ui (by norm_num) b8.ne',
  Ui b8.ne' (by norm_num)]
 ring
lemma kc (d:ℕ) :
  au d≤o1 d:=by
 unfold au o1
 apply max_le
 ·have gw:0<2^42*(av d+13)^4:=by
   positivity
  omega
 ·unfold ra
  apply Nat.ceil_le.mpr
  rw[sL (bP d)]
  have hk:=nY d
  have MO:(fE (aR d):ℝ) ≤
    (2^38*(av d+13)^3:ℕ):=by
   exact_mod_cast hk
  have Cr:Real.log (2:ℝ)≤1:=by
   convert QX (show(0:ℝ)<2 by norm_num) using 1
   norm_num
  have A6:Real.log (4:ℝ)≤2:=by
   rw[show(4:ℝ)=2^2 by norm_num,QB]
   have hmul:=iO Cr
    (show(0:ℝ)≤2 by norm_num)
   norm_num at hmul ⊢
   exact hmul
  have Fd :
    Real.log (2/aR d) ≤
     (av d+1:ℝ):=by
   unfold aR
   have uV :
     2/(1/(2:ℝ)^av d) =
      (2:ℝ)^(av d+1):=by
    field_simp
    rw[RB]
    ring
   rw[uV,QB]
   push_cast
   nlinarith[iO Cr
    (show(0:ℝ)≤(av d+1:ℕ) by positivity)]
  have Pd :
    (av d+1:ℝ) ≤
     av d+13:=by norm_num
  have F0 :
    (1:ℝ)≤(av d+13)^4:=by
   have Pe:(0:ℝ)≤av d:=by positivity
   have:(1:ℝ)≤av d+13:=by nlinarith
   exact RH this
  have DD :
    0≤Real.log (2/aR d):=by
   apply Qv
   apply(Qs (bP d)).2
   nlinarith[i3 d]
  have Nr :
    (fE (aR d):ℝ) ≤
     (2^38:ℝ)*(av d+13)^3:=by
   norm_num at MO ⊢
   exact MO
  have DE :
    Real.log (2/aR d) ≤
     av d+13:=Fd.trans Pd
  have hmul :
    (fE (aR d):ℝ) *
      Real.log (2/aR d) ≤
     (2^38:ℝ)*(av d+13)^3 *
      (av d+13):=by
   exact QW Nr DE DD (by positivity)
  push_cast at ⊢
  calc
   8*(1+(Real.log 4 +
     (fE (aR d):ℝ) *
      Real.log (2/aR d))) ≤
    8*(1+(2 +
     (2^38*(av d+13)^3:ℝ) *
      (av d+13))):=by
       have oG :
         Real.log 4 +
           (fE (aR d):ℝ) *
            Real.log (2/aR d) ≤
          2+(2^38:ℝ) *
           (av d+13)^3 *
            (av d+13):=by
        linarith
       nlinarith
   _=8*(3 +
     (2^38:ℝ)*(av d+13)^4):=by ring
   _≤(2^42:ℝ)*(av d+13)^4:=by
    norm_num at ⊢
    nlinarith
   _=(4398046511104:ℝ) *
     (av d+13)^4:=by norm_num
lemma jB (d:ℕ) :
  au d ≤
   aH*(d+1)^8:=by
 have hE:=gU d
 have MP:1≤(d+1)^2:=by
  exact RH (by omega)
 have Go :
   av d+13≤1720335*(d+1)^2:=by
  nlinarith
 calc
  au d ≤
    2^42*(av d+13)^4 :=
   kc d
  _≤2^42*(1720335*(d+1)^2)^4:=by
   gcongr
  _=aH*(d+1)^8:=by
   unfold aH
   ring
lemma fe (d:ℕ) :
  ar.ax d (au d) ≤
   (1024*aH)*(d+1)^9:=by
 unfold ar.ax
 calc
  1024*(d+1)*au d ≤
    1024*(d+1) *
     (aH*(d+1)^8):=by
   gcongr
   exact jB d
  _=(1024*aH)*(d+1)^9:=by
   ring
lemma ff:Real.log (2:ℝ)≤1:=by
 have h :=
  QX (show(0:ℝ)<2 by norm_num)
 norm_num at h ⊢
 exact h
lemma cV {n:ℕ} (hn:0<n) :
  Real.log (n:ℝ)≤n:=by
 have h:=QX
  (show(0:ℝ)<n by exact_mod_cast hn)
 nlinarith
lemma p8 (d:ℕ) :
  Real.log (bE d:ℝ) ≤
   (av d+13:ℝ):=by
 rw[tf]
 push_cast
 rw[show(8192:ℝ)=2^13 by norm_num, ←RL,
  QB]
 push_cast
 have uc:(0:ℝ)≤13+av d:=by positivity
 nlinarith[iO ff uc]
lemma o4 (d:ℕ) :
  Real.log (bE d:ℝ) ≤
   1720335*((d+1:ℕ):ℝ)^2:=by
 have hE:=gU d
 have MP:1≤(d+1)^2:=by
  exact RH (by omega)
 have Go :
   av d+13≤1720335*(d+1)^2:=by
  nlinarith
 calc
  Real.log (bE d:ℝ) ≤
    (av d+13:ℝ) :=
   p8 d
  _≤1720335*((d+1:ℕ):ℝ)^2:=by
   exact_mod_cast Go
lemma o5 (d:ℕ) :
  Real.log (au d:ℝ) ≤
   42+4*(av d+13:ℝ):=by
 have ym:=kc d
 have Kw :
   (au d:ℝ) ≤
    ((2^42*(av d+13)^4:ℕ):ℝ):=by
  exact_mod_cast ym
 have wm:(0:ℝ)<au d:=by
  exact_mod_cast bX d
 have eu :
   Real.log (au d:ℝ) ≤
    Real.log ((2^42*(av d+13)^4:ℕ):ℝ) :=
  QG wm Kw
 have Gq :
   Real.log ((2^42*(av d+13)^4:ℕ):ℝ) =
    42*Real.log 2 +
     4*Real.log ((av d+13:ℕ):ℝ):=by
  push_cast
  rw[show(4398046511104:ℝ)=(2:ℝ)^42 by norm_num]
  rw[Ql (Rg _ (by norm_num))
   (Rg _ (by positivity)),
   QB,QB]
  push_cast
  ring
 have Ip:0<av d+13:=by positivity
 have Iq :
   Real.log ((av d+13:ℕ):ℝ) ≤
    (av d+13:ℕ) :=
  cV Ip
 rw[Gq] at eu
 have MQ:42*Real.log (2:ℝ)≤42:=by
  nlinarith[iO ff
   (show(0:ℝ)≤42 by norm_num)]
 have Gr:=iO Iq
  (show(0:ℝ)≤4 by norm_num)
 push_cast at eu Gr
 nlinarith
lemma fM (d:ℕ) :
  Real.log (au d:ℝ) ≤
   6881382*((d+1:ℕ):ℝ)^2:=by
 have hE:=gU d
 have MP:1≤(d+1)^2:=by
  exact RH (by omega)
 have Ir :
   42+4*(av d+13) ≤
    6881382*(d+1)^2:=by
  nlinarith
 calc
  Real.log (au d:ℝ) ≤
    42+4*(av d+13:ℝ) :=
   o5 d
  _≤6881382*((d+1:ℕ):ℝ)^2:=by
   exact_mod_cast Ir
lemma p9
  {R:ℕ} (hR:0<R) :
  Real.log ((8*R+1:ℕ):ℝ) ≤
   9+Real.log (R:ℝ):=by
 have L8:1≤R:=Nat.one_le_iff_ne_zero.mpr hR.ne'
 have sB:8*R+1≤9*R:=by omega
 have zc:(0:ℝ)<((8*R+1:ℕ):ℝ):=by
  exact_mod_cast(show 0<8*R+1 by positivity)
 have kR:(0:ℝ)<R:=by exact_mod_cast hR
 have eu :
   Real.log ((8*R+1:ℕ):ℝ) ≤
    Real.log ((9*R:ℕ):ℝ) :=
  QG zc (by exact_mod_cast sB)
 have tb :
   Real.log ((9*R:ℕ):ℝ) =
    Real.log 9+Real.log (R:ℝ):=by
  push_cast
  rw[Ql (by norm_num) kR.ne']
 rw[tb] at eu
 have h9:Real.log (9:ℝ)≤9 :=
  cV (by norm_num)
 nlinarith
lemma m2 (d:ℕ) :
  Real.log
    ((bE d*(8*au d+1:ℕ):ℕ):ℝ) ≤
   8601726*((d+1:ℕ):ℝ)^2:=by
 have Hj:0<bE d:=by
  unfold bE
  exact gV (bP d)
 have kR:=bX d
 have Kx:(0:ℝ)<bE d:=by exact_mod_cast Hj
 have Fe:(0:ℝ)<8*au d+1:=by positivity
 have L9:= o4 d
 have Gs:=p9 kR
 have wO:=fM d
 have o6:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tg:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 push_cast
 rw[Ql Kx.ne' Fe.ne']
 push_cast at L9 wO o6 Gs
 nlinarith
lemma eG (d:ℕ) :
  Real.log
    (ar.ax d (au d):ℝ) ≤
   6881393*((d+1:ℕ):ℝ)^2:=by
 have Gt:=bX d
 have wm:(0:ℝ)<au d:=by
  exact_mod_cast Gt
 have hdPos:0<d+1:=by omega
 have Ff:(0:ℝ)<d+1:=by exact_mod_cast hdPos
 have Ma:Real.log ((d+1:ℕ):ℝ)≤(d+1:ℕ) :=
  cV hdPos
 have Gu:=fM d
 have Ns:((d+1:ℕ):ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tg:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 unfold ar.ax
 push_cast
 rw[Ql
   (Rl (by norm_num) Ff.ne') wm.ne',
  Ql (by norm_num) Ff.ne']
 have Nt:Real.log (1024:ℝ)≤10:=by
  rw[show(1024:ℝ)=2^10 by norm_num,QB]
  push_cast
  nlinarith[iO ff
   (show(0:ℝ)≤10 by norm_num)]
 push_cast at Ma Gu Ns ⊢
 have o6:(1:ℝ)≤(↑d+1)^2:=by
  nlinarith
 nlinarith
lemma qa (d:ℕ) :
  Real.log
    (ar.bn d (au d):ℝ) ≤
   7700594*((d+1:ℕ):ℝ)^2:=by
 have hR:=eG d
 have hconst:Real.log (819200:ℝ)≤819200 :=
  cV (by norm_num)
 have hpow:(d:ℝ)*Real.log 2≤d:=by
  nlinarith[iO ff
   (show(0:ℝ)≤d by positivity)]
 have o6:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tg:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have Gv:(d:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have hd:(d:ℝ)≤d+1:=by norm_num
  push_cast at o6 ⊢
  nlinarith
 have kR:0<ar.ax d (au d) :=
  ar.iK (bX d)
 have wq:(0:ℝ) <
   ar.ax d (au d):=by
  exact_mod_cast kR
 unfold ar.bn
 push_cast
 rw[Ql (Rl (by norm_num) wq.ne')
   (Rg _ (by norm_num)),
  Ql (by norm_num) wq.ne',QB]
 push_cast at hR hpow Gv ⊢
 nlinarith
lemma qb (d:ℕ) :
  Real.log
    (ar.bd d (au d):ℝ) ≤
   6958194*((d+1:ℕ):ℝ)^2:=by
 have hR:=eG d
 have hconst:Real.log (76800:ℝ)≤76800 :=
  cV (by norm_num)
 have hpow:((d+1:ℕ):ℝ)*Real.log 2≤d+1:=by
  have hmul:=iO ff
   (show(0:ℝ)≤((d+1:ℕ):ℝ) by positivity)
  norm_num at hmul ⊢
  exact hmul
 have o6:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tg:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have Gv:((d+1:ℕ):ℝ) ≤
   ((d+1:ℕ):ℝ)^2:=by
  have tg:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have kR:0<ar.ax d (au d) :=
  ar.iK (bX d)
 have wq:(0:ℝ) <
   ar.ax d (au d):=by
  exact_mod_cast kR
 unfold ar.bd
 push_cast
 rw[Ql (Rl (by norm_num) wq.ne')
   (Rg _ (by norm_num)),
  Ql (by norm_num) wq.ne',QB]
 push_cast at hR hpow Gv ⊢
 nlinarith
lemma kS
  (d ax:ℕ) (u8:0<ax) {LR:ℝ}
  (KV:Real.log (ax:ℝ)≤LR) :
  Real.log
    ((8388608*max ax 1 *
     2^av d:ℕ):ℝ) ≤
   23+LR+av d:=by
 have lE:max ax 1=ax :=
  max_eq_left (Nat.one_le_iff_ne_zero.mpr u8.ne')
 rw[lE]
 have zv:(0:ℝ)<ax:=by exact_mod_cast u8
 have MR:Real.log (8388608:ℝ)≤23:=by
  rw[show(8388608:ℝ)=2^23 by norm_num,QB]
  push_cast
  nlinarith[iO ff
   (show(0:ℝ)≤23 by norm_num)]
 have NW :
   (av d:ℝ)*Real.log 2 ≤
    av d:=by
  nlinarith[iO ff
   (show(0:ℝ)≤av d by positivity)]
 push_cast
 rw[Ql
   (Rl (by norm_num) zv.ne')
   (Rg _ (by norm_num)),
  Ql (by norm_num) zv.ne',QB]
 nlinarith
lemma m3 (d:ℕ) :
  (2/(bE d:ℝ)) *
    Real.sqrt (2/aR d)≤1/2048:=by
 unfold bE
 exact qM
  (bP d) (dZ d)
lemma pw (d:ℕ) :
  (2*(1/2:ℝ)^b1 d) *
    Real.sqrt (2/aR d)≤1/2048:=by
 unfold b1
 exact s6
  (bP d) (dZ d)
def dH (rank delta n:ℕ):ℕ :=
 n^delta*4^(rank+delta)
def cL (d:ℕ):ℕ :=
 dH
  (ar.ax d (au d))
  (au d)
  (bE d*(8*au d+1))
def eW:ℕ :=
 aH*8601726 +
  2*(1024*aH +
   aH)
def bG (rank m:ℕ):ℕ :=
 (3*m)^rank*4^rank
def bT (rank bn bd:ℕ):ℕ :=
 bG rank bn*bG rank bd
def bR (rank:ℕ):ℕ :=
 bG rank (1600*max rank 1) *
  bG rank (200*max rank 1) *
   bG rank (200*max rank 1)
def cd (d ax:ℕ):ℕ :=
 8388608*max ax 1*2^av d
lemma vB
  {rank delta n R D N:ℕ}
  (hn:0<n) (Hk:n≤N)
  (cK:rank≤R) (cu:delta≤D) :
  dH rank delta n≤dH R D N:=by
 unfold dH
 have hN:0<N:=hn.trans_le Hk
 have jw:n^delta≤N^D:=by
  calc
   n^delta≤N^delta:=R4 Hk _
   _≤N^D:=QR hN cu
 have ud:4^(rank+delta)≤4^(R+D):=by
  apply QR (by norm_num)
  exact Nat.add_le_add cK cu
 exact Ra jw ud
lemma o7 (R:ℕ) :
  ⌈8*(R:ℝ)⌉₊+1=8*R+1:=by
 rw[show 8*(R:ℝ)=((8*R:ℕ):ℝ) by
  push_cast
  ring]
 rw[Nat.ceil_natCast]
def bx (rank d4 m:ℕ):ℕ :=
 200*max rank 1*(2*d4+1)*m
lemma kd {rank d4 m:ℕ} (hm:0< m) :
  0<bx rank d4 m:=by
 unfold bx
 positivity
lemma uC {rank d4 m:ℕ} (hm:0< m) :
  Real.log (bx rank d4 m:ℝ) =
   Real.log 200+Real.log ((max rank 1:ℕ):ℝ) +
    Real.log ((2*d4+1:ℕ):ℝ)+Real.log (m:ℝ):=by
 have qA:(0:ℝ)< m:=by exact_mod_cast hm
 unfold bx
 push_cast
 rw[Ql (by positivity) qA.ne',
  Ql (by positivity) (by positivity),
  Ql (by norm_num) (by positivity)]
lemma m4
  {rank d4 m:ℕ} {LR LC LM:ℝ} (hm:0< m)
  (PG:Real.log ((max rank 1:ℕ):ℝ)≤LR)
  (PN:Real.log ((2*d4+1:ℕ):ℝ)≤LC)
  (hM:Real.log (m:ℝ)≤LM) :
  Real.log (bx rank d4 m:ℝ) ≤
   200+LR+LC+LM:=by
 rw[uC hm]
 have DF:Real.log (200:ℝ)≤200 :=
  cV (by norm_num)
 nlinarith
lemma kv
  {rank ax:ℕ} (u8:0<ax) (cK:rank≤ax) :
  Real.log ((max rank 1:ℕ):ℝ)≤Real.log (ax:ℝ):=by
 have lE:max rank 1≤ax :=
  max_le cK (Nat.one_le_iff_ne_zero.mpr u8.ne')
 have wP:(0:ℝ)< max rank 1:=by positivity
 exact QG wP (by exact_mod_cast lE)
lemma ke
  {d4 R:ℕ} (hR:0<R) (o8:d4≤8*R) :
  Real.log ((2*d4+1:ℕ):ℝ) ≤
   17+Real.log (R:ℝ):=by
 have L8:1≤R:=Nat.one_le_iff_ne_zero.mpr hR.ne'
 have sB:2*d4+1≤17*R:=by
  nlinarith
 have zc:(0:ℝ)<((2*d4+1:ℕ):ℝ):=by
  exact_mod_cast(show 0<2*d4+1 by positivity)
 have kR:(0:ℝ)<R:=by exact_mod_cast hR
 have eu :
   Real.log ((2*d4+1:ℕ):ℝ) ≤
    Real.log ((17*R:ℕ):ℝ) :=
  QG zc (by exact_mod_cast sB)
 have tb :
   Real.log ((17*R:ℕ):ℝ) =
    Real.log 17+Real.log (R:ℝ):=by
  push_cast
  rw[Ql (by norm_num) kR.ne']
 rw[tb] at eu
 have P5:Real.log (17:ℝ)≤17 :=
  cV (by norm_num)
 nlinarith
lemma iR
  (d rank d4:ℕ)
  (cK:rank ≤
   ar.ax d (au d))
  (o8:d4≤8*au d) :
  Real.log
    (bx rank d4
     (8388608 *
      max (ar.ax d (au d)) 1 *
       2^av d):ℝ) ≤
   22364730*((d+1:ℕ):ℝ)^2:=by
 let R:=ar.ax d (au d)
 let m:=8388608*max R 1*2^av d
 have kR:0<R:=by
  unfold R
  exact ar.iK (bX d)
 have hm:0< m:=by
  unfold m
  positivity
 have wO:Real.log (R:ℝ) ≤
   6881393*((d+1:ℕ):ℝ)^2:=by
  simpa[R] using eG d
 have Gw:Real.log ((max rank 1:ℕ):ℝ) ≤
   6881393*((d+1:ℕ):ℝ)^2 :=
  (kv kR (by simpa[R] using cK)).trans wO
 have It:Real.log ((2*d4+1:ℕ):ℝ) ≤
   17+6881382*((d+1:ℕ):ℝ)^2:=by
  calc
   Real.log ((2*d4+1:ℕ):ℝ) ≤
     17+Real.log (au d:ℝ) :=
    ke
     (bX d) o8
   _≤17+6881382*((d+1:ℕ):ℝ)^2:=by
    gcongr
    exact fM d
 have Mb:Real.log (m:ℝ) ≤
   23+8601715*((d+1:ℕ):ℝ)^2:=by
  have pV:=kS d R kR wO
  have hE:=gU d
  have P6:(av d:ℝ) ≤
    1720322*((d+1:ℕ):ℝ)^2:=by
   exact_mod_cast hE
  unfold m
  nlinarith
 have gL:=m4
  (rank:=rank) (d4:=d4) (m:=m) hm Gw It Mb
 have o6:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tg:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 simpa[m,R] using(by nlinarith :
  Real.log (bx rank d4 m:ℝ) ≤
   22364730*((d+1:ℕ):ℝ)^2)
lemma jS
  (d rank d4:ℕ)
  (cK:rank ≤
   ar.ax d (au d))
  (o8:d4≤8*au d) :
  Real.log
    (((3*bx rank d4
     (cd d
      (ar.ax d (au d))))^rank:ℕ):ℝ) ≤
   (1024*aH*22364733:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
 let R:=ar.ax d (au d)
 let m:=cd d R
 let P:=bx rank d4 m
 have hm:0< m:=by
  unfold m cd
  positivity
 have hP:0<P:=by
  unfold P
  exact kd hm
 have PH:Real.log (P:ℝ) ≤
   22364730*((d+1:ℕ):ℝ)^2:=by
  simpa[P,m,R,cd] using
   iR d rank d4 cK o8
 have Pf:Real.log ((3*P:ℕ):ℝ) ≤
   3+22364730*((d+1:ℕ):ℝ)^2:=by
  have Pg:(0:ℝ)<P:=by exact_mod_cast hP
  have h3:Real.log (3:ℝ)≤3 :=
   cV (by norm_num)
  rw[show((3*P:ℕ):ℝ)=(3:ℝ)*(P:ℝ) by norm_num]
  rw[Ql (by norm_num) Pg.ne']
  nlinarith
 have o6:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tg:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have n6:Real.log ((3*P:ℕ):ℝ) ≤
   22364733*((d+1:ℕ):ℝ)^2:=by
  nlinarith
 have sM:(rank:ℝ) ≤
   (1024*aH:ℕ) *
    ((d+1:ℕ):ℝ)^9:=by
  calc
   (rank:ℝ)≤(R:ℝ):=by exact_mod_cast(by simpa[R] using cK)
   _≤(1024*aH:ℕ) *
     ((d+1:ℕ):ℝ)^9:=by
    simpa[R] using(show
     (ar.ax d (au d):ℝ) ≤
      (1024*aH:ℕ) *
       ((d+1:ℕ):ℝ)^9 by
     exact_mod_cast fe d)
 have zU:0≤Real.log ((3*P:ℕ):ℝ):=by
  apply Qv
  exact_mod_cast(show 1≤3*P by omega)
 have hmul:=QW sM n6 zU (by positivity)
 push_cast
 rw[QB]
 push_cast at hmul ⊢
 nlinarith
lemma i4
  {G:Type*} [AddCommGroup G] [Fintype G]
  (B:aj G) (T:Finset G) (eta:ℝ) (m:ℕ)
  (hm:0< m) (a8:NNReal) (jL:1/2≤a8) :
  ((bx B.rank
    (aI.dg B T eta) m:NNReal)⁻¹) ≤
   a8*aI.cJ B T eta *
    (m:NNReal)⁻¹ :=by
 classical
 unfold bx aI.cJ
 have cK:(0:NNReal)< max B.rank 1:=by positivity
 have o8:(0:NNReal) <
   (2*aI.dg B T eta+1:ℕ):=by
  positivity
 have w3:(0:NNReal)< m:=by exact_mod_cast hm
 have hmul :
   (200*(max B.rank 1:NNReal) *
     (2*aI.dg B T eta+1:ℕ) *
     (m:NNReal))*(1/2) ≤
    (200*(max B.rank 1:NNReal) *
     (2*aI.dg B T eta+1:ℕ) *
     (m:NNReal))*a8:=by
  exact iO jL (by positivity)
 field_simp
 norm_num at hmul ⊢
 convert hmul using 1; ring
lemma f5
  {G:Type*} [AddCommGroup G] [Fintype G]
  (B:aj G) (P:ℕ) (hP:0<P) {a8:NNReal}
  (jL:((P:NNReal)⁻¹)≤a8) :
  B.Zc.card ≤
   (3*P)^B.rank*(B.ai a8).Zc.card:=by
 classical
 have dc :=
  aj.cM B 1 hP
 have xS :
   (B.ai ((P:NNReal)⁻¹)).Zc.card ≤
    (B.ai a8).Zc.card :=
  Qu (aj.b5 jL)
 calc
  B.Zc.card=(B.ai 1).Zc.card:=by simp
  _≤(3*P)^B.rank *
    (B.ai ((P:NNReal)⁻¹)).Zc.card:=by
     simpa[Qw] using dc
  _≤(3*P)^B.rank*(B.ai a8).Zc.card :=
   Qr _ xS
lemma wt
  {rank delta n:ℕ} (hn:0<n) :
  Real.log (dH rank delta n:ℝ) =
   (delta:ℝ)*Real.log (n:ℝ) +
    (rank+delta:ℝ)*Real.log 4:=by
 have Kd:(0:ℝ)<n:=by exact_mod_cast hn
 unfold dH
 push_cast
 rw[Ql (Rg _ Kd.ne') (Rg _ (by norm_num)),
  QB,QB]
 push_cast
 ring
lemma ck {rank m:ℕ} (hm:0< m) :
  0<bG rank m:=by
 unfold bG
 positivity
lemma f0 {rank m:ℕ} (hm:0< m) :
  Real.log (bG rank m:ℝ) =
   (rank:ℝ) *
    (Real.log ((3*m:ℕ):ℝ)+Real.log 4):=by
 have qA:(0:ℝ)< m:=by exact_mod_cast hm
 unfold bG
 push_cast
 rw[Ql (Rg _ (Rl (by norm_num) qA.ne'))
   (Rg _ (by norm_num)),QB,QB]
 ring
lemma qc {rank bn bd:ℕ}
  (eH:0<bn) (fw:0<bd) :
  Real.log (bT rank bn bd:ℝ) =
   (rank:ℝ) *
    (Real.log ((3*bn:ℕ):ℝ)+Real.log 4) +
   (rank:ℝ) *
    (Real.log ((3*bd:ℕ):ℝ)+Real.log 4):=by
 unfold bT
 push_cast
 rw[Ql
   (by exact_mod_cast(ck eH).ne')
   (by exact_mod_cast(ck fw).ne'),
  f0 eH,f0 fw]
 push_cast
 ring
lemma nB (rank:ℕ) :
  Real.log (bR rank:ℝ) =
   (rank:ℝ) *
     (Real.log ((3*(1600*max rank 1):ℕ):ℝ) +
      Real.log 4) +
    (rank:ℝ) *
     (Real.log ((3*(200*max rank 1):ℕ):ℝ) +
      Real.log 4) +
    (rank:ℝ) *
     (Real.log ((3*(200*max rank 1):ℕ):ℝ) +
      Real.log 4):=by
 have lE:0< max rank 1:=by positivity
 have DG:0<1600*max rank 1:=by positivity
 have DF:0<200*max rank 1:=by positivity
 have uJ :
   ((bG rank (1600*max rank 1):ℕ):ℝ)≠0:=by
  exact_mod_cast(ck DG).ne'
 have Gx :
   ((bG rank (200*max rank 1):ℕ):ℝ)≠0:=by
  exact_mod_cast(ck DF).ne'
 unfold bR
 push_cast
 rw[Ql
   (Rl uJ Gx) Gx,
  Ql uJ Gx,
  f0 DG,
  f0 DF]
 push_cast
 ring
lemma fI
  {m:ℕ} {L:ℝ} (hm:0< m)
  (eu:Real.log (m:ℝ)≤L) :
  Real.log ((3*m:ℕ):ℝ)≤3+L:=by
 have qA:(0:ℝ)< m:=by exact_mod_cast hm
 have h3:Real.log (3:ℝ)≤3 :=
  cV (by norm_num)
 push_cast
 rw[Ql (by norm_num) qA.ne']
 nlinarith
lemma lP:Real.log (4:ℝ)≤2:=by
 rw[show(4:ℝ)=2^2 by norm_num,QB]
 have hmul:=iO ff
  (show(0:ℝ)≤2 by norm_num)
 norm_num at hmul ⊢
 exact hmul
lemma ia
  (d rank:ℕ)
  (cK:rank ≤
   ar.ax d (au d)) :
  Real.log
    (bT rank
     (ar.bn d (au d))
     (ar.bd d (au d)):ℝ) ≤
   (1024*aH*14658798:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
 let bn:=ar.bn d (au d)
 let bd:=ar.bd d (au d)
 have eH:0<bn:=by
  unfold bn
  exact ar.me (bX d)
 have fw:0<bd:=by
  unfold bd
  exact ar.mf (bX d)
 have Gy:Real.log (bn:ℝ) ≤
   7700594*((d+1:ℕ):ℝ)^2:=by
  simpa[bn] using qa d
 have Gz:Real.log (bd:ℝ) ≤
   6958194*((d+1:ℕ):ℝ)^2:=by
  simpa[bd] using qb d
 have Nu:=fI eH Gy
 have Nv:=fI fw Gz
 have o6:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tg:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have DH :
   Real.log ((3*bn:ℕ):ℝ)+Real.log 4 ≤
    7700599*((d+1:ℕ):ℝ)^2:=by
  nlinarith[lP]
 have DI :
   Real.log ((3*bd:ℕ):ℝ)+Real.log 4 ≤
    6958199*((d+1:ℕ):ℝ)^2:=by
  nlinarith[lP]
 have sM:(rank:ℝ) ≤
   (1024*aH:ℕ) *
    ((d+1:ℕ):ℝ)^9:=by
  calc
   (rank:ℝ) ≤
     (ar.ax d (au d):ℝ):=by
    exact_mod_cast cK
   _≤(1024*aH:ℕ) *
     ((d+1:ℕ):ℝ)^9:=by
    exact_mod_cast fe d
 have xF :
   0≤Real.log ((3*bn:ℕ):ℝ)+Real.log 4:=by
  have h3:(1:ℝ)≤(3*bn:ℕ):=by
   exact_mod_cast(show 1≤3*bn by omega)
  nlinarith[Qv h3,Qv (show(1:ℝ)≤4 by norm_num)]
 have xG :
   0≤Real.log ((3*bd:ℕ):ℝ)+Real.log 4:=by
  have h3:(1:ℝ)≤(3*bd:ℕ):=by
   exact_mod_cast(show 1≤3*bd by omega)
  nlinarith[Qv h3,Qv (show(1:ℝ)≤4 by norm_num)]
 rw[qc eH fw]
 have GA:=QW sM DH xF (by positivity)
 have GB:=QW sM DI xG (by positivity)
 push_cast at GA GB ⊢
 nlinarith
lemma gD
  (d rank:ℕ)
  (cK:rank ≤
   ar.ax d (au d)) :
  Real.log (bR rank:ℝ) ≤
   (1024*aH*20646194:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
 let R:=ar.ax d (au d)
 have kR:0<R:=by
  unfold R
  exact ar.iK (bX d)
 have wO:Real.log (R:ℝ) ≤
   6881393*((d+1:ℕ):ℝ)^2:=by
  simpa[R] using eG d
 have NX:Real.log ((max rank 1:ℕ):ℝ) ≤
   6881393*((d+1:ℕ):ℝ)^2 :=
  (kv kR (by simpa[R] using cK)).trans wO
 have wP:0< max rank 1:=by positivity
 have A7:(0:ℝ)< max rank 1:=by exact_mod_cast wP
 have o6:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tg:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have Iu :
   Real.log ((1600*max rank 1:ℕ):ℝ) ≤
    1600+6881393*((d+1:ℕ):ℝ)^2:=by
  rw[show((1600*max rank 1:ℕ):ℝ) =
    (1600:ℝ)*((max rank 1:ℕ):ℝ) by norm_num]
  rw[Ql (by norm_num) A7.ne']
  have DG:Real.log (1600:ℝ)≤1600 :=
   cV (by norm_num)
  nlinarith
 have Fh :
   Real.log ((200*max rank 1:ℕ):ℝ) ≤
    200+6881393*((d+1:ℕ):ℝ)^2:=by
  rw[show((200*max rank 1:ℕ):ℝ) =
    (200:ℝ)*((max rank 1:ℕ):ℝ) by norm_num]
  rw[Ql (by norm_num) A7.ne']
  have DF:Real.log (200:ℝ)≤200 :=
   cV (by norm_num)
  nlinarith
 have Iv:0<1600*max rank 1:=by positivity
 have Fi:0<200*max rank 1:=by positivity
 have Nw:=fI Iv Iu
 have Mc:=fI Fi Fh
 have DJ :
   Real.log ((3*(1600*max rank 1):ℕ):ℝ)+Real.log 4 ≤
    6882998*((d+1:ℕ):ℝ)^2:=by
  nlinarith[lP]
 have A8 :
   Real.log ((3*(200*max rank 1):ℕ):ℝ)+Real.log 4 ≤
    6881598*((d+1:ℕ):ℝ)^2:=by
  nlinarith[lP]
 have sM:(rank:ℝ) ≤
   (1024*aH:ℕ) *
    ((d+1:ℕ):ℝ)^9:=by
  calc
   (rank:ℝ)≤(R:ℝ):=by exact_mod_cast(by simpa[R] using cK)
   _≤(1024*aH:ℕ) *
     ((d+1:ℕ):ℝ)^9:=by
    simpa[R] using(show
     (ar.ax d (au d):ℝ) ≤
      (1024*aH:ℕ) *
       ((d+1:ℕ):ℝ)^9 by
     exact_mod_cast fe d)
 have xH :
   0≤Real.log ((3*(1600*max rank 1):ℕ):ℝ)+Real.log 4:=by
  have h3:(1:ℝ)≤(3*(1600*max rank 1):ℕ):=by
   exact_mod_cast(show 1≤3*(1600*max rank 1) by omega)
  nlinarith[Qv h3,Qv (show(1:ℝ)≤4 by norm_num)]
 have wu :
   0≤Real.log ((3*(200*max rank 1):ℕ):ℝ)+Real.log 4:=by
  have h3:(1:ℝ)≤(3*(200*max rank 1):ℕ):=by
   exact_mod_cast(show 1≤3*(200*max rank 1) by omega)
  nlinarith[Qv h3,Qv (show(1:ℝ)≤4 by norm_num)]
 rw[nB]
 have GC:=QW sM DJ xH (by positivity)
 have DK:=QW sM A8 wu (by positivity)
 push_cast at GC DK ⊢
 nlinarith
def cv (d rank d4:ℕ):ℕ :=
 bT rank
   (ar.bn d (au d))
   (ar.bd d (au d)) *
  bR rank *
   (3*bx rank d4
    (cd d
     (ar.ax d (au d))))^rank *
    cL d
def cW:ℕ :=
 1024*aH*57669725 +
  eW
lemma lF (d:ℕ) :
  Real.log (cL d:ℝ) ≤
   (eW:ℝ) *
    ((d+1:ℕ):ℝ)^10:=by
 let R:=ar.ax d (au d)
 let delta:=au d
 let n:=bE d*(8*au d+1)
 have Hj:0<bE d:=by
  unfold bE
  exact gV (bP d)
 have MS:0<delta:=by
  simpa[delta] using bX d
 have hn:0<n:=by
  unfold n
  positivity
 have Md:Real.log (n:ℝ) ≤
   8601726*((d+1:ℕ):ℝ)^2:=by
  simpa[n] using m2 d
 have BZ:0≤Real.log (n:ℝ):=by
  apply Qv
  exact_mod_cast(show 1≤n by exact Nat.one_le_iff_ne_zero.mpr hn.ne')
 have cu:(delta:ℝ) ≤
   (aH:ℝ) *
    ((d+1:ℕ):ℝ)^8:=by
  unfold delta
  exact_mod_cast jB d
 have hR:(R:ℝ) ≤
   (1024*aH:ℕ) *
    ((d+1:ℕ):ℝ)^9:=by
  unfold R
  exact_mod_cast fe d
 have hx:(1:ℝ)≤((d+1:ℕ):ℝ):=by
  exact_mod_cast(show 1≤d+1 by omega)
 have PI:((d+1:ℕ):ℝ)^8 ≤
   ((d+1:ℕ):ℝ)^10 :=
  Se hx (by omega)
 have PJ:((d+1:ℕ):ℝ)^9 ≤
   ((d+1:ℕ):ℝ)^10 :=
  Se hx (by omega)
 have jw :
   (delta:ℝ)*Real.log (n:ℝ) ≤
    ((aH:ℝ)*8601726) *
     ((d+1:ℕ):ℝ)^10:=by
  calc
   (delta:ℝ)*Real.log (n:ℝ) ≤
     ((aH:ℝ) *
      ((d+1:ℕ):ℝ)^8) *
      (8601726*((d+1:ℕ):ℝ)^2) :=
    QW cu Md BZ (by positivity)
   _=((aH:ℝ)*8601726) *
     ((d+1:ℕ):ℝ)^10:=by ring
 have Ky:(R+delta:ℝ) ≤
   (1024*aH +
    aH:ℕ) *
     ((d+1:ℕ):ℝ)^10:=by
  calc
   (R:ℝ)+delta ≤
     ((1024*aH:ℕ):ℝ) *
       ((d+1:ℕ):ℝ)^9 +
      aH *
       ((d+1:ℕ):ℝ)^8:=Sr hR cu
   _≤((1024*aH:ℕ):ℝ) *
       ((d+1:ℕ):ℝ)^10 +
      aH *
       ((d+1:ℕ):ℝ)^10:=by
    gcongr
   _=((1024*aH +
      aH:ℕ):ℝ) *
     ((d+1:ℕ):ℝ)^10:=by
    push_cast
    ring
 have A6:Real.log (4:ℝ)≤2:=by
  rw[show(4:ℝ)=2^2 by norm_num,QB]
  have hmul:=iO ff
   (show(0:ℝ)≤2 by norm_num)
  norm_num at hmul ⊢
  exact hmul
 have zd:0≤Real.log (4:ℝ) :=
  Qv (by norm_num)
 have ud :
   (R+delta:ℝ)*Real.log 4 ≤
    (2:ℝ) *
     (1024*aH +
      aH) *
     ((d+1:ℕ):ℝ)^10:=by
  calc
   (R+delta:ℝ)*Real.log 4 ≤
     ((1024*aH +
      aH:ℕ):ℝ) *
      ((d+1:ℕ):ℝ)^10*2 :=
    QW Ky A6 zd (by positivity)
   _=(2:ℝ) *
     (1024*aH +
      aH) *
     ((d+1:ℕ):ℝ)^10:=by
    push_cast
    ring
 unfold cL
 change Real.log (dH R delta n:ℝ)≤_
 rw[wt hn]
 unfold eW
 push_cast at jw ud ⊢
 nlinarith
lemma jW
  (d rank d4:ℕ)
  (cK:rank ≤
   ar.ax d (au d))
  (o8:d4≤8*au d) :
  Real.log (cv d rank d4:ℝ) ≤
   (cW:ℝ) *
    ((d+1:ℕ):ℝ)^11:=by
 let two:=bT rank
  (ar.bn d (au d))
  (ar.bd d (au d))
 let smooth:=bR rank
 let source :=
  (3*bx rank d4
   (cd d
    (ar.ax d (au d))))^rank
 let cell:=cL d
 have u9:Real.log (two:ℝ) ≤
   (1024*aH*14658798:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
  simpa[two] using
   ia d rank cK
 have j6:Real.log (smooth:ℝ) ≤
   (1024*aH*20646194:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
  simpa[smooth] using
   gD d rank cK
 have gL:Real.log (source:ℝ) ≤
   (1024*aH*22364733:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
  simpa[source] using
   jS d rank d4 cK o8
 have lM:Real.log (cell:ℝ) ≤
   (eW:ℝ) *
    ((d+1:ℕ):ℝ)^10:=by
  simpa[cell] using lF d
 have hx:(1:ℝ)≤((d+1:ℕ):ℝ):=by
  exact_mod_cast(show 1≤d+1 by omega)
 have Kz:((d+1:ℕ):ℝ)^10 ≤
   ((d+1:ℕ):ℝ)^11 :=
  Se hx (by omega)
 have Iw:Real.log (cell:ℝ) ≤
   (eW:ℝ) *
    ((d+1:ℕ):ℝ)^11 :=
  lM.trans (iO Kz (by positivity))
 have uD:(0:ℝ)<two:=by
  have eH:=ar.me (d:=d)
   (aq:=au d) (bX d)
  have fw:=ar.mf (d:=d)
   (aq:=au d) (bX d)
  unfold two bT
  exact_mod_cast QP
   (ck eH) (ck fw)
 have va:(0:ℝ)<smooth:=by
  unfold smooth bR bG
  positivity
 have yw:(0:ℝ)<source:=by
  unfold source bx cd
  positivity
 have GD:(0:ℝ)<cell:=by
  have hq:0<bE d:=by
   unfold bE
   exact gV (bP d)
  unfold cell cL dH
  positivity
 change Real.log ((two*smooth*source*cell:ℕ):ℝ)≤_
 push_cast
 rw[Ql
   (Rl
    (Rl uD.ne' va.ne') yw.ne')
   GD.ne',
  Ql (Rl uD.ne' va.ne') yw.ne',
  Ql uD.ne' va.ne']
 unfold cW
 push_cast at u9 j6 gL Iw ⊢
 nlinarith
end
end ay.aa
end
section
open Finset Fintype Function
open scoped BigOperators NNReal Pointwise translate
namespace ay.uE
noncomputable section
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
omit [DecidableEq G] [Fintype G] in
lemma vo
    {H:Type*} [AddCommGroup H]
    (B:aj G) (e:G ≃+ H) (a8:NNReal) :
    (B.map e).ai a8=(B.ai a8).map e:=by
  classical
  rfl
omit [DecidableEq G] in
lemma wY
  {H:Type*} [AddCommGroup H] [Fintype H]
  (B:aj G) (e:G ≃+ H) (hB:B.a1) :
  (B.map e).a1:=by
 classical
 unfold aj.a1 at hB ⊢
 simp only[aj.Ap]
 intro aF dy
 have h:=hB aF dy
 rw[vo,vo,
  aj.ky,aj.ky,
  aj.ky]
 exact h
lemma qN
  {M:ℕ} [NeZero M] (hM:Odd M) (B:aj (ZMod M))
  (hB:B.a1) :
  (aO.hU M hM B).a1:=by
 exact wY B (aj.eK M hM) hB
omit [DecidableEq G] in
lemma fW
  (B:aj G) (m:ℕ) (hm:0< m) :
  ∃ c:ah.bt (G:=G),
   c.ba.a1 ∧
   c.ba.rank=B.rank ∧
   c.outer=1 ∧
   c.Zc=c.ba.Zc ∧
   c.Zc⊆(B.ai ((m:NNReal)⁻¹)).Zc ∧
   B.Zc.card ≤
    ((3*m)^B.rank*4^B.rank)*c.Zc.card:=by
 classical
 let D:=B.ai ((m:NNReal)⁻¹)
 obtain ⟨R,qi,oP,Hb,yb⟩ :=
  ag.kt D
 obtain ⟨c,A9,_hcouter,wv⟩ :=
  ah.bt.n7 R qi
 refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_⟩
 ·simpa[A9] using qi
 ·simpa[A9,D] using oP
 ·exact _hcouter
 ·simpa[A9] using wv
 ·simpa[wv,D] using Hb
 ·have c3 :=
   aj.cM
    B 1 hm
  have uA :
    B.Zc.card ≤
     (3*m)^B.rank *
      (B.ai ((m:NNReal)⁻¹)).Zc.card:=by
   simpa[Qw] using c3
  calc
   B.Zc.card ≤
     (3*m)^B.rank *
      (B.ai ((m:NNReal)⁻¹)).Zc.card:=uA
   _≤(3*m)^B.rank*(4^B.rank*R.Zc.card):=by
    exact Qr _ (by simpa[D] using yb)
   _=((3*m)^B.rank*4^B.rank)*c.Zc.card:=by
    rw[wv]
    ring
def b9 (B:aj G) (m:ℕ):ℕ :=
 (3*m)^B.rank*4^B.rank
def bI (B:aj G) (bn bd:ℕ):ℕ :=
 b9 B bn*b9 B bd
structure c7 (B:aj G) (bn bd:ℕ) where
 ak:ah.bt (G:=G)
 aB:ah.bt (G:=G)
 ez:ak.ba.a1
 fc:aB.ba.a1
 rankOne:ak.ba.rank=B.rank
 p0:aB.ba.rank=B.rank
 fT:ak.outer=1
 g3:aB.outer=1
 eD:ak.Zc=ak.ba.Zc
 nZ:aB.Zc=aB.ba.Zc
 nS:ak.Zc⊆(B.ai ((bn:NNReal)⁻¹)).Zc
 pZ:aB.Zc⊆(B.ai ((bn:NNReal)⁻¹)).Zc
 Ba :
  aB.Zc ⊆
   (ak.ba.ai ((bd:NNReal)⁻¹)).Zc
 kT :
  aO.a4 aB.Zc ⊆
   (ak.ba.ai
    ((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹)).Zc
 mz :
  B.Zc.card ≤
   b9 B bn*ak.Zc.card
 mA :
  B.Zc.card ≤
   bI B bn bd*aB.Zc.card
lemma rO (B:aj G)
  (bn bd:ℕ) (eH:0<bn) (fw:0<bd)
  (xI:((bd:NNReal)⁻¹)≤1) :
  Nonempty (c7 B bn bd):=by
 obtain ⟨Bb,Ix,xJ,Fj,tM,zw,vb⟩ :=
  fW B bn eH
 obtain ⟨xK,Iy,Fk,Fl,B0,rY,B1⟩ :=
  fW Bb.ba bd fw
 have Fm:xK.Zc ⊆
   (B.ai ((bn:NNReal)⁻¹)).Zc:=by
  intro x hx
  apply zw
  rw[tM]
  simpa using aj.b5 xI (rY hx)
 have GF :
   aO.a4 xK.Zc ⊆
    (Bb.ba.ai
     ((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹)).Zc:=by
  intro x hx
  obtain ⟨y,hy,rfl⟩:=aO.mY.mp hx
  exact aj.e7 (rY hy) (rY hy)
 have GG:xK.ba.rank=B.rank:=Fk.trans xJ
 have xL :
   B.Zc.card ≤
    bI B bn bd*xK.Zc.card:=by
  calc
   B.Zc.card ≤
     b9 B bn*Bb.Zc.card :=
    vb
   _≤b9 B bn *
     (b9 Bb.ba bd *
      xK.Zc.card) :=
    Qr _
     (by simpa[tM,b9] using B1)
   _=bI B bn bd*xK.Zc.card:=by
    simp[b9,bI,xJ]
    ring
 exact ⟨{
  ak:=Bb
  aB:=xK
  ez:=Ix
  fc:=Iy
  rankOne:=xJ
  p0:=GG
  fT:=Fj
  g3:=Fl
  eD:=tM
  nZ:=B0
  nS:=zw
  pZ:=Fm
  Ba:=rY
  kT:=GF
  mz:=vb
  mA:=xL }⟩
structure gj {original:Finset G}
  (s:ah.aA original) (bn bd:ℕ)
  (epsilon aU:ℝ) where
 Bc:s.restriction.outer=1
 iJ:s.restriction.ba.a1
 yx :
  ((bn:NNReal)⁻¹) ≤
   1/(100*(max s.restriction.ba.rank 1:ℕ):NNReal)
 vq :
  400*((max s.restriction.ba.rank 1:ℕ):ℝ) *
    (((bn:NNReal)⁻¹ :NNReal):ℝ)≤epsilon*s.Zd/4
 th :
  Real.exp (-aU)*(s.card:ℝ) ≤
   ((b9 s.restriction.ba bn:ℕ):ℝ)⁻¹ *
    (s.restriction.ba.Zc.card:ℝ)
 ti :
  Real.exp (-aU)*(s.card:ℝ) ≤
   ((bI s.restriction.ba bn bd:ℕ):ℝ)⁻¹ *
    (s.restriction.ba.Zc.card:ℝ)
lemma mh
  {original:Finset G} (s:ah.aA original)
  {g5:ℕ} {aU:ℝ} {child:Finset G}
  (mF:(0:ℝ)<(g5:ℝ))
  (n8 :
   Real.exp (-aU)*(s.card:ℝ) ≤
    (g5:ℝ)⁻¹ *(s.restriction.ba.Zc.card:ℝ))
  (GH :
   (s.restriction.ba.Zc.card:ℝ) ≤
    (g5:ℝ)*(child.card:ℝ)) :
  Real.exp (-aU)*(s.card:ℝ)≤child.card:=by
 calc
  Real.exp (-aU)*(s.card:ℝ) ≤
    (g5:ℝ)⁻¹ *(s.restriction.ba.Zc.card:ℝ):=n8
  _≤(g5:ℝ)⁻¹ *((g5:ℝ)*(child.card:ℝ)):=by
   exact iO GH (by positivity)
  _=child.card:=by
   field_simp
lemma jk
  {original:Finset G} (s:ah.aA original)
  (ju:s.restriction.outer=1)
  {g5:ℕ} {aU:ℝ}
  (mF:(0:ℝ)<(g5:ℝ))
  (eu:Real.log (g5:ℝ)≤aU) :
  Real.exp (-aU)*(s.card:ℝ) ≤
   (g5:ℝ)⁻¹ *(s.restriction.ba.Zc.card:ℝ):=by
 have l5 :
   Real.exp (-aU)≤(g5:ℝ)⁻¹ :=by
  have eY: -aU≤ -Real.log (g5:ℝ):=TO eu
  have h:=Real.exp_le_exp.mpr eY
  calc
   Real.exp (-aU)≤Real.exp (-Real.log (g5:ℝ)):=h
   _=(g5:ℝ)⁻¹ :=by
    rw[Uh,Real.exp_log mF]
 have ch :
   (s.card:ℝ)=(s.restriction.ba.Zc.card:ℝ):=by
  unfold ah.aA.card br.aY.card
   br.aY.e8
  simp[ju]
 rw[ch]
 exact Qi l5 (by positivity)
lemma os
  {g5:ℕ} {aU:ℝ} (mF:0<g5)
  (eu:Real.log (g5:ℝ)≤aU) :
  Real.exp (-aU)*(g5:ℝ)≤1:=by
 have l5:Real.exp (-aU)≤(g5:ℝ)⁻¹ :=by
  have eY: -aU≤ -Real.log (g5:ℝ):=TO eu
  calc
   Real.exp (-aU)≤Real.exp (-Real.log (g5:ℝ)) :=
    Real.exp_le_exp.mpr eY
   _=(g5:ℝ)⁻¹ :=by
    rw[Uh,Real.exp_log (by exact_mod_cast mF)]
 calc
  Real.exp (-aU)*(g5:ℝ)≤(g5:ℝ)⁻¹ *g5:=by gcongr
  _=1:=by
   have Ph:(0:ℝ)<g5:=by exact_mod_cast mF
   field_simp
omit [Fintype G] in
lemma lG
  {A S T D:Finset G} (k:ℕ) {alpha C:ℝ}
  (b8:0≤alpha) (hC:0<C)
  (hA:A.Nonempty) (hS:S.Nonempty)
  (Cs:alpha*(D.card:ℝ)≤(A.card:ℝ))
  (hsum:((A+S).card:ℝ)≤C*(D.card:ℝ))
  (hT :
   (((A.card:ℝ)^k/2*S.card) /
     ((A+S).card:ℝ)^k≤(T.card:ℝ))) :
  (((alpha/C)^k/2)*(S.card:ℝ))≤(T.card:ℝ):=by
 have rV:(0:ℝ)<(A+S).card:=by
  exact_mod_cast(hA.add hS).card_pos
 have Iz:(0:ℝ)<((A+S).card:ℝ)^k:=by
  positivity
 apply Sj ?_ hT
 apply(Qs Iz).2
 calc
  ((alpha/C)^k/2)*(S.card:ℝ) *
    ((A+S).card:ℝ)^k ≤
   ((alpha/C)^k/2)*(S.card:ℝ) *
    (C*(D.card:ℝ))^k:=by
     gcongr
  _=(alpha*(D.card:ℝ))^k/2*S.card:=by
     have PO:C≠0:=hC.ne'
     rw[QL]
     field_simp
     have IA:alpha/C*C=alpha:=by field_simp
     rw[←QL (alpha/C) C,IA, ←QL]
  _≤(A.card:ℝ)^k/2*S.card:=by
     gcongr
lemma nC
  (B:aj G) (A S:Finset G) {a8:NNReal}
  (hA:A⊆B.Zc)
  (hS:S⊆(B.ai a8).Zc) :
  (-A)+S⊆(B.ai (1+a8)).Zc:=by
 intro x hx
 obtain ⟨u,hu,v,hv,rfl⟩:=Finset.mem_add.mp hx
 obtain ⟨a,ha,rfl⟩:=Finset.mem_neg.mp hu
 exact aj.e7
  (by simpa using(aj.ec.mpr (hA ha))) (hS hv)
lemma ij
  (B:aj G) (rE:B.a1)
  (A S:Finset G) {a8:NNReal}
  (hA:A⊆B.Zc)
  (hS:S⊆(B.ai a8).Zc)
  (jL :
   a8≤1/(100*(max B.rank 1:ℕ):NNReal)) :
  (-A+S).card≤2*B.Zc.card:=by
 have l0:=nC B A S hA hS
 have ch :
   ((B.ai (1+a8)).Zc.card:ℝ) ≤
    (1+100*((max B.rank 1:ℕ):ℝ)*(a8:ℝ)) *
     (B.Zc.card:ℝ) :=
  (rE a8 jL).2
 have qI :
   1+100*((max B.rank 1:ℕ):ℝ)*(a8:ℝ)≤2:=by
  have Nx :
    (a8:ℝ) ≤
     1/(100*((max B.rank 1:ℕ):ℝ)):=by
   exact_mod_cast jL
  have Ny:(0:ℝ)<(max B.rank 1:ℕ):=by positivity
  have hmul :
    100*((max B.rank 1:ℕ):ℝ)*(a8:ℝ)≤1:=by
   calc
    100*((max B.rank 1:ℕ):ℝ)*(a8:ℝ) ≤
      100*((max B.rank 1:ℕ):ℝ) *
       (1/(100*((max B.rank 1:ℕ):ℝ))):=by
        gcongr
    _=1:=by field_simp
  nlinarith
 have KA :
   ((B.ai (1+a8)).Zc.card:ℝ) ≤
    2*(B.Zc.card:ℝ):=by
  calc
   ((B.ai (1+a8)).Zc.card:ℝ) ≤
     (1+100*((max B.rank 1:ℕ):ℝ)*(a8:ℝ)) *
      (B.Zc.card:ℝ):=ch
   _≤2*(B.Zc.card:ℝ):=by
    gcongr
 have GI :
   ((-A+S).card:ℝ) ≤
    ((B.ai (1+a8)).Zc.card:ℝ):=by
  exact_mod_cast Qu l0
 exact_mod_cast GI.trans KA
lemma o9
  (B:aj G) (rE:B.a1)
  (S:Finset G) {a8:NNReal}
  (hS:S⊆(B.ai a8).Zc)
  (jL :
   a8≤1/(100*(max B.rank 1:ℕ):NNReal)) :
  (B.Zc-S).card≤2*B.Zc.card:=by
 have h :=
  ij B rE B.Zc S
   (fun _ hx↦hx) hS jL
 have eY :
   (B.Zc-S).card=(-B.Zc+S).card:=by
  rw[←Finset.card_neg]
  simp[Qy,RV]
 rw[eY]
 exact h
lemma mH
  (B:aj G) (rE:B.a1)
  (S:Finset G) {a8:NNReal}
  (hS:S⊆(B.ai a8).Zc)
  (jL :
   a8≤1/(100*(max B.rank 1:ℕ):NNReal))
  (z:G) :
  ((z+ᵥ B.Zc)-S).card≤2*B.Zc.card:=by
 have dc:= o9 B rE S hS jL
 have heq :
   (z+ᵥ B.Zc)-S=z+ᵥ (B.Zc-S):=by
  ext x
  constructor
  ·intro hx
   obtain ⟨u,hu,v,hv,rfl⟩:=Finset.mem_sub.mp hx
   obtain ⟨b,hb,rfl⟩:=Finset.mem_vadd_finset.mp hu
   apply Finset.mem_vadd_finset.mpr
   exact ⟨b-v,Finset.mem_sub.mpr ⟨b,hb,v,hv,rfl⟩,by
    simp only[Uz]
    abel⟩
  ·intro hx
   obtain ⟨u,hu,rfl⟩:=Finset.mem_vadd_finset.mp hx
   obtain ⟨b,hb,v,hv,rfl⟩:=Finset.mem_sub.mp hu
   apply Finset.mem_sub.mpr
   exact ⟨z+b,Finset.mem_vadd_finset.mpr ⟨b,hb,rfl⟩,
    v,hv,by
     simp only[Uz]
     abel⟩
 rw[heq,Finset.card_vadd_finset]
 exact dc
structure bU (W:aj G) where
 eta:NNReal
 b6:aj G
 vc:NNReal
 theta:NNReal
 bu:aj G
 vd:NNReal
 phi:NNReal
 bl:aj G
 pa:NNReal
 Fn:eta=1/(1600*(max W.rank 1:ℕ):NNReal)
 ux:0<eta
 mD :
  4*eta≤1/(400*(max W.rank 1:ℕ):NNReal)
 GJ:b6=(W.ai eta).ai vc
 zx:1/2≤vc
 GK:vc≤1
 zy:b6.a1
 Bd:theta=1/(200*(max b6.rank 1:ℕ):NNReal)
 theta_pos:0<theta
 w8 :
  theta≤1/(100*(max b6.rank 1:ℕ):NNReal)
 GM:bu=(b6.ai theta).ai vd
 zz:1/2≤vd
 GN:vd≤1
 zA:bu.a1
 Fo:phi=1/(200*(max bu.rank 1:ℕ):NNReal)
 IB:0<phi
 zB :
  phi≤1/(100*(max bu.rank 1:ℕ):NNReal)
 ze:bl=(bu.ai phi).ai pa
 w9:1/2≤pa
 DL:pa≤1
 wx:bl.a1
 rW:b6.Zc⊆(W.ai eta).Zc
 rX:bu.Zc⊆(W.ai eta).Zc
 xb:bu.Zc⊆(b6.ai theta).Zc
 DM:bl.Zc⊆(W.ai eta).Zc
 wy:bl.Zc⊆(bu.ai phi).Zc
omit [DecidableEq G] in
lemma rP (W:aj G) :
  Nonempty (bU W):=by
 classical
 let dW:ℕ:=max W.rank 1
 let eta:NNReal:=1/(1600*(dW:NNReal))
 have P7:0<dW:=by simp[dW]
 have IC:0<eta:=by
  dsimp[eta]
  positivity
 have ve :
   4*eta≤1/(400*(max W.rank 1:ℕ):NNReal):=by
  dsimp[eta,dW]
  have hd:(0:NNReal)<(max W.rank 1:ℕ):=by positivity
  field_simp
  norm_num
 obtain ⟨vc,Fp,Be,Me⟩ :=
  (W.ai eta).eP
 let b6:aj G:=(W.ai eta).ai vc
 let dD:ℕ:=max b6.rank 1
 let theta:NNReal:=1/(200*(dD:NNReal))
 have P8:0<dD:=by simp[dD]
 have Fq:0<theta:=by
  dsimp[theta]
  positivity
 have xc :
   theta≤1/(100*(max b6.rank 1:ℕ):NNReal):=by
  dsimp[theta,dD]
  have hd:(0:NNReal)<(max b6.rank 1:ℕ):=by positivity
  field_simp
  norm_num
 obtain ⟨vd,Fr,Bf,Mf⟩ :=
  (b6.ai theta).eP
 let bu:aj G:=(b6.ai theta).ai vd
 let dE:ℕ:=max bu.rank 1
 let phi:NNReal:=1/(200*(dE:NNReal))
 have P9:0<dE:=by simp[dE]
 have ID:0<phi:=by
  dsimp[phi]
  positivity
 have zC :
   phi≤1/(100*(max bu.rank 1:ℕ):NNReal):=by
  dsimp[phi,dE]
  have hd:(0:NNReal)<(max bu.rank 1:ℕ):=by positivity
  field_simp
  norm_num
 obtain ⟨pa,B2,yy,sw⟩ :=
  (bu.ai phi).eP
 let bl:aj G:=(bu.ai phi).ai pa
 have gp:b6.Zc⊆(W.ai eta).Zc:=by
  dsimp[b6]
  simpa using
   (aj.b5 Be :
    ((W.ai eta).ai vc).Zc ⊆
     ((W.ai eta).ai 1).Zc)
 have Ct :
   bu.Zc⊆(b6.ai theta).Zc:=by
  dsimp[bu]
  simpa using
   (aj.b5 Bf :
    ((b6.ai theta).ai vd).Zc ⊆
     ((b6.ai theta).ai 1).Zc)
 have Fs:theta≤1:=by
  calc
   theta≤1/(100*(max b6.rank 1:ℕ):NNReal) :=
    xc
   _≤1:=by
    rw[Q9]
    ·exact_mod_cast(show 1≤100*max b6.rank 1 by omega)
    ·positivity
 have lh:bu.Zc⊆(W.ai eta).Zc:=by
  apply Ct.trans
  apply(aj.b5 Fs).trans
  simpa using gp
 have Bg :
   bl.Zc⊆(bu.ai phi).Zc:=by
  dsimp[bl]
  simpa using
   (aj.b5 yy :
    ((bu.ai phi).ai pa).Zc ⊆
     ((bu.ai phi).ai 1).Zc)
 have IE:phi≤1:=by
  calc
   phi≤1/(100*(max bu.rank 1:ℕ):NNReal) :=
    zC
   _≤1:=by
    rw[Q9]
    ·exact_mod_cast(show 1≤100*max bu.rank 1 by omega)
    ·positivity
 have DN:bl.Zc⊆(W.ai eta).Zc:=by
  apply Bg.trans
  apply(aj.b5 IE).trans
  simpa using lh
 exact ⟨{
  eta:=eta
  b6:=b6
  vc:=vc
  theta:=theta
  bu:=bu
  vd:=vd
  phi:=phi
  bl:=bl
  pa:=pa
  Fn:=rfl
  ux:=IC
  mD:=ve
  GJ:=rfl
  zx:=Fp
  GK:=Be
  zy:=by simpa[b6] using Me
  Bd:=rfl
  theta_pos:=Fq
  w8:=xc
  GM:=rfl
  zz:=Fr
  GN:=Bf
  zA:=by simpa[bu] using Mf
  Fo:=rfl
  IB:=ID
  zB:=zC
  ze:=rfl
  w9:=B2
  DL:=yy
  wx:=by simpa[bl] using sw
  rW:=gp
  rX:=lh
  xb:=Ct
  DM:=DN
  wy:=Bg }⟩
omit [DecidableEq G] in
lemma d0
  (B:aj G) (a8:NNReal) (jL:1/2≤a8) :
  B.Zc.card≤4^B.rank*(B.ai a8).Zc.card:=by
 classical
 have iB:=B.de
 have xS :
   (B.ai (1/2)).Zc.card≤(B.ai a8).Zc.card :=
  Qu (aj.b5 jL)
 calc
  B.Zc.card≤4^B.rank*(B.ai (1/2)).Zc.card :=
   by simpa using iB
  _≤4^B.rank*(B.ai a8).Zc.card :=
   Qr _ xS
omit [DecidableEq G] in
lemma mi (W:aj G) (H:bU W) :
  H.b6.rank=W.rank∧H.bu.rank=W.rank∧H.bl.rank=W.rank:=by
 have hD:H.b6.rank=W.rank:=by
  rw[H.GJ,aj.f6,aj.f6]
 have hE:H.bu.rank=W.rank:=by
  rw[H.GM,aj.f6,aj.f6]
  exact hD
 have hB:H.bl.rank=W.rank:=by
  rw[H.ze,aj.f6,aj.f6]
  exact hE
 constructor
 ·exact hD
 constructor
 ·exact hE
 ·exact hB
def b7 (W:aj G):ℕ :=
 ((3*(1600*max W.rank 1))^W.rank*4^W.rank) *
  ((3*(200*max W.rank 1))^W.rank*4^W.rank) *
  ((3*(200*max W.rank 1))^W.rank*4^W.rank)
omit [DecidableEq G] in
lemma qd
  (W:aj G) (H:bU W) :
  W.Zc.card≤b7 W*H.bl.Zc.card:=by
 classical
 let qe:ℕ:=1600*max W.rank 1
 let jC:ℕ:=200*max W.rank 1
 have Mg:0<qe:=by dsimp[qe]; positivity
 have Cu:0<jC:=by dsimp[jC]; positivity
 have uF:=mi W H
 have Mh :
   W.Zc.card≤(3*qe)^W.rank *
    (W.ai H.eta).Zc.card:=by
  have c3 :=
   aj.cM W 1 Mg
  rw[H.Fn]
  simpa[qe,Qw] using c3
 have Mi :
   (W.ai H.eta).Zc.card≤4^W.rank*H.b6.Zc.card:=by
  rw[H.GJ]
  simpa only[aj.f6] using
   d0
    (W.ai H.eta) H.vc H.zx
 have IF :
   H.b6.Zc.card≤(3*jC)^W.rank *
    (H.b6.ai H.theta).Zc.card:=by
  have c3 :=
   aj.cM H.b6 1 Cu
  rw[H.Bd]
  simpa[jC,uF.1,Qw] using c3
 have Pj :
   (H.b6.ai H.theta).Zc.card ≤
    4^W.rank*H.bu.Zc.card:=by
  rw[H.GM]
  simpa[uF.1] using
   d0
    (H.b6.ai H.theta) H.vd H.zz
 have IG :
   H.bu.Zc.card≤(3*jC)^W.rank *
    (H.bu.ai H.phi).Zc.card:=by
  have c3 :=
   aj.cM H.bu 1 Cu
  rw[H.Fo]
  simpa[jC,uF.2.1,Qw] using c3
 have Pk :
   (H.bu.ai H.phi).Zc.card ≤
    4^W.rank*H.bl.Zc.card:=by
  rw[H.ze]
  simpa[uF.2.1] using
   d0
    (H.bu.ai H.phi) H.pa H.w9
 unfold b7
 calc
  W.Zc.card≤(3*qe)^W.rank *
    (W.ai H.eta).Zc.card:=Mh
  _≤(3*qe)^W.rank*(4^W.rank*H.b6.Zc.card) :=
   Qr _ Mi
  _≤((3*qe)^W.rank*4^W.rank) *
    ((3*jC)^W.rank *
     (H.b6.ai H.theta).Zc.card):=by
   have h:=Qr
    ((3*qe)^W.rank*4^W.rank) IF
   simpa[SZ,R8,U6] using h
  _≤((3*qe)^W.rank*4^W.rank) *
    ((3*jC)^W.rank*(4^W.rank*H.bu.Zc.card)):=by
   gcongr
  _≤((3*qe)^W.rank*4^W.rank) *
    (((3*jC)^W.rank*4^W.rank) *
     ((3*jC)^W.rank *
      (H.bu.ai H.phi).Zc.card)):=by
   have h:=Qr
    (((3*qe)^W.rank*4^W.rank) *
     ((3*jC)^W.rank*4^W.rank)) IG
   simpa[SZ,R8,U6] using h
  _≤((3*qe)^W.rank*4^W.rank) *
    (((3*jC)^W.rank*4^W.rank) *
     ((3*jC)^W.rank*(4^W.rank*H.bl.Zc.card))):=by
   gcongr
  _=(((3*(1600*max W.rank 1))^W.rank*4^W.rank) *
    ((3*(200*max W.rank 1))^W.rank*4^W.rank) *
    ((3*(200*max W.rank 1))^W.rank*4^W.rank)) *
    H.bl.Zc.card:=by
   simp[qe,jC]
   ring
lemma kg
  (W:aj G) {D E:Finset G} {eta:NNReal}
  (hD:D⊆(W.ai eta).Zc)
  (hE:E⊆(W.ai eta).Zc) :
  ∀ t,aN.bh D E t≠0 →
   t∈(W.ai (4*eta)).Zc:=by
 intro t ht
 have zD :
   t∈Function.support (aN.bh D E):=ht
 have qj :
   0≤aN.dU D E:=by
  simp[aN.dU]
 have KB:t∈(D+E)-(D+E):=by
  rw[aN.bh,
   f8 qj qj,
   aN.dU,
   tT cC cC,
   jo,jo] at zD
  simpa only[←coe_add, ←coe_sub,mem_coe] using zD
 obtain ⟨u,hu,v,hv,rfl⟩:=Finset.mem_sub.mp KB
 obtain ⟨d₁,Mj,KC,Mk,rfl⟩:=Finset.mem_add.mp hu
 obtain ⟨d₂,Ml,KD,Mm,rfl⟩:=Finset.mem_add.mp hv
 have Pl :
   d₁+KC∈(W.ai (eta+eta)).Zc :=
  aj.e7 (hD Mj) (hE Mk)
 have Pm :
   d₂+KD∈(W.ai (eta+eta)).Zc :=
  aj.e7 (hD Ml) (hE Mm)
 have l0 :
   (d₁+KC)-(d₂+KD) ∈
    (W.ai ((eta+eta)+(eta+eta))).Zc :=
  aj.j0 Pl Pm
 simpa[show(eta+eta)+(eta+eta)=4*eta by ring] using l0
lemma la
  {original:Finset G} (s:ah.aA original)
  {bn bd:ℕ}
  (C:c7 s.restriction.ba bn bd)
  (W:aj G) (H:bU W)
  (kx:W.Zc=aO.a4 C.aB.Zc) :
  ∀ t,
   aN.bh H.bu.Zc H.b6.Zc t≠0 →
   t∈(C.ak.ba.ai
    ((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹)).Zc:=by
 intro t ht
 have KE :
   t∈(W.ai (4*H.eta)).Zc :=
  kg W H.rX H.rW t ht
 have GO:4*H.eta≤(1:NNReal):=by
  calc
   4*H.eta ≤
     1/(400*(max W.rank 1:ℕ):NNReal):=H.mD
   _≤1:=by
    rw[Q9]
    ·exact_mod_cast(show 1≤400*max W.rank 1 by omega)
    ·positivity
 have MT:t∈W.Zc:=by
  simpa only[aj.oD] using
   (aj.b5 GO KE)
 rw[kx] at MT
 exact C.kT MT
def gk
  (W:aj G) (H:bU W) (a3:Finset G):Finset G :=
 (-a3)+H.bl.Zc
def cI
  (W:aj G) (H:bU W) (a3:Finset G):ℝ :=
 (gk W H a3).card
def cq
  (W:aj G) (H:bU W):ℝ :=
 H.bl.Zc.card
def du (a3:Finset G):ℝ :=
 (-a3).card
section wz
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
def b3
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (W:aj G) (H:bU W)
  (_data:ah.aW A aL H.bu.Zc p sigma delta)
  (k:ℕ):ℝ :=
 ((ah.bj A aL H.bu.Zc p/2)^k)/2
omit [DiscreteMeasurableSpace G] in
lemma mj
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (W:aj G) (H:bU W)
  (data:ah.aW A aL H.bu.Zc p sigma delta)
  (cu:delta<1)
  (k:ℕ) (T:Finset G)
  (hT :
   ((du data.a3^k/2 *
     cq W H) /
     cI W H data.a3^k≤(T.card:ℝ))) :
  ((((ah.bj A aL H.bu.Zc p/2)^k) /
    2)*cq W H)≤(T.card:ℝ):=by
 have gM:=data.lO cu
 have Ft:(0:ℝ)<H.bu.Zc.card:=by
  exact_mod_cast H.bu.aE.card_pos
 have Cs :
   ah.bj A aL H.bu.Zc p *
     (H.bu.Zc.card:ℝ)≤(data.a3.card:ℝ):=by
  exact(Qs Ft).mp data.tA
 have DO :
   ah.bj A aL H.bu.Zc p *
     (H.bu.Zc.card:ℝ)≤((-data.a3).card:ℝ):=by
  simpa using Cs
 have yW :
   (gk W H data.a3).card ≤
    2*H.bu.Zc.card:=by
  unfold gk
  apply ij H.bu H.zA
   data.a3 (H.bl).Zc data.rJ H.wy H.zB
 have hsum :
   cI W H data.a3 ≤
    2*(H.bu.Zc.card:ℝ):=by
  unfold cI
  exact_mod_cast yW
 have b8 :
   0≤ah.bj A aL H.bu.Zc p:=by
  unfold ah.bj
  exact RS (Qn (by norm_num) (QH tU _))
   (by positivity)
 have Mn:(-data.a3).Nonempty:=by
  obtain ⟨a,ha⟩:=gM.2
  exact ⟨-a,by simpa using ha⟩
 simpa only[du,cq,cI,
  gk,show(2:ℝ)=2 by rfl] using
  (lG
   (A:=-data.a3) (S:=(H.bl).Zc) (T:=T)
   (D:=H.bu.Zc) k b8 (by norm_num:(0:ℝ)<2)
   Mn (H.bl).aE DO hsum hT)
omit [DiscreteMeasurableSpace G] in
lemma i5
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (W:aj G) (H:bU W)
  (data:ah.aW A aL H.bu.Zc p sigma delta)
  (cu:delta<1)
  (k:ℕ) (T:Finset G) (Delta:Finset (AddChar G Complex))
  (g8:0 <
   b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
    (delta:=delta) W H data k)
  (hT :
   ((du data.a3^k/2 *
     cq W H) /
     cI W H data.a3^k≤(T.card:ℝ)))
  (dQ:(Delta.card:ℝ) ≤
   aI.bf H.bl T (1/2)) :
  Delta.card ≤
   ⌈8*(1+Real.log (2 /
    b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
     (delta:=delta) W H data k))⌉₊:=by
 have wA :
   b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
     (delta:=delta) W H data k*(H.bl.Zc.card:ℝ) ≤
    (T.card:ℝ):=by
  simpa[b3,cq] using
   mj W H data cu k T hT
 have oM :
   aI.bf H.bl T (1/2) ≤
    8*(1+Real.log (2 /
     b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
      (delta:=delta) W H data k)) :=
  fR H.bl T g8
   (by
    have gw:(0:ℝ) <
      b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
       (delta:=delta) W H data k *
      (H.bl.Zc.card:ℝ) :=
     QM g8 (by exact_mod_cast H.bl.aE.card_pos)
    have DP:(0:ℝ)<T.card:=gw.trans_le wA
    exact Finset.card_pos.mp (by exact_mod_cast DP))
   wA
 exact om Delta (dQ.trans oM)
omit [DiscreteMeasurableSpace G] in
lemma ot
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (W:aj G) (H:bU W)
  (data:ah.aW A aL H.bu.Zc p sigma delta)
  (cu:delta<1)
  (k:ℕ) (T:Finset G)
  (g8:0 <
   b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
    (delta:=delta) W H data k)
  (hT :
   ((du data.a3^k/2 *
     cq W H) /
     cI W H data.a3^k≤(T.card:ℝ))) :
  aI.bf H.bl T (1/2) ≤
   8*(1+Real.log (2 /
    b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
     (delta:=delta) W H data k)):=by
 have wA :
   b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
     (delta:=delta) W H data k*(H.bl.Zc.card:ℝ) ≤
    (T.card:ℝ):=by
  simpa[b3,cq] using
   mj W H data cu k T hT
 apply fR H.bl T g8
 ·have gw:(0:ℝ) <
    b3 (A:=A) (aL:=aL) (p:=p) (sigma:=sigma)
      (delta:=delta) W H data k *
     (H.bl.Zc.card:ℝ) :=
   QM g8 (by exact_mod_cast H.bl.aE.card_pos)
  have DP:(0:ℝ)<T.card:=gw.trans_le wA
  exact Finset.card_pos.mp (by exact_mod_cast DP)
 ·exact wA
end wz
lemma n0
  {original:Finset G} (s:ah.aA original)
  {d:ℕ}
  (c3:(1/(2:ℝ)^d)≤ s.Zd) :
  (2/3:ℝ)^(4*(d+1)) ≤
   (1-(1/512:ℝ))*s.Zd:=by
 have dc:(2/3:ℝ)^4≤1/2:=by norm_num
 have hpow :
   (2/3:ℝ)^(4*(d+1))≤(1/2:ℝ)^(d+1):=by
  calc
   (2/3:ℝ)^(4*(d+1)) =
     ((2/3:ℝ)^4)^(d+1):=by rw[QU]
   _≤(1/2:ℝ)^(d+1) :=
    Qp (by positivity) dc (d+1)
 have vG :
   (1/2:ℝ)^(d+1) ≤
    (511/512:ℝ)*(1/(2:ℝ)^d):=by
  have DQ:0≤(1/2:ℝ)^d:=by positivity
  rw[RB]
  calc
   (1/2:ℝ)^d*(1/2) ≤
     (1/2:ℝ)^d*(511/512) :=
    iO (by norm_num) DQ
   _=(511/512:ℝ)*(1/(2:ℝ)^d):=by
    simp[R6,Te,Qx]
 calc
  (2/3:ℝ)^(4*(d+1))≤(1/2:ℝ)^(d+1):=hpow
  _≤(511/512:ℝ)*(1/(2:ℝ)^d):=vG
  _≤(511/512:ℝ)*s.Zd :=
   iO c3 (by norm_num)
  _=(1-(1/512:ℝ))*s.Zd:=by ring
noncomputable def bF
    {original:Finset G}
    (s:bA.aG original)
    {bn bd:ℕ} (eH:0<bn) (fw:0<bd)
    (C:c7 s.aV.restriction.ba bn bd)
    {epsilon aU:ℝ} {aq:ℕ}
    (kD:gj s.aV bn bd epsilon aU) :
    bA.dB s epsilon aU aq:=by
  have zV :
      (0:ℝ)<(b9 s.aV.restriction.ba bn:ℝ):=by
    unfold b9
    positivity
  have zW :
      (0:ℝ) <
        (bI s.aV.restriction.ba bn bd:ℝ):=by
    unfold bI b9
    positivity
  have IH :
      (s.aV.restriction.ba.Zc.card:ℝ) ≤
        (b9 s.aV.restriction.ba bn:ℝ) *
          (C.ak.Zc.card:ℝ):=by
    exact_mod_cast C.mz
  have IJ :
      (s.aV.restriction.ba.Zc.card:ℝ) ≤
        (bI s.aV.restriction.ba bn bd:ℝ) *
          (C.aB.Zc.card:ℝ):=by
    exact_mod_cast C.mA
  have vb :
      Real.exp (-aU)*(s.card:ℝ)≤C.ak.Zc.card:=by
    simpa[bA.aG.card] using
      mh s.aV zV kD.th IH
  have xL :
      Real.exp (-aU)*(s.card:ℝ)≤C.aB.Zc.card:=by
    simpa[bA.aG.card] using
      mh s.aV zW kD.ti IJ
  have o0 :
      cp s.aV.restriction.set
          s.aV.restriction.ba.Zc=s.aV.Zd:=by
    unfold ah.aA.Zd
      br.aY.Zd cp
      br.aY.e8
    simp[s.fS]
  refine
    { aF:=(bn:NNReal)⁻¹
      w7:=kD.yx
      ak:=C.ak
      aB:=C.aB
      fT:=C.fT
      g3:=C.g3
      ez:=C.ez
      fc:=C.fc
      nS:=C.nS
      pZ:=C.pZ
      td:= ?_
      rankOne:= ?_
      p0:= ?_
      mz:=vb
      mA:=xL }
  · simpa only[o0] using kD.vq
  · rw[C.rankOne]
    simp[bA.aG.rank,
      ah.aA.rank,br.aY.rank]
  · rw[C.p0]
    simp[bA.aG.rank,
      ah.aA.rank,br.aY.rank]
def cX {original:Finset G}
  (s:ah.aA original)
  (ak aB:ah.bt (G:=G)) {epsilon:ℝ}
  (aQ:ah.bV s ak aB epsilon):Finset G :=
 ah.dn s.restriction.set ak.Zc
  (aO.cr aQ)
def jD {original:Finset G}
  (s:ah.aA original)
  (ak aB:ah.bt (G:=G)) {epsilon:ℝ}
  (aQ:ah.bV s ak aB epsilon):Finset G :=
 ah.dn s.restriction.set aB.Zc
  (aO.cr aQ)
def a5 {original:Finset G}
  (s:ah.aA original) (epsilon:ℝ):ℝ :=
 (1-epsilon)*s.Zd
lemma pb
  {original:Finset G} (s:ah.aA original)
  (ak aB:ah.bt (G:=G)) {epsilon:ℝ}
  (aQ:ah.bV s ak aB epsilon)
  (b2:epsilon<1) :
  (cX s ak aB aQ).Nonempty:=by
 let alpha:=a5 s epsilon
 have b8:0<alpha :=
  QM (sub_pos.mpr b2) s.dI
 have lC:alpha ≤
   a9 s.restriction.set ak.Zc
    (aO.cr aQ):=by
  simpa[alpha,a5] using
   aO.c0 aQ
 apply ah.bK
  ak.aE
 exact b8.trans_le lC
lemma qO
  {original:Finset G} (s:ah.aA original)
  (ak aB:ah.bt (G:=G)) {epsilon:ℝ}
  (aQ:ah.bV s ak aB epsilon) :
  cX s ak aB aQ⊆ak.Zc:=by
 exact ah.dz
  (B:=ak.ba) (a8:=ak.outer)
  (A:=s.restriction.set) (C:=ak.Zc)
  (x:=aO.cr aQ) (fun _ hz↦hz)
noncomputable def iG
    {original:Finset G} (s:ah.aA original)
    (ak aB:ah.bt (G:=G)) {epsilon:ℝ}
    (aQ:ah.bV s ak aB epsilon)
    (_hepsilon_nonneg:0≤epsilon) (b2:epsilon<1)
    {p:ℕ} (hp:0<p) (f:G→ℝ)
    (jy:(2/3:ℝ)^p≤a5 s epsilon)
    (ew :
      |(aO.bb
            (cX s ak aB aQ)
            (jD s ak aB aQ) -
          (Fintype.card G:ℝ)/(#ak.Zc:ℝ)) -
          aw.Zp f
            (aO.a4
              (jD s ak aB aQ))| ≤
        ((Fintype.card G:ℝ)/(#ak.Zc:ℝ))/8)
    (ee :
      an.aM
          (af (aO.a4 aB.Zc))
          f p ≤
        ((Fintype.card G:ℝ)/(#ak.Zc:ℝ))/8) :
    aO.eh original:=by
  let x:G:=aO.cr aQ
  let A':Finset G:=cX s ak aB aQ
  let b4:Finset G:=jD s ak aB aQ
  let B:Finset G:=ak.Zc
  let B':Finset G:=aB.Zc
  let alpha:ℝ:=a5 s epsilon
  have lC:alpha≤a9 s.restriction.set B x:=by
    simpa[alpha,x,B,a5] using
      aO.c0 aQ
  have oW:alpha≤a9 s.restriction.set B' x:=by
    simpa[alpha,x,B',a5] using
      aO.ea aQ
  have b8:0<alpha:=by
    exact QM (sub_pos.mpr b2) s.dI
  have qG:A'.Nonempty:=by
    apply ah.bK
      ak.aE
    exact b8.trans_le lC
  have gN:b4.Nonempty:=by
    apply ah.bK
      aB.aE
    exact b8.trans_le oW
  have j9:b4⊆B':=by
    exact ah.dz
      (B:=aB.ba) (a8:=aB.outer)
      (A:=s.restriction.set) (C:=aB.Zc)
      (x:=x) (fun _ hz↦hz)
  have gO: ∀ z∈A',z-(s.shift-x)∈original:=by
    intro z hz
    have i1:x+z∈s.restriction.set :=
      (ah.e3.mp hz).2
    have hs:=s.eR (x+z) i1
    have heq:z-(s.shift-x)=(x+z)-s.shift:=by abel
    rwa[heq]
  have fP: ∀ z∈b4,z-(s.shift-x)∈original:=by
    intro z hz
    have i1:x+z∈s.restriction.set :=
      (ah.e3.mp hz).2
    have hs:=s.eR (x+z) i1
    have heq:z-(s.shift-x)=(x+z)-s.shift:=by abel
    rwa[heq]
  have nn:alpha*(#B:ℝ)≤(#A':ℝ):=by
    have wL:(0:ℝ)< #B:=by
      exact_mod_cast ak.aE.card_pos
    rw[ah.bk
      ak.aE x] at lC
    exact(Qs wL).mp lC
  have np:alpha*(#B':ℝ)≤(#b4:ℝ):=by
    have wb:(0:ℝ)< #B':=by
      exact_mod_cast aB.aE.card_pos
    rw[ah.bk
      aB.aE x] at oW
    exact(Qs wb).mp oW
  have qH :
      (2/3:ℝ)^p≤aw.bL b4 B':=by
    calc
      (2/3:ℝ)^p≤alpha:=jy
      _≤a9 s.restriction.set B' x:=by
        simpa[alpha,x,B',a5] using
          aO.ea aQ
      _=aw.bL b4 B':=by
        rw[ah.bk
          aB.aE x]
        rfl
  have oX:(aO.a4 B').Nonempty :=
    aO.eJ aB.aE
  have uk :
      aw.cO (aO.a4 B') p f ≤
        (((Fintype.card G:ℝ)/(#B:ℝ))/8)^p:=by
    apply aO.fb
      oX hp f (by positivity)
    simpa[B,B'] using ee
  exact
    { A':=A'
      b4:=b4
      B:=B
      B':=B'
      translate:=s.shift-x
      alpha:=alpha
      p:=p
      f:=f
      jP:=qG
      iZ:=gN
      kM:=ak.aE
      h6:=j9
      fL:=gO
      fl:=fP
      i0:=b8.le
      kN:=nn
      jQ:=np
      p_pos:=hp
      gf:=qH
      e6:=by simpa[A',b4,B] using ew
      gg:=uk }
noncomputable def bB
  {original:Finset G} (s:ah.aA original)
  (ak aB:ah.bt (G:=G)) {epsilon:ℝ}
  (aQ:ah.bV s ak aB epsilon)
  (b2:epsilon<1) :
  ah.aA original:=by
 let x:=aO.cr aQ
 have n6:0<a5 s epsilon :=
  QM (sub_pos.mpr b2) s.dI
 have hx:a5 s epsilon ≤
   a9 s.restriction.set ak.Zc x:=by
  simpa[x,a5] using
   aO.c0 aQ
 exact ah.di s ak x (n6.trans_le hx)
@[simp] lemma DZ
  {original:Finset G} (s:ah.aA original)
  (ak aB:ah.bt (G:=G)) {epsilon:ℝ}
  (aQ:ah.bV s ak aB epsilon)
  (b2:epsilon<1) :
  (bB s ak aB aQ b2).restriction.set =
   cX s ak aB aQ:=by
 rfl
lemma m5
  {original:Finset G} (s:ah.aA original)
  {bn bd:ℕ} (eH:0<bn)
  (C:c7 s.restriction.ba bn bd)
  {epsilon:ℝ}
  (aQ:ah.bV s C.ak C.aB epsilon)
  (b2:epsilon<1)
  (ju:s.restriction.outer=1) :
  (bB s C.ak C.aB aQ b2).card≤ s.card:=by
 have GQ:((bn:NNReal)⁻¹)≤1:=by
  apply(inv_le_one₀ (by exact_mod_cast eH)).2
  exact_mod_cast(show 1≤bn by omega)
 have A2:C.ak.Zc.card≤ s.restriction.ba.Zc.card:=by
  calc
   C.ak.Zc.card ≤
     (s.restriction.ba.ai ((bn:NNReal)⁻¹)).Zc.card :=
    Qu C.nS
   _≤(s.restriction.ba.ai 1).Zc.card :=
    Qu (aj.b5 GQ)
   _=s.restriction.ba.Zc.card:=by simp
 calc
  (bB s C.ak C.aB aQ b2).card =
    C.ak.Zc.card:=by
   simp[bB,ah.di,
    ah.bt.en,
    ah.aA.card,br.aY.card,
    br.aY.e8,C.fT,
    C.eD]
  _≤ s.restriction.ba.Zc.card:=A2
  _=s.card:=by
   unfold ah.aA.card br.aY.card
    br.aY.e8
   simp[ju]
lemma ml
  {original:Finset G} (s:ah.aA original)
  {bn bd:ℕ} (eH:0<bn)
  (C:c7 s.restriction.ba bn bd)
  {epsilon:ℝ}
  (aQ:ah.bV s C.ak C.aB epsilon)
  (b2:epsilon<1)
  (ju:s.restriction.outer=1)
  (W:aj G) (H:bU W)
  (wB:W.Zc.card=C.aB.Zc.card) :
  ((bB s C.ak C.aB aQ b2).card:ℝ) ≤
   ((bI s.restriction.ba bn bd *
     b7 W:ℕ):ℝ)*(H.bl.Zc.card:ℝ):=by
 have md :
   (bB s C.ak C.aB aQ b2).card ≤
    s.card :=
  m5 s eH C aQ b2 ju
 have KF :
   s.card≤bI s.restriction.ba bn bd*W.Zc.card:=by
  have hC:=C.mA
  unfold ah.aA.card br.aY.card
   br.aY.e8
  rw[wB]
  simpa[ju] using hC
 have Mo:=qd W H
 have sB :
   (bB s C.ak C.aB aQ b2).card ≤
    (bI s.restriction.ba bn bd *
     b7 W)*H.bl.Zc.card:=by
  calc
   (bB s C.ak C.aB aQ b2).card ≤
     s.card:=md
   _≤bI s.restriction.ba bn bd*W.Zc.card:=KF
   _≤bI s.restriction.ba bn bd *
     (b7 W*H.bl.Zc.card) :=
    Qr _ Mo
   _=(bI s.restriction.ba bn bd *
     b7 W)*H.bl.Zc.card:=by ring
 exact_mod_cast sB
section xM
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
lemma mI
  (A aL a0:Finset G) {p:ℕ} (hp:0<p) :
  ah.bj A aL a0 p =
   (4:ℝ)⁻¹ *
    ((A.card:ℝ) *
     an.aM
      (fun x:G=>(((al ((@mu (ℝ≥0) _ _) aL) (mu a0))) x:ℝ))
      ((al ((@mu (ℝ) _ _) A) (mu A))) p)^(2*p):=by
 let w:G→ℝ≥0:=(al (mu aL) (mu a0))
 have rI :
   ((al ((Set.indicator A fun _↦(1:Real))) ((Set.indicator A fun _↦(1:_))))) =
    ((A.card:ℝ)^2)•((al ((@mu (ℝ) _ _) A) (mu A))):=by
  rw[←l1 ℝ A,oy,oz]
  funext x
  simp[RD,Q2,TI]
  ring
 have c3 :=
  aN.gv w
   ((al ((@mu (ℝ) _ _) A) (mu A))) ((A.card:ℝ)^2) (by positivity) hp
 have oO :
   (b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:Real))) ((Set.indicator A fun _↦(1:_)))))) =
    (A.card:ℝ)^2 *
     an.aM
      ((↑) ∘ w)
      ((al ((@mu (ℝ) _ _) A) (mu A))) p:=by
  rw[rI]
  simpa only[aN.dN w
   ((A.card:ℝ)^2•((al ((@mu (ℝ) _ _) A) (mu A)))) hp] using c3
 dsimp[w,Function.comp_def] at oO
 rw[ah.bj,oO]
 by_cases MU:(A.card:ℝ)=0
 ·have u9:2*p≠0:=by omega
  simp[MU,u9]
 have hpow:(A.card:ℝ)^(2*p)≠0:=Rg _ MU
 field_simp[hpow]
 ring
lemma mJ
  (A aL a0:Finset G) {p:ℕ} (hp:0<p)
  (hB:(aL∩a0).Nonempty) (hA:A.Nonempty) :
  0<ah.bj A aL a0 p:=by
 classical
 have x0:p≠0:=hp.ne'
 have rH:aL.Nonempty:=hB.mono Sh
 have uZ:a0.Nonempty:=hB.mono Sd
 let N:ℝ:=(b0 p ((al (mu aL) (mu a0))) ((al ((Set.indicator A fun _↦(1:(ℝ)))) ((Set.indicator A fun _↦(1:_))))))
 have KG :=
  ah.gQ A aL a0 p x0 rH uZ
 obtain ⟨b,hb⟩:=hB
 obtain ⟨a,ha⟩:=hA
 let sC:Fin p→G:=fun _↦b-a
 have v5:b∈cA.cS A aL sC:=by
  simp only[cA.jn,sC]
  refine ⟨Sh hb, ?_⟩
  intro i
  have:b-(b-a)=a:=by abel
  rwa[this]
 have v7:b∈cA.cS A a0 sC:=by
  simp only[cA.jn,sC]
  refine ⟨Sd hb, ?_⟩
  intro i
  have:b-(b-a)=a:=by abel
  rwa[this]
 have rV :
   0< ∑ u:Fin p→G,
    ((cA.cS A aL u).card:ℝ) *
     (cA.cS A a0 u).card:=by
  apply Finset.sum_pos'
  ·intro u hu
   positivity
  ·refine ⟨sC,Sz _, ?_⟩
   exact QM
    (by exact_mod_cast(Finset.card_pos.mpr ⟨b,v5⟩))
    (by exact_mod_cast(Finset.card_pos.mpr ⟨b,v7⟩))
 have Hc:0<N^p:=by
  rw[KG] at rV
  have jt:0<(aL.card:ℝ)*a0.card:=by positivity
  rcases mul_pos_iff.mp rV with gw | eY
  ·simpa[N] using gw.2
  ·exact(Rd jt.le eY.1).elim
 have GR:0≤N:=by
  dsimp[N]
  exact tU
 have Nz:N≠0:=by
  intro MI
  rw[MI] at Hc
  simp[x0] at Hc
 have Mp:0<N:=SM GR (Ne.symm Nz)
 unfold ah.bj
 have r0:(0:ℝ)<A.card:=by
  exact_mod_cast(Finset.card_pos.mpr ⟨a,ha⟩)
 dsimp[N] at Mp
 positivity
omit [DiscreteMeasurableSpace G] in
lemma ik
  (H:bU W)
  {A:Finset G} {p:ℕ} {sigma delta alpha:ℝ} (z:G)
  (data:ah.aW A
   (z+ᵥ H.b6.Zc) H.bu.Zc p sigma delta)
  (cu:delta<1)
  (b8:0≤alpha)
  (dS :
   alpha≤ah.bj A
    (z+ᵥ H.b6.Zc) H.bu.Zc p) :
  alpha/2 ≤
   (data.aX.card:ℝ) /
    (ah.aW.bg A
     (z+ᵥ H.b6.Zc) H.bu.Zc p sigma).card:=by
 let S:Finset G :=
  ah.aW.bg A
   (z+ᵥ H.b6.Zc) H.bu.Zc p sigma
 have vf:S.Nonempty:=by
  simpa[S] using data.gK cu
 have DR:(0:ℝ)<S.card:=by exact_mod_cast vf.card_pos
 have yk :
   ((z+ᵥ H.b6.Zc).card:ℝ) =
    (H.b6.Zc.card:ℝ):=by
  simp
 have Mq :
   alpha*(H.b6.Zc.card:ℝ)≤(data.aX.card:ℝ):=by
  have aQ :
    alpha≤(data.aX.card:ℝ)/(z+ᵥ H.b6.Zc).card :=
   dS.trans data.tz
  rw[yk] at aQ
  have Mr:(0:ℝ)<H.b6.Zc.card:=by
   exact_mod_cast H.b6.aE.card_pos
  exact(Qs Mr).mp aQ
 have Fu :
   S.card≤2*H.b6.Zc.card:=by
  calc
   S.card≤((z+ᵥ H.b6.Zc)-H.bu.Zc).card:=by
    exact Qu
     (ah.aW.oT
      A (z+ᵥ H.b6.Zc) H.bu.Zc p sigma)
   _≤2*H.b6.Zc.card :=
    mH H.b6 H.zy
     H.bu.Zc H.xb H.w8 z
 have EZ:(S.card:ℝ)≤2*(H.b6.Zc.card:ℝ):=by
  exact_mod_cast Fu
 apply(Qs DR).2
 calc
  alpha/2*(S.card:ℝ) ≤
    alpha/2*(2*(H.b6.Zc.card:ℝ)):=by
   exact iO EZ (by positivity)
  _=alpha*(H.b6.Zc.card:ℝ):=by ring
  _≤(data.aX.card:ℝ):=Mq
omit [AddCommGroup G] [DecidableEq G] [DiscreteMeasurableSpace G] [Fintype G] [MeasurableSpace G] in
lemma ou
  {aX S:Finset G} {alpha:ℝ}
  (b8:0<alpha) (fY:aX.Nonempty) (hS:S.Nonempty)
  (eO:alpha/2≤(aX.card:ℝ)/S.card) :
  Real.sqrt ((S.card:ℝ)/aX.card)≤Real.sqrt (2/alpha):=by
 have xx:(0:ℝ)<aX.card:=by exact_mod_cast fY.card_pos
 have DR:(0:ℝ)<S.card:=by exact_mod_cast hS.card_pos
 have hmul:alpha/2*(S.card:ℝ)≤(aX.card:ℝ) :=
  (Qs DR).mp eO
 have hdiv:(S.card:ℝ)/aX.card≤2/alpha:=by
  apply(Sy xx b8).2
  nlinarith
 exact Real.sqrt_le_sqrt hdiv
omit [AddCommGroup G] [DecidableEq G] [DiscreteMeasurableSpace G] [Fintype G] [MeasurableSpace G] in
lemma tN
  (d:ℕ) {rank:ℕ} {aF:NNReal}
  {aX S:Finset G}
  (fY:aX.Nonempty) (hS:S.Nonempty)
  (eO :
   aa.aR d/2 ≤
    (aX.card:ℝ)/S.card)
  (d5 :
   (400*((max rank 1:ℕ):ℝ) *
     (aF+aF:NNReal)) *
    Real.sqrt (2/aa.aR d) ≤
    1/2048) :
  2*aa.cH +
    (2/(aa.bE d:ℝ) +
     400*((max rank 1:ℕ):ℝ) *
      (aF+aF:NNReal) +
     2*(1/2:ℝ)^aa.b1 d) *
    Real.sqrt ((S.card:ℝ)/aX.card)≤(1/512:ℝ):=by
 classical
 have fX:=aa.bP d
 have DC :
   Real.sqrt ((S.card:ℝ)/aX.card) ≤
    Real.sqrt (2/aa.aR d) :=
  ou fX fY hS eO
 have l4 :
   (2/(aa.bE d:ℝ)) *
     Real.sqrt ((S.card:ℝ)/aX.card)≤1/2048:=by
  calc
   (2/(aa.bE d:ℝ)) *
     Real.sqrt ((S.card:ℝ)/aX.card) ≤
    (2/(aa.bE d:ℝ)) *
     Real.sqrt (2/aa.aR d):=by
      gcongr
   _≤1/2048:=aa.m3 d
 have Cq :
   (400*((max rank 1:ℕ):ℝ) *
     (aF+aF:NNReal)) *
    Real.sqrt ((S.card:ℝ)/aX.card)≤1/2048:=by
  calc
   (400*((max rank 1:ℕ):ℝ) *
     (aF+aF:NNReal)) *
    Real.sqrt ((S.card:ℝ)/aX.card) ≤
    (400*((max rank 1:ℕ):ℝ) *
     (aF+aF:NNReal)) *
    Real.sqrt (2/aa.aR d):=by
     gcongr
   _≤1/2048:=d5
 have uU :
   (2*(1/2:ℝ)^aa.b1 d) *
     Real.sqrt ((S.card:ℝ)/aX.card)≤1/2048:=by
  calc
   (2*(1/2:ℝ)^aa.b1 d) *
     Real.sqrt ((S.card:ℝ)/aX.card) ≤
    (2*(1/2:ℝ)^aa.b1 d) *
     Real.sqrt (2/aa.aR d):=by
      gcongr
   _≤1/2048:=aa.pw d
 unfold aa.cH
 nlinarith
def bD (d ax:ℕ):ℕ :=
 8388608*max ax 1 *
  2^(2+2*d*aa.bH d)
def ct (d ax:ℕ):NNReal :=
 ((bD d ax:ℕ):NNReal)⁻¹
lemma jE (d ax:ℕ) :
  0<bD d ax:=by
 unfold bD
 positivity
lemma rb
  (d ax rank:ℕ) (cK:rank≤ax) :
  (400*((max rank 1:ℕ):ℝ) *
    (ct d ax +
     ct d ax:NNReal)) *
   Real.sqrt (2/aa.aR d) ≤
   1/2048:=by
 let e:ℕ:=2+2*d*aa.bH d
 let P:ℕ:=bD d ax
 have Ms:(0:ℝ)<P:=by
  dsimp[P,bD,e]
  positivity
 have lE:max rank 1≤ max ax 1 :=
  Sn 1 cK
 have DC :
   Real.sqrt (2/aa.aR d) ≤
    2/aa.aR d :=
  aa.jj
   (aa.bP d)
   (aa.dZ d)
 have hbound :
   (400*((max rank 1:ℕ):ℝ) *
     (ct d ax +
      ct d ax:NNReal)) *
    Real.sqrt (2/aa.aR d) ≤
   (400*((max rank 1:ℕ):ℝ) *
     (ct d ax +
      ct d ax:NNReal)) *
    (2/aa.aR d):=by
  gcongr
 apply hbound.trans
 unfold ct bD
  aa.aR
 change
  (400*((max rank 1:ℕ):ℝ) *
    (((P:ℕ):ℝ)⁻¹ +((P:ℕ):ℝ)⁻¹)) *
   (2/(1/(2:ℝ)^e))≤1/2048
 have NA:((max rank 1:ℕ):ℝ)≤ max ax 1:=by
  exact_mod_cast lE
 have Im:(0:ℝ)<(2:ℝ)^e:=by positivity
 have Mt :
   (400*((max rank 1:ℕ):ℝ) *
     (((P:ℕ):ℝ)⁻¹ +((P:ℕ):ℝ)⁻¹)) *
    (2/(1/(2:ℝ)^e)) =
   1600*((max rank 1:ℕ):ℝ)*(2:ℝ)^e/P:=by
  field_simp
  ring
 rw[Mt]
 have hP :
   (8388608:ℝ)*(max ax 1:ℕ)*(2:ℝ)^e =
    (P:ℝ):=by
  dsimp[P,bD]
  norm_cast
 rw[←hP]
 have sh:(0:ℝ) <
   (8388608:ℝ)*(max ax 1:ℕ)*(2:ℝ)^e:=by
  positivity
 apply(QF sh).2
 calc
  1600*((max rank 1:ℕ):ℝ)*(2:ℝ)^e ≤
    1600*((max ax 1:ℕ):ℝ)*(2:ℝ)^e:=by
   gcongr
  _≤(1/2048:ℝ) *
    ((8388608:ℝ)*(max ax 1:ℕ)*(2:ℝ)^e):=by
   have wP:(0:ℝ)<(max ax 1:ℕ):=by positivity
   nlinarith
lemma lH
  (d ax rank:ℕ) (cK:rank≤ax) :
  ct d ax+ct d ax ≤
   1/(100*(max rank 1:ℕ):NNReal):=by
 let e:ℕ:=2+2*d*aa.bH d
 let P:ℕ:=bD d ax
 have Ms:(0:ℝ)<P:=by
  dsimp[P,bD,e]
  positivity
 have s9:(0:ℝ)<100*(max rank 1:ℕ):=by positivity
 have lE:max rank 1≤ max ax 1 :=
  Sn 1 cK
 have sB:2*(100*max rank 1)≤P:=by
  dsimp[P,bD]
  have hpow:1≤2^e:=Nat.one_le_pow _ _ (by omega)
  calc
   2*(100*max rank 1)≤200*max ax 1:=by
    omega
   _≤8388608*max ax 1*2^e:=by
    have qI:200≤8388608:=by norm_num
    calc
     200*max ax 1≤8388608*max ax 1 :=
      QQ _ qI
     _≤8388608*max ax 1*2^e :=
      Q4 _ (by positivity)
 have uO :
   (2:ℝ)*(P:ℝ)⁻¹ ≤
    1/(100*(max rank 1:ℕ):ℝ):=by
  have NB:(2:ℝ)*(100*(max rank 1:ℕ))≤P:=by
   exact_mod_cast sB
  field_simp
  linarith
 unfold ct
 change
  ((P:ℕ):NNReal)⁻¹ +((P:ℕ):NNReal)⁻¹ ≤
   1/(100*(max rank 1:ℕ):NNReal)
 have Pn :
   (2:NNReal)*((P:ℕ):NNReal)⁻¹ ≤
    1/(100*(max rank 1:ℕ):NNReal):=by
  exact_mod_cast uO
 simpa[R5] using Pn
omit [DiscreteMeasurableSpace G] in
lemma e5
  (W:aj G) (H:bU W)
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW A aL H.bu.Zc p sigma delta)
  (d k:ℕ)
  (dS :
   aa.aR d ≤
    ah.bj A aL H.bu.Zc p)
  (hk:k≤aa.dC d) :
  ⌈8*(1+Real.log (2 /
   b3 W H data k))⌉₊ ≤
   aa.au d:=by
 let alpha:=aa.aR d
 let K:=aa.dC d
 let DS:=ah.bj A aL H.bu.Zc p
 have fX:0<alpha:=by
  simpa[alpha] using aa.bP d
 have wC:alpha≤1:=by
  simpa[alpha] using aa.dZ d
 have xN:0<DS:=fX.trans_le (by simpa[DS,alpha] using dS)
 have qj:0≤alpha/2:=by positivity
 have xO:alpha/2≤1:=by linarith
 have IK:(alpha/2)^K≤(alpha/2)^k:=by
  have hK:k+(K-k)=K:=Nat.add_sub_of_le hk
  calc
   (alpha/2)^K=(alpha/2)^(k+(K-k)):=by rw[hK]
   _=(alpha/2)^k*(alpha/2)^(K-k):=by rw[RL]
   _≤(alpha/2)^k*1:=by
    exact iO
     (Uy qj xO) (by positivity)
   _=(alpha/2)^k:=by ring
 have GS:(alpha/2)^k≤(DS/2)^k:=by
  apply Qp
  ·positivity
  ·simpa[DS,alpha] using(Qz dS (by norm_num))
 have DT :
   aa.gs alpha K≤b3 W H data k:=by
  unfold aa.gs b3
  exact Qz (IK.trans GS) (by norm_num)
 have NC:0<b3 W H data k:=by
  unfold b3
  positivity
 have Fv:0<aa.gs alpha K :=
  aa.zT fX
 have hdiv :
   2/b3 W H data k ≤
    2/aa.gs alpha K:=by
  exact Rb (by norm_num) Fv DT
 have eu :
   Real.log (2/b3 W H data k) ≤
    Real.log (2/aa.gs alpha K) :=
  QG (by positivity) hdiv
 have za :
   8*(1+Real.log (2/b3 W H data k)) ≤
    8*(1+Real.log (2/aa.gs alpha K)):=by
  nlinarith
 apply Sj (S3 za)
 unfold aa.au aa.ra
 exact le_max_right _ _
omit [DiscreteMeasurableSpace G] in
lemma gR
  (W:aj G) (H:bU W)
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW A aL H.bu.Zc p sigma delta)
  (cu:delta<1)
  (d k:ℕ)
  (dS :
   aa.aR d ≤
    ah.bj A aL H.bu.Zc p)
  (hk:k≤aa.dC d)
  (T:Finset G)
  (hT :
   ((du data.a3^k/2 *
     cq W H) /
     cI W H data.a3^k≤(T.card:ℝ))) :
  aI.bf H.bl T (1/2) ≤
   aa.au d:=by
 have xN :
   0<ah.bj A aL H.bu.Zc p :=
  (aa.bP d).trans_le dS
 have g8:0<b3 W H data k:=by
  unfold b3
  positivity
 have oM:= ot W H data cu k T g8 hT
 have rG :
   8*(1+Real.log (2/b3 W H data k)) ≤
    (⌈8*(1+Real.log (2/b3 W H data k))⌉₊:ℝ) :=
  Rr _
 have cK:=e5 W H data d k dS hk
 have Fw :
   (⌈8*(1+Real.log (2/b3 W H data k))⌉₊:ℝ) ≤
    aa.au d:=by
  exact_mod_cast cK
 exact oM.trans (rG.trans Fw)
omit [DiscreteMeasurableSpace G] in
lemma m6
  (W:aj G) (H:bU W)
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW A aL H.bu.Zc p sigma delta)
  (cu:delta<1)
  (d k ax:ℕ)
  (dS :
   aa.aR d ≤
    ah.bj A aL H.bu.Zc p)
  (hk:k≤aa.dC d)
  (g6:H.bl.rank≤ax)
  (T:Finset G) (Delta:Finset (AddChar G Complex))
  (hT :
   ((du data.a3^k/2 *
     cq W H) /
     cI W H data.a3^k≤(T.card:ℝ)))
  (dQ:(Delta.card:ℝ) ≤
   aI.bf H.bl T (1/2)) :
  (aa.bE d *
    ag.a6
     (aI.bf H.bl T (1/2))) ^
    Delta.card*4^(H.bl.rank+Delta.card) ≤
   aa.dH ax
    (aa.au d)
    (aa.bE d *
     (⌈8*(aa.au d:ℝ)⌉₊+1)):=by
 let dim:=aI.bf H.bl T (1/2)
 have oM:dim≤aa.au d:=by
  simpa[dim] using gR W H data cu d k
   dS hk T hT
 have Fx :
   ag.a6 dim ≤
    ⌈8*(aa.au d:ℝ)⌉₊+1:=by
  unfold ag.a6
  apply RZ
  apply S3
  have lE:max dim 0≤(aa.au d:ℝ) :=
   max_le oM (by positivity)
  have Ai:2*Real.pi≤(8:ℝ):=by
   nlinarith[Real.pi_lt_four]
  calc
   2*Real.pi*max dim 0 ≤
     2*Real.pi*aa.au d:=by
    gcongr
   _≤8*(aa.au d:ℝ):=by
    gcongr
 have hq:0<aa.bE d:=by
  unfold aa.bE
  exact aa.gV (aa.bP d)
 have GU :
   0<ag.a6 dim:=by
  unfold ag.a6
  positivity
 have hn :
   0<aa.bE d *
    ag.a6 dim :=
  QP hq GU
 have Hk :
   aa.bE d *
     ag.a6 dim ≤
    aa.bE d *
     (⌈8*(aa.au d:ℝ)⌉₊+1) :=
  Qr _ Fx
 have xN :
   0<ah.bj A aL H.bu.Zc p :=
  (aa.bP d).trans_le dS
 have g8:0<b3 W H data k:=by
  unfold b3
  positivity
 have DU:Delta.card≤aa.au d:=by
  apply(i5 W H data cu k T Delta
   g8 hT dQ).trans
  exact e5 W H data d k dS hk
 simpa[aa.dH,dim] using
  aa.vB hn Hk g6 DU
lemma i6
  (A aL a0 K:Finset G) (d:ℕ)
  (hK:K.Nonempty)
  (c8:1/(2:ℝ)^d≤(A.card:ℝ)/K.card)
  (oO :
   (65/64:ℝ)*(K.card:ℝ)⁻¹ ≤
    an.aM
     (fun x:G=>(((al ((@mu (ℝ≥0) _ _) aL) (mu a0))) x:ℝ))
     ((al ((@mu (ℝ) _ _) A) (mu A)))
     (aa.bH d)) :
  aa.aR d ≤
   ah.bj A aL a0
    (aa.bH d):=by
 let r:=aa.bH d
 have hr:0<r:=by
  simpa[r] using aa.fU d
 have x7:(0:ℝ)<K.card:=by exact_mod_cast hK.card_pos
 have Bh:(0:ℝ)≤A.card:=by positivity
 have KH:0≤(A.card:ℝ)/K.card:=by positivity
 have AY :
   1/(2:ℝ)^d ≤
    (A.card:ℝ) *
     an.aM
      (fun x:G=>(((al ((@mu (ℝ≥0) _ _) aL) (mu a0))) x:ℝ))
      ((al ((@mu (ℝ) _ _) A) (mu A))) r:=by
  calc
   1/(2:ℝ)^d≤(A.card:ℝ)/K.card:=c8
   _≤(65/64:ℝ)*((A.card:ℝ)/K.card):=by
    nlinarith
   _=(A.card:ℝ)*((65/64:ℝ)*(K.card:ℝ)⁻¹):=by
    field_simp
   _≤(A.card:ℝ) *
     an.aM
      (fun x:G=>(((al ((@mu (ℝ≥0) _ _) aL) (mu a0))) x:ℝ))
      ((al ((@mu (ℝ) _ _) A) (mu A))) r :=
    iO (by simpa[r] using oO) Bh
 have sx :
   aa.aR d =
    (4:ℝ)⁻¹ *(1/(2:ℝ)^d)^(2*r):=by
  unfold aa.aR
  unfold aa.av
  dsimp[r]
  simp only[R6, ←Te,RL,QU]
  field_simp
  have hpow :
    (1/2:ℝ) ^
      (d*aa.bH d*2) *
     (4:ℝ)^(d*aa.bH d)=1:=by
   rw[show d*aa.bH d*2 =
     2*(d*aa.bH d) by omega]
   rw[show(4:ℝ)=(2:ℝ)^2 by norm_num, ←QU]
   rw[R6,Te]
   field_simp
  norm_num[QU,RL] at hpow ⊢
  have Mu :
    (((1/2:ℝ)^d)^aa.bH d)^2 =
     (((1/2:ℝ)^d)^2) ^
      aa.bH d:=by
   conv_lhs =>
    rw[←QU, ←QU]
   conv_rhs =>
    rw[←QU, ←QU]
   congr 1
   simp[R8]
  rw[Mu] at hpow
  nlinarith
 rw[sx,mI A aL a0 hr]
 gcongr
lemma qP (d:ℕ) :
  ((1/8192:ℝ)⁻¹)*Real.log (2/(1/8192:ℝ)) ≤
   aa.bH d:=by
 have Mv:Real.log (2:ℝ)≤1:=by
  convert QX (show(0:ℝ)<2 by norm_num) using 1
  norm_num
 have eu:Real.log (2/(1/8192:ℝ))≤14:=by
  rw[show(2/(1/8192:ℝ))=(2:ℝ)^14 by norm_num,
   QB]
  norm_num at Mv ⊢
  nlinarith
 have kz :
   ((1/8192:ℝ)⁻¹)*Real.log (2/(1/8192:ℝ)) ≤
    (114688:ℝ):=by
  norm_num
  nlinarith
 apply kz.trans
 unfold aa.bH aa.dt
 rw[an.pB]
 norm_num[cP]
 have hd:1≤d+1:=by omega
 norm_num at hd ⊢
 nlinarith
lemma sN :
  (1+(1/8:ℝ)/32) ≤
   (65/64:ℝ)*(1-1/8192) *
    (1-1/8192-1/512):=by
 norm_num
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma rQ
  {original:Finset G} (s:ah.aA original)
  {bn bd:ℕ} (C:c7 s.restriction.ba bn bd)
  {d1:ℝ}
  (aQ:ah.bV s C.ak C.aB d1)
  (bZ:d1<1) :
  (1+(1/8:ℝ)/32) *
    (bB s C.ak C.aB aQ
     bZ).Zd ≤
   ((bB s C.ak C.aB aQ
     bZ).restriction.set.card:ℝ) *
    (((1-(1/8192:ℝ)) *
      ((65/64:ℝ)*(C.ak.ba.Zc.card:ℝ)⁻¹)) *
     (1-(1/8192:ℝ)-(1/512:ℝ))):=by
 let u:=bB s C.ak C.aB aQ bZ
 have x7:(0:ℝ)<C.ak.ba.Zc.card:=by
  exact_mod_cast C.ak.ba.aE.card_pos
 have c8 :
   u.Zd=(u.restriction.set.card:ℝ) /
    C.ak.ba.Zc.card:=by
  simp only[u,bB,ah.hO]
  rw[ah.bk
   C.ak.aE]
  simp[ah.di,ah.bt.en,
   C.eD]
 rw[show(bB s C.ak C.aB aQ
   bZ).Zd=u.Zd by rfl,
  show(bB s C.ak C.aB aQ
   bZ).restriction.set=u.restriction.set by rfl,
  c8]
 have kD:=sN
 have hA:(0:ℝ)≤u.restriction.set.card:=by positivity
 calc
  (1+(1/8:ℝ)/32) *
    ((u.restriction.set.card:ℝ)/C.ak.ba.Zc.card) ≤
   ((65/64:ℝ)*(1-1/8192) *
    (1-1/8192-1/512)) *
     ((u.restriction.set.card:ℝ)/C.ak.ba.Zc.card):=by
   gcongr
  _=(u.restriction.set.card:ℝ) *
    (((1-(1/8192:ℝ)) *
      ((65/64:ℝ)*(C.ak.ba.Zc.card:ℝ)⁻¹)) *
     (1-(1/8192:ℝ)-(1/512:ℝ))):=by
   field_simp
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma m7
  {original:Finset G} (s:ah.aA original)
  {bn bd:ℕ} (C:c7 s.restriction.ba bn bd)
  {d1:ℝ}
  (aQ:ah.bV s C.ak C.aB d1)
  (zX:d1=(1/512:ℝ))
  (bZ:d1<1)
  {d:ℕ} (c3:1/(2:ℝ)^d≤ s.Zd) :
  1/(2:ℝ)^(d+1) ≤
   (bB s C.ak C.aB aQ
    bZ).Zd:=by
 let u:=bB s C.ak C.aB aQ bZ
 have wD:a5 s d1≤u.Zd:=by
  let x:=aO.cr aQ
  have hx:a5 s d1 ≤
    a9 s.restriction.set C.ak.Zc x:=by
   simpa[x,a5] using
    aO.c0 aQ
  simpa[u,bB,ah.hO] using hx
 have iB :
   1/(2:ℝ)^(d+1) ≤
    (1-(1/512:ℝ))*(1/(2:ℝ)^d):=by
  rw[RB]
  have hpow:(0:ℝ)≤(2:ℝ)^d:=by positivity
  field_simp
  nlinarith
 calc
  1/(2:ℝ)^(d+1) ≤
    (1-(1/512:ℝ))*(1/(2:ℝ)^d):=iB
  _≤(1-(1/512:ℝ))*s.Zd:=by gcongr
  _=a5 s d1:=by simp[a5,zX]
  _≤u.Zd:=wD
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma lZ
  {original:Finset G} (s:ah.aA original)
  {d:ℕ} (c3:1/(2:ℝ)^d≤ s.Zd) :
  (2/3:ℝ)^aa.dt (d+1) ≤
   a5 s (1/512:ℝ):=by
 have dc:0≤(2/3:ℝ):=by norm_num
 have xO:(2/3:ℝ)≤1:=by norm_num
 have l5:aa.dt d ≤
   aa.dt (d+1):=by
  unfold aa.dt
  omega
 calc
  (2/3:ℝ)^aa.dt (d+1) ≤
    (2/3:ℝ)^aa.dt d:=by
   exact SJ dc xO l5
  _≤(1-(1/512:ℝ))*s.Zd:=by
   simpa[aa.dt] using
    n0 s c3
  _=a5 s (1/512:ℝ):=by
   simp[a5]
lemma m8
  {vg i9 alpha width:ℝ}
  (r0:0<vg) (ye:0< i9)
  (b8:0<alpha) (wC:alpha≤1)
  (lL:alpha*i9≤vg)
  (d5:width≤alpha/384) (wE:0≤width) :
  2*(vg⁻¹ *width)+i9⁻¹ *width ≤
   (1/64:ℝ)*i9⁻¹ :=by
 have IL:0<alpha*i9:=QM b8 ye
 have PK:vg⁻¹ ≤(alpha*i9)⁻¹ :=
  (RJ r0 IL).2 lL
 have jw:vg⁻¹ *width≤ i9⁻¹ /384:=by
  calc
   vg⁻¹ *width≤(alpha*i9)⁻¹ *width:=by gcongr
   _≤(alpha*i9)⁻¹ *(alpha/384):=by gcongr
   _=i9⁻¹ /384:=by
    field_simp
 have Fy:width≤1/384:=by
  calc
   width≤alpha/384:=d5
   _≤1/384:=by gcongr
 have ud:i9⁻¹ *width≤ i9⁻¹ /384:=by
  simpa[Qw] using
   iO Fy (by positivity:0≤ i9⁻¹)
 calc
  2*(vg⁻¹ *width)+i9⁻¹ *width ≤
    2*(i9⁻¹ /384)+i9⁻¹ /384:=by gcongr
  _≤(1/64:ℝ)*i9⁻¹ :=by
   have L7:0≤ i9⁻¹ :=by positivity
   nlinarith
omit [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma uG
  {original:Finset G} (s:ah.aA original)
  {d aq bn:ℕ}
  (C:c7 s.restriction.ba bn
   (ar.bd (d+1) aq))
  (aQ:ah.bV s C.ak C.aB (1/512:ℝ))
  (c3:1/(2:ℝ)^d≤ s.Zd)
  (cK:s.rank≤ar.ax (d+1) aq)
  (cE:0<aq) :
  2*(((cX s C.ak C.aB aQ).card:ℝ)⁻¹ *
    (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
     (((ar.bd (d+1) aq:NNReal)⁻¹ +
      (ar.bd (d+1) aq:NNReal)⁻¹ :NNReal):ℝ))) +
   (C.ak.ba.Zc.card:ℝ)⁻¹ *
    (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
     (((ar.bd (d+1) aq:NNReal)⁻¹ +
      (ar.bd (d+1) aq:NNReal)⁻¹ :NNReal):ℝ)) ≤
   (1/8:ℝ)/8*(C.ak.ba.Zc.card:ℝ)⁻¹ :=by
 let alpha:ℝ:=(1-(1/512:ℝ))*(1/(2:ℝ)^d)
 let width:ℝ :=
  200*((max C.ak.ba.rank 1:ℕ):ℝ) *
   (((ar.bd (d+1) aq:NNReal)⁻¹ +
    (ar.bd (d+1) aq:NNReal)⁻¹ :NNReal):ℝ)
 have uJ:(cX s C.ak C.aB aQ).Nonempty :=
  pb s C.ak C.aB aQ (by norm_num)
 have Mw:(0:ℝ)<(cX s C.ak C.aB aQ).card:=by
  exact_mod_cast uJ.card_pos
 have x7:(0:ℝ)<C.ak.ba.Zc.card:=by
  exact_mod_cast C.ak.ba.aE.card_pos
 have fX:0<alpha:=by unfold alpha; positivity
 have wC:alpha≤1:=by
  unfold alpha
  have c8:1/(2:ℝ)^d≤1:=by
   have hpow:(1:ℝ)≤(2:ℝ)^d:=RH (by norm_num)
   exact(QF (by positivity)).2 (by simpa using hpow)
  nlinarith
 have lC:alpha ≤
   a9 s.restriction.set C.ak.Zc
    (aO.cr aQ):=by
  calc
   alpha≤(1-(1/512:ℝ))*s.Zd:=by
    unfold alpha
    gcongr
   _=a5 s (1/512:ℝ):=by simp[a5]
   _≤a9 s.restriction.set C.ak.Zc
     (aO.cr aQ):=by
    simpa[a5] using aO.c0 aQ
 have lL:alpha*(C.ak.ba.Zc.card:ℝ) ≤
   (cX s C.ak C.aB aQ).card:=by
  rw[ah.bk
   C.ak.aE] at lC
  have Mx:(0:ℝ)<C.ak.Zc.card:=by
   exact_mod_cast C.ak.aE.card_pos
  simpa[cX,C.eD] using
   (Qs Mx).mp lC
 have wE:0≤width:=by unfold width; positivity
 have d5:width≤alpha/384:=by
  have lE:max C.ak.ba.rank 1 ≤
    ar.ax (d+1) aq:=by
   rw[C.rankOne]
   exact ar.i8 cE cK
  have Hi:(0:ℝ)<ar.bd (d+1) aq:=by
   exact_mod_cast ar.mf cE
  have kR:(0:ℝ)<ar.ax (d+1) aq:=by
   exact_mod_cast ar.iK cE
  have My:((max C.ak.ba.rank 1:ℕ):ℝ) ≤
    ar.ax (d+1) aq:=by exact_mod_cast lE
  have Po:max (C.ak.ba.rank:ℝ) 1 ≤
    ar.ax (d+1) aq:=by
   simpa[Nat.cast_max] using My
  unfold width alpha ar.bd
  simp only[NNReal.coe_add,SE,S9]
  push_cast
  change 200*max (C.ak.ba.rank:ℝ) 1 *
    ((76800*ar.ax (d+1) aq *
     2^(d+1+1):ℝ)⁻¹ +
     (76800*ar.ax (d+1) aq *
     2^(d+1+1):ℝ)⁻¹) ≤
   ((1-1/512)*(1/(2:ℝ)^d))/384
  field_simp
  have hpow:(0:ℝ)<(2:ℝ)^d:=by positivity
  have Mz:(2:ℝ)^(d+1+1)=4*(2:ℝ)^d:=by
   rw[show d+1+1=d+2 by omega,RL]
   norm_num
   ring
  rw[Mz]
  nlinarith
 convert m8 Mw x7 fX wC
   lL d5 wE using 1
 norm_num
open ah in
lemma lI
  {original:Finset G} (s:ah.aA original)
  (W:aj G) (H:bU W)
  {aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW s.restriction.set aL
   H.bu.Zc p sigma delta)
  (hp:0<p)
  (hB:(aL∩H.bu.Zc).Nonempty)
  (cu:delta<1)
  (dv:ℝ) (sF:0<dv)
  (m:ℕ) (hm:m≠0)
  (aF:NNReal)
  (dy:aF+aF ≤
   1/(100*(max H.bl.rank 1:ℕ):NNReal))
  (dh:ℕ) (pT:0<dh)
  (bm aU:ℝ)
  (dV: ∀ (T:Finset G) (Delta:Finset (AddChar G Complex)),
   (Delta.card:ℝ) ≤
    aI.bf H.bl T (1/2) →
   2*dv +
     (2/(dh:ℝ) +
      400*((max H.bl.rank 1:ℕ):ℝ) *
       (aF+aF:NNReal) +
      2*(1/2:ℝ)^m) *
     Real.sqrt
      (((ah.aW.bg
        s.restriction.set aL H.bu.Zc p sigma).card:ℝ) /
       data.aX.card)≤bm)
  {aq bq:ℕ}
  (g6:H.bl.rank≤ s.rank)
  (B3 :
   ⌈8*(1+Real.log (2 /
    b3 W H data
     (ah.cm
      (-(ah.aW.bg
       s.restriction.set aL H.bu.Zc p sigma))
      data.aX dv m)))⌉₊≤aq)
  (DV: ∀ (T:Finset G) (Delta:Finset (AddChar G Complex)),
   ((du data.a3 ^
     (ah.cm
      (-(ah.aW.bg
       s.restriction.set aL H.bu.Zc p sigma))
      data.aX dv m)/2 *
     cq W H) /
     cI W H data.a3 ^
      (ah.cm
       (-(ah.aW.bg
        s.restriction.set aL H.bu.Zc p sigma))
       data.aX dv m)≤(T.card:ℝ)) →
   (Delta.card:ℝ) ≤
    aI.bf H.bl T (1/2) →
   (dh*ag.a6
     (aI.bf H.bl T (1/2))) ^
     Delta.card *
    4^(H.bl.rank+Delta.card)≤bq)
  (pc:0<bq)
  (gL: ∀ (T:Finset G) (a8:NNReal) (fk:aj G)
    (_Delta:Finset (AddChar G Complex)),
   ((du data.a3 ^
     (ah.cm
      (-(ah.aW.bg
       s.restriction.set aL H.bu.Zc p sigma))
      data.aX dv m)/2 *
     cq W H) /
     cI W H data.a3 ^
      (ah.cm
       (-(ah.aW.bg
        s.restriction.set aL H.bu.Zc p sigma))
       data.aX dv m)≤(T.card:ℝ)) →
   1/2≤a8 →
   fk=H.bl.ai (a8 *
    aI.cJ H.bl T (1/2)) →
   Real.exp (-aU)*(s.card:ℝ)*(bq:ℝ) ≤
    ((fk.ai aF).Zc.card:ℝ)) :
  ∃ (parent:aj G) (dR:NNReal)
   (source:Finset G) (pd:ℕ),
   ∃ P:ah.cb data parent
    dR source aq pd bm,
    P.child.rank≤ s.rank+aq ∧
    Real.exp (-aU)*(s.card:ℝ)≤P.child.Zc.card:=by
 obtain ⟨T,X,a8,fk,Delta,nf,ue,pP,dQ,
   gI,lf,oQ,GV⟩ :=
  ei
   data cu dv sF m hm H.bl H.wx
   aF dy dh pT bm dV
 obtain ⟨GV⟩:=GV
 let vr:ℕ :=
  (dh*ag.a6
    (aI.bf H.bl T (1/2))) ^
    Delta.card *
   4^(H.bl.rank+Delta.card)
 let k:ℕ :=
  ah.cm
   (-(ah.aW.bg
    s.restriction.set aL H.bu.Zc p sigma))
   data.aX dv m
 have zf :
   ((du data.a3^k/2 *
     cq W H) /
     cI W H data.a3^k≤(T.card:ℝ)):=by
  simpa[k,du,cq,
   cI,gk] using nf
 have xN :
   0<ah.bj s.restriction.set aL
    H.bu.Zc p :=
  mJ s.restriction.set aL
   H.bu.Zc hp hB s.restriction.nonempty
 have g8 :
   0<b3 W H data k:=by
  unfold b3
  positivity
 have A5:Delta.card≤aq:=by
  apply(i5 W H data cu k T Delta
   g8 zf dQ).trans
  simpa[k] using B3
 have KI:vr≤bq:=by
  simpa[vr] using DV T Delta zf dQ
 let P:=GV.mono A5 KI (le_refl bm)
 have Bi:P.child.rank≤ s.rank+aq:=by
  have pV:=P.rK
  calc
   P.child.rank≤H.bl.rank+aq:=by
    simpa[P,oQ,aj.f6] using pV
   _≤ s.rank+aq:=RZ g6 aq
 have GW :
   Real.exp (-aU)*(s.card:ℝ)*(bq:ℝ) ≤
    ((fk.ai aF).Zc.card:ℝ) :=
  gL T a8 fk Delta zf gI oQ
 have Fz :
   ((fk.ai aF).Zc.card:ℝ) ≤
    (bq:ℝ)*(P.child.Zc.card:ℝ):=by
  have sB :
    (fk.ai aF).Zc.card ≤
     bq*P.child.Zc.card:=by
   exact P.nH
  exact_mod_cast sB
 have FA :
   (bq:ℝ) *
     (Real.exp (-aU)*(s.card:ℝ)) ≤
    (bq:ℝ)*(P.child.Zc.card:ℝ):=by
  calc
   (bq:ℝ) *
     (Real.exp (-aU)*(s.card:ℝ)) =
     Real.exp (-aU)*(s.card:ℝ)*bq:=by ring
   _≤((fk.ai aF).Zc.card:ℝ):=GW
   _≤(bq:ℝ)*(P.child.Zc.card:ℝ):=Fz
 have GX:(0:ℝ)<bq:=by exact_mod_cast pc
 have Bj :
   Real.exp (-aU)*(s.card:ℝ)≤P.child.Zc.card :=
  Uj FA GX
 exact ⟨fk,aF+aF,(fk.ai aF).Zc,
  bq,P,Bi,Bj⟩
lemma jF
  {original:Finset G} (s:ah.aA original)
  (W:aj G) (H:bU W)
  {d:ℕ} (z:G)
  {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW s.restriction.set
   (z+ᵥ H.b6.Zc) H.bu.Zc p sigma delta)
  (hp:0<p)
  (hB:((z+ᵥ H.b6.Zc)∩H.bu.Zc).Nonempty)
  (cu:delta<1)
  (dS :
   aa.aR d ≤
    ah.bj s.restriction.set
     (z+ᵥ H.b6.Zc) H.bu.Zc p)
  (aF:NNReal)
  (dy:aF+aF ≤
   1/(100*(max H.bl.rank 1:ℕ):NNReal))
  (bm aU:ℝ)
  (vC:(1/512:ℝ)≤bm)
  (d5 :
   (400*((max H.bl.rank 1:ℕ):ℝ) *
     (aF+aF:NNReal)) *
    Real.sqrt (2/aa.aR d) ≤
     1/2048)
  {bq:ℕ}
  (g6:H.bl.rank≤ s.rank)
  (DV: ∀ (T:Finset G) (Delta:Finset (AddChar G Complex)),
   ((du data.a3 ^
     (ah.cm
      (-(ah.aW.bg
       s.restriction.set (z+ᵥ H.b6.Zc)
        H.bu.Zc p sigma))
      data.aX aa.cH
       (aa.b1 d))/2 *
     cq W H) /
     cI W H data.a3 ^
      (ah.cm
       (-(ah.aW.bg
        s.restriction.set (z+ᵥ H.b6.Zc)
         H.bu.Zc p sigma))
       data.aX aa.cH
        (aa.b1 d))≤(T.card:ℝ)) →
   (Delta.card:ℝ) ≤
    aI.bf H.bl T (1/2) →
   (aa.bE d *
     ag.a6
      (aI.bf H.bl T (1/2))) ^
     Delta.card *
    4^(H.bl.rank+Delta.card)≤bq)
  (pc:0<bq)
  (gL: ∀ (T:Finset G) (a8:NNReal) (fk:aj G)
    (_Delta:Finset (AddChar G Complex)),
   ((du data.a3 ^
     (ah.cm
      (-(ah.aW.bg
       s.restriction.set (z+ᵥ H.b6.Zc)
        H.bu.Zc p sigma))
      data.aX aa.cH
       (aa.b1 d))/2 *
     cq W H) /
     cI W H data.a3 ^
      (ah.cm
       (-(ah.aW.bg
        s.restriction.set (z+ᵥ H.b6.Zc)
         H.bu.Zc p sigma))
       data.aX aa.cH
        (aa.b1 d))≤(T.card:ℝ)) →
   1/2≤a8 →
   fk=H.bl.ai (a8 *
    aI.cJ H.bl T (1/2)) →
   Real.exp (-aU)*(s.card:ℝ)*(bq:ℝ) ≤
    ((fk.ai aF).Zc.card:ℝ)) :
  ∃ (parent:aj G) (dR:NNReal)
   (source:Finset G) (pd:ℕ),
   ∃ P:ah.cb data parent
    dR source (aa.au d)
     pd bm,
    P.child.rank≤ s.rank+aa.au d ∧
    Real.exp (-aU)*(s.card:ℝ)≤P.child.Zc.card:=by
 let S:Finset G :=
  ah.aW.bg s.restriction.set
   (z+ᵥ H.b6.Zc) H.bu.Zc p sigma
 let k:ℕ :=
  ah.cm (-S) data.aX
   aa.cH
   (aa.b1 d)
 have fX:=aa.bP d
 have eO :
   aa.aR d/2 ≤
    (data.aX.card:ℝ)/(-S).card:=by
  simpa[S] using
   ik H z data cu
    (aa.bP d).le dS
 have vh :
   0<aa.b1 d:=by
  unfold aa.b1
  exact aa.sK
   (aa.bP d)
   (aa.dZ d)
 have hk :
   k≤aa.dC d:=by
  dsimp[k]
  unfold aa.dC
  exact aa.ig
   (-S) data.aX fX
   (aa.i3 d) eO vh
 have dV :
   ∀ (T:Finset G) (Delta:Finset (AddChar G Complex)),
   (Delta.card:ℝ) ≤
    aI.bf H.bl T (1/2) →
   2*aa.cH +
     (2/(aa.bE d:ℝ) +
      400*((max H.bl.rank 1:ℕ):ℝ) *
       (aF+aF:NNReal) +
      2*(1/2:ℝ)^aa.b1 d) *
     Real.sqrt
      (((ah.aW.bg
        s.restriction.set (z+ᵥ H.b6.Zc)
        H.bu.Zc p sigma).card:ℝ) /
       data.aX.card)≤bm:=by
  intro T Delta dQ
  have gM:=data.lO cu
  have vf:S.Nonempty:=by
   simpa[S] using data.gK cu
  apply(tN d gM.1 vf
   (by simpa[S] using eO) d5).trans
  exact vC
 apply lI s W H data hp hB cu
  aa.cH
  aa.ny
  (aa.b1 d) vh.ne'
  aF dy (aa.bE d)
  (by
   unfold aa.bE
   exact aa.gV fX)
  bm aU dV g6
 ·simpa[k,S] using
   e5 W H data d k dS hk
 ·exact DV
 ·exact pc
 ·exact gL
omit [DecidableEq G] [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma mK
  (B:aj G) (source:Finset G) {a8:NNReal}
  (P:ℕ) (hP:0<P)
  (jL:((P:NNReal)⁻¹)≤a8)
  {mm d2 aU:ℝ} {bq:ℕ}
  (nD:0≤d2)
  (dc:mm≤d2*(B.Zc.card:ℝ))
  (gL:source=(B.ai a8).Zc)
  (n8 :
   Real.exp (-aU)*d2 *
     (((3*P)^B.rank:ℕ):ℝ)*(bq:ℝ)≤1) :
  Real.exp (-aU)*mm*(bq:ℝ) ≤
   (source.card:ℝ):=by
 classical
 have B4 :
   B.Zc.card≤(3*P)^B.rank*source.card:=by
  rw[gL]
  exact aa.f5
   B P hP jL
 have GY :
   (B.Zc.card:ℝ) ≤
    (((3*P)^B.rank:ℕ):ℝ)*(source.card:ℝ):=by
  exact_mod_cast B4
 have KW :
   mm≤d2 *
     (((3*P)^B.rank:ℕ):ℝ)*(source.card:ℝ):=by
  calc
   mm≤d2*(B.Zc.card:ℝ):=dc
   _≤d2 *
     ((((3*P)^B.rank:ℕ):ℝ)*(source.card:ℝ)) :=
    iO GY nD
   _=d2*(((3*P)^B.rank:ℕ):ℝ) *
     (source.card:ℝ):=by ring
 calc
  Real.exp (-aU)*mm*(bq:ℝ) ≤
    Real.exp (-aU) *
     (d2*(((3*P)^B.rank:ℕ):ℝ) *
      (source.card:ℝ))*(bq:ℝ):=by
       gcongr
  _=(Real.exp (-aU)*d2 *
     (((3*P)^B.rank:ℕ):ℝ)*(bq:ℝ)) *
     (source.card:ℝ):=by ring
  _≤1*(source.card:ℝ) :=
   Qi n8 (by positivity)
  _=(source.card:ℝ):=by ring
omit [DecidableEq G] [DiscreteMeasurableSpace G] [MeasurableSpace G] in
lemma mL
  (H:bU W) (d ax:ℕ)
  (T:Finset G) (a8:NNReal) (fk:aj G)
  (jL:1/2≤a8)
  (oQ:fk=H.bl.ai (a8 *
   aI.cJ H.bl T (1/2)))
  {mm d2 aU:ℝ} {bq:ℕ}
  (nD:0≤d2)
  (dc:mm≤d2*(H.bl.Zc.card:ℝ))
  (n8 :
   Real.exp (-aU)*d2 *
     (((3*aa.bx H.bl.rank
       (aI.dg H.bl T (1/2))
       (bD d ax))^H.bl.rank:ℕ):ℝ) *
      (bq:ℝ)≤1) :
  Real.exp (-aU)*mm*(bq:ℝ) ≤
   ((fk.ai (ct d ax)).Zc.card:ℝ):=by
 classical
 let m:=bD d ax
 let P:=aa.bx H.bl.rank
  (aI.dg H.bl T (1/2)) m
 have hm:0< m:=by
  simpa[m] using jE d ax
 have hP:0<P:=by
  exact aa.kd hm
 have c3 :
   ((P:NNReal)⁻¹) ≤
    a8*aI.cJ H.bl T (1/2) *
     (m:NNReal)⁻¹ :=by
  simpa[P] using
   aa.i4
    H.bl T (1/2) m hm a8 jL
 have GZ :
   (fk.ai (ct d ax)).Zc =
    (H.bl.ai
     (a8*aI.cJ H.bl T (1/2) *
      (m:NNReal)⁻¹)).Zc:=by
  rw[oQ]
  simp[ct,m,aj.vl,
   Qx,Q6]
 apply mK
  (a8:=a8*aI.cJ H.bl T (1/2) *
  (m:NNReal)⁻¹)
  H.bl (fk.ai (ct d ax)).Zc P hP
 ·exact c3
 ·exact nD
 ·exact dc
 ·exact GZ
 ·simpa[P,m] using n8
def jG (d:ℕ):ℕ :=
 aa.bE d *
  (⌈8*(aa.au d:ℝ)⌉₊+1)
def cB (d ax:ℕ):ℕ :=
 aa.dH ax
  (aa.au d) (jG d)
def bY (d ax:ℕ):ℕ :=
 aa.bx ax
  (aa.au d+1)
  (bD d ax)
lemma vD (d:ℕ):0<jG d:=by
 unfold jG
 have hq:0<aa.bE d:=by
  unfold aa.bE
  exact aa.gV (aa.bP d)
 positivity
lemma sO (d ax:ℕ) :
  0<cB d ax:=by
 unfold cB aa.dH
 have hn:=vD d
 positivity
omit [DiscreteMeasurableSpace G] in
lemma nE
  (W:aj G) (H:bU W)
  {A aL:Finset G} {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW A aL H.bu.Zc p sigma delta)
  (cu:delta<1)
  (d k:ℕ)
  (dS :
   aa.aR d ≤
    ah.bj A aL H.bu.Zc p)
  (hk:k≤aa.dC d)
  (T:Finset G)
  (hT :
   ((du data.a3^k/2 *
     cq W H) /
     cI W H data.a3^k≤(T.card:ℝ))) :
  aI.dg H.bl T (1/2) ≤
   aa.au d+1:=by
 unfold aI.dg
 apply RZ
 apply Nat.ceil_le.mpr
 exact gR W H data cu d k
  dS hk T hT
lemma il
  {original:Finset G} (s:ah.aA original)
  (W:aj G) (H:bU W)
  {d:ℕ} (z:G)
  {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW s.restriction.set
   (z+ᵥ H.b6.Zc) H.bu.Zc p sigma delta)
  (hp:0<p)
  (hB:((z+ᵥ H.b6.Zc)∩H.bu.Zc).Nonempty)
  (cu:delta<1)
  (dS :
   aa.aR d ≤
    ah.bj s.restriction.set
     (z+ᵥ H.b6.Zc) H.bu.Zc p)
  (ax:ℕ)
  (B5:H.bl.rank≤ s.rank)
  (g6:H.bl.rank≤ax)
  {d2 c9:ℝ}
  (nD:0≤d2)
  (dc:(s.card:ℝ)≤d2*(H.bl.Zc.card:ℝ))
  (n8 :
   Real.exp (-c9)*d2 *
     (((3*bY d ax)^ax:ℕ):ℝ) *
      (cB d ax:ℝ)≤1) :
  ∃ (parent:aj G) (dR:NNReal)
   (source:Finset G) (pd:ℕ),
   ∃ P:ah.cb data parent
    dR source (aa.au d)
     pd (1/512:ℝ),
    P.child.rank≤ s.rank+aa.au d ∧
    Real.exp (-c9)*(s.card:ℝ)≤P.child.Zc.card:=by
 let S:Finset G :=
  ah.aW.bg s.restriction.set
   (z+ᵥ H.b6.Zc) H.bu.Zc p sigma
 let k:ℕ:=ah.cm (-S) data.aX
  aa.cH (aa.b1 d)
 have fX:=aa.bP d
 have eO :
   aa.aR d/2 ≤
    (data.aX.card:ℝ)/(-S).card:=by
  simpa[S] using ik H z data cu
   fX.le dS
 have vh:0<aa.b1 d:=by
  unfold aa.b1
  exact aa.sK fX
   (aa.dZ d)
 have hk:k≤aa.dC d:=by
  dsimp[k]
  unfold aa.dC
  exact aa.ig
   (-S) data.aX fX (aa.i3 d)
   eO vh
 apply jF s W H z data hp hB cu
  dS (ct d ax)
  (lH d ax H.bl.rank g6)
  (1/512:ℝ) c9 (SF)
  (rb d ax H.bl.rank g6)
  B5
 ·intro T Delta hT dQ
  simpa[cB,jG,k,S] using
   m6 W H data cu d k ax
    dS hk g6 T Delta (by simpa[k,S] using hT) dQ
 ·exact sO d ax
 ·intro T a8 fk Delta hT gI oQ
  have o8 :
    aI.dg H.bl T (1/2) ≤
     aa.au d+1 :=
   nE W H data cu d k dS hk T
    (by simpa[k,S] using hT)
  have hP :
    aa.bx H.bl.rank
      (aI.dg H.bl T (1/2))
      (bD d ax) ≤
     bY d ax:=by
   unfold bY aa.bx
   have lE:max H.bl.rank 1≤ max ax 1 :=
    Sn 1 g6
   gcongr
  have hpow :
    (3*aa.bx H.bl.rank
      (aI.dg H.bl T (1/2))
      (bD d ax))^H.bl.rank ≤
     (3*bY d ax)^ax:=by
   calc
    (3*aa.bx H.bl.rank
      (aI.dg H.bl T (1/2))
      (bD d ax))^H.bl.rank ≤
     (3*bY d ax)^H.bl.rank:=by
      apply R4
      gcongr
    _≤(3*bY d ax)^ax:=by
     apply QR
     ·have IM:0<bY d ax:=by
       unfold bY
       exact aa.kd
        (jE d ax)
      exact QP (by norm_num) IM
     ·exact g6
  have xC :
    Real.exp (-c9)*d2 *
     (((3*aa.bx H.bl.rank
       (aI.dg H.bl T (1/2))
       (bD d ax))^H.bl.rank:ℕ):ℝ) *
      (cB d ax:ℝ)≤1:=by
   apply Sj ?_ n8
   gcongr
  exact mL H d ax T a8 fk
   gI oQ nD dc xC
theorem gW
    {original : Finset G} (s : ah.aA original)
    {D E : Finset G}
    (hD : D.Nonempty) (hE : E.Nonempty)
    {epsilon sigma delta bm fx aU : ℝ}
    {aq r : ℕ}
    (eM : 0 < epsilon)
    (iX : 0 < sigma) (qQ : sigma ≤ 1)
    (cu : 0 < delta) (wF : delta < 1)
    (hr : 0 < r) (Bk : Even r) (DW : 2 ≤ r)
    (Bl : sigma⁻¹ * Real.log (2 / delta) ≤ r)
    (rR : 0 ≤ fx)
    (mx : fx ≤
      an.aM
        ((↑) ∘ aN.bh D E)
        ((_root_.al ((@_root_.mu (ℝ) _ _) s.restriction.set) (_root_.mu s.restriction.set))) r)
    (DX :
      (1 + epsilon / 32) * s.Zd ≤
        (s.restriction.set.card : ℝ) *
          (((1 - sigma) * fx) *
            (1 - delta - bm)))
    (pe :
      ∀ (z : G), z ∈ D - E → ((z +ᵥ E) ∩ D).Nonempty →
        fx ≤
          (_root_.b0 r ((_root_.al (_root_.mu (z +ᵥ E)) (_root_.mu D))) ((_root_.al ((@_root_.mu (ℝ) _ _) s.restriction.set) (_root_.mu s.restriction.set)))) →
        ∀ data : ah.aW s.restriction.set
            (z +ᵥ E) D r sigma delta,
          ∃ (parent : aj G) (dR : NNReal)
            (source : Finset G) (bq : ℕ),
            ∃ P : ah.cb data parent
              dR source aq bq bm,
              P.child.rank ≤ s.rank + aq ∧
              Real.exp (-aU) * (s.card : ℝ) ≤ P.child.Zc.card) :
    ∃ t : bA.aG original,
      br.dk (1 + epsilon / 32) aq aU
        s.restriction t.aV.restriction := by
  obtain ⟨z, hz, ui, rS⟩ :=
    ah.lB hD hE
      s.restriction.nonempty hr rR mx
  let aL : Finset G := z +ᵥ E
  let a0 : Finset G := D
  have hB : (aL ∩ a0).Nonempty := by
    simpa [aL, a0] using ui
  obtain ⟨data⟩ :=
    ah.kJ
      (A := s.restriction.set) (p := r) (epsilon := sigma) (delta := delta)
      aL a0 iX qQ cu Bk DW Bl hB
      s.restriction.nonempty
  obtain ⟨parent, dR, source, bq, P, Bi, Bj⟩ :=
    pe z hz (by simpa [aL, a0] using ui)
      (by simpa [aL, a0] using rS)
      (by simpa [aL, a0] using data)
  have gM := data.lO wF
  let S : Finset G :=
    ah.aW.bg
      s.restriction.set aL a0 r sigma
  have ft :
      1 - delta - bm ≤
        ag.bC
          (ag.d9
            (ag.aS P.child.Zc)
            (ag.a2
              (ag.aS data.aX)
              (ag.aS data.a3)))
          (ag.bJ S) := by
    exact ah.nh gM.1 gM.2
      (by
        simpa only [ah.ca]
          using data.ni)
      (by simpa [S] using P.oU)
  have oV : 0 ≤ (1 - sigma) * fx :=
    mul_nonneg (sub_nonneg.mpr qQ) rR
  have sD : ∀ x ∈ S,
      (1 - sigma) * fx ≤
        ((_root_.al ((@_root_.mu (ℝ) _ _) s.restriction.set) (_root_.mu s.restriction.set))) x := by
    intro x hx
    have xA : x ∈ _root_.s r sigma aL a0 s.restriction.set := by
      have FB := hx
      change x ∈ _root_.s r sigma aL a0 s.restriction.set ∩ (aL - a0) at FB
      exact (Finset.mem_inter.mp FB).1
    have FC :
        (1 - sigma) *
            (_root_.b0 r ((_root_.al (_root_.mu aL) (_root_.mu a0))) ((_root_.al ((@_root_.mu (ℝ) _ _) s.restriction.set) (_root_.mu s.restriction.set)))) <
          ((_root_.al ((@_root_.mu (ℝ) _ _) s.restriction.set) (_root_.mu s.restriction.set))) x :=
      (I7.mp xA)
    exact (mul_le_mul_of_nonneg_left rS
      (sub_nonneg.mpr qQ)).trans FC.le
  have rI : ∀ x, 0 ≤
      ((_root_.al ((@_root_.mu (ℝ) _ _) s.restriction.set) (_root_.mu s.restriction.set))) x := by
    intro x
    exact dM cC cC x
  obtain ⟨x, hx⟩ :=
    ah.jx
      P.child.aE gM.1 gM.2 s.restriction.nonempty
      oV rI sD ft
      (show ((1 - sigma) * fx) * (1 - delta - bm) ≤
          ((1 - sigma) * fx) * (1 - delta - bm) from le_rfl)
  obtain ⟨child, yA, B6, vs⟩ :=
    ah.bt.n7 P.child P.k2
  have FB :
      (1 + epsilon / 32) * s.Zd ≤
        a9 s.restriction.set child.Zc x := by
    rw [vs]
    exact DX.trans hx
  have gw : 0 < a9 s.restriction.set child.Zc x :=
    (mul_pos (by nlinarith [eM]) s.dI).trans_le FB
  let t := ah.di s child x gw
  refine ⟨{ aV := t, fS := ?_, iJ := ?_ }, ?_⟩
  · simpa [t, ah.di, ah.bt.en]
      using B6
  · simpa [t, ah.di, ah.bt.en,
      yA] using P.k2
  · apply ah.fa s child x gw FB
    · simpa [yA] using Bi
    · simpa [vs] using Bj
lemma gq
  {original:Finset G} (s:ah.aA original)
  {bn bd:ℕ} (C:c7 s.restriction.ba bn bd)
  {d1:ℝ}
  (aQ:ah.bV s C.ak C.aB d1)
  (bZ:d1<1)
  {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty)
  {epsilon sigma delta bm fx eb
   c9:ℝ} {aq r:ℕ}
  (eM:0<epsilon)
  (iX:0<sigma) (qQ:sigma≤1)
  (cu:0<delta) (wF:delta<1)
  (hr:0<r) (Bk:Even r) (DW:2≤r)
  (Bl:sigma⁻¹ *Real.log (2/delta)≤r)
  (rR:0≤fx)
  (jw :
   Real.exp (-eb)*(s.card:ℝ)≤C.ak.Zc.card)
  (mx:fx ≤
   an.aM
    ((↑) ∘ aN.bh D E)
    ((al ((@mu Real _ _)
     (bB s C.ak C.aB aQ bZ).restriction.set) (mu (bB s C.ak C.aB aQ bZ).restriction.set)))
    r)
  (DX :
   (1+epsilon/32) *
     (bB s C.ak C.aB aQ
      bZ).Zd ≤
    ((bB s C.ak C.aB aQ
      bZ).restriction.set.card:ℝ) *
     (((1-sigma)*fx) *
      (1-delta-bm)))
  (pe :
   ∀ (z:G),z∈D-E→((z+ᵥ E)∩D).Nonempty →
    fx ≤
     (b0 r ((al (mu (z+ᵥ E)) (mu D))) ((al ((@mu (ℝ) _ _)
       (bB s C.ak C.aB aQ
        bZ).restriction.set) (mu (bB s C.ak C.aB aQ
        bZ).restriction.set)))) →
    ∀ data:ah.aW
      (bB s C.ak C.aB aQ
       bZ).restriction.set
      (z+ᵥ E) D r sigma delta,
     ∃ (parent:aj G) (dR:NNReal)
      (source:Finset G) (bq:Nat),
      ∃ P:ah.cb data parent
       dR source aq bq bm,
       P.child.rank ≤
        (bB s C.ak C.aB aQ
         bZ).rank+aq ∧
       Real.exp (-c9) *
         ((bB s C.ak C.aB aQ
          bZ).card:ℝ)≤P.child.Zc.card) :
  ∃ t:bA.aG original,
   (1+epsilon/32)*a5 s d1≤t.Zd ∧
   t.rank≤ s.rank+aq ∧
   Real.exp (-(eb+c9))*(s.card:ℝ) ≤
    (t.card:ℝ):=by
 let u:=bB s C.ak C.aB aQ bZ
 obtain ⟨t,ht⟩ :=
  gW u hD hE eM
   iX qQ cu wF hr Bk DW Bl rR
   (by simpa[u] using mx) (by simpa[u] using DX)
   (by simpa[u] using pe)
 have wD:a5 s d1≤u.Zd:=by
  let x:=aO.cr aQ
  have hx:a5 s d1 ≤
    a9 s.restriction.set C.ak.Zc x:=by
   simpa[x,a5] using
    aO.c0 aQ
  simpa[u,bB,ah.hO] using hx
 have IN :
   Real.exp (-eb)*(s.card:ℝ)≤(u.card:ℝ):=by
  change Real.exp (-eb)*(s.card:ℝ) ≤
   (C.ak.Zc.card:ℝ)
  exact jw
 refine ⟨t, ?_, ?_, ?_⟩
 ·exact(iO wD (by nlinarith)).trans ht.1
 ·have Bm:u.rank=s.rank:=by
   simpa[u,bB,ah.aA.rank,
    br.aY.rank,
    ah.di,ah.bt.en]
    using C.rankOne
  rw[←Bm]
  exact ht.2.1
 ·calc
   Real.exp (-(eb+c9))*(s.card:ℝ) =
     Real.exp (-c9) *
      (Real.exp (-eb)*(s.card:ℝ)):=by
    rw[show-(eb+c9) =
      -c9+ -eb by ring,R7]
    ring
   _≤Real.exp (-c9)*(u.card:ℝ) :=
    iO IN (Q1 _).le
   _≤(t.card:ℝ):=ht.2.2
end xM
section IP
def es (K:aj G) (A:Finset G):G→ℝ :=
 (Fintype.card G:ℝ) •
  ao ((@mu (ℝ) _ _) A-mu K.Zc) (mu A-mu K.Zc)
lemma m9
  {original:Finset G} (s:ah.aA original)
  {bn bd:ℕ} (C:c7 s.restriction.ba bn bd)
  {epsilon:ℝ}
  (aQ:ah.bV s C.ak C.aB epsilon)
  (b2:epsilon<1)
  (dy :
   (bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ ≤
    1/(100*(max C.ak.ba.rank 1:ℕ):NNReal))
  (d5 :
   2*(((cX s C.ak C.aB aQ).card:ℝ)⁻¹ *
     (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
      (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ))) +
    (C.ak.ba.Zc.card:ℝ)⁻¹ *
     (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
      (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ)) ≤
    (1/8:ℝ)/8*(C.ak.ba.Zc.card:ℝ)⁻¹) :
  |(aO.bb
     (cX s C.ak C.aB aQ)
     (jD s C.ak C.aB aQ) -
    (Fintype.card G:ℝ)/(#C.ak.Zc:ℝ)) -
    aw.Zp
     (es C.ak.ba
      (cX s C.ak C.aB aQ))
     (aO.a4
      (jD s C.ak C.aB aQ))| ≤
   ((Fintype.card G:ℝ)/(#C.ak.Zc:ℝ))/8:=by
 let alpha:=a5 s epsilon
 have b8:0<alpha :=
  QM (sub_pos.mpr b2) s.dI
 have lC:alpha ≤
   a9 s.restriction.set C.ak.Zc
    (aO.cr aQ):=by
  simpa[alpha,a5] using
   aO.c0 aQ
 have oW:alpha ≤
   a9 s.restriction.set C.aB.Zc
    (aO.cr aQ):=by
  simpa[alpha,a5] using
   aO.ea aQ
 have hA :
   (cX s C.ak C.aB aQ).Nonempty:=by
  apply ah.bK
   C.ak.aE
  exact b8.trans_le lC
 have gN :
   (jD s C.ak C.aB aQ).Nonempty:=by
  apply ah.bK
   C.aB.aE
  exact b8.trans_le oW
 have lL :
   cX s C.ak C.aB aQ ⊆
    C.ak.ba.Zc:=by
  rw[←C.eD]
  exact ah.dz
   (B:=C.ak.ba) (a8:=C.ak.outer)
   (A:=s.restriction.set) (C:=C.ak.Zc)
   (x:=aO.cr aQ) (fun _ hz↦hz)
 have rY :
   jD s C.ak C.aB aQ⊆C.aB.Zc:=by
  exact ah.dz
   (B:=C.aB.ba) (a8:=C.aB.outer)
   (A:=s.restriction.set) (C:=C.aB.Zc)
   (x:=aO.cr aQ) (fun _ hz↦hz)
 have dV :
   aO.a4
     (jD s C.ak C.aB aQ) ⊆
    (C.ak.ba.ai
     ((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹)).Zc :=
  (aO.qE rY).trans C.kT
 have h :=
  pF.e4
   C.ez dy hA lL gN dV d5
 simpa[es,C.eD] using h
lemma kh
    {original:Finset G}
    (s:bA.aG original)
    {bn bd:ℕ} (eH:0<bn) (fw:0<bd)
    (C:c7 s.aV.restriction.ba bn bd)
    {epsilon aU:ℝ} {aq p:ℕ}
    (kD:gj s.aV bn bd epsilon aU)
    (aQ:ah.bV s.aV
      (bF
        (aq:=aq) s eH fw C kD).ak
      (bF
        (aq:=aq) s eH fw C kD).aB epsilon)
    (b2:epsilon<1)
    (W:aj G) (u6:W.a1)
    (kx :
      W.Zc=aO.a4 C.aB.Zc)
    {eta:ℝ≥0} (fC:0<eta)
    (ve :
      4*eta≤1/(400*(max W.rank 1:ℕ):ℝ≥0))
    {D E:Finset G} (hD:D.Nonempty) (hE:E.Nonempty)
    (gp:D⊆(W.ai eta).Zc)
    (lh:E⊆(W.ai eta).Zc)
    {aF:ℝ≥0}
    (Bn :
      aF=(bd:NNReal)⁻¹ +(bd:NNReal)⁻¹)
    (dy :
      aF ≤
        1/(100*(max C.ak.ba.rank 1:ℕ):ℝ≥0))
    (kF :
      ∀ t,aN.bh D E t≠0 →
        t∈(C.ak.ba.ai aF).Zc)
    (d5 :
      2*(((cX s.aV C.ak C.aB aQ).card:ℝ)⁻¹ *
          (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
            (aF:ℝ))) +
        (C.ak.ba.Zc.card:ℝ)⁻¹ *
          (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
            (aF:ℝ)) ≤
        (1/8:ℝ)/8*(C.ak.ba.Zc.card:ℝ)⁻¹)
    (jy :
      (2/3:ℝ)^p ≤
        aO.a5 s.aV epsilon)
    (mx :
      (1+(1/8:ℝ)/8) *
          (C.ak.ba.Zc.card:ℝ)⁻¹ ≤
          an.aM
            ((↑) ∘ aN.bh D E)
            ((al ((@mu (ℝ) _ _) (bA.a7 aQ)) (mu (bA.a7 aQ))))
            (an.cz (1/8:ℝ) p) →
        ∃ t:bA.aG original,
          (257/256:ℝ) *
              aO.a5 s.aV epsilon≤t.Zd ∧
          t.rank≤ s.rank+aq ∧
          Real.exp (-aU)*(s.card:ℝ)≤(t.card:ℝ)) :
    Nonempty
      (bA.eS (p:=p) s
        (bF
          (aq:=aq) s eH fw C kD) aQ):=by
  let P:=bF
    (aq:=aq) s eH fw C kD
  change ah.bV s.aV C.ak C.aB epsilon at aQ
  have md :
      (bA.a7 aQ).Nonempty:=by
    simpa[bA.a7,cX] using
      pb s.aV C.ak C.aB aQ b2
  have IQ :
      bA.a7 aQ⊆C.ak.ba.Zc:=by
    rw[←C.eD]
    simpa[bA.a7,cX] using
      qO s.aV C.ak C.aB aQ
  have ew :
      |(aO.bb
            (bA.a7 aQ)
            (bA.d3 aQ) -
          (Fintype.card G:ℝ)/(#C.ak.Zc:ℝ)) -
          aw.Zp
            (bA.es C.ak.ba
              (bA.a7 aQ))
            (aO.a4
              (bA.d3 aQ))| ≤
        ((Fintype.card G:ℝ)/(#C.ak.Zc:ℝ))/8:=by
    have IS :
        (bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ ≤
          1/(100*(max C.ak.ba.rank 1:ℕ):NNReal):=by
      simpa[Bn] using dy
    have Bo :
        2*(((cX s.aV C.ak C.aB aQ).card:ℝ)⁻¹ *
            (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
              (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ))) +
          (C.ak.ba.Zc.card:ℝ)⁻¹ *
            (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
              (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ)) ≤
          (1/8:ℝ)/8*(C.ak.ba.Zc.card:ℝ)⁻¹ :=by
      simpa[Bn] using d5
    simpa[bA.a7,
      bA.d3,cX,jD,
      bA.es,es] using
      m9 s.aV C aQ b2
        IS Bo
  exact ⟨{
    base:=C.ak.ba
    weight:=W
    wd:=C.ez
    uu:=u6
    we:=by
      change C.ak.ba.Zc=C.ak.Zc
      exact C.eD.symm
    uv:=kx
    ro:=md
    te:=IQ
    eta:=eta
    ux:=fC
    mD:=ve
    D:=D
    E:=E
    yp:=hD
    yq:=hE
    rW:=gp
    rX:=lh
    aF:=aF
    yr:=dy
    rp:=kF
    uy:=d5
    vn:=jy
    e6:=ew
    qJ:=mx }⟩
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
lemma iE
    {original:Finset G}
    (s:bA.aG original)
    {d ax bn bd:ℕ}
    (eH:0<bn) (fw:0<bd)
    (C:c7 s.aV.restriction.ba bn bd)
    {eb c9:ℝ}
    (kD:gj s.aV bn bd (1/512:ℝ)
      (eb+c9))
    (jw :
      Real.exp (-eb)*(s.card:ℝ)≤C.ak.Zc.card)
    (aQ:ah.bV s.aV
      (bF
        (aq:=aa.au (d+1))
        s eH fw C kD).ak
      (bF
        (aq:=aa.au (d+1))
        s eH fw C kD).aB (1/512:ℝ))
    (c3:1/(2:ℝ)^d≤ s.Zd)
    (W:aj G) (u6:W.a1)
    (kx:W.Zc=aO.a4 C.aB.Zc)
    (wB:W.Zc.card=C.aB.Zc.card)
    (yB:W.rank=s.rank)
    (H:bU W)
    (jH:s.rank≤ax)
    (dy :
      (bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ ≤
        1/(100*(max C.ak.ba.rank 1:ℕ):NNReal))
    (d5 :
      2*(((cX s.aV C.ak C.aB aQ).card:ℝ)⁻¹ *
          (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
            (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ))) +
        (C.ak.ba.Zc.card:ℝ)⁻¹ *
          (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
            (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ)) ≤
        (1/8:ℝ)/8*(C.ak.ba.Zc.card:ℝ)⁻¹)
    (sP :
      Real.exp (-c9) *
          ((bI s.aV.restriction.ba bn bd *
            b7 W:ℕ):ℝ) *
          (((3*bY (d+1) ax)^ax:ℕ):ℝ) *
            (cB (d+1) ax:ℝ)≤1) :
    Nonempty (bA.eS
      (p:=aa.dt (d+1)) s
      (bF
        (aq:=aa.au (d+1))
        s eH fw C kD) aQ):=by
  change ah.bV s.aV C.ak C.aB
    (1/512:ℝ) at aQ
  let u:=bB s.aV C.ak C.aB aQ (by norm_num)
  have uF:=mi W H
  have xd:H.bl.rank=s.rank:=uF.2.2.trans yB
  have Bp:H.bl.rank≤ax:=by rw[xd]; exact jH
  have Bm:u.rank=s.rank:=by
    simpa[u,bB,ah.aA.rank,
      bA.aG.rank,
      br.aY.rank,
      ah.di,ah.bt.en]
      using C.rankOne
  have DY:H.bl.rank≤u.rank:=by
    rw[xd,Bm]
  have NY:1/(2:ℝ)^(d+1)≤u.Zd:=by
    simpa[u] using m7 s.aV C aQ rfl
      (by norm_num) c3
  have dc:(u.card:ℝ) ≤
      ((bI s.aV.restriction.ba bn bd *
          b7 W:ℕ):ℝ)*(H.bl.Zc.card:ℝ):=by
    simpa[u] using ml s.aV eH C aQ
      (by norm_num) s.fS W H wB
  have pe :
      ∀ (z:G),z∈H.bu.Zc-H.b6.Zc →
        ((z+ᵥ H.b6.Zc)∩H.bu.Zc).Nonempty →
        (65/64:ℝ)*(C.ak.ba.Zc.card:ℝ)⁻¹ ≤
          (b0 (aa.bH (d+1)) ((al (mu (z+ᵥ H.b6.Zc)) (mu H.bu.Zc))) ((al ((@mu (ℝ) _ _) u.restriction.set) (mu u.restriction.set)))) →
        ∀ data:ah.aW u.restriction.set
            (z+ᵥ H.b6.Zc) H.bu.Zc
            (aa.bH (d+1))
            (1/8192:ℝ) (1/8192:ℝ),
          ∃ (parent:aj G) (dR:NNReal)
            (source:Finset G) (bq:Nat),
            ∃ P:ah.cb data parent
              dR source (aa.au (d+1))
              bq (1/512:ℝ),
              P.child.rank≤u.rank+aa.au (d+1) ∧
              Real.exp (-c9)*(u.card:ℝ)≤P.child.Zc.card:=by
    intro z hz ui rS data
    have B7 :
        (65/64:ℝ)*(C.ak.ba.Zc.card:ℝ)⁻¹ ≤
          an.aM
            ((NNReal.toReal ∘ ((al (mu (z+ᵥ H.b6.Zc)) (mu H.bu.Zc)))):G→ℝ)
            ((al ((@mu (ℝ) _ _) u.restriction.set) (mu u.restriction.set)))
            (aa.bH (d+1)):=by
      rw[aN.dN
        ((al (mu (z+ᵥ H.b6.Zc)) (mu H.bu.Zc)))
        ((al ((@mu (ℝ) _ _) u.restriction.set) (mu u.restriction.set)))
        (aa.fU (d+1))]
      exact rS
    have b8 :
        aa.aR (d+1) ≤
          ah.bj u.restriction.set
            (z+ᵥ H.b6.Zc) H.bu.Zc
            (aa.bH (d+1)) :=
      i6
        u.restriction.set (z+ᵥ H.b6.Zc) H.bu.Zc
        C.ak.ba.Zc (d+1)
        C.ak.ba.aE
        (by
          have c8 :
              u.Zd=(u.restriction.set.card:ℝ) /
                C.ak.ba.Zc.card:=by
            simp only[u,bB,ah.hO]
            rw[ah.bk
              C.ak.aE]
            simp[ah.di,ah.bt.en,
              C.eD]
          rwa[←c8]) B7
    exact il u W H z data
      (aa.fU (d+1)) ui (by norm_num)
      b8 ax DY Bp (by positivity) dc sP
  apply kh s eH fw C kD aQ
    (by norm_num) W u6 kx H.ux H.mD
    H.bu.aE H.b6.aE H.rX H.rW
    (show(bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ =
      (bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ from rfl)
    dy
    (la s.aV C W H kx)
    d5 (lZ s.aV c3)
  intro mx
  obtain ⟨t,zE,KJ,KK⟩ :=
    gq
      s.aV C aQ (by norm_num) H.bu.aE
      H.b6.aE (epsilon:=(1/8:ℝ))
      (sigma:=(1/8192:ℝ)) (delta:=(1/8192:ℝ))
      (bm:=(1/512:ℝ))
      (fx:=(65/64:ℝ) *
        (C.ak.ba.Zc.card:ℝ)⁻¹)
      (eb:=eb) (c9:=c9)
      (aq:=aa.au (d+1))
      (r:=aa.bH (d+1))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (aa.fU (d+1))
      (aa.nA (d+1))
      (by
        have gw:=aa.fU (d+1)
        have mq:=aa.nA (d+1)
        rcases mq with ⟨k,hk⟩
        omega)
      (qP (d+1)) (by positivity) jw
      (by
        norm_num at mx ⊢
        simpa[u,aa.bH,
          bA.a7,cX,
          bF] using mx)
      (rQ s.aV C aQ (by norm_num))
      (by simpa[u] using pe)
  exact ⟨t,by norm_num at zE ⊢; exact zE,KJ,by
    simpa[bA.aG.card,
      RV,add_left_comm,add_assoc] using KK⟩
def fm:ℝ :=
 4096*(aa.cW:ℝ)
lemma iL
  (d rank d4:ℕ)
  (cK:rank≤ar.ax (d+1)
   (aa.au (d+1)))
  (o8:d4≤8*aa.au (d+1)) :
  Real.log (aa.cv (d+1) rank d4:ℝ) ≤
   2048*(aa.cW:ℝ) *
    ((d+1:ℕ):ℝ)^11:=by
 have eu:=aa.jW
  (d+1) rank d4 cK o8
 have dc:((d+1+1:ℕ):ℝ)≤2*((d+1:ℕ):ℝ):=by
  push_cast
  nlinarith
 have hpow:((d+1+1:ℕ):ℝ)^11 ≤
   (2:ℝ)^11*((d+1:ℕ):ℝ)^11:=by
  calc
   ((d+1+1:ℕ):ℝ)^11 ≤
     (2*((d+1:ℕ):ℝ))^11 :=
    Qp (by positivity) dc 11
   _=(2:ℝ)^11*((d+1:ℕ):ℝ)^11:=by rw[QL]
 calc
  Real.log (aa.cv (d+1) rank d4:ℝ) ≤
    (aa.cW:ℝ) *
     ((d+1+1:ℕ):ℝ)^11:=by simpa using eu
  _≤(aa.cW:ℝ) *
    ((2:ℝ)^11*((d+1:ℕ):ℝ)^11):=by gcongr
  _=2048*(aa.cW:ℝ) *
    ((d+1:ℕ):ℝ)^11:=by norm_num; ring
lemma f3
  (d rank:ℕ)
  (cK:rank≤ar.ax (d+1)
   (aa.au (d+1))) :
  Real.log (aa.bT rank
   (ar.bn (d+1) (aa.au (d+1)))
   (ar.bd (d+1) (aa.au (d+1))):ℝ) ≤
   2048*(aa.cW:ℝ) *
    ((d+1:ℕ):ℝ)^11:=by
 let d4:=aa.au (d+1)+1
 have o8:d4≤8*aa.au (d+1):=by
  dsimp[d4]
  have gw:=aa.bX (d+1)
  omega
 have KL:=iL d rank d4 cK o8
 have uD:(0:ℝ)<aa.bT rank
   (ar.bn (d+1) (aa.au (d+1)))
   (ar.bd (d+1) (aa.au (d+1))):=by
  exact_mod_cast QP
   (aa.ck
    (ar.me (aa.bX (d+1))))
   (aa.ck
    (ar.mf (aa.bX (d+1))))
 have hle:aa.bT rank
   (ar.bn (d+1) (aa.au (d+1)))
   (ar.bd (d+1) (aa.au (d+1))) ≤
   aa.cv (d+1) rank d4:=by
  unfold aa.cv
  rw[show
   aa.bT rank
     (ar.bn (d+1) (aa.au (d+1)))
     (ar.bd (d+1) (aa.au (d+1))) *
     aa.bR rank *
     (3*aa.bx rank d4
      (aa.cd (d+1)
       (ar.ax (d+1)
        (aa.au (d+1)))))^rank *
     aa.cL (d+1) =
    aa.bT rank
     (ar.bn (d+1) (aa.au (d+1)))
     (ar.bd (d+1) (aa.au (d+1))) *
     (aa.bR rank *
     (3*aa.bx rank d4
      (aa.cd (d+1)
       (ar.ax (d+1)
        (aa.au (d+1)))))^rank *
     aa.cL (d+1)) by ring]
  apply Q4
  have j6:0<aa.bR rank:=by
   unfold aa.bR
    aa.bG
   positivity
  have gL:0 <
    (3*aa.bx rank d4
     (aa.cd (d+1)
      (ar.ax (d+1)
       (aa.au (d+1)))))^rank:=by
   unfold aa.bx aa.cd
   positivity
  have lM:0<aa.cL (d+1):=by
   unfold aa.cL aa.dH
   have hq:0<aa.bE (d+1):=by
    unfold aa.bE
    exact aa.gV
     (aa.bP (d+1))
   positivity
  exact QP (QP j6 gL) lM
 exact(QG uD (by exact_mod_cast hle)).trans KL
lemma gE
  (d rank:ℕ)
  (cK:rank≤ar.ax (d+1)
   (aa.au (d+1))) :
  Real.log (aa.bG rank
   (ar.bn (d+1) (aa.au (d+1))):ℝ) ≤
   2048*(aa.cW:ℝ) *
    ((d+1:ℕ):ℝ)^11:=by
 have u9:=f3 d rank cK
 have IT:(0:ℝ)<aa.bG rank
   (ar.bn (d+1) (aa.au (d+1))):=by
  exact_mod_cast aa.ck
   (ar.me (aa.bX (d+1)))
 have hle:aa.bG rank
   (ar.bn (d+1) (aa.au (d+1))) ≤
   aa.bT rank
    (ar.bn (d+1) (aa.au (d+1)))
    (ar.bd (d+1) (aa.au (d+1))):=by
  unfold aa.bT
  apply Q4
  exact aa.ck
   (ar.mf (aa.bX (d+1)))
 exact(QG IT (by exact_mod_cast hle)).trans u9
lemma sQ :
    ∃ K:ℝ,0<K∧bA.rq K:=by
  refine ⟨fm, ?_, ?_⟩
  · unfold fm
    unfold aa.cW
      aa.aH
      aa.eW
    positivity
  · intro N A hA d hd
    let e:ℕ:=d+1
    let aq:ℕ:=aa.au e
    let p:ℕ:=aa.dt e
    refine ⟨aq,p, ?_, ?_⟩
    · dsimp[p]
      exact aa.mg e
    · intro n hn s c3 cK
      let ax:ℕ:=ar.ax e aq
      let bn:ℕ:=ar.bn e aq
      let bd:ℕ:=ar.bd e aq
      let eN:ℝ :=
        2048*(aa.cW:ℝ) *
          ((d+1:ℕ):ℝ)^11
      have cE:0<aq:=by
        dsimp[aq]
        exact aa.bX e
      have jH:s.rank≤ax:=by
        dsimp[ax,e,aq]
        unfold ar.ax
        have Kc:n≤1024*(d+1+1):=by omega
        exact Sj cK (QQ _ Kc)
      have eH:0<bn:=by
        dsimp[bn]
        exact ar.me cE
      have fw:0<bd:=by
        dsimp[bd]
        exact ar.mf cE
      have IU:1/(2:ℝ)^e≤ s.Zd:=by
        calc
          1/(2:ℝ)^e≤1/(2:ℝ)^d:=by
            dsimp[e]
            rw[RB]
            have hpow:(0:ℝ)<(2:ℝ)^d:=by positivity
            field_simp
            nlinarith
          _≤ s.Zd:=c3
      have kD:gj s.aV bn bd (1/512:ℝ)
          (fm*((d+1:ℕ):ℝ)^11):=by
        refine
          { Bc:=s.fS
            iJ:=s.iJ
            yx:= ?_
            vq:= ?_
            th:= ?_
            ti:= ?_ }
        · dsimp[bn]
          exact ar.tJ cE jH
        · dsimp[bn]
          exact ar.wj cE jH IU
        · have mF :
              (0:ℝ) <
                (b9 s.aV.restriction.ba bn:ℕ):=by
            unfold b9
            positivity
          apply jk s.aV s.fS mF
          have eu:=gE d s.rank jH
          apply eu.trans
          unfold fm
          gcongr
          norm_num
        · have mF :
              (0:ℝ) <
                (bI s.aV.restriction.ba bn bd:ℕ):=by
            unfold bI b9
            positivity
          apply jk s.aV s.fS mF
          have eu:=f3 d s.rank jH
          apply eu.trans
          unfold fm
          gcongr
          norm_num
      have xI:((bd:NNReal)⁻¹)≤1:=by
        apply(inv_le_one₀ (by exact_mod_cast fw)).2
        exact_mod_cast(show 1≤bd by omega)
      let C:c7 s.aV.restriction.ba bn bd :=
        Classical.choice (rO s.aV.restriction.ba
          bn bd eH fw xI)
      have ym :
          eN+eN =
            fm*((d+1:ℕ):ℝ)^11:=by
        dsimp[eN,fm]
        ring
      have Bq :
          gj s.aV bn bd (1/512:ℝ)
            (eN+eN):=by
        rw[ym]
        exact kD
      rw[←ym]
      let P:bA.dB s (1/512:ℝ)
          (eN+eN) aq :=
        bF
          (aq:=aq) s eH fw C Bq
      refine ⟨P, ?_⟩
      intro aQ
      have Br :
          Real.exp (-eN)*(s.aV.card:ℝ) ≤
            ((b9 s.aV.restriction.ba bn:ℕ):ℝ)⁻¹ *
              (s.aV.restriction.ba.Zc.card:ℝ):=by
        have mF :
            (0:ℝ) <
              (b9 s.aV.restriction.ba bn:ℕ):=by
          unfold b9
          positivity
        apply jk s.aV s.fS mF
        simpa[eN,b9,
          aa.bG,bn,e,aq,
          bA.aG.rank,
          ah.aA.rank,
          br.aY.rank] using
          (gE d s.rank jH)
      have jw :
          Real.exp (-eN)*(s.card:ℝ)≤C.ak.Zc.card:=by
        have mF :
            (0:ℝ) <
              (b9 s.aV.restriction.ba bn:ℕ):=by
          unfold b9
          positivity
        have GH :
            (s.aV.restriction.ba.Zc.card:ℝ) ≤
              (b9 s.aV.restriction.ba bn:ℝ) *
                (C.ak.Zc.card:ℝ):=by
          exact_mod_cast C.mz
        simpa[bA.aG.card] using
          mh s.aV mF Br GH
      let:NeZero (aD N):=⟨by simp[aD]⟩
      have A1:Odd (aD N):=by
        exact ⟨N,by simp[aD,R5]⟩
      let W:aj (ZMod (aD N)) :=
        aO.hU (aD N) A1 C.aB.ba
      have u6:W.a1:=by
        dsimp[W]
        exact qN A1 C.aB.ba
          C.fc
      have kx :
          W.Zc=aO.a4 C.aB.Zc:=by
        rw[C.nZ]
        dsimp[W]
        exact
          (aO.jO
            A1 C.aB.ba).symm
      have wB:W.Zc.card=C.aB.Zc.card:=by
        dsimp[W]
        rw[aO.p3]
        exact QA Finset.card C.nZ.symm
      have yB:W.rank=s.rank:=by
        dsimp[W]
        rw[aO.u4,C.p0]
        rfl
      let H:bU W :=
        Classical.choice (rP W)
      have dy :
          (bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ ≤
            1/(100*(max C.ak.ba.rank 1:ℕ):NNReal):=by
        rw[C.rankOne]
        simpa[bd,e,aq,
          bA.aG.rank,
          ah.aA.rank,
          br.aY.rank] using
          (ar.q8 cE jH)
      have d5 :
          2*(((cX s.aV C.ak C.aB aQ).card:ℝ)⁻¹ *
              (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
                (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ))) +
            (C.ak.ba.Zc.card:ℝ)⁻¹ *
              (200*((max C.ak.ba.rank 1:ℕ):ℝ) *
                (((bd:NNReal)⁻¹ +(bd:NNReal)⁻¹ :NNReal):ℝ)) ≤
            (1/8:ℝ)/8*(C.ak.ba.Zc.card:ℝ)⁻¹ :=by
        simpa[bd,e,aq] using
          (uG s.aV C aQ c3 jH cE)
      let d4:ℕ:=aq+1
      have o8:d4≤8*aa.au e:=by
        dsimp[d4,aq]
        have gw:=aa.bX e
        omega
      have FD :
          0<aa.cv e ax d4:=by
        have KM:0<ar.bn e
            (aa.au e) :=
          ar.me (aa.bX e)
        have KN:0<ar.bd e
            (aa.au e) :=
          ar.mf (aa.bX e)
        have hq:0<aa.bE e:=by
          unfold aa.bE
          exact aa.gV
            (aa.bP e)
        have u9:0<aa.bT ax
            (ar.bn e (aa.au e))
            (ar.bd e (aa.au e)):=by
          unfold aa.bT
          exact QP
            (aa.ck KM)
            (aa.ck KN)
        have j6 :
            0<aa.bR ax:=by
          unfold aa.bR
            aa.bG
          positivity
        have gL :
            0<(3*aa.bx ax d4
              (aa.cd e
                (ar.ax e
                  (aa.au e))))^ax:=by
          unfold aa.bx
            aa.cd
          positivity
        have lM:0<aa.cL e:=by
          unfold aa.cL
            aa.dH
          positivity
        unfold aa.cv
        exact QP (QP (QP u9 j6) gL) lM
      have Bs :
          Real.exp (-eN) *
              (aa.cv e ax d4:ℝ) ≤
            1:=by
        apply os FD
        simpa[eN,e] using
          (iL d ax d4 (SF) o8)
      have FE :
          (bI s.aV.restriction.ba bn bd *
              b7 W) *
              (3*bY e ax)^ax *
              cB e ax ≤
            aa.cv e ax d4:=by
        have zF :
            s.aV.restriction.ba.rank≤ax:=by
          simpa[bA.aG.rank,
            ah.aA.rank,
            br.aY.rank] using jH
        have xe {m:ℕ} (hm:0< m) :
            b9 s.aV.restriction.ba m ≤
              aa.bG ax m:=by
          unfold b9 aa.bG
          exact Ra
            (QR (by omega) zF)
            (QR (by norm_num) zF)
        have u9 :
            bI s.aV.restriction.ba bn bd ≤
              aa.bT ax bn bd:=by
          unfold bI aa.bT
          exact Ra (xe eH) (xe fw)
        have lE:max s.rank 1≤ max ax 1 :=
          Sn 1 jH
        have rd (c:ℕ) (hc:0<c) :
            (3*(c*max s.rank 1))^s.rank*4^s.rank ≤
              aa.bG ax
                (c*max ax 1):=by
          unfold aa.bG
          have dc :
              3*(c*max s.rank 1)≤3*(c*max ax 1):=by
            gcongr
          have xD:0<3*(c*max ax 1):=by positivity
          have jw :
              (3*(c*max s.rank 1))^s.rank ≤
                (3*(c*max ax 1))^ax:=by
            calc
              (3*(c*max s.rank 1))^s.rank ≤
                  (3*(c*max ax 1))^s.rank :=
                R4 dc _
              _≤(3*(c*max ax 1))^ax :=
                QR xD jH
          exact Ra jw
            (QR (by norm_num) jH)
        have j6 :
            b7 W ≤
              aa.bR ax:=by
          unfold b7
            aa.bR
          rw[yB]
          exact Ra
            (Ra (rd 1600 (by norm_num))
              (rd 200 (by norm_num)))
            (rd 200 (by norm_num))
        have gL :
            (3*bY e ax)^ax =
              (3*aa.bx ax d4
                (aa.cd e
                  (ar.ax e
                    (aa.au e))))^ax:=by
          unfold bY bD
            aa.bx
            aa.cd
            aa.av
          dsimp[ax,aq,d4]
        have lM :
            cB e ax =
              aa.cL e:=by
          unfold cB jG
            aa.cL
          rw[aa.o7]
        unfold aa.cv
        rw[←gL, ←lM]
        dsimp[bn,bd,aq]
        exact Ra
          (Ra (Ra u9 j6) (SF))
          (SF)
      have sP :
          Real.exp (-eN) *
              ((bI s.aV.restriction.ba bn bd *
                b7 W:ℕ):ℝ) *
              (((3*bY e ax)^ax:ℕ):ℝ) *
                (cB e ax:ℝ)≤1:=by
        calc
          Real.exp (-eN) *
              ((bI s.aV.restriction.ba bn bd *
                b7 W:ℕ):ℝ) *
              (((3*bY e ax)^ax:ℕ):ℝ) *
                (cB e ax:ℝ) ≤
              Real.exp (-eN) *
                (aa.cv e ax d4:ℝ):=by
                  have yC :
                      ((bI s.aV.restriction.ba bn bd *
                        b7 W) *
                        (3*bY e ax)^ax *
                        cB e ax:ℝ) ≤
                        (aa.cv
                          e ax d4:ℝ):=by
                    exact_mod_cast FE
                  push_cast at yC ⊢
                  calc
                    Real.exp (-eN) *
                        ((bI s.aV.restriction.ba bn bd:ℝ) *
                          b7 W) *
                        (3*bY e ax:ℝ)^ax *
                          cB e ax =
                        Real.exp (-eN) *
                          (((bI s.aV.restriction.ba bn bd:ℝ) *
                            b7 W) *
                            (3*bY e ax:ℝ)^ax *
                              cB e ax):=by ring
                    _≤Real.exp (-eN) *
                        (aa.cv e ax d4:ℝ) :=
                      iO yC (Q1 _).le
          _≤1:=Bs
      simpa[p,e] using
        (iE
          (d:=d) (ax:=ax) (bn:=bn) (bd:=bd)
          s eH fw C Bq jw aQ c3 W u6
          kx wB yB H jH dy d5 sP)
end IP
end
end ay.uE
end
theorem Zr : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
    (rothNumberNat N : ℝ) ≤ N * Real.exp (-c * (Real.log N) ^ (1/12 : ℝ)) := by
  obtain ⟨K,hK,increment⟩ := ay.uE.sQ
  obtain ⟨L,_,estimate⟩ := ay.i2 ⟨8 + 2050 * (2 : ℝ)^12 * K, ay.bA.k9 hK increment⟩
  refine ⟨Real.log 2 / (2 * L ^ (1/12 : ℝ)), div_pos (Real.log_pos (by norm_num)) (mul_pos two_pos (Real.rpow_pos_of_pos estimate.1 _)), ?_⟩
  simpa only [ay.vt] using ay.fo estimate
open Finset Filter Real
open scoped Topology
namespace DistanceRoth
theorem Zu (c : ℝ) (hc : 0 < c)
    (estimate : ∀ᶠ n : ℕ in atTop,
      (rothNumberNat n : ℝ) ≤ n * exp (-c * (log n) ^ (1/12 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (B : Finset ℕ), B ⊆ range n →
      ThreeAPFree (B : Set ℕ) → (B.card : ℝ) * log (4 * (n : ℝ)) ≤ C*n := by
  have logs : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have small := ((isLittleO_log_rpow_atTop (show (0:ℝ) < 1/12 by norm_num)).bound hc)
  have eventual : ∀ᶠ n : ℕ in atTop, (rothNumberNat n : ℝ) * log (4*(n:ℝ)) ≤ 2*n := by
    filter_upwards [estimate, logs.eventually small, eventually_ge_atTop 4] with n hn hlog hn4
    have n4 : (4:ℝ) ≤ n := by exact_mod_cast hn4
    have npos : (0:ℝ) < n := by linarith
    have lp : 0 < log (n : ℝ) := log_pos (by linarith)
    have hlog' : log (log (n : ℝ)) ≤ c * (log n) ^ (1/12 : ℝ) := by
      calc
        _ ≤ |log (log (n : ℝ))| := le_abs_self _
        _ ≤ _ := by simpa only [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg lp.le _)] using hlog
    have e := exp_le_exp.mpr hlog'
    rw [exp_log lp] at e
    have h4 : log (4*(n:ℝ)) ≤ 2*log (n:ℝ) := by
      rw [log_mul (by norm_num) npos.ne']
      linarith [log_le_log (by norm_num : (0:ℝ)<4) n4]
    have hpos : 0 ≤ log (4*(n:ℝ)) := log_nonneg (by linarith)
    calc
      _ ≤ ((n:ℝ)*exp (-c * (log n) ^ (1/12 : ℝ))) *
          (2*exp (c * (log n) ^ (1/12 : ℝ))) :=
        mul_le_mul hn (h4.trans (by linarith)) hpos (by positivity)
      _ = _ := by rw [neg_mul, exp_neg]; field_simp
  obtain ⟨N,hN⟩ := eventually_atTop.mp eventual
  have hC : 0 ≤ log (4*((N:ℝ)+1)) := log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) N])
  refine ⟨2 + log (4*((N:ℝ)+1)), by linarith, ?_⟩
  intro n B hB hfree
  have hn0 : (0:ℝ) ≤ n := by positivity
  have hcard : B.card ≤ rothNumberNat n := hfree.le_addRothNumber hB
  by_cases hn : N ≤ n
  · by_cases hz : n=0
    · subst n; simp
    have hl : 0 ≤ log (4*(n:ℝ)) := log_nonneg (by
      have : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      linarith)
    have hb : (B.card : ℝ) * log (4*(n:ℝ)) ≤ 2*n :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hl).trans (hN n hn)
    nlinarith [mul_nonneg hn0 hC]
  · by_cases hz : n=0
    · subst n; simp
    have np : (0:ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hz)
    have hnN : (n:ℝ) ≤ N := by exact_mod_cast (by omega : n ≤ N)
    have hl : log (4*(n:ℝ)) ≤ log (4*((N:ℝ)+1)) :=
      log_le_log (by positivity) (by linarith)
    have hb : (B.card : ℝ) ≤ n := by exact_mod_cast (hcard.trans (rothNumberNat_le n))
    calc
      _ ≤ (B.card:ℝ)* log (4*((N:ℝ)+1)) := by gcongr
      _ ≤ (n:ℝ) * log (4*((N:ℝ)+1)) := mul_le_mul_of_nonneg_right hb hC
      _ ≤ _ := by nlinarith
end DistanceRoth
theorem OMA.L2.solve : OMA.R1.H2 := by
  obtain ⟨c, hc, estimate⟩ := Zr
  exact DistanceRoth.Zu c hc estimate
theorem OMA.solution : type_of% @Erdos657.erdos_657.variants.dim_one_lower :=
  OMA.R1.main OMA.L1.solve OMA.L2.solve
