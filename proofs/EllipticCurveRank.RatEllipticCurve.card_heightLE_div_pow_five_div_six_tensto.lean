import FormalConjectures.Wikipedia.EllipticCurveRank

/-! # Counting reduced Weierstrass coefficient pairs and removing singular ones -/
-- Credit: @steveDOTdigital

namespace OMA.R_EllipticCurveRank_RatEllipticCurve_card_heightLE_div_pow_five_div_six_tensto_R1
open EllipticCurveRank EllipticCurveRank.RatEllipticCurve Filter Set
open scoped Topology

-- The lattice-point sieve for the simultaneous fourth- and sixth-power exclusions.
def H1 : Prop := Tendsto (fun H : ℕ =>
    (({z : ℤ × ℤ | max (4*z.1.natAbs^3) (27*z.2.natAbs^2) ≤ H ∧
      ∀ p : ℕ, p.Prime → ¬ ((p^4 : ℤ) ∣ z.1 ∧ (p^6 : ℤ) ∣ z.2)}.ncard : ℝ) / (H : ℝ)^(5/6 : ℝ)))
    atTop (𝓝 (2^(4/3 : ℝ)*3^(-3/2 : ℝ)/(riemannZeta 10).re))

-- The zero-discriminant locus is negligible on the volume scale.
def H2 : Prop := Tendsto (fun H : ℕ =>
    (({z : ℤ × ℤ | (max (4*z.1.natAbs^3) (27*z.2.natAbs^2) ≤ H ∧
      ∀ p : ℕ, p.Prime → ¬ ((p^4 : ℤ) ∣ z.1 ∧ (p^6 : ℤ) ∣ z.2)) ∧
      4*z.1^3+27*z.2^2 = 0}.ncard : ℝ) / (H : ℝ)^(5/6 : ℝ))) atTop (𝓝 0)

theorem main : H1 → H2 → type_of% @EllipticCurveRank.RatEllipticCurve.card_heightLE_div_pow_five_div_six_tensto := by
  classical
  intro sieve negligible
  let R (H : ℕ) := {z : ℤ × ℤ | max (4*z.1.natAbs^3) (27*z.2.natAbs^2) ≤ H ∧
      ∀ p : ℕ, p.Prime → ¬ ((p^4 : ℤ) ∣ z.1 ∧ (p^6 : ℤ) ∣ z.2)}
  let T (H : ℕ) := {z : ℤ × ℤ | z ∈ R H ∧ 4*z.1^3+27*z.2^2 = 0}
  have hfin (H : ℕ) : (R H).Finite := by
    apply ((Set.finite_Icc (-(H : ℤ)) H).prod (Set.finite_Icc (-(H : ℤ)) H)).subset
    rintro ⟨a,b⟩ h
    obtain ⟨hh,_⟩ := h
    obtain ⟨ha,hb⟩ := max_le_iff.mp hh
    change 4*a.natAbs^3 ≤ H at ha
    change 27*b.natAbs^2 ≤ H at hb
    have ha' : a.natAbs ≤ H := by have := Nat.le_self_pow (by decide : 3 ≠ 0) a.natAbs; omega
    have hb' : b.natAbs ≤ H := by have := Nat.le_self_pow (by decide : 2 ≠ 0) b.natAbs; omega
    change (-(H : ℤ) ≤ a ∧ a ≤ H) ∧ (-(H : ℤ) ≤ b ∧ b ≤ H)
    omega
  have hcard (H : ℕ) : (heightLE H).ncard = (R H \ T H).ncard := by
    refine Set.ncard_congr' {toFun := fun E => ?_, invFun := fun z => ?_, left_inv := ?_, right_inv := ?_}
    · refine ⟨(E.val.A,E.val.B),⟨E.property,E.val.reduced⟩,?_⟩
      exact fun h => E.val.Δ_ne_zero h.2
    · obtain ⟨⟨a,b⟩,hz⟩ := z
      exact ⟨⟨a,b,hz.1.2,fun e => hz.2 ⟨hz.1,e⟩⟩,hz.1.1⟩
    · rintro ⟨⟨a,b,hr,hn⟩,hh⟩; rfl
    · rintro ⟨⟨a,b⟩,h⟩; rfl
  have hl := (show Tendsto (fun H : ℕ => ((R H).ncard : ℝ)/(H : ℝ)^(5/6 : ℝ)) _ _ from sieve).sub
    (show Tendsto (fun H : ℕ => ((T H).ncard : ℝ)/(H : ℝ)^(5/6 : ℝ)) _ _ from negligible)
  rw [sub_zero] at hl
  apply hl.congr'
  filter_upwards with H
  rw [hcard, ← sub_div]
  have h := Set.ncard_sdiff_add_ncard_of_subset (show T H ⊆ R H from fun _ h => h.1) (hfin H)
  have eqr : (((R H \ T H).ncard : ℕ) : ℝ) + (T H).ncard = (R H).ncard := by exact_mod_cast h
  congr 1
  linarith

end OMA.R_EllipticCurveRank_RatEllipticCurve_card_heightLE_div_pow_five_div_six_tensto_R1

-- Density of reduced Weierstrass coefficient pairs
namespace OMA.CoefficientSieve
open Finset Filter ArithmeticFunction
open scoped Classical
open scoped Topology ArithmeticFunction.Moebius ArithmeticFunction.zeta

private def Good (a b : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬ (p^4 ∣ a ∧ p^6 ∣ b)
private def commonRoot (a b : ℕ) := (Nat.floorRoot 4 a).gcd (Nat.floorRoot 6 b)

private lemma root_dvd (a b d : ℕ) : d ∣ commonRoot a b ↔ d^4 ∣ a ∧ d^6 ∣ b := by
  simp [commonRoot,Nat.dvd_gcd_iff,Nat.pow_dvd_iff_dvd_floorRoot]

private lemma good_iff (a b : ℕ) : Good a b ↔ commonRoot a b = 1 := by
  constructor
  · intro h
    by_contra ne
    obtain ⟨p,prime,div⟩ := Nat.exists_prime_and_dvd ne
    exact h p prime ((root_dvd a b p).mp div)
  · intro eq p prime hp
    have h := (root_dvd a b p).mpr hp
    rw [eq] at h
    exact prime.not_dvd_one h

private noncomputable def posCount (A B : ℕ) := by
  classical
  exact (((Ioc 0 A) ×ˢ (Ioc 0 B)).filter (fun z : ℕ × ℕ => Good z.1 z.2)).card

private lemma weight (A a b : ℕ) (ha : 0 < a) (ub : a ≤ A) :
    (if Good a b then 1 else 0 : ℝ) =
      ∑ d ∈ Ioc 0 A, if d^4 ∣ a ∧ d^6 ∣ b then (μ d : ℝ) else 0 := by
  classical
  let g := commonRoot a b
  have gn : g ≠ 0 := Nat.gcd_ne_zero_left (Nat.floorRoot_ne_zero.mpr ⟨(by decide : 4 ≠ 0),ha.ne'⟩)
  have divisors : (Ioc 0 A).filter (fun d => d^4 ∣ a ∧ d^6 ∣ b) = g.divisors := by
    ext d
    simp only [mem_filter,mem_Ioc,Nat.mem_divisors,← root_dvd]
    constructor
    · exact fun h => ⟨h.2,gn⟩
    · rintro ⟨dvd,_⟩
      have h := ((root_dvd a b d).mp dvd).1
      have le : d^4 ≤ a := Nat.le_of_dvd ha h
      have pos : d ≠ 0 := fun z => gn (by simpa [z] using dvd)
      have de := Nat.le_self_pow (a := d) (by decide : 4 ≠ 0)
      exact ⟨⟨Nat.pos_of_ne_zero pos,by omega⟩,dvd⟩
  rw [← sum_filter,divisors]
  have mi : ∑ d ∈ g.divisors, μ d = (if g = 1 then 1 else 0 : ℤ) := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply]
  rw [good_iff]
  by_cases one : g = 1
  · have e : commonRoot a b = 1 := one
    simp only [if_pos one] at mi
    simp only [if_pos e]
    exact_mod_cast mi.symm
  · have e : commonRoot a b ≠ 1 := one
    simp only [if_neg one] at mi
    simp only [if_neg e]
    exact_mod_cast mi.symm

private lemma exact_box (A B : ℕ) : (posCount A B : ℝ) =
    ∑ d ∈ Ioc 0 A, (μ d : ℝ) * (A / d^4 : ℕ) * (B / d^6 : ℕ) := by
  classical
  let P := (Ioc 0 A) ×ˢ (Ioc 0 B)
  have muls (d : ℕ) :
      (P.filter (fun z => d^4 ∣ z.1 ∧ d^6 ∣ z.2)).card = (A / d^4) * (B / d^6) := by
    have eq : P.filter (fun z => d^4 ∣ z.1 ∧ d^6 ∣ z.2) =
        ((Ioc 0 A).filter (fun x => d^4 ∣ x)) ×ˢ ((Ioc 0 B).filter (fun y => d^6 ∣ y)) := by
      ext ⟨x,y⟩
      simp only [P,mem_filter,mem_product]
      tauto
    rw [eq,card_product,Nat.Ioc_filter_dvd_card_eq_div,Nat.Ioc_filter_dvd_card_eq_div]
  calc
    _ = ∑ z ∈ P, (if Good z.1 z.2 then 1 else 0 : ℝ) := by simp [posCount,P]
    _ = ∑ z ∈ P, ∑ d ∈ Ioc 0 A, (if d^4 ∣ z.1 ∧ d^6 ∣ z.2 then (μ d : ℝ) else 0) := by
      apply sum_congr rfl
      intro z hz
      obtain ⟨hz1,hz2⟩ := mem_product.mp hz
      exact weight A z.1 z.2 (mem_Ioc.mp hz1).1 (mem_Ioc.mp hz1).2
    _ = ∑ d ∈ Ioc 0 A, ∑ z ∈ P, (if d^4 ∣ z.1 ∧ d^6 ∣ z.2 then (μ d : ℝ) else 0) := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro d _
      rw [← sum_filter,sum_const,nsmul_eq_mul,muls]
      push_cast
      ring


private lemma mobius_series : (∑' d : ℕ, (μ d : ℝ) / (d : ℝ)^10) = 1 / (riemannZeta 10).re := by
  let s := ∑' d : ℕ, (μ d : ℝ) / (d : ℝ)^10
  have castS : (s : ℂ) = LSeries (fun n : ℕ => (μ n : ℂ)) 10 := by
    rw [show (s : ℂ) = _ from Complex.ofReal_tsum (fun d : ℕ => (μ d : ℝ) / (d : ℝ)^10)]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst n; simp [LSeries.term]
    · rw [LSeries.term,if_neg hn]
      push_cast
      rw [show (10 : ℂ) = ((10 : ℕ) : ℂ) by norm_num,Complex.cpow_natCast]
  have eq := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (s := 10) (by norm_num)
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta (by norm_num),← castS] at eq
  have re := congrArg Complex.re eq
  simp [Complex.mul_re] at re
  change s = _
  apply (eq_div_iff (show (riemannZeta 10).re ≠ 0 by intro z; rw [z,zero_mul] at re; norm_num at re)).mpr
  simpa [mul_comm] using re

private noncomputable def ratio (k d A : ℕ) : ℝ := ((A / d^k : ℕ) : ℝ) / (A : ℝ)

private lemma ratio_le (k d A : ℕ) : ratio k d A ≤ 1 / (d : ℝ)^k := by
  by_cases ha : A = 0
  · simp [ratio,ha]
  by_cases hd : d^k = 0
  · have hz : (d : ℝ)^k = 0 := by exact_mod_cast hd
    simp [ratio,hd,hz]
  have hA : 0 < (A : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ha
  have hD : 0 < (d : ℝ)^k := by exact_mod_cast Nat.pos_of_ne_zero hd
  rw [ratio,div_le_div_iff₀ hA hD,one_mul]
  exact_mod_cast Nat.div_mul_le_self A (d^k)

private lemma ratio_lim (k d : ℕ) : Tendsto (ratio k d) atTop (𝓝 (1 / (d : ℝ)^k)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ)
    (a := 1 / (d : ℝ)^k) (by positivity)).comp tendsto_natCast_atTop_atTop
  apply h.congr
  intro a
  simp only [Function.comp_apply,ratio]
  rw [one_div_mul_eq_div,← Nat.cast_pow,Nat.floor_div_natCast,Nat.floor_natCast]

private lemma pos_density (A B : ℕ → ℕ) (ga : Tendsto A atTop atTop) (gb : Tendsto B atTop atTop) :
    Tendsto (fun H => (posCount (A H) (B H) : ℝ) / ((A H : ℝ) * (B H : ℝ)))
      atTop (𝓝 (1 / (riemannZeta 10).re)) := by
  classical
  let f (H d : ℕ) := (μ d : ℝ) * ratio 4 d (A H) * ratio 6 d (B H)
  have aux (d : ℕ) : (1 / (d : ℝ)^4) * (1 / (d : ℝ)^6) = 1 / (d : ℝ)^10 := by
    rw [div_mul_div_comm,← pow_add]; norm_num
  have lim (d : ℕ) : Tendsto (fun H => f H d) atTop (𝓝 ((μ d : ℝ) / (d : ℝ)^10)) := by
    have h := ((tendsto_const_nhds (x := (μ d : ℝ))).mul ((ratio_lim 4 d).comp ga)).mul
      ((ratio_lim 6 d).comp gb)
    rw [mul_assoc,aux] at h
    simpa only [f,Function.comp_apply,div_eq_mul_inv,one_mul] using h
  have major (H d : ℕ) : ‖f H d‖ ≤ 1 / (d : ℝ)^10 := by
    have mu : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    have p (k A : ℕ) : 0 ≤ ratio k d A := by unfold ratio; positivity
    rw [← aux,show ‖f H d‖ = |(μ d : ℝ)| * ratio 4 d (A H) * ratio 6 d (B H) by
      simp [f,Real.norm_eq_abs,abs_of_nonneg (p _ _)]]
    calc
      _ ≤ (1 * (1 / (d : ℝ)^4)) * (1 / (d : ℝ)^6) :=
        mul_le_mul (mul_le_mul mu (ratio_le ..) (p ..) zero_le_one) (ratio_le ..) (p ..) (by positivity)
      _ = _ := by rw [one_mul]
  have conv := tendsto_tsum_of_dominated_convergence
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 10)) lim
    (Eventually.of_forall major)
  rw [mobius_series] at conv
  apply conv.congr
  intro H
  have tail (d : ℕ) (hd : d ∉ Ioc 0 (A H)) : f H d = 0 := by
    by_cases zero : d = 0
    · simp [f,zero]
    have gt : A H < d := by simpa [mem_Ioc,Nat.pos_of_ne_zero zero] using hd
    have div : A H / d^4 = 0 := Nat.div_eq_of_lt (gt.trans_le (Nat.le_self_pow (by decide) d))
    simp [f,ratio,div]
  rw [tsum_eq_sum tail,exact_box,Finset.sum_div]
  apply sum_congr rfl
  intro d _
  dsimp [f,ratio]
  ring


private noncomputable def positive (A B : ℕ) : Finset (ℕ × ℕ) :=
  ((Ioc 0 A) ×ˢ (Ioc 0 B)).filter (fun z => Good z.1 z.2)

private noncomputable def signedBox (A B : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-(A : ℤ)) A) ×ˢ (Icc (-(B : ℤ)) B)).filter (fun z => Good z.1.natAbs z.2.natAbs)

private def pm (s : Bool) (n : ℕ) : ℤ := if s then n else -(n : ℤ)

private lemma abs_pm (s : Bool) (n : ℕ) : (pm s n).natAbs = n := by
  cases s <;> simp [pm]

private lemma pm_inj {i j : Bool} {n m : ℕ} (hn : 0 < n) (e : pm i n = pm j m) :
    i = j ∧ n = m := by
  have h := congrArg Int.natAbs e
  simp only [abs_pm] at h
  subst m
  cases i <;> cases j <;> simp_all [pm]

private lemma pm_rep (x : ℤ) : ∃ i, pm i x.natAbs = x := by
  rcases Int.natAbs_eq x with h|h
  · exact ⟨true, by simpa [pm] using h.symm⟩
  · exact ⟨false, by simpa [pm] using h.symm⟩

private lemma signed_bounds (A B : ℕ) : 4 * posCount A B ≤ (signedBox A B).card ∧
    (signedBox A B).card ≤ 4 * posCount A B + (2*A+1) + (2*B+1) := by
  classical
  let U := signedBox A B
  let K := U.filter fun z => z.1 ≠ 0 ∧ z.2 ≠ 0
  let S := positive A B
  let D := (univ : Finset (Bool × Bool)) ×ˢ S
  let f (z : (Bool × Bool) × (ℕ × ℕ)) := (pm z.1.1 z.2.1,pm z.1.2 z.2.2)
  have posInfo {z : ℕ × ℕ} : z ∈ S ↔ (0 < z.1 ∧ z.1 ≤ A) ∧ (0 < z.2 ∧ z.2 ≤ B) ∧ Good z.1 z.2 := by
    simp [S,positive,and_assoc]
  have signedInfo {z : ℤ × ℤ} : z ∈ U ↔ z.1.natAbs ≤ A ∧ z.2.natAbs ≤ B ∧ Good z.1.natAbs z.2.natAbs := by
    simp only [U,signedBox,mem_filter,mem_product,mem_Icc]
    constructor
    · rintro ⟨⟨⟨ax,bx⟩,⟨ay,by'⟩⟩,g⟩
      exact ⟨by omega,by omega,g⟩
    · rintro ⟨a,b,g⟩
      exact ⟨⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩,g⟩
  have bij : D.card = K.card := by
    apply card_bij (fun z _ => f z)
    · intro ⟨⟨i,j⟩,⟨a,b⟩⟩ hz
      obtain ⟨⟨ap,au⟩,⟨bp,bu⟩,good⟩ := posInfo.mp (mem_product.mp hz).2
      change 0 < a at ap
      change 0 < b at bp
      apply mem_filter.mpr
      refine ⟨signedInfo.mpr ?_,?_⟩
      · simpa only [f,abs_pm] using And.intro au (And.intro bu good)
      · dsimp [f]
        constructor <;> intro e <;> have hh := congrArg Int.natAbs e <;> simp [abs_pm] at hh <;> omega
    · intro ⟨⟨i,j⟩,⟨a,b⟩⟩ hz ⟨⟨i',j'⟩,⟨a',b'⟩⟩ _ eq
      obtain ⟨⟨ap,_⟩,⟨bp,_⟩,_⟩ := posInfo.mp (mem_product.mp hz).2
      obtain ⟨rfl,rfl⟩ := pm_inj ap (congrArg Prod.fst eq)
      obtain ⟨rfl,rfl⟩ := pm_inj bp (congrArg Prod.snd eq)
      rfl
    · intro ⟨x,y⟩ h
      obtain ⟨su,xn,yn⟩ := mem_filter.mp h
      obtain ⟨xu,yu,good⟩ := signedInfo.mp su
      obtain ⟨i,hi⟩ := pm_rep x
      obtain ⟨j,hj⟩ := pm_rep y
      refine ⟨((i,j),x.natAbs,y.natAbs),mem_product.mpr ⟨mem_univ _,posInfo.mpr ?_⟩,Prod.ext hi hj⟩
      exact ⟨⟨Int.natAbs_pos.mpr xn,xu⟩,⟨Int.natAbs_pos.mpr yn,yu⟩,good⟩
  have kc : K.card = 4 * posCount A B := by
    rw [← bij,show D.card = _ from card_product _ _]
    have bo : (univ : Finset (Bool × Bool)).card = 4 := by decide
    rw [bo]
    rfl
  refine ⟨kc ▸ card_le_card (filter_subset _ _),?_⟩
  let Xaxis := (Icc (-(A : ℤ)) A) ×ˢ ({0} : Finset ℤ)
  let Yaxis := ({0} : Finset ℤ) ×ˢ (Icc (-(B : ℤ)) B)
  have sx : Xaxis.card = 2*A+1 := by simp [Xaxis,Int.card_Icc]; omega
  have sy : Yaxis.card = 2*B+1 := by simp [Yaxis,Int.card_Icc]; omega
  have sub : U ⊆ K ∪ Xaxis ∪ Yaxis := by
    intro z hz
    obtain ⟨a,b⟩ := mem_product.mp (mem_filter.mp hz).1
    by_cases y : z.2 = 0
    · exact mem_union_left _ (mem_union_right _ (mem_product.mpr ⟨a,mem_singleton.mpr y⟩))
    by_cases x : z.1 = 0
    · exact mem_union_right _ (mem_product.mpr ⟨mem_singleton.mpr x,b⟩)
    exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hz,x,y⟩))
  have le := card_le_card sub
  have p := card_union_le K Xaxis
  have q := card_union_le (K ∪ Xaxis) Yaxis
  change U.card ≤ _
  omega


private lemma signed_density (A B : ℕ → ℕ) (ga : Tendsto A atTop atTop) (gb : Tendsto B atTop atTop) :
    Tendsto (fun H => ((signedBox (A H) (B H)).card : ℝ) / ((A H : ℝ) * (B H : ℝ)))
      atTop (𝓝 (4 * (1 / (riemannZeta 10).re))) := by
  have pos := (pos_density A B ga gb).const_mul 4
  have ai : Tendsto (fun H => (A H : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp ga)
  have bi : Tendsto (fun H => (B H : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp gb)
  have top := ((pos.add (ai.const_mul 2)).add (bi.const_mul 2)).add ((ai.mul bi).const_mul 2)
  simp only [mul_zero,add_zero] at top
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' pos top
  · filter_upwards with H
    have lo := (signed_bounds (A H) (B H)).1
    have realLo : 4 * (posCount (A H) (B H) : ℝ) ≤ (signedBox (A H) (B H)).card := by exact_mod_cast lo
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right realLo (by positivity)
  · filter_upwards [ga.eventually (eventually_ge_atTop 1),gb.eventually (eventually_ge_atTop 1)] with H ha hb
    have high := (signed_bounds (A H) (B H)).2
    have up : ((signedBox (A H) (B H)).card : ℝ) ≤
        4*(posCount (A H) (B H) : ℝ)+(2*(A H : ℝ)+1)+(2*(B H : ℝ)+1) := by exact_mod_cast high
    have a : 0 < (A H : ℝ) := by exact_mod_cast ha
    have b : 0 < (B H : ℝ) := by exact_mod_cast hb
    change _ / ((A H : ℝ) * (B H : ℝ)) ≤
      4 * ((posCount (A H) (B H) : ℝ) / ((A H : ℝ) * (B H : ℝ))) +
        2*(A H : ℝ)⁻¹ + 2*(B H : ℝ)⁻¹ + 2*((A H : ℝ)⁻¹*(B H : ℝ)⁻¹)
    apply (div_le_iff₀ (mul_pos a b)).mpr
    refine up.trans_eq ?_
    field_simp [a.ne',b.ne'] <;> ring

private noncomputable def cscale (k c : ℕ) : ℝ := (c : ℝ)^(-(1/(k:ℝ)))
private noncomputable def width (k c H : ℕ) : ℕ :=
  ⌊cscale k c * (H : ℝ)^(1/(k : ℝ))⌋₊

private lemma width_iff (k c H n : ℕ) (hk : 0 < k) (hc : 0 < c) :
    n ≤ width k c H ↔ c*n^k ≤ H := by
  have kp : 0 < (k : ℝ) := by exact_mod_cast hk
  have cp : 0 < (c : ℝ) := by exact_mod_cast hc
  have sc : 0 < cscale k c := Real.rpow_pos_of_pos cp _
  let w := cscale k c * (H : ℝ)^(1/(k:ℝ))
  have wn : 0 ≤ w := by dsimp [w]; positivity
  have val : w^k = (H:ℝ)/c := by
    rw [show w = _ from rfl,mul_pow,cscale,← Real.rpow_mul_natCast cp.le,
      ← Real.rpow_mul_natCast (Nat.cast_nonneg H),neg_mul,one_div_mul_cancel kp.ne',
      Real.rpow_neg_one,Real.rpow_one]
    ring
  change n ≤ ⌊w⌋₊ ↔ _
  rw [Nat.le_floor_iff wn,← Real.rpow_le_rpow_iff (Nat.cast_nonneg n) wn kp,
    Real.rpow_natCast,Real.rpow_natCast,val,le_div_iff₀ cp]
  exact_mod_cast (by rw [Nat.mul_comm c] : n^k*c ≤ H ↔ c*n^k ≤ H)

private lemma width_limits (k c : ℕ) (hk : 0 < k) (hc : 0 < c) :
    Tendsto (width k c) atTop atTop ∧
    Tendsto (fun H : ℕ => (width k c H : ℝ)/(H:ℝ)^(1/(k:ℝ))) atTop (𝓝 (cscale k c)) := by
  have kp : 0 < (k : ℝ) := by exact_mod_cast hk
  have cp : 0 < (c : ℝ) := by exact_mod_cast hc
  have sc : 0 < cscale k c := Real.rpow_pos_of_pos cp _
  have power : Tendsto (fun H : ℕ => (H : ℝ)^(1/(k:ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  exact ⟨tendsto_nat_floor_atTop.comp ((tendsto_const_mul_atTop_of_pos sc).mpr power),
    (tendsto_nat_floor_mul_div_atTop sc.le).comp power⟩


private lemma coeffCount (H : ℕ) :
    {z : ℤ × ℤ | max (4*z.1.natAbs^3) (27*z.2.natAbs^2) ≤ H ∧
      ∀ p : ℕ, p.Prime → ¬ ((p^4 : ℤ) ∣ z.1 ∧ (p^6 : ℤ) ∣ z.2)}.ncard =
      (signedBox (width 3 4 H) (width 2 27 H)).card := by
  classical
  have coord (x : ℤ) (n : ℕ) : (-(n:ℤ) ≤ x ∧ x ≤ n) ↔ x.natAbs ≤ n := by omega
  have red (a b : ℤ) : Good a.natAbs b.natAbs ↔
      (∀ p : ℕ, p.Prime → ¬ ((p^4 : ℤ) ∣ a ∧ (p^6 : ℤ) ∣ b)) := by
    simp only [Good, ← Nat.cast_pow, Int.natCast_dvd]
  have eq : {z : ℤ × ℤ | max (4*z.1.natAbs^3) (27*z.2.natAbs^2) ≤ H ∧
      ∀ p : ℕ, p.Prime → ¬ ((p^4 : ℤ) ∣ z.1 ∧ (p^6 : ℤ) ∣ z.2)} =
      (↑(signedBox (width 3 4 H) (width 2 27 H)) : Set (ℤ × ℤ)) := by
    ext z
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, signedBox, mem_filter, mem_product, mem_Icc, coord,
      width_iff 3 4 H _ (by decide) (by decide), width_iff 2 27 H _ (by decide) (by decide),
      max_le_iff, red]
  rw [eq, Set.ncard_coe_finset]

private lemma scale_value :
    4*(1/(riemannZeta 10).re)*(cscale 3 4*cscale 2 27) =
      2^(4/3 : ℝ)*3^(-3/2 : ℝ)/(riemannZeta 10).re := by
  have s : cscale 3 4 = (2:ℝ)^(-2/3 : ℝ) := by
    calc
      _ = ((2:ℝ)^(2:ℕ))^(-(1/3:ℝ)) := by norm_num [cscale]
      _ = (2:ℝ)^(((2:ℕ):ℝ)*(-(1/3:ℝ))) := (Real.rpow_natCast_mul (by norm_num) 2 _).symm
      _ = _ := by norm_num
  have t : cscale 2 27 = (3:ℝ)^(-3/2 : ℝ) := by
    calc
      _ = ((3:ℝ)^(3:ℕ))^(-(1/2:ℝ)) := by norm_num [cscale]
      _ = (3:ℝ)^(((3:ℕ):ℝ)*(-(1/2:ℝ))) := (Real.rpow_natCast_mul (by norm_num) 3 _).symm
      _ = _ := by norm_num
  have u : (4:ℝ)*2^(-2/3:ℝ) = 2^(4/3:ℝ) := by
    calc
      _ = (2:ℝ)^(2:ℝ)*2^(-2/3:ℝ) := by norm_num
      _ = (2:ℝ)^(2 + -2/3:ℝ) := (Real.rpow_add (by norm_num) _ _).symm
      _ = _ := by norm_num
  rw [s,t,← u]
  ring

theorem coefficient_density : Tendsto (fun H : ℕ =>
    (({z : ℤ × ℤ | max (4*z.1.natAbs^3) (27*z.2.natAbs^2) ≤ H ∧
      ∀ p : ℕ, p.Prime → ¬ ((p^4 : ℤ) ∣ z.1 ∧ (p^6 : ℤ) ∣ z.2)}.ncard : ℝ) / (H : ℝ)^(5/6 : ℝ)))
    atTop (𝓝 (2^(4/3 : ℝ)*3^(-3/2 : ℝ)/(riemannZeta 10).re)) := by
  obtain ⟨ga,sa⟩ := width_limits 3 4 (by decide) (by decide)
  obtain ⟨gb,sb⟩ := width_limits 2 27 (by decide) (by decide)
  have prod := (signed_density _ _ ga gb).mul (sa.mul sb)
  rw [scale_value] at prod
  apply prod.congr'
  filter_upwards [eventually_ge_atTop 1,ga.eventually (eventually_ge_atTop 1),
    gb.eventually (eventually_ge_atTop 1)] with H hH hA hB
  have h : 0 < (H:ℝ) := by exact_mod_cast hH
  have a : 0 < (width 3 4 H : ℝ) := by exact_mod_cast hA
  have b : 0 < (width 2 27 H : ℝ) := by exact_mod_cast hB
  have pH : (H:ℝ)^(5/6:ℝ) = (H:ℝ)^(1/3:ℝ)*(H:ℝ)^(1/2:ℝ) := by
    rw [← Real.rpow_add h]
    norm_num
  rw [coeffCount, pH]
  change (_/((width 3 4 H : ℝ)*(width 2 27 H : ℝ))) *
    (((width 3 4 H : ℝ)/(H:ℝ)^(1/(3:ℝ)))*((width 2 27 H : ℝ)/(H:ℝ)^(1/(2:ℝ)))) = _
  field_simp [a.ne',b.ne', (Real.rpow_pos_of_pos h (1/3)).ne', (Real.rpow_pos_of_pos h (1/2)).ne']

end OMA.CoefficientSieve

-- A square-root bound on singular Weierstrass pairs
section
open Filter Set
open scoped Topology
namespace OMA.SingularCurves
theorem negligible : OMA.R_EllipticCurveRank_RatEllipticCurve_card_heightLE_div_pow_five_div_six_tensto_R1.H2 := by
  classical
  let S (H : ℕ) := {z : ℤ × ℤ | (max (4*z.1.natAbs^3) (27*z.2.natAbs^2) ≤ H ∧
      ∀ p : ℕ, p.Prime → ¬ ((p^4 : ℤ) ∣ z.1 ∧ (p^6 : ℤ) ∣ z.2)) ∧
      4*z.1^3+27*z.2^2 = 0}
  have count (H : ℕ) : (S H).ncard ≤ 2*H.sqrt+1 := by
    let J := Finset.Icc (-(H.sqrt : ℤ)) (H.sqrt : ℤ)
    have bound : (S H).ncard ≤ (J : Set ℤ).ncard := by
      apply Set.ncard_le_ncard_of_injOn Prod.snd
      · rintro ⟨a,b⟩ hh
        have h := (max_le_iff.mp hh.1.1).2
        change 27*b.natAbs^2 ≤ H at h
        have hs : b.natAbs ≤ H.sqrt := Nat.le_sqrt'.mpr (by omega)
        change b ∈ Finset.Icc _ _
        rw [Finset.mem_Icc]; omega
      · rintro ⟨a,b⟩ hab ⟨c,e⟩ hce eq
        change b = e at eq; subst e
        have h₁ : 4*a^3+27*b^2=0 := hab.2
        have h₂ : 4*c^3+27*b^2=0 := hce.2
        have h₃ : a^3=c^3 := by linarith
        obtain rfl := (show Odd 3 by decide).pow_injective h₃
        rfl
    rw [Set.ncard_coe_finset,Int.card_Icc] at bound
    omega
  change Tendsto (fun H : ℕ => ((S H).ncard : ℝ) / (H : ℝ)^(5/6 : ℝ)) atTop (𝓝 0)
  have hlim : Tendsto (fun H : ℕ => (3 : ℝ)*(H : ℝ)^(-(1/3 : ℝ))) atTop (𝓝 0) := by
    simpa using (((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/3)).comp
      tendsto_natCast_atTop_atTop).const_mul (3 : ℝ))
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => by positivity) _ hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with H hH
  have hx : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hx' : (0 : ℝ) < H := by linarith
  have hs := Real.nat_sqrt_le_real_sqrt (a := H)
  have hsq : (1 : ℝ) ≤ Real.sqrt H := by simpa using Real.sqrt_le_sqrt hx
  have hcc : ((S H).ncard : ℝ) ≤ 2*(H.sqrt : ℝ)+1 := by exact_mod_cast count H
  calc
    _ ≤ 3*Real.sqrt H / (H : ℝ)^(5/6 : ℝ) := by gcongr; linarith
    _ = _ := by
      rw [Real.sqrt_eq_rpow, mul_div_assoc, ← Real.rpow_sub hx']
      norm_num
end OMA.SingularCurves
end

theorem OMA.solution : type_of% @EllipticCurveRank.RatEllipticCurve.card_heightLE_div_pow_five_div_six_tensto :=
  OMA.R_EllipticCurveRank_RatEllipticCurve_card_heightLE_div_pow_five_div_six_tensto_R1.main
    OMA.CoefficientSieve.coefficient_density OMA.SingularCurves.negligible
