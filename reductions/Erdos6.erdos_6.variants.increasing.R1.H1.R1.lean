import OMAReductions.R_Erdos6_erdos_6_variants_increasing_R1
import Mathlib

/-!
# Bombieri–Vinogradov via primitive characters

The conductor decomposition is the one used by @nil-commits in Arithmetica4,
RHDirect/Stage11BombieriVinogradov.lean, commit
023f6441c22a9ca0db1670e351e8ac44f00555ea (Apache-2.0).
The principal character contributes the ordinary prime number theorem.
The nonprincipal contribution is a weighted mean of primitive character sums.
Removing higher prime powers costs at most a square-root error per modulus.
-/
namespace OMA.R_Erdos6_erdos_6_variants_increasing_R1_H1_R1
open Filter Real Finset Asymptotics
open scoped ArithmeticFunction.vonMangoldt Classical Topology

/-- Quantitative prime number theorem for the principal contribution. -/
def H1 : Prop := ∀ A : ℝ, 0<A →
  (fun x : ℝ => (∑ n ∈ range (⌊x⌋₊+1), (Λ n : ℝ))-x)
    =o[atTop] fun x : ℝ => x/(log x)^A

/-- Averaged von Mangoldt sums over primitive characters of conductor at least three. -/
def H2 : Prop := ∀ A : ℝ, 0<A → ∃ B C : ℝ, A+3≤B ∧ 0<C ∧ ∀ᶠ x : ℝ in atTop,
  (∑ k ∈ Ico 2 ⌊sqrt x/(log x)^B⌋₊, (1/(Nat.totient (k+1):ℝ)) *
    ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ (k+1) => χ.IsPrimitive),
      ‖∑ n ∈ range (⌊x⌋₊+1), χ (n : ZMod (k+1)) * (Λ n : ℂ)‖) ≤ C*x/(log x)^A

/-- Character orthogonality and passage to primitive conductors, including the cost
of deleting higher prime powers when returning to primes. -/
def H3 : Prop := ∀ x : ℝ, 3≤x → ∀ Q : ℕ, 1≤Q → (Q:ℝ)≤x →
  ∀ a : ℕ→ℕ, (∀ q, Nat.Coprime (a q) q) →
  (∑ q ∈ Icc 1 Q, |∑ p ∈ (range (⌊x⌋₊+1)).filter (fun p => p.Prime ∧ p%q=a q%q),
    log p - x/(Nat.totient q:ℝ)|) ≤
    2*Q*sqrt x*log x + 12*log x*(|(∑ n ∈ range (⌊x⌋₊+1), (Λ n:ℝ))-x| + 2*(log x)^2) +
    Q*(log x)^2 + 12*log x*
      ∑ k ∈ Ico 2 Q, (1/(Nat.totient (k+1):ℝ)) *
        ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ (k+1) => χ.IsPrimitive),
          ‖∑ n ∈ range (⌊x⌋₊+1), χ (n : ZMod (k+1)) * (Λ n : ℂ)‖

lemma bounded_range {X A B : ℝ} (hX : 3≤X) (hA : 0<A) (hB : 0≤B) :
    ∃ C : ℝ, 0≤C ∧ ∀ x : ℝ, 2≤x → x≤X → ∀ a : ℕ→ℕ,
      (∑ q ∈ Icc 1 ⌊sqrt x/(log x)^B⌋₊,
        |∑ p ∈ (range (⌊x⌋₊+1)).filter (fun p => p.Prime ∧ p%q=a q%q),
          log p - x/(Nat.totient q:ℝ)|) ≤ C*x/(log x)^A := by
  let K := ⌊sqrt X/(log 2)^B⌋₊
  let T := ((⌊X⌋₊:ℝ)+1)*X+X
  have Xp : 0<X := by linarith
  have l2 : 0<log 2 := log_pos (by norm_num)
  have lX : 0<log X := log_pos (by linarith)
  have T0 : 0≤T := by dsimp [T]; positivity
  refine ⟨K*T*(log X)^A,by positivity,?_⟩
  intro x hx hxX a
  have xp : 0<x := by linarith
  have lx : 0<log x := log_pos (by linarith)
  have lp := rpow_pos_of_pos lx A
  let Q := ⌊sqrt x/(log x)^B⌋₊
  have qK : Q≤K := Nat.floor_mono (div_le_div₀ (sqrt_nonneg _)
    (sqrt_le_sqrt hxX) (rpow_pos_of_pos l2 B)
    (rpow_le_rpow l2.le (log_le_log (by norm_num) hx) hB))
  have count (q:ℕ) : ((range (⌊x⌋₊+1)).filter (fun p => p.Prime ∧ p%q=a q%q)).card ≤ ⌊X⌋₊+1 :=
    (card_filter_le _ _).trans (by simpa using Nat.add_le_add_right (Nat.floor_mono hxX) 1)
  have each (q : ℕ) (hq : q∈Icc 1 Q) :
      |∑ p ∈ (range (⌊x⌋₊+1)).filter (fun p => p.Prime ∧ p%q=a q%q),
        log p - x/(Nat.totient q:ℝ)| ≤ T := by
    let S := (range (⌊x⌋₊+1)).filter (fun p => p.Prime ∧ p%q=a q%q)
    have su : (∑ p ∈ S, log p) ≤ ((⌊X⌋₊:ℝ)+1)*X := by
      calc _ ≤ ∑ p ∈ S, X := by
             apply sum_le_sum; intro p hp
             have pp := (mem_filter.mp hp).2.1
             have pn := mem_range.mp (mem_filter.mp hp).1
             have le : (p:ℝ)≤x := (show (p:ℝ)≤⌊x⌋₊ by exact_mod_cast (show p≤⌊x⌋₊ by omega)).trans (Nat.floor_le xp.le)
             exact (log_le_self (by exact_mod_cast pp.pos.le)).trans (le.trans hxX)
           _ ≤ _ := by
             rw [sum_const,nsmul_eq_mul]
             exact mul_le_mul_of_nonneg_right (by exact_mod_cast count q) Xp.le
    have sl : 0≤∑ p ∈ S, log p := sum_nonneg (fun p hp =>
      log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.1.one_le))
    have tq : 1≤(Nat.totient q:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (mem_Icc.mp hq).1
    have dv := div_le_self xp.le tq
    change |(∑ p ∈ S, log p)-x/(Nat.totient q:ℝ)|≤T
    dsimp only [T]
    rw [abs_le]
    constructor <;> nlinarith [div_nonneg xp.le (by positivity : (0:ℝ)≤Nat.totient q),
      mul_nonneg (by positivity : 0≤(⌊X⌋₊:ℝ)+1) Xp.le]
  have est : (∑ q ∈ Icc 1 Q, |∑ p ∈ (range (⌊x⌋₊+1)).filter
      (fun p => p.Prime ∧ p%q=a q%q), log p-x/(Nat.totient q:ℝ)|) ≤ K*T := by
    calc _ ≤ ∑ _q ∈ Icc 1 Q, T := sum_le_sum each
         _ ≤ _ := by simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]; gcongr
  apply (le_div_iff₀ lp).mpr
  calc _ ≤ K*T*(log X)^A := mul_le_mul est (rpow_le_rpow lx.le (log_le_log xp hxX) hA.le) lp.le (by positivity)
       _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith)

lemma large_range (pnt : H1) (mean : H2) (liftBound : H3) (A : ℝ) (hA : 0<A) :
    ∃ B C : ℝ, 0≤B ∧ 0<C ∧ ∀ᶠ x : ℝ in atTop, ∀ a : ℕ→ℕ, (∀ q, Nat.Coprime (a q) q) →
    (∑ q ∈ Icc 1 ⌊sqrt x/(log x)^B⌋₊,
      |∑ p ∈ (range (⌊x⌋₊+1)).filter (fun p => p.Prime ∧ p%q=a q%q),
        log p-x/(Nat.totient q:ℝ)|) ≤ C*x/(log x)^A := by
  obtain ⟨B,C,hB,hC,hm⟩ := mean (A+1) (by linarith)
  have he := (pnt (A+1) (by linarith)).bound zero_lt_one
  have growth := (isLittleO_log_rpow_rpow_atTop (A+3) (show 0<(1/2:ℝ) by norm_num)).bound zero_lt_one
  refine ⟨B,39+12*C,by linarith,by positivity,?_⟩
  filter_upwards [he,hm,growth,eventually_ge_atTop (3:ℝ),tendsto_log_atTop.eventually_ge_atTop 1]
    with x hp hm hg hx hl
  intro a ha
  let L := log x
  let R := L^A
  let Q := ⌊sqrt x/L^B⌋₊
  let P := |(∑ n ∈ range (⌊x⌋₊+1),(Λ n:ℝ))-x|
  let S := ∑ k ∈ Ico 2 Q, (1/(Nat.totient (k+1):ℝ)) *
      ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ (k+1) => χ.IsPrimitive),
        ‖∑ n ∈ range (⌊x⌋₊+1), χ (n : ZMod (k+1)) * (Λ n : ℂ)‖
  have xp : 0<x := by linarith
  have lp : 0<L := by dsimp [L]; linarith
  have l1 : 1≤L := hl
  have rp : 0<R := rpow_pos_of_pos lp _
  have ap : L^(A+1)=R*L := by rw [rpow_add lp,rpow_one]
  have a3 : L^(A+3)=R*L^3 := by rw [rpow_add lp]; norm_num [R]
  have ht : 1≤L^B := one_le_rpow l1 (by linarith)
  have su : sqrt x ≤ x := (sqrt_le_sqrt (show x≤x^2 by nlinarith)).trans_eq (sqrt_sq xp.le)
  have sq := Real.sq_sqrt xp.le
  have qle : (Q:ℝ) * L^B ≤ sqrt x :=
    (le_div_iff₀ (rpow_pos_of_pos lp _)).mp (Nat.floor_le (by positivity))
  have qr : (Q:ℝ) ≤ sqrt x :=
    (le_mul_of_one_le_right (Nat.cast_nonneg _) ht).trans qle
  have qrl : (Q:ℝ)*(R*L) ≤ sqrt x := by
    rw [←ap]
    exact (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le l1 (by linarith)) (Nat.cast_nonneg _)).trans qle
  have power : R*L^3 ≤ sqrt x := by
    change ‖L^(A+3)‖ ≤ 1*‖x^(1/2:ℝ)‖ at hg
    rw [Real.norm_eq_abs,abs_of_pos (rpow_pos_of_pos lp _),one_mul,
      Real.norm_eq_abs,abs_of_pos (rpow_pos_of_pos xp _),←sqrt_eq_rpow,a3] at hg
    exact hg
  have psl : P*(R*L) ≤ x := by
    change ‖(∑ n ∈ range (⌊x⌋₊+1),(Λ n:ℝ))-x‖ ≤ 1*‖x/L^(A+1)‖ at hp
    rw [Real.norm_eq_abs,one_mul,Real.norm_eq_abs,abs_of_pos (div_pos xp (rpow_pos_of_pos lp _)),ap] at hp
    exact (le_div_iff₀ (mul_pos rp lp)).mp hp
  have msl : S*(R*L) ≤ C*x := by
    change S≤C*x/L^(A+1) at hm
    rw [ap] at hm
    exact (le_div_iff₀ (mul_pos rp lp)).mp hm
  have qp : (Q:ℝ)*sqrt x*L*R ≤ x := by
    nlinarith only [mul_le_mul_of_nonneg_right qrl (sqrt_nonneg x),sq]
  have pow2 : R*L^2 ≤ sqrt x := by
    apply le_trans _ power
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ l1 (by norm_num : 2≤3)) rp.le
  have qt : (Q:ℝ)*L^2*R ≤ x := by
    nlinarith only [mul_le_mul qr pow2 (mul_nonneg rp.le (sq_nonneg L)) (sqrt_nonneg x),sq]
  by_cases hQ : 1≤Q
  · have bound := liftBound x hx Q hQ (qr.trans su) a ha
    change _ ≤ 2*(Q:ℝ)*sqrt x*L+12*L*(P+2*L^2)+(Q:ℝ)*L^2+12*L*S at bound
    apply (le_div_iff₀ rp).mpr
    have t := mul_le_mul_of_nonneg_right bound rp.le
    nlinarith only [t,qp,qt,psl,msl,power.trans su]
  · have eq : Q=0 := by omega
    change (∑ q ∈ Icc 1 Q, _) ≤ _
    simp only [eq,show Icc 1 (0:ℕ)=∅ by decide,sum_empty]
    positivity

theorem main : H1 → H2 → H3 → OMA.R_Erdos6_erdos_6_variants_increasing_R1.H1 := by
  intro pnt mean liftBound A hA
  obtain ⟨B,C,B0,C0,h⟩ := large_range pnt mean liftBound A hA
  obtain ⟨Y,hY⟩ := eventually_atTop.1 h
  let X := max 3 Y
  obtain ⟨D,D0,hD⟩ := bounded_range (X:=X) (le_max_left _ _) hA B0
  refine ⟨B,max C D,?_⟩
  intro x hx a ha
  have xp : 0<x := by linarith
  have denom : 0≤(log x)^A := (rpow_pos_of_pos (log_pos (by linarith)) _).le
  by_cases hL : X≤x
  · exact (hY x ((le_max_right _ _).trans hL) a ha).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) xp.le) denom)
  · exact (hD x hx (le_of_not_ge hL) a).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) xp.le) denom)

end OMA.R_Erdos6_erdos_6_variants_increasing_R1_H1_R1
