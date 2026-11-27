import OMAReductions.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1
import Mathlib

/-! Expanding the variance separates the diagonal from ordered pairs at
nonzero square-divisible differences. For small sets, counting prime
divisors suffices. The remaining discrepancy estimate concerns only
sets larger than N to the power 7/15. -/
namespace OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1
open Finset Real Filter
open scoped Classical

/-- Elementary sparse estimate by the number of prime divisors of each nonzero difference. -/
def H1 : Prop := ∀ N X : ℕ, 1 ≤ N → ∀ A ⊆ Icc 1 N,
  let P := (range (X+1)).filter Nat.Prime
  let C (p : ℕ) := ((A ×ˢ A).filter (fun t => t.1 ≠ t.2 ∧ t.1%(p*p) = t.2%(p*p))).card
  ∑ p ∈ P, ((p*p:ℕ):ℝ)*C p ≤ 2*(X:ℝ)^2*log N*(A.card:ℝ)^2

/-- Konyagin’s off-diagonal discrepancy for dense sets at the square-modulus cutoff. -/
def H2 : Prop := ∀ η : ℝ, 0<η → ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Icc 1 N,
  let Z := (A.card:ℝ)
  let X := ⌊(N:ℝ)^(4/15:ℝ)⌋₊
  let P := (range (X+1)).filter Nat.Prime
  let C (p : ℕ) := ((A ×ˢ A).filter (fun t => t.1 ≠ t.2 ∧ t.1%(p*p) = t.2%(p*p))).card
  (N:ℝ)^(7/15:ℝ) < Z →
    ∑ p ∈ P, ((p*p:ℕ):ℝ)*C p ≤ P.card*Z^2 +
      (N:ℝ)^η*((N:ℝ)*Z+(N:ℝ)^(64/75:ℝ)*Z^(6/5:ℝ))

lemma pair_identity (A : Finset ℕ) (q : ℕ) (hq : 0<q) :
    (q:ℝ)*(∑ h ∈ range q, (((A.filter (fun a => a%q=h)).card:ℝ)-A.card/(q:ℝ))^2) =
      q*(A.card + (((A ×ˢ A).filter (fun t => t.1 ≠ t.2 ∧ t.1%q=t.2%q)).card:ℝ))-(A.card:ℝ)^2 := by
  let F h := A.filter (fun a => a%q=h)
  let T := (A ×ˢ A).filter (fun t => t.1%q=t.2%q)
  let C := (A ×ˢ A).filter (fun t => t.1 ≠ t.2 ∧ t.1%q=t.2%q)
  have S₁ : ∑ h ∈ range q, (F h).card = A.card :=
    (card_eq_sum_card_fiberwise (f:=fun a => a%q) (fun _ _ => mem_range.mpr (Nat.mod_lt _ hq))).symm
  have S₂ : ∑ h ∈ range q, ((F h).card)^2 = T.card := by
    rw [card_eq_sum_card_fiberwise (s:=T) (t:=range q) (f:=fun t => t.1%q)
      (fun _ _ => mem_range.mpr (Nat.mod_lt _ hq))]
    refine sum_congr rfl fun h _ => ?_
    rw [pow_two,←card_product]
    congr 1
    ext t
    simp only [F,T,mem_product,mem_filter]
    aesop
  have tD : T.filter (fun t => t.1=t.2) = A.diag := by
    ext t
    simp only [T,mem_filter,mem_product,mem_diag]
    aesop
  have tC : T.filter (fun t => ¬t.1=t.2) = C := by
    ext t
    simp only [T,C,mem_filter]
    tauto
  have tot := card_filter_add_card_filter_not (s:=T) (fun t => t.1=t.2)
  rw [tD,tC,diag_card] at tot
  have r₁ : ∑ h ∈ range q, ((F h).card:ℝ) = A.card := by exact_mod_cast S₁
  have r₂ : ∑ h ∈ range q, ((F h).card:ℝ)^2 = A.card+C.card := by exact_mod_cast S₂.trans tot.symm
  have q0 : (q:ℝ) ≠ 0 := by positivity
  change (q:ℝ)*(∑ h ∈ range q, (((F h).card:ℝ)-A.card/q)^2) = q*(A.card+C.card)-(A.card:ℝ)^2
  simp_rw [sub_sq]
  rw [sum_add_distrib,sum_sub_distrib]
  simp only [sum_const,card_range,nsmul_eq_mul]
  rw [←sum_mul,←mul_sum,r₁,r₂]
  field_simp
  <;> ring

theorem main : H1 → H2 → OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1.H1 := by
  intro sparse dense η hη
  have de := dense (η/2) (by positivity)
  have lg := (isLittleO_log_rpow_atTop hη).bound (show (0:ℝ)<1/4 by norm_num)
  have big := (tendsto_rpow_atTop (show 0<η/2 by positivity)).eventually_ge_atTop (2:ℝ)
  filter_upwards [de,tendsto_natCast_atTop_atTop.eventually lg,
    tendsto_natCast_atTop_atTop.eventually big,eventually_ge_atTop (1:ℕ)] with N hd hl hb hN
  intro A hA
  let Z := (A.card:ℝ)
  let X := ⌊(N:ℝ)^(4/15:ℝ)⌋₊
  let P := (range (X+1)).filter Nat.Prime
  let C (p : ℕ) := ((A ×ˢ A).filter (fun t => t.1 ≠ t.2 ∧ t.1%(p*p)=t.2%(p*p))).card
  let V := (N:ℝ)*Z + (N:ℝ)^(64/75:ℝ)*Z^(6/5:ℝ)
  have zn : 0≤Z := Nat.cast_nonneg _
  have n1 : (1:ℝ)≤N := by exact_mod_cast hN
  have np : (0:ℝ)<N := by linarith
  have logN := log_nonneg n1
  have epos := rpow_pos_of_pos np η
  have vv : (N:ℝ)*Z ≤ V := le_add_of_nonneg_right (by positivity)
  have vpos : 0≤V := (mul_nonneg np.le zn).trans vv
  have cap : (X:ℝ) ≤ (N:ℝ)^(4/15:ℝ) := Nat.floor_le (rpow_nonneg np.le _)
  have ps (p) (hp:p∈P) : p≤X := Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hp).1)
  have card : P.card ≤ X := by
    have sub : P ⊆ Icc 1 X := fun p hp => mem_Icc.mpr ⟨(mem_filter.mp hp).2.pos,ps p hp⟩
    simpa using card_le_card sub
  have diag : ∑ p ∈ P, ((p*p:ℕ):ℝ)*Z ≤ (N:ℝ)*Z := by
    calc
      _ ≤ ∑ _p ∈ P, (X:ℝ)^2*Z := sum_le_sum fun p hp => by
        have le : (p:ℝ) ≤ X := by exact_mod_cast ps p hp
        push_cast
        rw [pow_two]
        gcongr
      _ = (P.card:ℝ)*((X:ℝ)^2*Z) := by simp
      _ ≤ (X:ℝ)*((X:ℝ)^2*Z) := mul_le_mul_of_nonneg_right (by exact_mod_cast card) (by positivity)
      _ = (X:ℝ)^3*Z := by ring
      _ ≤ ((N:ℝ)^(4/15:ℝ))^3*Z := by gcongr
      _ ≤ (N:ℝ)*Z := by
        apply mul_le_mul_of_nonneg_right _ zn
        rw [←Real.rpow_natCast,←Real.rpow_mul np.le]
        simpa using rpow_le_rpow_of_exponent_le n1 (by norm_num : (4/15:ℝ)*(3:ℕ) ≤ 1)
  let E := ∑ p ∈ P, ((p*p:ℕ):ℝ)*C p
  have variance :
      ∑ p ∈ P, ((p*p:ℕ):ℝ)*∑ h ∈ range (p*p), (((A.filter (fun a => a%(p*p)=h)).card:ℝ)-Z/(p*p:ℕ))^2 =
      (∑ p ∈ P, ((p*p:ℕ):ℝ)*Z) + E - P.card*Z^2 := by
    calc
      _ = ∑ p ∈ P, (((p*p:ℕ):ℝ)*Z + ((p*p:ℕ):ℝ)*C p - Z^2) := by
        refine sum_congr rfl fun p hp => ?_
        have := pair_identity A (p*p) (Nat.mul_pos (mem_filter.mp hp).2.pos (mem_filter.mp hp).2.pos)
        simpa only [Z,C,mul_add] using this
      _ = _ := by simp [E,sum_sub_distrib,sum_add_distrib]
  change _ ≤ (N:ℝ)^η*V
  rw [variance]
  have poweq : (N:ℝ)^η = ((N:ℝ)^(η/2))^2 := by rw [←rpow_natCast,←rpow_mul np.le]; congr 1; ring
  have coeff : 1+(N:ℝ)^(η/2) ≤ (N:ℝ)^η := by rw [poweq]; nlinarith
  by_cases hz : (N:ℝ)^(7/15:ℝ) < Z
  · have hden : E ≤ P.card*Z^2 + (N:ℝ)^(η/2)*V := hd A hA hz
    have hh := mul_le_mul_of_nonneg_right coeff vpos
    nlinarith only [diag,vv,hden,hh]
  · have zs := le_of_not_gt hz
    have scale : (X:ℝ)^2*Z ≤ N := by
      calc
        _ ≤ ((N:ℝ)^(4/15:ℝ))^2*((N:ℝ)^(7/15:ℝ)) := by gcongr
        _ = _ := by rw [←rpow_natCast,←rpow_mul np.le,←rpow_add np]; norm_num
    have bound : E ≤ 2*(X:ℝ)^2*log N*Z^2 := sparse N X hN A hA
    have sb := mul_le_mul_of_nonneg_right scale (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) logN) zn)
    have logc : log N ≤ 1/4*(N:ℝ)^η := by simpa [Real.norm_eq_abs,abs_of_nonneg logN,abs_of_pos epos] using hl
    have large : 4 ≤ (N:ℝ)^η := by rw [poweq]; nlinarith
    have sc : 1+2*log N ≤ (N:ℝ)^η := by linarith
    have hbudget := mul_le_mul_of_nonneg_right sc (mul_nonneg np.le zn)
    have hfull := mul_le_mul_of_nonneg_left vv epos.le
    have nn : 0 ≤ (P.card:ℝ)*Z^2 := by positivity
    nlinarith only [diag,bound,sb,hbudget,hfull,nn]

end OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1
