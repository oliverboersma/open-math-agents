import FormalConjectures.Wikipedia.ElliottHalberstamConjecture
import Mathlib

/-! Use the maximal globally centered Mangoldt discrepancy, in the form
used in @kimihiro64's Apache-2.0 bombieri-vinogradov formalization
(commit 7a1748306e026825ed6a5555516cc2f28989b2ac).
Finite Abel summation removes the logarithmic weight. The higher prime
powers cost at most ψ(x)−ϑ(x) per modulus, which Chebyshev's bound absorbs
for every exponent strictly below one half. -/
namespace OMA.R_ElliottHalberstamConjecture_elliott_halberstam_variants_bombieri_vinogradov_R1

open Finset Real Filter ArithmeticFunction ElliottHalberstamConjecture

/-- The maximal weighted estimate, centered at the global Mangoldt sum. -/
def H1 : Prop := ∀ θ : ℝ, θ < 1/2 → ∀ A : ℝ, 0 < A → ∃ C > (0:ℝ),
  ∀ x : ℕ, 2 < x → ∃ M : ℕ → ℝ,
  (∀ q ∈ Icc 1 ⌊(x:ℝ)^θ⌋₊, ∀ a : (ZMod q)ˣ, ∀ t ≤ x,
    |∑ n ∈ Icc 1 t, ((if (n : ZMod q) = (a : ZMod q) then (1:ℝ) else 0)
      - 1 / q.totient) * (Λ n : ℝ)| ≤ M q) ∧
  ∑ q ∈ Icc 1 ⌊(x:ℝ)^θ⌋₊, M q ≤ C*x/(Real.log x)^A

/-- Finite partial summation for bounded coefficients: remove higher prime
powers, then remove log p using monotonicity of its reciprocal. -/
def H2 : Prop := ∀ (x : ℕ) (f : ℕ → ℝ) (M : ℝ), 2 ≤ x →
  (∀ n ≤ x, |f n| ≤ 1) →
  (∀ t ≤ x, |∑ n ∈ Icc 1 t, f n * (Λ n : ℝ)| ≤ M) →
  |∑ p ∈ Nat.primesLE x, f p| ≤ (M + (Chebyshev.psi x - Chebyshev.theta x)) / Real.log 2

lemma power_saving {θ A : ℝ} (ht : θ < 1/2) (ha : 0<A) :
    ∃ D > (0:ℝ), ∀ x : ℕ, 2<x →
      (⌊(x:ℝ)^θ⌋₊:ℝ) * (Chebyshev.psi x - Chebyshev.theta x) ≤ D*x/(Real.log x)^A := by
  obtain ⟨c,hc⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let K := max c 1
  have hk : 0<K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let e := (1/2-θ)/A
  have he : 0<e := div_pos (sub_pos.mpr ht) ha
  refine ⟨K/e^A,by positivity,?_⟩
  intro x hx
  have xp : (0:ℝ)<x := by exact_mod_cast (by omega : 0<x)
  have xl : (1:ℝ)<x := by exact_mod_cast (by omega : 1<x)
  have lg := log_pos xl
  have lw := rpow_le_rpow lg.le (log_natCast_le_rpow_div x he) ha.le
  rw [div_rpow (by positivity) he.le, ← rpow_mul xp.le] at lw
  have expid : θ + 1/2 + e*A = 1 := by dsimp [e]; field_simp; ring
  apply (le_div_iff₀ (rpow_pos_of_pos lg A)).2
  calc
    _ ≤ ((x:ℝ)^θ * (K*sqrt x)) * (Real.log x)^A := by
      apply mul_le_mul_of_nonneg_right _ (rpow_nonneg lg.le A)
      refine (mul_le_mul_of_nonneg_left ((hc x).trans (mul_le_mul_of_nonneg_right
        (le_max_left c 1) (sqrt_nonneg _))) (Nat.cast_nonneg _)).trans ?_
      exact mul_le_mul_of_nonneg_right (Nat.floor_le (rpow_nonneg xp.le θ)) (mul_nonneg hk.le (sqrt_nonneg _))
    _ ≤ ((x:ℝ)^θ * (K*sqrt x)) * (x^(e*A)/e^A) := by gcongr
    _ = K/e^A*((x:ℝ)^θ*x^(1/2:ℝ)*x^(e*A)) := by rw [sqrt_eq_rpow]; ring
    _ = _ := by rw [← rpow_add xp,← rpow_add xp,expid,rpow_one]

lemma residue_sum (x q : ℕ) (a : (ZMod q)ˣ) :
    (∑ n ∈ Nat.primesLE x, ((if (n : ZMod q) = (a : ZMod q) then (1:ℝ) else 0)
      - 1/q.totient)) = (x.primeCountingMod q a:ℝ) - (x.primeCounting:ℝ)/q.totient := by
  have sets : ((Nat.primesLE x).filter fun n : ℕ => (n : ZMod q) = (a : ZMod q)) =
      ((range (x+1)).filter fun n : ℕ => n.Prime ∧ (n : ZMod q) = (a : ZMod q)) := by
    ext n
    simp only [mem_filter,Nat.mem_primesLE,mem_range,Nat.lt_succ_iff,and_assoc]
  rw [sum_sub_distrib, sum_boole,sets,Nat.primeCountingMod,sum_const,nsmul_eq_mul,
    Nat.primesLE_card_eq_primeCounting]
  ring

theorem main : H1 → H2 → type_of% @ElliottHalberstamConjecture.elliott_halberstam.variants.bombieri_vinogradov := by
  classical
  intro weighted abel θ ht A ha
  obtain ⟨C,hc,h⟩ := weighted θ ht A ha
  obtain ⟨D,hd,err⟩ := power_saving ht ha
  have log2 : 0<Real.log 2 := log_pos (by norm_num)
  refine ⟨(C+D)/Real.log 2,by positivity,?_⟩
  intro x hx
  let Q := ⌊(x:ℝ)^θ⌋₊
  obtain ⟨M,major,mean⟩ := h x hx
  let r := Chebyshev.psi x - Chebyshev.theta x
  have each (q : ℕ) (hq : q ∈ Icc 1 Q) : E x q ≤ (M q + r)/Real.log 2 := by
    obtain ⟨qpos,_⟩ := mem_Icc.mp hq
    have φ : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr qpos
    unfold E
    apply ciSup_le
    intro a
    rw [← residue_sum]
    apply abel x _ (M q) (by omega) _ (major q hq a)
    intro n _
    have inv : (1:ℝ)/q.totient ≤ 1 := (div_le_one (by linarith)).mpr φ
    have nn : 0 ≤ (1:ℝ)/q.totient := by positivity
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  calc
    ∑ q ∈ Icc 1 Q, E x q ≤ ∑ q ∈ Icc 1 Q, (M q+r)/Real.log 2 := sum_le_sum each
    _ = ((∑ q ∈ Icc 1 Q, M q) + Q*r)/Real.log 2 := by
      rw [← sum_div,sum_add_distrib,sum_const,nsmul_eq_mul,Nat.card_Icc]
      simp
    _ ≤ (C*x/(Real.log x)^A + D*x/(Real.log x)^A)/Real.log 2 :=
      div_le_div_of_nonneg_right (add_le_add mean (err x hx)) log2.le
    _ = _ := by ring

end OMA.R_ElliottHalberstamConjecture_elliott_halberstam_variants_bombieri_vinogradov_R1
