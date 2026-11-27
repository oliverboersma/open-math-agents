import OMAReductions.R_ElliottHalberstamConjecture_elliott_halberstam_variants_bombieri_vinogradov_R1
import Mathlib

/-! The two inputs are the imprimitive character reduction and the primitive
maximal mean. Their common conductor weight uses the normalization of
@kimihiro64's Bombieri–Vinogradov project, commit
7a1748306e026825ed6a5555516cc2f28989b2ac (Apache-2.0). -/
namespace OMA.R_ElliottHalberstamConjecture_elliott_halberstam_variants_bombieri_vinogradov_R1_H1_R1

open Finset Real Filter ArithmeticFunction
open scoped Classical

/-- Orthogonality, induction of characters and the summed Euler correction. -/
def H1 : Prop :=
  let P (x d : ℕ) := (∑ χ ∈ ((Finset.univ.filter
    (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)).erase 1),
      (Finset.range (x+1)).sup' (by simp) (fun y => ‖∑ n ∈ Icc 1 y,
        (Λ n : ℂ) * χ (n : ZMod d)‖)) / (d.totient : ℝ)
  ∀ x Q : ℕ, 2 < x → ∃ M : ℕ → ℝ,
    (∀ q ∈ Icc 1 Q, ∀ a : (ZMod q)ˣ, ∀ t ≤ x,
      |∑ n ∈ Icc 1 t, ((if (n : ZMod q) = (a : ZMod q) then (1:ℝ) else 0)
        - 1/q.totient) * (Λ n : ℝ)| ≤ M q) ∧
    ∑ q ∈ Icc 1 Q, M q ≤ (1 + Real.log Q)^2 * (∑ d ∈ Icc 1 Q, P x d) +
      Q * Real.log Q * Real.log x / Real.log 2

/-- Arbitrary logarithmic saving in the primitive nonprincipal conductor mean. -/
def H2 : Prop :=
  let P (x d : ℕ) := (∑ χ ∈ ((Finset.univ.filter
    (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)).erase 1),
      (Finset.range (x+1)).sup' (by simp) (fun y => ‖∑ n ∈ Icc 1 y,
        (Λ n : ℂ) * χ (n : ZMod d)‖)) / (d.totient : ℝ)
  ∀ θ : ℝ, θ < 1/2 → ∀ B : ℝ, 0 < B → ∃ C > (0:ℝ), ∀ x : ℕ, 2 < x →
    ∑ d ∈ Icc 1 ⌊(x:ℝ)^θ⌋₊, P x d ≤ C*x/(Real.log x)^B

lemma cutoff_log_cost {θ B : ℝ} (ht : θ < 1) (hb : 0 < B) :
    ∃ D > (0:ℝ), ∀ x : ℕ, 2 < x → (⌊(x:ℝ)^θ⌋₊:ℝ) * (Real.log x)^B ≤ D*x := by
  let e := (1-θ)/B
  have he : 0<e := div_pos (sub_pos.mpr ht) hb
  refine ⟨1/e^B, by positivity, ?_⟩
  intro x hx
  have xp : (0:ℝ)<x := by exact_mod_cast (by omega : 0<x)
  have x1 : (1:ℝ) ≤ x := by exact_mod_cast (by omega : 1≤x)
  have lw := rpow_le_rpow (log_nonneg x1) (log_natCast_le_rpow_div x he) hb.le
  rw [div_rpow (by positivity) he.le, ← rpow_mul xp.le] at lw
  have powId : θ+e*B = 1 := by dsimp [e]; field_simp; ring
  calc
    _ ≤ (x:ℝ)^θ * (x^(e*B)/e^B) :=
      mul_le_mul (Nat.floor_le (rpow_nonneg xp.le θ)) lw (rpow_nonneg (log_nonneg x1) _) (rpow_nonneg xp.le _)
    _ = (x:ℝ)^(θ+e*B)/e^B := by rw [rpow_add xp]; ring
    _ = _ := by rw [powId,rpow_one]; ring

theorem main : H1 → H2 → OMA.R_ElliottHalberstamConjecture_elliott_halberstam_variants_bombieri_vinogradov_R1.H1 := by
  intro lift prim θ ht A ha
  obtain ⟨C,hC,hm⟩ := prim θ ht (A+2) (by linarith)
  obtain ⟨D,hD,hd⟩ := cutoff_log_cost (B := A+2) (by linarith : θ<1) (by linarith)
  have l2 : 0 < Real.log 2 := log_pos (by norm_num)
  refine ⟨4*C+D/Real.log 2, by positivity, ?_⟩
  intro x hx
  let Q := ⌊(x:ℝ)^θ⌋₊
  obtain ⟨M,major,total⟩ := lift x Q hx
  refine ⟨M,major,total.trans ?_⟩
  have x3 : (3:ℝ) ≤ x := by exact_mod_cast (by omega : 3 ≤ x)
  have xp : (0:ℝ)<x := by linarith
  have x1 : (1:ℝ) ≤ x := by linarith
  have L : 1 ≤ Real.log x := (le_log_iff_exp_le xp).mpr (Real.exp_one_lt_d9.le.trans (by linarith))
  have lpos : 0 < Real.log x := by linarith
  have qx : (Q:ℝ) ≤ x := (Nat.floor_le (rpow_nonneg xp.le θ)).trans (by
    simpa using (rpow_le_rpow_of_exponent_le x1 (by linarith : θ ≤ 1)))
  have lq : 0 ≤ Real.log Q ∧ Real.log Q ≤ Real.log x := by
    by_cases z : Q=0
    · simp [z, lpos.le]
    have q1 : (1:ℝ) ≤ Q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr z
    exact ⟨log_nonneg q1,log_le_log (by linarith) qx⟩
  have logs : (1+Real.log Q)^2 ≤ 4*(Real.log x)^2 := by
    have lo : 0 ≤ 2*Real.log x-(1+Real.log Q) := by linarith [lq.2]
    have hi : 0 ≤ 2*Real.log x+(1+Real.log Q) := by linarith [lq.1]
    nlinarith [mul_nonneg lo hi]
  have prod : (Real.log x)^(A+2) = (Real.log x)^A * (Real.log x)^2 := by rw [rpow_add lpos,rpow_two]
  have liftBound := mul_le_mul_of_nonneg_left (hm x hx) (sq_nonneg (1+Real.log Q))
  refine (add_le_add liftBound (le_refl _)).trans ?_
  have lA := rpow_pos_of_pos lpos A
  have first : (1+Real.log Q)^2 * (C*x/(Real.log x)^(A+2)) ≤ 4*C*x/(Real.log x)^A := by
    calc
      _ ≤ 4*(Real.log x)^2 * (C*x/(Real.log x)^(A+2)) := by gcongr
      _ = _ := by rw [prod]; field_simp
  have second : (Q:ℝ)*Real.log Q*Real.log x/Real.log 2 ≤ (D/Real.log 2)*x/(Real.log x)^A := by
    apply (le_div_iff₀ lA).mpr
    have est : (Q:ℝ) * (Real.log x)^A * (Real.log x)^2 ≤ D*x := by
      simpa only [prod, mul_assoc] using hd x hx
    have hqmul := mul_le_mul_of_nonneg_left lq.2 (show 0 ≤ (Q:ℝ)*Real.log x*(Real.log x)^A by positivity)
    calc
      _ = ((Q:ℝ)*Real.log Q*Real.log x*(Real.log x)^A)/Real.log 2 := by ring
      _ ≤ (D*x)/Real.log 2 := div_le_div_of_nonneg_right (by nlinarith) l2.le
      _ = _ := by ring
  calc
    _ ≤ 4*C*x/(Real.log x)^A + (D/Real.log 2)*x/(Real.log x)^A := add_le_add first second
    _ = _ := by ring
end OMA.R_ElliottHalberstamConjecture_elliott_halberstam_variants_bombieri_vinogradov_R1_H1_R1

