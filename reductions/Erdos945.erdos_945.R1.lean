/-
Copyright 2026 Jonathan Kleid.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.ErdosProblems.«945»

/-! A squarefree-gap criterion for the maximal run of distinct divisor counts.
The lemmas about the maximal run are adapted from Jonathan Kleid,
jkleid/erdos945-equivalence@a8ec707e749946646455ecd749afd45169098840,
Apache-2.0. The squarefree block argument follows the observation proposed in
the pinned formal-conjectures statement. -/
-- Credit: @marcusbuffett

open Filter Real

namespace Erdos945

/- ### Groundwork on F -/

/-- The witness set defining F x. -/
private def runSet (x : ℝ) : Set ℕ := {k | ∃ (n : ℕ), n + k ≤ x ∧ (Set.Ioc n (n + k)).InjOn τ}

lemma F_def' (x : ℝ) : F x = sSup (runSet x) := rfl

lemma runSet_bddAbove (x : ℝ) : BddAbove (runSet x) := by
  refine ⟨⌊x⌋.toNat, fun k hk => ?_⟩
  obtain ⟨n, hnk, -⟩ := hk
  have h1 : (k : ℝ) ≤ x :=
    le_trans (le_add_of_nonneg_left (Nat.cast_nonneg n)) hnk
  have h2 : (k : ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr (by exact_mod_cast h1)
  have h3 := Int.toNat_le_toNat h2
  simpa using h3

lemma zero_mem_runSet {x : ℝ} (hx : 0 ≤ x) : 0 ∈ runSet x :=
  ⟨0, by simpa using hx, by simp⟩

lemma F_mem_runSet {x : ℝ} (hx : 0 ≤ x) : F x ∈ runSet x :=
  Nat.sSup_mem ⟨0, zero_mem_runSet hx⟩ (runSet_bddAbove x)

end Erdos945

namespace OMA.R_Erdos945_erdos_945_R1
open Erdos945 Filter Real

/-- A uniform polylogarithmic bound on the gaps between squarefree integers,
on the dyadic scale n ≤ 2^m. -/
def H1 : Prop := ∃ A D : ℕ, ∀ m n : ℕ, n ≤ 2^m →
  ∃ q : ℕ, n < q ∧ q ≤ n + D*(m+1)^A ∧ Squarefree q

/-- The exact divisor count of a squarefree integer. -/
def H2 : Prop := ∀ n : ℕ, Squarefree n → τ n = 2^n.primeFactors.card

private theorem length_le (spec : ∀ n : ℕ, Squarefree n → τ n = 2^n.primeFactors.card) {m n k L : ℕ} (hmax : n+k ≤ 2^m)
    (hrun : (Set.Ioc n (n+k)).InjOn τ)
    (hits : ∀ a : ℕ, a ≤ 2^m → ∃ b : ℕ, a < b ∧ b ≤ a+L ∧ Squarefree b) :
    k ≤ (m+2)*L := by
  classical
  by_contra! hlong
  have hstart (j : Fin (m+2)) : n+j.val*L ≤ 2^m := by
    have hb := Nat.mul_le_mul_right L j.isLt.le
    omega
  choose q hqlo hqhi hsq using fun j : Fin (m+2) => hits _ (hstart j)
  have hmem (j : Fin (m+2)) : q j ∈ Set.Ioc n (n+k) := by
    have hh := hqhi j
    have hlo := hqlo j
    have hb' := Nat.mul_le_mul_right L (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at hb'
    exact ⟨by omega, by omega⟩
  have hmono : StrictMono q := by
    intro i j hij
    have hb := Nat.mul_le_mul_right L (Nat.succ_le_of_lt (show i.val < j.val from hij))
    rw [Nat.succ_mul] at hb
    have h₁ := hqhi i
    have h₂ := hqlo j
    omega
  have hexp (j : Fin (m+2)) : (q j).primeFactors.card ≤ m := by
    apply (pow_le_pow_iff_right₀ (by decide : 1 < (2:ℕ))).1
    rw [←spec _ (hsq j)]
    exact (Nat.card_divisors_le_self _).trans ((hmem j).2.trans hmax)
  let f (j : Fin (m+2)) : Fin (m+1) := ⟨(q j).primeFactors.card, Nat.lt_succ_of_le (hexp j)⟩
  have hf : Function.Injective f := by
    intro i j he
    apply hmono.injective
    apply hrun (hmem i) (hmem j)
    rw [spec _ (hsq i), spec _ (hsq j)]
    exact congrArg (fun t : ℕ => 2^t) (congrArg Fin.val he)
  have hn := Fintype.card_le_of_injective f hf
  simp at hn

theorem main : H1 → H2 → type_of% @Erdos945.erdos_945 := by
  rintro ⟨A,D,gap⟩ spec
  let d : ℕ := 2*A+3
  refine ⟨fun _ => (d:ℝ), Asymptotics.isBigO_const_const _ (one_ne_zero : (1:ℝ) ≠ 0) atTop,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop
    (max (D:ℝ) (max 1 ((Real.log 2)⁻¹+3)))] with x hx hlog
  let m := ⌈Real.logb 2 x⌉₊
  have hxpos : 0 < x := by linarith
  have hm : x ≤ (2:ℝ)^m := by
    rw [← Real.rpow_natCast, ←Real.rpow_logb (by norm_num : 0 < (2:ℝ)) (by norm_num) hxpos]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  obtain ⟨n,hbound,hrun⟩ := Erdos945.F_mem_runSet hxpos.le
  have hn : n + F x ≤ (2:ℕ)^m := by exact_mod_cast hbound.trans hm
  have hb := length_le spec hn hrun (gap m)
  have hL : 1 ≤ log x := le_trans (le_max_left _ _) ((le_max_right _ _).trans hlog)
  have hK : (log 2)⁻¹+3 ≤ log x := le_trans (le_max_right _ _) ((le_max_right _ _).trans hlog)
  have hD : (D:ℝ) ≤ log x := (le_max_left _ _).trans hlog
  have hbpos := Real.log_nonneg hx
  have hlogb : 0 ≤ Real.logb 2 x := by rw [Real.logb]; positivity
  have hceil : (m:ℝ) < Real.logb 2 x + 1 := Nat.ceil_lt_add_one hlogb
  have hmsq : (m:ℝ)+2 ≤ log x ^ 2 := by
    rw [Real.logb,div_eq_mul_inv] at hceil
    nlinarith [mul_le_mul_of_nonneg_right hK hbpos]
  have hsq : (m:ℝ)+1 ≤ log x ^ 2 := by linarith
  have hbc : (F x : ℝ) ≤ ((m:ℝ)+2) * ((D:ℝ)*((m:ℝ)+1)^A) := by exact_mod_cast hb
  calc
    (F x:ℝ) ≤ _ := hbc
    _ ≤ (log x)^2 * (log x * ((log x)^2)^A) := by
      gcongr
    _ = (log x)^d := by dsimp [d]; rw [pow_add,pow_mul]; ring
    _ = Real.rpow (log x) (d:ℝ) := (Real.rpow_natCast _ _).symm
end OMA.R_Erdos945_erdos_945_R1
