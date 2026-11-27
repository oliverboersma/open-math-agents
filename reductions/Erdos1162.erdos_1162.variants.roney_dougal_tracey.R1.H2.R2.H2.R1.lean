import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2
import Mathlib

/-!
This uses the soluble-group stage of Proposition 8.7 and Theorem 8.4
(Aschbacher and Guralnick) of Roney-Dougal and Tracey, arXiv:2503.05416.

Counting a soluble subgroup together with one extra permutation costs at
most a factorial. Nilpotent subgroups of a block group inject into the
ambient nilpotent subgroups. Both comparisons are proved below.
-/

open Filter

namespace OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1

/-- The soluble-group step of Proposition 8.7. It suffices to count the
nilpotent subgroups of permutation groups with all orbit sizes below C. -/
def H1 : Prop := ∃ (C : ℕ) (κ : ℝ), 0 ≤ κ ∧ ∀ g : ℕ → ℝ, Monotone g →
  (∀ (n : ℕ) (D : Subgroup (Equiv.Perm (Fin n))),
    (∀ i : Fin n, Nat.card (MulAction.orbit D i) < C) →
    (Nat.card {H : Subgroup D // Group.IsNilpotent H} : ℝ) ≤ (2:ℝ)^((n:ℝ)^2/16 + g n)) →
  ∀ n : ℕ, (Nat.card {A : Subgroup (Equiv.Perm (Fin n)) // Group.IsSolvable A} : ℝ) ≤
    (2:ℝ)^((n:ℝ)^2/16 + g n + κ*n*Real.sqrt n)

/-- The one-extra-generator theorem, restricted to permutation groups. -/
def H2 : Prop := ∀ (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n))),
  ∃ (A : Subgroup (Equiv.Perm (Fin n))) (x : Equiv.Perm (Fin n)),
    Group.IsSolvable A ∧ A ⊔ Subgroup.zpowers x = H

theorem nilCount (n : ℕ) (D : Subgroup (Equiv.Perm (Fin n))) :
    Nat.card {H : Subgroup D // Group.IsNilpotent H} ≤ Nat.card {H : Subgroup (Equiv.Perm (Fin n)) // Group.IsNilpotent H} := by
  let f (H : {H : Subgroup D // Group.IsNilpotent H}) : {H : Subgroup (Equiv.Perm (Fin n)) // Group.IsNilpotent H} :=
    ⟨H.1.map D.subtype,(Group.isNilpotent_congr
      (H.1.equivMapOfInjective D.subtype D.subtype_injective)).mp H.2⟩
  apply Nat.card_le_card_of_injective f
  intro A B h
  apply Subtype.ext
  apply Subgroup.map_subtype_inj.mp
  exact congrArg Subtype.val h

theorem count (gen : H2) (n : ℕ) :
    Erdos1162.f n ≤ Nat.card {A : Subgroup (Equiv.Perm (Fin n)) // Group.IsSolvable A} * n.factorial := by
  let f (pair : {A : Subgroup (Equiv.Perm (Fin n)) // Group.IsSolvable A} × Equiv.Perm (Fin n)) :
      Subgroup (Equiv.Perm (Fin n)) := pair.1.1 ⊔ Subgroup.zpowers pair.2
  have onto : Function.Surjective f := by
    intro H
    obtain ⟨A,x,hs,hx⟩ := gen n H
    exact ⟨(⟨A,hs⟩,x),hx⟩
  have h := Nat.card_le_card_of_surjective f onto
  simpa only [Erdos1162.f,Nat.card_prod,Nat.card_perm,Nat.card_fin] using h

theorem log_sqrt (n : ℕ) : Real.logb 2 n ≤ (2/Real.log 2)*Real.sqrt n := by
  have h := Real.log_le_rpow_div (Nat.cast_nonneg n : 0 ≤ (n:ℝ)) (by norm_num : (0:ℝ)<1/2)
  rw [← Real.sqrt_eq_rpow] at h
  rw [Real.logb,div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2))]
  linarith

theorem factorial_bound (n : ℕ) :
    (n.factorial:ℝ) ≤ (2:ℝ)^((2/Real.log 2)*n*Real.sqrt n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hp : (0:ℝ)<n := by exact_mod_cast hn
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (show 0<(n.factorial:ℝ) by exact_mod_cast n.factorial_pos)).mp
  have powbound : (n.factorial:ℝ) ≤ (n:ℝ)^n := by exact_mod_cast n.factorial_le_pow
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (show 0<(n.factorial:ℝ) by exact_mod_cast n.factorial_pos) powbound
  rw [Real.logb_pow] at hlog
  have h := mul_le_mul_of_nonneg_left (log_sqrt n) hp.le
  linarith

theorem main : H1 → H2 → OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2.H2 := by
  rintro ⟨C,κ,hκ,hlift⟩ gen
  refine ⟨κ+2/Real.log 2, ?_⟩
  intro g hmono hnil n
  have hs := hlift g hmono (fun m D _ => by
    apply le_trans _ (hnil m)
    exact_mod_cast nilCount m D) n
  have hcount : (Erdos1162.f n:ℝ) ≤
      (Nat.card {A : Subgroup (Equiv.Perm (Fin n)) // Group.IsSolvable A}:ℝ)*n.factorial := by
    exact_mod_cast count gen n
  calc
    (Erdos1162.f n:ℝ) ≤ _ := hcount
    _ ≤ _ := mul_le_mul hs (factorial_bound n) (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]; congr 1; ring

end OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1
