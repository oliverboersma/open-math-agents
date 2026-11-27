import OMAReductions.R_Erdos69_erdos_69_R1_H1_R1_H2_R1_H1_R1
import Mathlib

/-! Index the progression by an initial interval. Each selected prime then
prescribes one index residue, and the Chinese remainder theorem combines
them. A single residue class in an initial interval has discrepancy at most one. -/
namespace Progression69
open Finset

lemma simultaneous (J : Finset ℕ) (hp : ∀ p ∈ J, Nat.Prime p) (i z : ℕ) :
    i ≡ z [MOD ∏ p ∈ J,p] ↔ ∀ p ∈ J, i ≡ z [MOD p] := by
  induction J using Finset.induction_on with
  | empty => simp [Nat.ModEq] <;> omega
  | @insert p J hnot ih =>
    have pj : ∀ q ∈ J, Nat.Prime q := fun q h => hp q (mem_insert_of_mem h)
    have pp := hp p (mem_insert_self ..)
    have cop : Nat.Coprime p (∏ q ∈ J,q) := Nat.coprime_prod_right_iff.mpr
      (fun q h => (Nat.coprime_primes pp (pj q h)).mpr (fun e => hnot (e ▸ h)))
    rw [prod_insert hnot,← Nat.modEq_and_modEq_iff_modEq_mul cop,ih pj]
    simp

lemma residue_count (a Q k : ℕ) (h : ℕ → ℤ) (J : Finset ℕ)
    (hp : ∀ p ∈ J, Nat.Prime p ∧ ¬ p ∣ Q) :
    |((((range k).filter fun i => ∀ p ∈ J, (p:ℤ) ∣ ((a+Q*i:ℕ):ℤ)+h p).card : ℝ) -
      k/(∏ p ∈ J,(p:ℝ)))| ≤ 1 := by
  classical
  let v (p : ℕ) := ((-((a : ZMod p)+(h p : ZMod p))) * (Q : ZMod p)⁻¹).val
  obtain ⟨z,hz⟩ := Nat.chineseRemainderOfFinset v id J (fun p h => (hp p h).1.ne_zero)
    (fun p h q k ne => (Nat.coprime_primes (hp p h).1 (hp q k).1).mpr ne)
  let m := ∏ p ∈ J,p
  have hm : 0 < m := prod_pos fun p h => (hp p h).1.pos
  have eqp (i p : ℕ) (hmem : p ∈ J) :
      (p:ℤ) ∣ ((a+Q*i:ℕ):ℤ)+h p ↔ i ≡ z [MOD p] := by
    letI : Fact p.Prime := ⟨(hp p hmem).1⟩
    have nz : (Q : ZMod p) ≠ 0 := fun e => (hp p hmem).2 ((ZMod.natCast_eq_zero_iff ..).mp e)
    have rz : (z : ZMod p) = -((a : ZMod p)+(h p : ZMod p)) / (Q : ZMod p) :=
      by simpa only [div_eq_mul_inv] using ((ZMod.natCast_eq_natCast_iff ..).mpr (hz p hmem)).trans (ZMod.natCast_zmod_val _)
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,← ZMod.natCast_eq_natCast_iff,rz,eq_div_iff nz]
    push_cast
    constructor <;> intro he <;> linear_combination he
  have sets : ((range k).filter fun i => ∀ p ∈ J, (p:ℤ) ∣ ((a+Q*i:ℕ):ℤ)+h p) =
      (range k).filter fun i => i ≡ z [MOD m] := by
    ext i
    simp only [mem_filter, and_congr_right_iff]
    intro _
    rw [simultaneous _ (fun p h => (hp p h).1)]
    exact forall_congr' fun p => forall_congr' fun hp => eqp i p hp
  rw [sets,← Nat.count_eq_card_filter_range,Nat.count_modEq_card _ hm]
  have prodcast : ∏ p ∈ J,(p:ℝ) = (m:ℝ) := by simp [m]
  rw [prodcast]
  have mr : (0:ℝ) < m := by exact_mod_cast hm
  have rem := Nat.mod_lt k hm
  have qlo : m*(k/m) ≤ k := Nat.mul_div_le k m
  have qhi : k ≤ m*(k/m+1) := by have := Nat.mod_add_div k m; rw [Nat.mul_add,Nat.mul_one]; omega
  have lo : ((k/m : ℕ):ℝ) ≤ (k:ℝ)/m := (le_div_iff₀ mr).mpr (by exact_mod_cast (Nat.mul_comm .. ▸ qlo : (k/m)*m ≤ k))
  have hi : (k:ℝ)/m ≤ ((k/m : ℕ):ℝ)+1 := (div_le_iff₀ mr).mpr (by exact_mod_cast (Nat.mul_comm .. ▸ qhi : k ≤ (k/m+1)*m))
  split <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

end Progression69

theorem OMA.solution : OMA.R_Erdos69_erdos_69_R1_H1_R1_H2_R1_H1_R1.H1 := by
  classical
  intro x Q b J h
  let N := (Finset.Icc (x/2) x).filter fun n => n%Q=b%Q
  change 0 < Q → _ → |((N.filter _).card : ℝ) - N.card / _| ≤ 1
  intro hQ hp
  by_cases empty : N.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp empty]; simp
  let a := N.min' empty
  let z := N.max' empty
  have ha : a ∈ N := Finset.min'_mem _ _
  have hz : z ∈ N := Finset.max'_mem _ _
  have ar := Finset.mem_filter.mp ha
  have zr := Finset.mem_filter.mp hz
  let k := (z-a)/Q+1
  let f (i : ℕ) := a+Q*i
  have inj : Function.Injective f := fun i j he => Nat.eq_of_mul_eq_mul_left hQ (Nat.add_left_cancel he)
  have eq : N = (Finset.range k).image f := by
    ext n
    constructor
    · intro hn
      have an : a ≤ n := Finset.min'_le _ _ hn
      have nz : n ≤ z := Finset.le_max' _ _ hn
      have md : a ≡ n [MOD Q] := ar.2.trans (Finset.mem_filter.mp hn).2.symm
      obtain ⟨i,hi⟩ := (Nat.modEq_iff_dvd' an).mp md
      refine Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr ?_,?_⟩
      · apply Nat.lt_succ_of_le
        apply (Nat.le_div_iff_mul_le hQ).mpr
        rw [Nat.mul_comm,← hi]; omega
      · dsimp [f]; omega
    · intro hn
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hn
      have ik := Finset.mem_range.mp hi
      change i < (z-a)/Q+1 at ik
      have bound := (Nat.le_div_iff_mul_le hQ).mp (show i ≤ (z-a)/Q by omega)
      have ax := Finset.mem_Icc.mp ar.1
      have zx := Finset.mem_Icc.mp zr.1
      have az : a ≤ z := Finset.le_max' _ _ ha
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by dsimp [f]; omega,by dsimp [f]; rw [Nat.mul_comm Q i]; omega⟩,?_⟩
      simpa [f,Nat.add_mod] using ar.2
  rw [eq,Finset.filter_image,Finset.card_image_of_injective _ inj,Finset.card_image_of_injective _ inj,Finset.card_range]
  exact Progression69.residue_count a Q k h J hp
