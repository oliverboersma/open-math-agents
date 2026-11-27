import FormalConjectures.ErdosProblems.«1072»
import Mathlib.NumberTheory.Wilson

/-!
Wilson reflection pairs factorials below and above the middle index. This
reduces the two prime classes to testing only lower-half factorials, with
an ordinary and a parity-dependent forbidden residue in each class.
-/

open Asymptotics Filter Finset Nat Set

namespace OMA.R_Erdos1072_erdos_1072_variants_littleo_R1

def H1 : Prop :=
  (fun x : ℕ ↦ (({p : ℕ | p.Prime ∧ p % 4 = 1 ∧
    (∀ k : ℕ, 0 < k → 2 * k ≤ p - 1 → (k ! : ZMod p) ≠ -1 ∧
      (k ! : ZMod p) ≠ (-1) ^ k)} ∩ Set.Icc 0 x).ncard : ℝ)) =o[atTop]
    (fun x ↦ x / Real.log x)

def H2 : Prop :=
  (fun x : ℕ ↦ (({p : ℕ | p.Prime ∧ p % 4 = 3 ∧
    (∀ k : ℕ, 0 < k → 2 * k ≤ p - 1 → (k ! : ZMod p) ≠ -1 ∧
      (k ! : ZMod p) ≠ (-1) ^ k)} ∩ Set.Icc 0 x).ncard : ℝ)) =o[atTop]
    (fun x ↦ x / Real.log x)

section Proof

private theorem factorial_reflection {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : k < p) :
    (k ! : ZMod p) * ((p - 1 - k)! : ZMod p) = (-1) ^ (k + 1) := by
  let : Fact p.Prime := ⟨hp⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < p := by omega
    have he : p - 1 - k = (p - 1 - (k + 1)) + 1 := by omega
    have hsum : (p - 1 - k) + (k + 1) = p := by omega
    have hcast : ((p - 1 - k : ℕ) : ZMod p) = -((k + 1 : ℕ) : ZMod p) := by
      apply eq_neg_of_add_eq_zero_left
      rw [← Nat.cast_add, hsum, ZMod.natCast_self]
    have hfac : ((p - 1 - k)! : ZMod p) =
        -((k + 1 : ℕ) : ZMod p) * ((p - 1 - (k + 1))! : ZMod p) := by
      nth_rewrite 1 [he, Nat.factorial_succ]
      rw [Nat.cast_mul, ← he, hcast]
    calc
      ((k + 1)! : ZMod p) * ((p - 1 - (k + 1))! : ZMod p) =
          -((k ! : ZMod p) * ((p - 1 - k)! : ZMod p)) := by
            rw [Nat.factorial_succ, Nat.cast_mul, hfac]
            ring
      _ = (-1) ^ (k + 1 + 1) := by rw [ih hk', pow_succ]; ring

private theorem congruence_iff {p n : ℕ} :
    n ! + 1 ≡ 0 [MOD p] ↔ (n ! : ZMod p) = -1 := by
  rw [Nat.modEq_zero_iff_dvd, ← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one]
  exact eq_neg_iff_add_eq_zero.symm

private theorem endpoint_iff {p : ℕ} (hp : p.Prime) :
    Erdos1072.f p = p - 1 ↔ ∀ n < p - 1, (n ! : ZMod p) ≠ -1 := by
  have hW : p - 1 ∈ {n | n ! + 1 ≡ 0 [MOD p]} := by
    let : Fact p.Prime := ⟨hp⟩
    exact congruence_iff.mpr (ZMod.wilsons_lemma p)
  have hne : {n | n ! + 1 ≡ 0 [MOD p]}.Nonempty := ⟨p-1, hW⟩
  change sInf {n | n ! + 1 ≡ 0 [MOD p]} = p - 1 ↔ _
  constructor
  · intro h n hn hfac
    have hmem : n ∈ {n | n ! + 1 ≡ 0 [MOD p]} := congruence_iff.mpr hfac
    have hle := Nat.sInf_le hmem
    exact (not_le_of_gt hn) (h ▸ hle)
  · intro h
    apply le_antisymm (Nat.sInf_le hW)
    refine le_csInf hne fun n hn => ?_
    by_contra! hlt
    exact h n hlt (congruence_iff.mp hn)

private theorem reflection_iff {p k : ℕ} (hp : p.Prime) (hk : k < p) :
    ((p - 1 - k)! : ZMod p) = -1 ↔ (k ! : ZMod p) = (-1) ^ k := by
  have h := factorial_reflection hp k hk
  rw [pow_succ] at h
  constructor
  · intro he
    rw [he] at h
    simpa using h
  · intro he
    rw [he] at h
    have hk0 : (-1 : ZMod p) ^ k ≠ 0 := by
      let : Fact p.Prime := ⟨hp⟩
      exact pow_ne_zero k (neg_ne_zero.mpr one_ne_zero)
    let : Fact p.Prime := ⟨hp⟩
    exact mul_left_cancel₀ hk0 h

theorem endpoint_lower_half {p : ℕ} (hp : p.Prime) :
    Erdos1072.f p = p - 1 ↔ 2 < p ∧
      ∀ k : ℕ, 0 < k → 2 * k ≤ p - 1 →
        (k ! : ZMod p) ≠ -1 ∧ (k ! : ZMod p) ≠ (-1) ^ k := by
  rw [endpoint_iff hp]
  constructor
  · intro h
    have hp' : 2 < p := by
      by_contra! hle
      have he : p = 2 := by have := hp.two_le; omega
      subst p
      exact h 0 (by decide) (by decide)
    refine ⟨hp', fun k hk hkle => ⟨h k (by omega), ?_⟩⟩
    exact fun he => h (p - 1 - k) (by omega) ((reflection_iff hp (by omega)).mpr he)
  · rintro ⟨hp', h⟩ n hn he
    by_cases hlow : 2 * n ≤ p - 1
    · by_cases hn0 : n = 0
      · subst n
        have hz : (2 : ZMod p) = 0 := by
          calc
            (2 : ZMod p) = 1 + 1 := by ring
            _ = -1 + 1 := (congrArg (fun z : ZMod p => z + 1) (by simpa using he : (1 : ZMod p) = -1))
            _ = 0 := neg_add_cancel 1
        have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact hz)
        exact (not_le_of_gt hp') (Nat.le_of_dvd (by decide) hd)
      · exact (h n (Nat.pos_of_ne_zero hn0) hlow).1 he
    · let k := p - 1 - n
      have hk : 0 < k := by dsimp [k]; omega
      have hkl : 2 * k ≤ p - 1 := by dsimp [k]; omega
      have hre : p - 1 - k = n := by dsimp [k]; omega
      have hs : ((p - 1 - k)! : ZMod p) = -1 := hre ▸ he
      exact (h k hk hkl).2 ((reflection_iff hp (by omega)).mp hs)

theorem main : H1 → H2 → type_of% @Erdos1072.erdos_1072.variants.littleo := by
  intro h1 h2
  let A : Set ℕ := {p | p.Prime ∧ Erdos1072.f p = p - 1}
  let S : ℕ → Set ℕ := fun r ↦ {p | p.Prime ∧ p % 4 = r ∧
    (∀ k : ℕ, 0 < k → 2 * k ≤ p - 1 → (k ! : ZMod p) ≠ -1 ∧
      (k ! : ZMod p) ≠ (-1) ^ k)}
  have hUnion : A = S 1 ∪ S 3 := by
    ext p
    constructor
    · intro ⟨hp, he⟩
      obtain ⟨hp2, h⟩ := (endpoint_lower_half hp).mp he
      obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
      have hclass : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases hclass with hr | hr
      · exact Or.inl ⟨hp, hr, h⟩
      · exact Or.inr ⟨hp, hr, h⟩
    · rintro (⟨hp, hr, h⟩ | ⟨hp, hr, h⟩) <;>
        exact ⟨hp, (endpoint_lower_half hp).mpr ⟨by have := hp.two_le; omega, h⟩⟩
  have hdisj : Disjoint (S 1) (S 3) := by
    refine Set.disjoint_left.mpr fun p h1 h3 => ?_
    have he1 : p % 4 = 1 := h1.2.1
    have he3 : p % 4 = 3 := h3.2.1
    omega
  have hEq (x : ℕ) :
      ((A ∩ Set.Icc 0 x).ncard : ℝ) =
        ((S 1 ∩ Set.Icc 0 x).ncard : ℝ) + ((S 3 ∩ Set.Icc 0 x).ncard : ℝ) := by
    rw [hUnion, Set.union_inter_distrib_right]
    have hd := hdisj.mono (Set.inter_subset_left : S 1 ∩ Set.Icc 0 x ⊆ S 1)
      (Set.inter_subset_left : S 3 ∩ Set.Icc 0 x ⊆ S 3)
    rw [Set.ncard_union_eq hd, Nat.cast_add]
  change (fun x : ℕ => ((A ∩ Set.Icc 0 x).ncard : ℝ)) =o[atTop] _
  simp_rw [hEq]
  exact h1.add h2

end Proof

end OMA.R_Erdos1072_erdos_1072_variants_littleo_R1
