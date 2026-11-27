import OMAReductions.R_Kourovka_20_51_kourovka_20_51_R1
import Mathlib

-- Step Kourovka.20.51.kourovka_20_51.R1.H2: hypothesis H2 of reduction Kourovka.20.51.kourovka_20_51.R1
-- Credit: @ivillar
-- H2: for odd primes p ∣ q - 1 there is a nonabelian group of odd order with p + (q-1)/p classes.
-- Proof: take g of order p in (ZMod q)ˣ and the affine group ZMod q ⋊ ZMod p with
-- (b, i) * (d, j) = (b + g^i d, i + j), of order pq. Two elements commute iff
-- b (1 - g^j) = d (1 - g^i); counting solutions gives q^2 + (p^2 - 1) q commuting pairs,
-- and the number of classes is that count divided by pq (card_comm_eq_card_conjClasses_mul_card).

namespace OMAKourovkaH2

/-- Elements of the affine group: a translation part and an exponent. -/
structure Aff (q p : ℕ) where
  b : ZMod q
  i : ZMod p

variable {q p : ℕ}

theorem Aff.ext' {x y : Aff q p} (h1 : x.b = y.b) (h2 : x.i = y.i) : x = y := by
  cases x
  cases y
  simp only [Aff.mk.injEq]
  exact ⟨h1, h2⟩

def Aff.equiv : Aff q p ≃ ZMod q × ZMod p where
  toFun x := (x.b, x.i)
  invFun y := ⟨y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance Aff.fintype (q p : ℕ) [NeZero q] [NeZero p] : Fintype (Aff q p) :=
  Fintype.ofEquiv _ Aff.equiv.symm

section

variable (w : ZMod p → ZMod q)

def amul (x y : Aff q p) : Aff q p := ⟨x.b + w x.i * y.b, x.i + y.i⟩

def ainv (x : Aff q p) : Aff q p := ⟨-(w (-x.i) * x.b), -x.i⟩

theorem amul_assoc (hadd : ∀ i j, w (i + j) = w i * w j) (x y z : Aff q p) :
    amul w (amul w x y) z = amul w x (amul w y z) :=
  Aff.ext' (by simp only [amul]; rw [hadd]; ring) (by simp only [amul]; ring)

theorem aone_mul (h0 : w 0 = 1) (x : Aff q p) : amul w ⟨0, 0⟩ x = x :=
  Aff.ext' (by simp only [amul, h0]; ring) (by simp only [amul]; ring)

theorem ainv_mul (x : Aff q p) : amul w (ainv w x) x = ⟨0, 0⟩ :=
  Aff.ext' (by simp only [amul, ainv]; ring) (by simp only [amul, ainv]; ring)

/-- The affine group structure. -/
def affGroup (h0 : w 0 = 1) (hadd : ∀ i j, w (i + j) = w i * w j) : Group (Aff q p) :=
  letI : Mul (Aff q p) := ⟨amul w⟩
  letI : One (Aff q p) := ⟨⟨0, 0⟩⟩
  letI : Inv (Aff q p) := ⟨ainv w⟩
  Group.ofLeftAxioms (amul_assoc w hadd) (aone_mul w h0) (ainv_mul w)

end

theorem count_pairs (hq : q.Prime) [NeZero q] [NeZero p] (w : ZMod p → ZMod q) (h0 : w 0 = 1)
    (hw : ∀ i, w i = 1 → i = 0) :
    (Finset.univ.filter (fun t : (ZMod q × ZMod p) × (ZMod q × ZMod p) =>
      t.1.1 + w t.1.2 * t.2.1 = t.2.1 + w t.2.2 * t.1.1)).card + q = q * q + p * (p * q) := by
  haveI := Fact.mk hq
  rw [Finset.card_filter]
  let σ : (ZMod q × ZMod p) × (ZMod q × ZMod p) ≃ (ZMod p × ZMod p) × (ZMod q × ZMod q) :=
    { toFun := fun t => ((t.1.2, t.2.2), (t.1.1, t.2.1))
      invFun := fun u => ((u.2.1, u.1.1), (u.2.2, u.1.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.sum_equiv σ
    (fun t => if t.1.1 + w t.1.2 * t.2.1 = t.2.1 + w t.2.2 * t.1.1 then 1 else 0)
    (fun u => if u.2.1 + w u.1.1 * u.2.2 = u.2.2 + w u.1.2 * u.2.1 then 1 else 0)
    (fun _ => rfl)]
  simp only [Fintype.sum_prod_type]
  have hS : ∀ i j : ZMod p,
      (∑ b : ZMod q, ∑ d : ZMod q, if b + w i * d = d + w j * b then 1 else 0) =
        if i = 0 ∧ j = 0 then q * q else q := by
    intro i j
    by_cases hi : i = 0
    · subst hi
      rw [h0]
      by_cases hj : j = 0
      · subst hj
        rw [h0]
        have key : ∀ b d : ZMod q, (b + 1 * d = d + 1 * b) := fun b d => by ring
        simp only [key, if_true, and_self, Finset.sum_const, Finset.card_univ, ZMod.card,
          smul_eq_mul, mul_one]
      · have hwj : w j ≠ 1 := fun h => hj (hw j h)
        have key : ∀ b d : ZMod q, (b + 1 * d = d + w j * b ↔ b = 0) := by
          intro b d
          constructor
          · intro h
            have h' : b * (1 - w j) = 0 := by linear_combination h
            rcases mul_eq_zero.mp h' with h'' | h''
            · exact h''
            · exact absurd (sub_eq_zero.mp h'').symm hwj
          · intro h
            subst h
            ring
        simp only [key, hj, and_false, if_false, Finset.sum_const, Finset.card_univ, ZMod.card,
          smul_eq_mul]
        simp
    · have hwi : 1 - w i ≠ 0 := fun h => hi (hw i (sub_eq_zero.mp h).symm)
      have key : ∀ b d : ZMod q,
          (b + w i * d = d + w j * b ↔ d = (b - w j * b) / (1 - w i)) := by
        intro b d
        rw [eq_div_iff hwi]
        constructor <;> intro h <;> linear_combination -h
      simp only [key, hi, false_and, if_false]
      simp
  simp only [hS]
  have e1 : ∀ i j : ZMod p, (if i = 0 ∧ j = 0 then q * q else q) + (if i = 0 ∧ j = 0 then q else 0) =
      q + (if i = 0 ∧ j = 0 then q * q else 0) := by
    intro i j
    split_ifs <;> ring
  have hX : ∀ X : ℕ, (∑ i : ZMod p, ∑ j : ZMod p, if i = 0 ∧ j = 0 then X else 0) = X := by
    intro X
    rw [Fintype.sum_eq_single 0 (fun i hi => by simp [hi])]
    rw [Fintype.sum_eq_single 0 (fun j hj => by simp [hj])]
    simp
  have h1 : (∑ i : ZMod p, ∑ j : ZMod p,
      ((if i = 0 ∧ j = 0 then q * q else q) + (if i = 0 ∧ j = 0 then q else 0))) =
      ∑ i : ZMod p, ∑ j : ZMod p, (q + (if i = 0 ∧ j = 0 then q * q else 0)) := by
    simp only [e1]
  simp only [Finset.sum_add_distrib, hX, Finset.sum_const, Finset.card_univ, ZMod.card,
    smul_eq_mul] at h1
  linarith

end OMAKourovkaH2

open OMAKourovkaH2 in
theorem OMA.solution : OMA.R_Kourovka_20_51_kourovka_20_51_R1.H2 := by
  unfold OMA.R_Kourovka_20_51_kourovka_20_51_R1.H2
  intro p q hp hpo hq hqo hpq
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hcard : Fintype.card (ZMod q)ˣ = q - 1 := ZMod.card_units q
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card p (G := (ZMod q)ˣ) (by rw [hcard]; exact hpq)
  let w : ZMod p → ZMod q := fun i => ((g ^ i.val : (ZMod q)ˣ) : ZMod q)
  have h0 : w 0 = 1 := by simp [w]
  have hadd : ∀ i j, w (i + j) = w i * w j := by
    intro i j
    have hm := pow_mod_orderOf g (i.val + j.val)
    rw [hg] at hm
    simp only [w]
    rw [ZMod.val_add, hm, pow_add, Units.val_mul]
  have hw : ∀ i, w i = 1 → i = 0 := by
    intro i hi
    have h1 : g ^ i.val = 1 := Units.val_eq_one.mp hi
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hg] at h2
    have h4 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h2 (ZMod.val_lt i)
    exact (ZMod.val_eq_zero i).mp h4
  letI G := affGroup w h0 hadd
  have hcardG : Nat.card (Aff q p) = q * p := by
    rw [Nat.card_congr Aff.equiv, Nat.card_prod, Nat.card_zmod, Nat.card_zmod]
  have hcomm : ∀ x y : Aff q p, Commute x y ↔ x.b + w x.i * y.b = y.b + w y.i * x.b := by
    intro x y
    constructor
    · intro h
      exact congrArg Aff.b h
    · intro h
      exact Aff.ext' h (add_comm x.i y.i)
  refine ⟨Aff q p, G, inferInstance, ⟨⟨1, 0⟩, ⟨0, 1⟩, ?_⟩, ?_, ?_⟩
  · intro h
    have hb : (1 : ZMod q) + w 0 * 0 = 0 + w 1 * 1 := congrArg Aff.b h
    rw [h0] at hb
    have hw1 : w 1 = 1 := by linear_combination -hb
    exact one_ne_zero (hw 1 hw1)
  · rw [hcardG]
    exact hqo.mul hpo
  · let e : {pr : Aff q p × Aff q p // Commute pr.1 pr.2} ≃
        {t : (ZMod q × ZMod p) × (ZMod q × ZMod p) //
          t.1.1 + w t.1.2 * t.2.1 = t.2.1 + w t.2.2 * t.1.1} :=
      Equiv.subtypeEquiv (Aff.equiv.prodCongr Aff.equiv) (fun pr => hcomm pr.1 pr.2)
    have hN : Nat.card {pr : Aff q p × Aff q p // Commute pr.1 pr.2} + q =
        q * q + p * (p * q) := by
      rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact count_pairs hq w h0 hw
    rw [card_comm_eq_card_conjClasses_mul_card, hcardG] at hN
    obtain ⟨m, hm⟩ := hpq
    have hq1 : q = p * m + 1 := by
      have := hq.one_lt
      omega
    have hdiv : (q - 1) / p = m := by
      rw [hm]
      exact Nat.mul_div_cancel_left m hp.pos
    rw [hdiv]
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hq.pos hp.pos)
    have hqq : q * q = q * (p * m) + q := by
      rw [hq1]
      ring
    nlinarith [hN, hqq]
