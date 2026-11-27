import OMAReductions.R_Erdos50_erdos_50_singular_R1_H2_R1_H2_R1
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Real.Basic

open Finset
open scoped BigOperators Function

private lemma crt_pattern_count (Q T : Finset ℕ) (hQ : ∀ p ∈ Q, Nat.Prime p) (hT : T ⊆ Q) :
    ((range (∏ p ∈ Q, p)).filter (fun n => Q.filter (· ∣ n) = T)).card =
      ∏ p ∈ Q \ T, (p - 1) := by
  classical
  let q := ∏ p : Q, (p : ℕ)
  have hq : q = ∏ p ∈ Q, p := Q.prod_coe_sort id
  have hq₀ : q ≠ 0 := by
    rw [hq]
    exact Finset.prod_ne_zero_iff.mpr fun p hp => (hQ p hp).ne_zero
  letI : NeZero q := ⟨hq₀⟩
  letI (p : Q) : NeZero (p : ℕ) := ⟨(hQ p p.property).ne_zero⟩
  have hc : Pairwise (Nat.Coprime on fun p : Q => (p : ℕ)) :=
    fun p r hpr => (Nat.coprime_primes (hQ p p.property) (hQ r r.property)).2
      (fun h => hpr (Subtype.ext h))
  let crt := ZMod.prodEquivPi (fun p : Q => (p : ℕ)) hc
  let domain := (range q).filter (fun n => Q.filter (· ∣ n) = T)
  let pattern (p : Q) (z : ZMod (p : ℕ)) : Prop := z = 0 ↔ (p : ℕ) ∈ T
  let e : (range q : Finset ℕ) ≃ ZMod q :=
    { toFun := fun n => (n.val : ZMod q)
      invFun := fun z => ⟨z.val, mem_range.mpr z.val_lt⟩
      left_inv := fun n => Subtype.ext (ZMod.val_natCast_of_lt (mem_range.mp n.property))
      right_inv := ZMod.natCast_zmod_val }
  let enc : (range q : Finset ℕ) ≃ (∀ p : Q, ZMod (p : ℕ)) :=
    e.trans crt.toEquiv
  have hcoord (n : (range q : Finset ℕ)) (p : Q) : enc n p = (n.val : ZMod (p : ℕ)) := by
    change crt (n.val : ZMod q) p = _
    exact congrFun (map_natCast crt n.val) p
  have hmatch (n : (range q : Finset ℕ)) :
      Q.filter (· ∣ n.val) = T ↔ ∀ p : Q, pattern p (enc n p) := by
    constructor
    · intro hn p
      change enc n p = 0 ↔ (p : ℕ) ∈ T
      rw [hcoord, ZMod.natCast_eq_zero_iff, ← hn, mem_filter]
      simp [p.property]
    · intro hn
      ext p
      by_cases hp : p ∈ Q
      · have h := hn ⟨p, hp⟩
        change enc n ⟨p, hp⟩ = 0 ↔ p ∈ T at h
        rw [hcoord, ZMod.natCast_eq_zero_iff] at h
        simpa [hp] using h
      · simp [hp, show p ∉ T from fun ht => hp (hT ht)]
  let edomain : domain ≃ {n : (range q : Finset ℕ) // Q.filter (· ∣ n.val) = T} :=
    { toFun := fun n => ⟨⟨n.val, (mem_filter.mp n.property).1⟩, (mem_filter.mp n.property).2⟩
      invFun := fun n => ⟨n.val.val, mem_filter.mpr ⟨n.val.property, n.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let ep : domain ≃ (∀ p : Q, {z : ZMod (p : ℕ) // pattern p z}) :=
    (edomain.trans (enc.subtypeEquiv hmatch)).trans Equiv.subtypePiEquivPi
  have hcard (p : Q) :
      Fintype.card {z : ZMod (p : ℕ) // pattern p z} =
        if (p : ℕ) ∈ T then 1 else (p : ℕ) - 1 := by
    by_cases hp : (p : ℕ) ∈ T
    · rw [if_pos hp]
      let ez : {z : ZMod (p : ℕ) // pattern p z} ≃ {z : ZMod (p : ℕ) // z = 0} :=
        Equiv.subtypeEquivRight (fun z => by simp [pattern, hp])
      rw [Fintype.card_congr ez, Fintype.card_subtype_eq]
    · rw [if_neg hp]
      let ez : {z : ZMod (p : ℕ) // pattern p z} ≃ {z : ZMod (p : ℕ) // z ≠ 0} :=
        Equiv.subtypeEquivRight (fun z => by simp [pattern, hp])
      rw [Fintype.card_congr ez, Fintype.card_subtype_compl, Fintype.card_subtype_eq, ZMod.card]
  rw [← hq]
  change domain.card = _
  rw [← Fintype.card_coe, Fintype.card_congr ep, Fintype.card_pi]
  simp_rw [hcard]
  rw [Finset.prod_coe_sort Q (fun p : ℕ => if p ∈ T then 1 else p - 1), Finset.prod_ite]
  simp [Finset.sdiff_eq_filter]

theorem OMA.solution : OMA.R_Erdos50_erdos_50_singular_R1_H2_R1_H2_R1.H2 := by
  classical
  intro Q hQ R
  let q := ∏ p ∈ Q, p
  let selected := (range q).filter (fun n => R (Q.filter (· ∣ n)))
  let patterns := Q.powerset.filter R
  change (selected.card : ℝ) / (q : ℝ) = _
  have hmaps : (selected : Set ℕ).MapsTo (fun n => Q.filter (· ∣ n)) patterns := by
    intro n hn
    exact mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _), (mem_filter.mp hn).2⟩
  rw [card_eq_sum_card_fiberwise hmaps, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T hT
  have hs := (mem_filter.mp hT).1
  have hR := (mem_filter.mp hT).2
  have hsub := mem_powerset.mp hs
  have hfiber : selected.filter (fun n => Q.filter (· ∣ n) = T) =
      (range q).filter (fun n => Q.filter (· ∣ n) = T) := by
    ext n
    simp only [selected, mem_filter]
    constructor
    · rintro ⟨⟨hn, _⟩, he⟩
      exact ⟨hn, he⟩
    · rintro ⟨hn, he⟩
      exact ⟨⟨hn, he.symm ▸ hR⟩, he⟩
  rw [hfiber, crt_pattern_count Q T hQ hsub]
  have hpf (p : ℕ) (hp : p ∈ Q \ T) :
      ((p - 1 : ℕ) : ℝ) / (p : ℝ) = 1 - 1 / (p : ℝ) := by
    have hpprime := hQ p (mem_sdiff.mp hp).1
    have hp₀ : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpprime.ne_zero
    rw [Nat.cast_sub hpprime.one_lt.le, sub_div, div_self hp₀]
    norm_num
  unfold q
  rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_sdiff hsub (f := fun p : ℕ => (p : ℝ))]
  rw [div_mul_eq_div_div]
  rw [← Finset.prod_div_distrib, div_eq_mul_inv, mul_comm, ← Finset.prod_inv_distrib]
  simp_rw [← one_div]
  congr 1
  exact Finset.prod_congr rfl hpf
