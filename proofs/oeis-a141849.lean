import OMAStatements.S_oeis_a141849
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

-- Formal proof of Federico Provvedi's 2018 observation in OEIS A141849.
-- Credit: @anmolspace, OpenAI Codex.
open Polynomial

private theorem shifted_eval (p : ℕ) (a : ZMod p) :
    (OMA.S_oeis_a141849.shiftedQuotient p).eval a =
      ∑ j ∈ Finset.range 11, (a+1)^j := by
  simp [OMA.S_oeis_a141849.shiftedQuotient, Polynomial.eval_finsetSum]

private theorem shifted_roots_card (p : ℕ) [Fact p.Prime] [NeZero (11 : ZMod p)] :
    (Finset.univ.filter (fun a : ZMod p => (OMA.S_oeis_a141849.shiftedQuotient p).eval a = 0)).card =
      (primitiveRoots 11 (ZMod p)).card := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h (a : ZMod p) : (OMA.S_oeis_a141849.shiftedQuotient p).eval a = 0 ↔
      a+1 ∈ primitiveRoots 11 (ZMod p) := by
    rw [mem_primitiveRoots (by decide : 0 < 11), ← Polynomial.isRoot_cyclotomic_iff]
    simp [Polynomial.IsRoot.def, Polynomial.cyclotomic_prime, shifted_eval, Polynomial.eval_finsetSum]
  refine Finset.card_bij' (fun a _ => a+1) (fun b _ => b-1) ?_ ?_ ?_ ?_
  · intro a ha
    exact (h a).mp (Finset.mem_filter.mp ha).2
  · intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h (b-1)).mpr (by simpa using hb)⟩
  · intro a _
    simp
  · intro b _
    simp

private theorem eleven_case : 11 % 11 = 1 ↔
    (Finset.univ.filter (fun a : ZMod 11 => (∑ j ∈ Finset.range 11, (a+1)^j) = 0)).card = 10 := by
  decide

theorem OMA.solution : type_of% @OMA.S_oeis_a141849.main := by
  intro p hp
  by_cases same : p = 11
  · subst p
    simp_rw [shifted_eval]
    exact eleven_case
  have hp0 := hp.out.pos
  have hnp : ¬ p ∣ 11 := fun hd =>
    same (((show Nat.Prime 11 by decide).eq_one_or_self_of_dvd p hd).resolve_left hp.out.ne_one)
  letI : NeZero (11 : ZMod p) := ⟨fun h => hnp ((ZMod.natCast_eq_zero_iff 11 p).mp h)⟩
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  rw [shifted_roots_card]
  constructor
  · intro hmod
    have hd : 11 ∣ Fintype.card (ZMod p)ˣ := by rw [ZMod.card_units]; omega
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 11 hd
    have hprim : IsPrimitiveRoot (u : ZMod p) 11 :=
      IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hu)
    rw [hprim.card_primitiveRoots, Nat.totient_prime (by decide : Nat.Prime 11)]
  · intro hcard
    have hpos : 0 < (primitiveRoots 11 (ZMod p)).card := by omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    have hprim := (mem_primitiveRoots (by decide : 0 < 11)).mp hz
    have hu := hprim.isUnit_unit (by decide : 11 ≠ 0)
    have hd := ZMod.orderOf_units_dvd_card_sub_one (hprim.isUnit (by decide)).unit
    rw [← hu.eq_orderOf] at hd
    omega
