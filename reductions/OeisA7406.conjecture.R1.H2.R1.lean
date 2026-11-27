import OMAReductions.R_OeisA7406_conjecture_R1
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-! Prime-adic pruning for sums of reciprocal squares. -/

open Finset

namespace WolstenholmeSquare

private def term (j : ℕ) : ℚ := 1 / ((j : ℚ) + 1)^2

private def H₂ (m : ℕ) : ℚ := ∑ j ∈ range m, term j

private theorem H₂_succ (m : ℕ) : H₂ (m+1) = H₂ m + term m :=
  sum_range_succ _ _

private def unitPart (p m : ℕ) : ℚ :=
  ∑ j ∈ range m, if p ∣ j+1 then 0 else term j

theorem split_multiples (p m : ℕ) (_hp : 0 < p) :
    H₂ m = H₂ (m/p) / (p : ℚ)^2 + unitPart p m := by
  induction m with
  | zero => simp [H₂, unitPart]
  | succ m ih =>
    rw [H₂, unitPart, sum_range_succ, sum_range_succ]
    change H₂ m + term m =
      H₂ ((m+1)/p) / (p : ℚ)^2 + (unitPart p m + _)
    rw [ih]
    by_cases h : p ∣ m+1
    · rw [Nat.succ_div_of_dvd h, if_pos h, add_zero, H₂_succ]
      have heq : p * (m/p+1) = m+1 := by
        rw [← Nat.succ_div_of_dvd h, Nat.mul_div_cancel' h]
      have hc : (p : ℚ) * ((m/p : ℕ) + 1) = (m : ℚ) + 1 := by exact_mod_cast heq
      have hterm : term m = term (m/p) / (p : ℚ)^2 := by
        unfold term
        rw [← hc, mul_pow, div_div, mul_comm ((p : ℚ)^2)]
      rw [hterm, add_div]
      ring
    · rw [Nat.succ_div_of_not_dvd h, if_neg h]
      ring

private theorem unitPart_nonneg_val (p : ℕ) [Fact p.Prime] (m : ℕ) :
    0 ≤ padicValRat p (unitPart p m) := by
  induction m with
  | zero => simp [unitPart]
  | succ m ih =>
    rw [unitPart, sum_range_succ]
    change 0 ≤ padicValRat p (unitPart p m + if p ∣ m+1 then 0 else term m)
    by_cases hd : p ∣ m+1
    · simpa [hd] using ih
    rw [if_neg hd]
    by_cases hz : unitPart p m + term m = 0
    · simp [hz]
    have hval : padicValRat p (term m) = 0 := by
      have h0 : ((m : ℚ) + 1)^2 ≠ 0 := by positivity
      rw [term, padicValRat.div one_ne_zero h0, padicValRat.one, padicValRat.pow]
      have hm : padicValRat p ((m : ℚ)+1) = 0 := by
        rw [← Nat.cast_succ, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hd, Nat.cast_zero]
      rw [hm]
      norm_num
    exact le_trans (le_min ih (by simp [hval])) (padicValRat.min_le_padicValRat_add hz)

theorem val_of_low_prefix (p m : ℕ) [Fact p.Prime] (hm : 0 < m/p)
    (hbelow : padicValRat p (H₂ (m/p)) < 2) :
    padicValRat p (H₂ m) = padicValRat p (H₂ (m/p)) - 2 := by
  have hp := (Fact.out : p.Prime)
  have Hpos {n : ℕ} (hn : 0 < n) : 0 < H₂ n := by
    unfold H₂
    exact sum_pos (fun j _ => by unfold term; positivity) ⟨0, mem_range.mpr hn⟩
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hx : 0 < H₂ (m/p) / (p : ℚ)^2 := div_pos (Hpos hm) (pow_pos hpQ 2)
  have hm' : 0 < m := hm.trans_le (Nat.div_le_self m p)
  have hval : padicValRat p (H₂ (m/p) / (p : ℚ)^2) =
      padicValRat p (H₂ (m/p)) - 2 := by
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [padicValRat.div (Hpos hm).ne' (pow_ne_zero _ hp0), padicValRat.pow,
      padicValRat.self hp.one_lt]
    norm_num
  rw [split_multiples p m hp.pos]
  by_cases hzero : unitPart p m = 0
  · simpa [hzero] using hval
  have hne : H₂ (m/p) / (p : ℚ)^2 + unitPart p m ≠ 0 := by
    rw [← split_multiples p m hp.pos]
    exact (Hpos hm').ne'
  have hlt : padicValRat p (H₂ (m/p) / (p : ℚ)^2) < padicValRat p (unitPart p m) := by
    have hle := unitPart_nonneg_val p m
    omega
  rw [padicValRat.add_eq_of_lt hne hx.ne' hzero hlt, hval]

end WolstenholmeSquare

namespace WolstenholmeSquare

private theorem small_prefix_certificate :
    ([2,3,5,7,11,13,17,19,23,29,31] : List ℕ).all (fun p =>
      (List.range 32).all fun q =>
        decide (32 / p ≤ q → padicValRat p (H₂ q) < 2)) = true := by
  decide +kernel

theorem val_negative_of_small_prime {p m : ℕ} [Fact p.Prime] (hp31 : p ≤ 31)
    (hm32 : 32 ≤ m) : padicValRat p (H₂ m) < 0 := by
  have hp := (Fact.out : p.Prime)
  have hpmem : p ∈ ([2,3,5,7,11,13,17,19,23,29,31] : List ℕ) := by
    have h2 := hp.two_le
    interval_cases p <;> first | decide | (exfalso; revert hp; decide)
  have hbase := List.all_eq_true.mp small_prefix_certificate p hpmem
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hqpos : 0 < m/p := Nat.div_pos (by omega) hp.pos
    have hqm : m/p < m := Nat.div_lt_self (by omega) hp.one_lt
    have hq : padicValRat p (H₂ (m/p)) < 2 := by
      by_cases hq32 : 32 ≤ m/p
      · exact (ih (m/p) hqm hq32).trans (by decide)
      · have hqmem : m/p ∈ List.range 32 := List.mem_range.mpr (by omega)
        have hval := List.all_eq_true.mp hbase (m/p) hqmem
        have hle : 32/p ≤ m/p := Nat.div_le_div_right hm32
        exact of_decide_eq_true hval hle
    rw [val_of_low_prefix p m hqpos hq]
    omega

end WolstenholmeSquare

namespace WolstenholmeSquare

private theorem sum_eq_Icc (m : ℕ) :
    H₂ m = ∑ k ∈ Icc 1 m, (1 : ℚ) / (k : ℚ)^2 := by
  induction m with
  | zero => simp [H₂]
  | succ m ih =>
    rw [H₂_succ, ih, sum_Icc_succ_top (by omega : 1 ≤ m+1)]
    simp [term]

private theorem not_dvd_num_of_negative {p : ℕ} {x : ℚ}
    (hp : p.Prime) (h : padicValRat p x < 0) : ¬ p ∣ x.num.natAbs := by
  intro hnum
  have hden : ¬ p ∣ x.den := by
    intro hd
    exact hp.not_dvd_one (x.reduced.gcd_eq_one ▸ Nat.dvd_gcd hnum hd)
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hden] at h
  omega

private theorem small_n_certificate :
    ([2,3,5,7,11,13,17,19,23,29,31] : List ℕ).all (fun p =>
      (List.range 33).all fun n =>
        decide (3 < n → ¬ n.Prime → p ∣ n → ¬ p ∣ OeisA7406.a (n-1))) = true := by
  decide +kernel

theorem small_prime_not_dvd_numerator {p n : ℕ} (hp : p.Prime) (hp31 : p ≤ 31)
    (hn : 3 < n) (hnp : ¬ n.Prime) (hd : p ∣ n) :
    ¬ p ∣ OeisA7406.a (n-1) := by
  by_cases h : 33 ≤ n
  · have hv := @val_negative_of_small_prime p (n-1) ⟨hp⟩ hp31 (by omega)
    unfold OeisA7406.a
    rw [← sum_eq_Icc]
    exact not_dvd_num_of_negative hp hv
  · have hp2 := hp.two_le
    have hpList : p ∈ ([2,3,5,7,11,13,17,19,23,29,31] : List ℕ) := by
      interval_cases p <;> first | decide | (exfalso; revert hp; decide)
    have hcert := List.all_eq_true.mp (List.all_eq_true.mp small_n_certificate p hpList)
      n (List.mem_range.mpr (by omega))
    exact of_decide_eq_true hcert hn hnp hd

end WolstenholmeSquare

namespace WolstenholmeSquare

private theorem pow_dvd_num_iff {p k : ℕ} [Fact p.Prime] {x : ℚ}
    (hx : x ≠ 0) (hk : 0 < k) :
    p^k ∣ x.num.natAbs ↔ (k : ℤ) ≤ padicValRat p x := by
  have hp := (Fact.out : p.Prime)
  have hnum : x.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hx)
  constructor
  · intro hd
    have hdiv : p ∣ x.num.natAbs :=
      (dvd_pow_self p (by omega : k ≠ 0)).trans hd
    have hden : ¬ p ∣ x.den := by
      intro h
      exact hp.not_dvd_one (x.reduced.gcd_eq_one ▸ Nat.dvd_gcd hdiv h)
    have hv := (padicValNat_dvd_iff_le hnum).mp hd
    rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hden]
    omega
  · intro hv
    apply (padicValNat_dvd_iff_le hnum).mpr
    rw [padicValRat_def, padicValInt] at hv
    omega

private theorem pos_val_iff {p : ℕ} [Fact p.Prime] {x : ℚ}
    (hx : x ≠ 0) : p ∣ x.num.natAbs ↔ 0 < padicValRat p x := by
  have h := pow_dvd_num_iff (p := p) (k := 1) hx (by decide)
  rw [pow_one] at h
  exact h.trans (by omega)

theorem large_factor_criterion_of_unit_vanishes {p m : ℕ} [Fact p.Prime]
    (hm : 0 < m/p)
    (hunit : unitPart p m = 0 ∨ 0 < padicValRat p (unitPart p m)) :
    p ∣ (H₂ m).num.natAbs ↔ p^3 ∣ (H₂ (m/p)).num.natAbs := by
  have hp := (Fact.out : p.Prime)
  have Hpos {n : ℕ} (hn : 0 < n) : 0 < H₂ n := by
    unfold H₂
    exact sum_pos (fun j _ => by unfold term; positivity) ⟨0, mem_range.mpr hn⟩
  have hm0 := hm.trans_le (Nat.div_le_self m p)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hx : H₂ (m/p) / (p : ℚ)^2 ≠ 0 :=
    div_ne_zero (Hpos hm).ne' (pow_ne_zero _ hp0)
  have htot : H₂ (m/p) / (p : ℚ)^2 + unitPart p m ≠ 0 := by
    rw [← split_multiples p m hp.pos]
    exact (Hpos hm0).ne'
  have hval : padicValRat p (H₂ (m/p) / (p : ℚ)^2) =
      padicValRat p (H₂ (m/p)) - 2 := by
    rw [padicValRat.div (Hpos hm).ne' (pow_ne_zero _ hp0), padicValRat.pow,
      padicValRat.self hp.one_lt]
    norm_num
  rw [pos_val_iff (Hpos hm0).ne', pow_dvd_num_iff (Hpos hm).ne' (by decide),
    split_multiples p m hp.pos]
  rcases hunit with hz | hpos
  · rw [hz, add_zero, hval]
    omega
  · constructor
    · intro htotal
      by_contra! hlow
      have hlt : padicValRat p (H₂ (m/p) / (p : ℚ)^2) < padicValRat p (unitPart p m) := by
        omega
      have hz : unitPart p m ≠ 0 := by
        rintro he
        rw [he, padicValRat.zero] at hpos
        omega
      rw [padicValRat.add_eq_of_lt htot hx hz hlt] at htotal
      omega
    · intro hh
      have hmin := padicValRat.min_le_padicValRat_add (p := p) htot
      omega

end WolstenholmeSquare

namespace WolstenholmeSquare

private def Reduces (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
  ∃ (a : ℤ) (b : ℕ), ¬p ∣ b ∧ x = Rat.divInt a (b : ℤ) ∧ z = (a : ZMod p) / (b : ZMod p)

private theorem reduces_zero (p : ℕ) [Fact p.Prime] : Reduces p 0 0 :=
  ⟨0, 1, (Fact.out : p.Prime).not_dvd_one, by simp, by simp⟩

private theorem reduces_add {p : ℕ} [Fact p.Prime] {x y : ℚ} {z w : ZMod p}
    (hx : Reduces p x z) (hy : Reduces p y w) : Reduces p (x+y) (z+w) := by
  obtain ⟨a,b,hb,rfl,rfl⟩ := hx
  obtain ⟨c,d,hd,rfl,rfl⟩ := hy
  have hp := (Fact.out : p.Prime)
  have hb₀ : (b : ℤ) ≠ 0 := by exact_mod_cast (fun h : b = 0 => hb (h ▸ dvd_zero p))
  have hd₀ : (d : ℤ) ≠ 0 := by exact_mod_cast (fun h : d = 0 => hd (h ▸ dvd_zero p))
  have hbz : (b : ZMod p) ≠ 0 := fun h => hb ((ZMod.natCast_eq_zero_iff ..).mp h)
  have hdz : (d : ZMod p) ≠ 0 := fun h => hd ((ZMod.natCast_eq_zero_iff ..).mp h)
  refine ⟨a*d+b*c, b*d, fun h => (hp.dvd_mul.mp h).elim hb hd, ?_, ?_⟩
  · rw [Rat.divInt_add_divInt a c hb₀ hd₀, Nat.cast_mul, mul_comm c (b : ℤ)]
  · push_cast
    field_simp [hbz, hdz]

private theorem reduces_term (p j : ℕ) [Fact p.Prime] (hj : ¬p ∣ j+1) :
    Reduces p (term j) (1 / ((j : ZMod p) + 1)^2) := by
  have hp := (Fact.out : p.Prime)
  refine ⟨1, (j+1)^2, ?_, ?_, ?_⟩
  · intro h
    exact hj (hp.dvd_of_dvd_pow h)
  · rw [Rat.divInt_eq_div]
    simp [term]
  · norm_cast

private def unitResidue (p : ℕ) [Fact p.Prime] (m : ℕ) : ZMod p :=
  ∑ j ∈ range m, if p ∣ j+1 then 0 else (1 : ZMod p) / ((j : ZMod p)+1)^2

private theorem reduces_unitPart (p : ℕ) [Fact p.Prime] (m : ℕ) :
    Reduces p (unitPart p m) (unitResidue p m) := by
  induction m with
  | zero => simpa [unitPart, unitResidue] using reduces_zero p
  | succ m ih =>
    rw [unitPart, unitResidue, sum_range_succ, sum_range_succ]
    change Reduces p (unitPart p m + _) (unitResidue p m + _)
    by_cases h : p ∣ m+1
    · simpa [h] using ih
    · rw [if_neg h, if_neg h]
      exact reduces_add ih (reduces_term p m h)

private theorem reduces_zero_num {p : ℕ} [Fact p.Prime] {x : ℚ}
    (h : Reduces p x 0) : p ∣ x.num.natAbs := by
  obtain ⟨a,b,hb,hx,hz⟩ := h
  have hb₀ : (b : ℤ) ≠ 0 := by exact_mod_cast (fun h : b = 0 => hb (h ▸ dvd_zero p))
  have hden : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hbz : (b : ZMod p) ≠ 0 := fun h => hb ((ZMod.natCast_eq_zero_iff ..).mp h)
  have ha : (a : ZMod p) = 0 :=
    (div_eq_zero_iff.mp hz.symm).resolve_right hbz
  have hr := Rat.divInt_eq_divInt_iff hden hb₀ |>.mp (x.num_divInt_den.trans hx)
  have hc := congrArg (fun i : ℤ => (i : ZMod p)) hr
  push_cast at hc
  rw [ha, zero_mul, mul_eq_zero] at hc
  have hnum := hc.resolve_right hbz
  rw [← Int.ofNat_dvd_left]
  exact (CharP.intCast_eq_zero_iff (ZMod p) p x.num).mp hnum

theorem unit_valuation_of_residue_zero {p m : ℕ} [Fact p.Prime]
    (h : unitResidue p m = 0) :
    unitPart p m = 0 ∨ 0 < padicValRat p (unitPart p m) := by
  by_cases hz : unitPart p m = 0
  · exact Or.inl hz
  · exact Or.inr ((pos_val_iff hz).mp (reduces_zero_num (h ▸ reduces_unitPart p m)))

end WolstenholmeSquare

namespace WolstenholmeSquare

theorem numerator_cube_of_endpoint_residue {p q : ℕ} [Fact p.Prime] (hq : 0 < q)
    (hzero : unitResidue p (p*(q+1)) = 0) :
    p ∣ OeisA7406.a (p*(q+1)-1) ↔ p^3 ∣ OeisA7406.a q := by
  have hp := (Fact.out : p.Prime)
  have hm : p*(q+1)-1+1 = p*(q+1) := by
    have hh : 0 < p*(q+1) := Nat.mul_pos hp.pos (by omega)
    omega
  have hdiv : p ∣ p*(q+1)-1+1 := by rw [hm]; exact dvd_mul_right _ _
  have hpart : unitResidue p (p*(q+1)-1) = 0 := by
    rw [← hm, unitResidue, sum_range_succ, if_pos hdiv, add_zero] at hzero
    exact hzero
  have hq' : (p*(q+1)-1)/p = q := by
    have h := Nat.succ_div_of_dvd hdiv
    rw [hm, Nat.mul_div_cancel_left _ hp.pos] at h
    omega
  have h := large_factor_criterion_of_unit_vanishes (p := p) (m := p*(q+1)-1)
    (by rwa [hq']) (unit_valuation_of_residue_zero hpart)
  rw [hq', sum_eq_Icc, sum_eq_Icc] at h
  exact h

end WolstenholmeSquare

namespace WolstenholmeSquare

private theorem unitResidue_mul {p : ℕ} [Fact p.Prime] (h : unitResidue p p = 0)
    (k : ℕ) : unitResidue p (p*k) = 0 := by
  induction k with
  | zero => simp [unitResidue]
  | succ k ih =>
    rw [Nat.mul_succ, unitResidue, sum_range_add]
    change unitResidue p (p*k) + _ = 0
    rw [ih, zero_add]
    refine Eq.trans (sum_congr rfl ?_) h
    intro j _
    have hshift : p ∣ p*k+j+1 ↔ p ∣ j+1 := by
      rw [Nat.add_assoc]
      exact (Nat.dvd_add_iff_right (dvd_mul_right p k)).symm
    have hcast : ((p*k+j : ℕ) : ZMod p) = (j : ZMod p) := by
      push_cast
      simp
    simp only [hshift, hcast]

end WolstenholmeSquare
open Finset

namespace A7406Blocks

/-- The sum of inverse squares over the prime field vanishes for primes above 3. -/
theorem inv_sq_sum_zero (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    (∑ x : ZMod p, (x⁻¹ : ZMod p)^2) = 0 := by
  classical
  let c : ZMod p := 2
  have hc : c ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hd
  let e : ZMod p ≃ ZMod p := Equiv.mulLeft₀ c hc
  let S : ZMod p := ∑ x : ZMod p, (x⁻¹ : ZMod p)^2
  have hchange : S = ∑ x : ZMod p, ((c * x)⁻¹ : ZMod p)^2 := by
    dsimp [S]
    symm
    exact Fintype.sum_equiv e _ _ (by intro x; rfl)
  have hscale : (∑ x : ZMod p, ((c * x)⁻¹ : ZMod p)^2) = c⁻¹ ^ 2 * S := by
    simp_rw [mul_inv, mul_pow]
    simp [S, Finset.mul_sum]
  have hfactor : c⁻¹ ^ 2 ≠ 1 := by
    intro h
    have h4 : (4 : ZMod p) = 1 := by
      have hmul := h
      field_simp [c] at hmul
      norm_num at hmul ⊢
      exact hmul.symm
    have h3 : (3 : ZMod p) = 0 := by linear_combination h4
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hd
  have hS : S = 0 := by
    have heq : c⁻¹ ^ 2 * S = S := by
      calc
        c⁻¹ ^ 2 * S = ∑ x : ZMod p, ((c * x)⁻¹ : ZMod p)^2 := hscale.symm
        _ = S := hchange.symm
    have hz : (c⁻¹ ^ 2 - 1) * S = 0 := by
      calc
        (c⁻¹ ^ 2 - 1) * S = c⁻¹ ^ 2 * S - S := by ring
        _ = 0 := sub_eq_zero.mpr heq
    rcases mul_eq_zero.mp hz with hzero | hzero
    · exact False.elim (hfactor (sub_eq_zero.mp hzero))
    · exact hzero
  simpa [S] using hS

end A7406Blocks

namespace WolstenholmeSquare
open scoped Fin.CommRing

private theorem complete_block_zero {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) :
    unitResidue p p = 0 := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let e : Fin p ≃ ZMod p := (ZMod.finEquiv p).toEquiv.trans (Equiv.addRight 1)
  have he (i : Fin p) : e i = (i.val : ZMod p) + 1 := by
    change ZMod.finEquiv p i + 1 = _
    have h := map_natCast (ZMod.finEquiv p) i.val
    rw [Fin.cast_val_eq_self] at h
    rw [h]
  unfold unitResidue
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ x : ZMod p, (x⁻¹)^2 := by
      apply Fintype.sum_equiv e
      intro i
      rw [he]
      by_cases h : p ∣ i.val+1
      · have hz : (i.val : ZMod p)+1 = 0 := by
          exact_mod_cast (ZMod.natCast_eq_zero_iff (i.val+1) p).mpr h
        simp [h,hz]
      · rw [if_neg h, one_div, inv_pow]
    _ = 0 := A7406Blocks.inv_sq_sum_zero p hp3

theorem numerator_cube_at_multiple {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hq : 0 < q) :
    p ∣ OeisA7406.a (p*(q+1)-1) ↔ p^3 ∣ OeisA7406.a q := by
  let : Fact p.Prime := ⟨hp⟩
  exact numerator_cube_of_endpoint_residue hq (unitResidue_mul (complete_block_zero hp3) (q+1))

end WolstenholmeSquare

namespace OMA.R_OeisA7406_conjecture_R1_H2_R1

/-- The prime-cube exclusion at prefixes at least as large as the prime. -/
def H1 : Prop :=
  ∀ p q : ℕ, p.Prime → 31 < p → p ≤ q → ¬ p^3 ∣ OeisA7406.a q

/-- The prime-cube exclusion at positive prefixes below the prime. -/
def H2 : Prop :=
  ∀ p q : ℕ, p.Prime → 31 < p → 0 < q → q < p → ¬ p^3 ∣ OeisA7406.a q

theorem main : H1 → H2 → OMA.R_OeisA7406_conjecture_R1.H2 := by
  intro hlong hshort n hn hnprime
  rw [OeisA89026.a, if_neg hnprime, ← Nat.coprime_iff_gcd_eq_one]
  by_contra h
  obtain ⟨p, hp, hpn, hpnum⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  by_cases hp31 : p ≤ 31
  · exact WolstenholmeSquare.small_prime_not_dvd_numerator hp hp31 hn hnprime hpn hpnum
  · obtain ⟨k, rfl⟩ := hpn
    have hk : 2 ≤ k := by
      by_contra! hlt
      interval_cases k <;> simp_all
    have hk' : k-1+1 = k := by omega
    have hcube := (WolstenholmeSquare.numerator_cube_at_multiple hp (by omega) (q := k-1)
      (by omega)).mp (by rwa [hk'])
    by_cases hq : p ≤ k-1
    · exact hlong p (k-1) hp (by omega) hq hcube
    · exact hshort p (k-1) hp (by omega) (by omega) (by omega) hcube

end OMA.R_OeisA7406_conjecture_R1_H2_R1
